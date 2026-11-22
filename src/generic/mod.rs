mod core;
mod parse;
use crate::pqw;
mod util;

use self::core::*;
use self::parse::{chunk_target, chunks, for_rows, B};
use self::util::{map_dir, par_run, Mapped};
use std::io;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

const SHARD_BYTES: usize = 4 << 20;

fn take<T: Default>(m: &Mutex<T>) -> T {
    std::mem::take(&mut *m.lock().unwrap_or_else(|e| e.into_inner()))
}

pub fn run(data_dir: &Path, out_dir: &Path, ncpu: usize) -> io::Result<()> {
    let ncpu = ncpu.max(1);
    let log = std::env::var_os("V1ND_LOG").is_some();
    let t0 = std::time::Instant::now();
    let mut last = t0;
    let mut lap = |what: &str| {
        if log {
            let now = std::time::Instant::now();
            eprintln!("[v1nd] {what:<12} {:>8.1} ms (total {:>8.1} ms)", (now - last).as_secs_f64() * 1e3, (now - t0).as_secs_f64() * 1e3);
            last = now;
        }
    };
    let man = Mapped::open(&data_dir.join("manifest.json"))?;
    let prodm = Mapped::open(&data_dir.join("products.csv"))?;
    let campm = Mapped::open(&data_dir.join("campaigns.csv"))?;
    let evm = map_dir(&data_dir.join("events"))?;
    let ckm = map_dir(&data_dir.join("clicks"))?;
    let lkm = map_dir(&data_dir.join("links"))?;
    let (ws, we) = parse::manifest(man.bytes())?;

    let mut prod_rows: Vec<(B, B)> = Vec::new();
    for c in chunks(&[prodm.bytes()], usize::MAX / 2) {
        for_rows(c, |_, [p, cat]: [B; 2]| prod_rows.push((p, cat)));
    }
    let mut cats = Names::new(0);
    let mut cat_first: Vec<B> = vec![b"unknown"];
    cats.insert(b"unknown", 0);
    let cat_of: Vec<u32> = prod_rows
        .iter()
        .map(|&(_, c)| {
            let id = cats.insert(c, cat_first.len() as u32);
            if id as usize == cat_first.len() {
                cat_first.push(c);
            }
            id
        })
        .collect();
    let mut cat_names = cat_first.clone();
    cat_names.sort_unstable();
    let rank: Vec<u32> = cat_first.iter().map(|c| cat_names.binary_search(c).unwrap() as u32).collect();
    let mut products = Names::new(prod_rows.len());
    for (&(p, _), &c) in prod_rows.iter().zip(&cat_of) {
        products.insert(p, rank[c as usize]);
    }
    let unknown_cat = rank[0];
    drop(prod_rows);
    let mut camp_ids: Vec<B> = Vec::new();
    let mut channels: Vec<B> = Vec::new();
    let mut campaigns = Names::new(0);
    for c in chunks(&[campm.bytes()], usize::MAX / 2) {
        for_rows(c, |_, [id, ch]: [B; 2]| {
            if campaigns.insert(id, camp_ids.len() as u32) as usize == camp_ids.len() {
                camp_ids.push(id);
                channels.push(ch);
            }
        });
    }
    let organic = camp_ids.len() as u32;
    camp_ids.push(b"organic");
    channels.push(b"organic");

    let ev_files: Vec<B> = evm.iter().map(|m| m.bytes()).collect();
    let ck_files: Vec<B> = ckm.iter().map(|m| m.bytes()).collect();
    let lk_files: Vec<B> = lkm.iter().map(|m| m.bytes()).collect();
    let ev_chunks = chunks(&ev_files, chunk_target(&ev_files, ncpu));
    let ck_chunks = chunks(&ck_files, chunk_target(&ck_files, ncpu));
    let lk_chunks = chunks(&lk_files, chunk_target(&lk_files, ncpu));
    let lo = ws - WEEK_MS;
    if we - lo > u32::MAX as i64 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "manifest: window too long"));
    }
    let ev_bytes: usize = ev_files.iter().map(|f| f.len()).sum();
    let nshard = (ev_bytes / SHARD_BYTES).next_power_of_two().min(4096);
    let huge = true;
    lap("setup");

    let ectx = EvCtx { lo, ws, we, products, unknown_cat };
    let (nl, ne, nc) = (lk_chunks.len(), ev_chunks.len(), ck_chunks.len());
    let lk_parts: Vec<Mutex<LinkPart>> = (0..nl).map(|_| Mutex::new(Vec::new())).collect();
    let lk_done = AtomicUsize::new(0);
    let links_slot: Mutex<Option<LinkMap>> = Mutex::new(None);
    let (_, mut parsed) = par_run(nl + ne, ncpu, || Parsed::new(nshard, huge), |st, i| {
        if i < nl {
            prefault(lk_chunks[i]);
            let v = parse_links(lk_chunks[i]);
            *lk_parts[i].lock().unwrap() = v;
            if lk_done.fetch_add(1, Ordering::AcqRel) + 1 == nl {
                let parts: Vec<LinkPart> = lk_parts.iter().map(take).collect();
                let lm = build_links(&parts, huge);
                *links_slot.lock().unwrap() = Some(lm);
            }
        } else {
            prefault(ev_chunks[i - nl]);
            parse_events(ev_chunks[i - nl], (i - nl) as u16, &ectx, st);
            release(ev_chunks[i - nl]);
        }
    });
    parsed.iter_mut().for_each(Parsed::finish);
    let links = links_slot.into_inner().unwrap().unwrap_or_else(|| build_links(&[], huge));
    drop(lk_parts);
    lap("parse+links");

    let cctx = CkCtx { lo, we, campaigns, links: &links };
    let (_, mut routed) = par_run(nshard + nc, ncpu, || Routed::new(nshard, huge), |st, i| {
        if i < nshard {
            dedup_route(&parsed, i, &links, nshard, st);
        } else {
            prefault(ck_chunks[i - nshard]);
            parse_clicks(ck_chunks[i - nshard], &cctx, nshard, st);
        }
    });
    routed.iter_mut().for_each(Routed::finish);
    lap("dedup+route");

    let day0 = parse::day_of(ws);
    let ndays = (parse::day_of(we - 1) - day0 + 1).max(1) as usize;
    let (_, workers) = par_run(nshard, ncpu, || Worker::new(cat_names.len(), camp_ids.len(), day0, ndays), |w, p| run_shard(&routed, &parsed, &links, p, lo, organic, w));
    let mut cells: Vec<[u64; 4]> = vec![[0; 4]; camp_ids.len() * ndays];
    for w in &workers {
        for ((c, v), a) in cells.iter_mut().zip(&w.acc.credit).zip(&w.acc.assist) {
            *c = [c[0] + v.0 as u64, c[1] + v.1 as u64, c[2] + v.2, c[3] + *a as u64];
        }
    }
    lap("sessions");
    let ud = out_dir.join("user_daily");
    let cd = out_dir.join("campaign_daily");
    std::fs::create_dir_all(&ud)?;
    std::fs::create_dir_all(&cd)?;
    clear_parquet(&ud)?;
    clear_parquet(&cd)?;
    let mut jobs: Vec<Box<dyn FnOnce() -> io::Result<()> + Send + '_>> = Vec::new();
    for (k, w) in workers.iter().enumerate() {
        let (ud, cat_names) = (&ud, &cat_names);
        jobs.push(Box::new(move || write_users(&ud.join(format!("part-{k}.parquet")), w, cat_names)));
    }
    jobs.push(Box::new(|| write_campaigns(&cd.join("part-0.parquet"), &cells, day0, ndays, &camp_ids, &channels)));
    jobs.push(Box::new(move || Ok(links.release())));
    for r in routed {
        jobs.push(Box::new(move || Ok(r.release())));
    }
    for p in parsed {
        jobs.push(Box::new(move || Ok(p.release())));
    }
    let jobs: Vec<Mutex<Option<Box<dyn FnOnce() -> io::Result<()> + Send + '_>>>> = jobs.into_iter().map(|j| Mutex::new(Some(j))).collect();
    let (res, _) = par_run(jobs.len(), ncpu, || (), |_, k| take(&jobs[k]).unwrap()());
    drop(jobs);
    for r in res {
        r?;
    }
    lap("write");
    drop(workers);
    drop(cells);
    lap("free");
    Ok(())
}

fn clear_parquet(dir: &Path) -> io::Result<()> {
    for e in std::fs::read_dir(dir)? {
        let e = e?;
        let p = e.path();
        if e.file_type()?.is_file() && p.extension().is_some_and(|x| x == "parquet") {
            std::fs::remove_file(&p)?;
        }
    }
    Ok(())
}

struct StrBuf {
    off: Vec<u32>,
    data: Vec<u8>,
}
impl StrBuf {
    fn new(n: usize, bytes: usize) -> StrBuf {
        let mut off = Vec::with_capacity(n + 1);
        off.push(0);
        StrBuf { off, data: Vec::with_capacity(bytes) }
    }
    fn push(&mut self, s: &[u8]) {
        self.data.extend_from_slice(s);
        self.off.push(self.data.len() as u32);
    }
    fn col(&self) -> pqw::StrCol<'_> {
        pqw::StrCol { offsets: &self.off, data: &self.data }
    }
}

const STREAM: pqw::Method = pqw::Method::Stream(1 << 20);

fn write_users(path: &Path, w: &Worker, cat_names: &[B]) -> io::Result<()> {
    use pqw::*;
    let r = &w.rows;
    let mut cats = StrBuf::new(cat_names.len(), 0);
    for c in cat_names {
        cats.push(c);
    }
    let ncat = cat_names.len();
    let top8: Vec<u8>;
    let top16: Vec<u16>;
    let tkeys = if ncat < u8::MAX as usize {
        top8 = r.top.iter().map(|&t| if t == u32::MAX { u8::MAX } else { t as u8 }).collect();
        Keys::U8(&top8)
    } else if ncat < u16::MAX as usize {
        top16 = r.top.iter().map(|&t| if t == u32::MAX { u16::MAX } else { t as u16 }).collect();
        Keys::U16(&top16)
    } else {
        Keys::U32(&r.top)
    };
    let cols = [
        Column { name: "user_id", data: Data::Dict { dict: StrCol { offsets: &w.name_off, data: &w.name_data }, keys: Keys::U32(&r.person), nullable: false, plain: false } },
        Column { name: "day", data: Data::Date(&r.day, IntEnc::Dense) },
        Column { name: "sessions", data: Data::I64(&r.sessions, IntEnc::Auto) },
        Column { name: "events", data: Data::I64(&r.events, IntEnc::Auto) },
        Column { name: "revenue_cents", data: Data::I64(&r.revenue, IntEnc::Plain) },
        Column { name: "top_category", data: Data::Dict { dict: cats.col(), keys: tkeys, nullable: true, plain: false } },
    ];
    write_file(path, &cols, &Opts::default(), STREAM)?;
    Ok(())
}

fn write_campaigns(path: &Path, cells: &[[u64; 4]], day0: i32, ndays: usize, camp_ids: &[B], channels: &[B]) -> io::Result<()> {
    use pqw::*;
    let n = cells.iter().filter(|v| **v != [0; 4]).count();
    let mut cid = StrBuf::new(n, n * 8);
    let mut ch = StrBuf::new(n, n * 8);
    let mut day = Vec::with_capacity(n);
    let mut s = Vec::with_capacity(n);
    let mut ps = Vec::with_capacity(n);
    let mut rev = Vec::with_capacity(n);
    let mut asst = Vec::with_capacity(n);
    for (i, v) in cells.iter().enumerate() {
        if *v == [0; 4] {
            continue;
        }
        cid.push(camp_ids[i / ndays]);
        ch.push(channels[i / ndays]);
        day.push(day0 + (i % ndays) as i32);
        s.push(v[0] as i64);
        ps.push(v[1] as i64);
        rev.push(v[2] as i64);
        asst.push(v[3] as i64);
    }
    let cols = [
        Column { name: "campaign_id", data: Data::Str(cid.col()) },
        Column { name: "channel", data: Data::Str(ch.col()) },
        Column { name: "day", data: Data::Date(&day, IntEnc::Dense) },
        Column { name: "sessions", data: Data::I64(&s, IntEnc::Auto) },
        Column { name: "purchasing_sessions", data: Data::I64(&ps, IntEnc::Auto) },
        Column { name: "revenue_cents", data: Data::I64(&rev, IntEnc::Plain) },
        Column { name: "assisted_sessions", data: Data::I64(&asst, IntEnc::Auto) },
    ];
    write_file(path, &cols, &Opts::default(), STREAM)?;
    Ok(())
}
