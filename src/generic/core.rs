use super::parse::{count_lines, day_of, first, for_rows, parse_price, parse_ts, B, DAY_MS};
use super::util::{mix, new_map, Map};

const T_SHORT: u8 = 0;
const T_LONG: u8 = 1;
const T_LINK: u8 = 2;

const C: [u64; 8] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xa076_1d64_78bd_642f,
    0xe703_7ed1_a0b4_28db,
    0x8ebc_6af0_9c88_c6e3,
];

const HEX: [u8; 256] = {
    let mut t = [255u8; 256];
    let mut i = 0;
    while i < 16 {
        t[b"0123456789abcdef"[i] as usize] = i as u8;
        i += 1;
    }
    t
};

#[inline(always)]
fn r64(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[i..i + 8].try_into().unwrap())
}
#[inline(always)]
fn r32(b: &[u8], i: usize) -> u64 {
    u32::from_le_bytes(b[i..i + 4].try_into().unwrap()) as u64
}

fn fingerprint(b: &[u8]) -> [u64; 2] {
    let n = b.len();
    let (mut x, mut y) = (C[0] ^ n as u64, C[1] ^ n as u64);
    let mut i = 0;
    while i + 16 < n {
        let (p, q) = (r64(b, i), r64(b, i + 8));
        x = mix(p ^ C[2], q ^ x);
        y = mix(p ^ C[3], q ^ y);
        i += 16;
    }
    let (p, q) = (r64(b, n - 16), r64(b, n - 8));
    x = mix(p ^ C[4], q ^ x);
    y = mix(p ^ C[5], q ^ y);
    [mix(x ^ C[6], C[7]), mix(y ^ C[7], C[6])]
}

#[inline]
fn key_of(b: &[u8]) -> (u8, [u64; 2]) {
    let n = b.len();
    if n <= 15 {
        let (lo, hi) = if n >= 8 {
            (r64(b, 0), if n > 8 { r64(b, n - 8) >> (8 * (16 - n)) } else { 0 })
        } else if n >= 4 {
            (r32(b, 0) | (r32(b, n - 4) << (8 * (n - 4))), 0)
        } else if n > 0 {
            (b[0] as u64 | ((b[n >> 1] as u64) << (8 * (n >> 1))) | ((b[n - 1] as u64) << (8 * (n - 1))), 0)
        } else {
            (0, 0)
        };
        return (T_SHORT, [lo, hi | ((n as u64) << 56)]);
    }
    if n == 33 && b[0] >= 0x21 {
        let mut k = [0u64; 2];
        let mut bad = 0u8;
        for i in 0..32 {
            let v = HEX[b[i + 1] as usize];
            bad |= v;
            k[i >> 4] = (k[i >> 4] << 4) | (v & 15) as u64;
        }
        if bad < 16 {
            return (b[0], k);
        }
    }
    (T_LONG, fingerprint(b))
}

#[inline]
fn khash(tag: u8, k: [u64; 2]) -> u64 {
    mix(mix(k[0] ^ C[0], k[1] ^ C[1] ^ tag as u64) ^ C[2], C[3])
}

#[inline]
fn shard_of(h: u64, nshard: usize) -> usize {
    (h >> 52) as usize & (nshard - 1)
}

#[inline(always)]
fn prefetch<T>(p: &T) {
    unsafe { std::arch::x86_64::_mm_prefetch::<{ std::arch::x86_64::_MM_HINT_T0 }>(p as *const T as *const i8) }
}

const BLOCK: usize = 256;
const SLAB: usize = 1024;

pub struct Bins<T> {
    slabs: Vec<Vec<T>>,
    free: usize,
    cur: Vec<[*mut T; 2]>,
    blocks: Vec<Vec<*const T>>,
}
unsafe impl<T: Send> Send for Bins<T> {}
unsafe impl<T: Sync> Sync for Bins<T> {}

impl<T: Copy> Bins<T> {
    fn new(n: usize) -> Self {
        Bins { slabs: Vec::new(), free: 0, cur: vec![[std::ptr::null_mut(); 2]; n], blocks: (0..n).map(|_| Vec::new()).collect() }
    }
    #[inline]
    fn push(&mut self, s: usize, x: T) {
        if self.cur[s][0] == self.cur[s][1] {
            self.grow(s);
        }
        let c = &mut self.cur[s];
        unsafe {
            c[0].write(x);
            c[0] = c[0].add(1);
        }
    }
    #[cold]
    #[inline(never)]
    fn grow(&mut self, s: usize) {
        if self.free == 0 {
            self.slabs.push(Vec::with_capacity(BLOCK * SLAB));
            self.free = SLAB;
        }
        let slab: &mut Vec<T> = self.slabs.last_mut().unwrap();
        let p: *mut T = unsafe { slab.as_mut_ptr().add((SLAB - self.free) * BLOCK) };
        self.free -= 1;
        self.blocks[s].push(p);
        self.cur[s] = [p, unsafe { p.add(BLOCK) }];
    }
    fn len(&self, s: usize) -> usize {
        match self.blocks[s].last() {
            Some(&p) => (self.blocks[s].len() - 1) * BLOCK + unsafe { self.cur[s][0].offset_from(p) } as usize,
            None => 0,
        }
    }
    fn blocks(&self, s: usize) -> impl Iterator<Item = &[T]> {
        let b = &self.blocks[s];
        let last = self.len(s) - b.len().saturating_sub(1) * BLOCK;
        b.iter().enumerate().map(move |(j, &p)| unsafe { std::slice::from_raw_parts(p, if j + 1 == b.len() { last } else { BLOCK }) })
    }
    fn get(&self, s: usize, i: usize) -> &T {
        unsafe { &*self.blocks[s][i / BLOCK].add(i % BLOCK) }
    }
}

#[derive(Default)]
struct Tab32 {
    slots: Vec<u32>,
    bits: u32,
}
impl Tab32 {
    fn reset(&mut self, n: usize) {
        self.bits = usize::BITS - n.leading_zeros();
        self.slots.clear();
        self.slots.resize((2 * n).next_power_of_two().max(16), 0);
    }
    #[inline]
    fn find(&self, h: u64, mut eq: impl FnMut(u32) -> bool) -> Result<(usize, u32), usize> {
        let mask = self.slots.len() - 1;
        let tag = ((h >> 32) << self.bits) as u32;
        let mut i = h as usize & mask;
        loop {
            let s = self.slots[i];
            if s == 0 {
                return Err(i);
            }
            if (s ^ tag) >> self.bits == 0 {
                let idx = (s ^ tag) - 1;
                if eq(idx) {
                    return Ok((i, idx));
                }
            }
            i = (i + 1) & mask;
        }
    }
    #[inline]
    fn set(&mut self, slot: usize, h: u64, idx: u32) {
        self.slots[slot] = ((h >> 32) << self.bits) as u32 | (idx + 1);
    }
}


#[derive(Clone, Copy)]
pub struct Id<'a> {
    k: [u64; 2],
    tag: u8,
    text: B<'a>,
}

#[derive(Clone, Copy)]
#[repr(align(32))]
struct Slot {
    k: [u64; 2],
    tag: u8,
    name: u32,
}

pub struct LinkMap<'a> {
    slots: Vec<Slot>,
    ids: Vec<B<'a>>,
}

impl LinkMap<'_> {
    #[inline]
    fn prefetch(&self, h: u64) {
        prefetch(&self.slots[h as usize & (self.slots.len() - 1)]);
    }
    #[inline]
    fn person(&self, tag: u8, k: [u64; 2], h: u64) -> (u8, [u64; 2]) {
        let mask = self.slots.len() - 1;
        let mut i = h as usize & mask;
        loop {
            let s = &self.slots[i];
            if s.name == 0 {
                return (tag, k);
            }
            if s.k == k && s.tag == tag {
                return (T_LINK, [(s.name - 1) as u64, 0]);
            }
            i = (i + 1) & mask;
        }
    }
}

fn find(parent: &mut [u32], mut x: u32) -> u32 {
    let mut r = x;
    while parent[r as usize] != r {
        r = parent[r as usize];
    }
    while parent[x as usize] != r {
        let n = parent[x as usize];
        parent[x as usize] = r;
        x = n;
    }
    r
}

pub type LinkPart<'a> = Vec<[Id<'a>; 2]>;

pub fn parse_links(c: B<'_>) -> LinkPart<'_> {
    let mut v = Vec::with_capacity(count_lines(c) + 1);
    for_rows(c, |_, ab: [B; 2]| {
        if !ab[0].is_empty() && !ab[1].is_empty() {
            v.push(ab.map(|text| {
                let (tag, k) = key_of(text);
                Id { k, tag, text }
            }));
        }
    });
    v
}

pub fn build_links<'a>(parts: &[LinkPart<'a>]) -> LinkMap<'a> {
    let n: usize = parts.iter().map(|p| p.len()).sum();
    let mask = (4 * n).next_power_of_two().max(16) - 1;
    let mut slots = vec![Slot { k: [0; 2], tag: 0, name: 0 }; mask + 1];
    let mut ids: Vec<B<'a>> = Vec::with_capacity(n + n / 2);
    let mut parent: Vec<u32> = Vec::with_capacity(n + n / 2);
    for p in parts {
        for blk in p.chunks(16) {
            for id in blk.iter().flatten() {
                prefetch(&slots[khash(id.tag, id.k) as usize & mask]);
            }
            for l in blk {
                let xy: [u32; 2] = l.map(|id| {
                    let mut i = khash(id.tag, id.k) as usize & mask;
                    loop {
                        let s = &mut slots[i];
                        if s.name == 0 {
                            parent.push(ids.len() as u32);
                            ids.push(id.text);
                            *s = Slot { k: id.k, tag: id.tag, name: ids.len() as u32 };
                        }
                        if s.k == id.k && s.tag == id.tag {
                            return s.name - 1;
                        }
                        i = (i + 1) & mask;
                    }
                });
                let rx = find(&mut parent, xy[0]);
                let ry = find(&mut parent, xy[1]);
                if rx < ry {
                    parent[ry as usize] = rx
                } else {
                    parent[rx as usize] = ry
                }
            }
        }
    }
    let m = ids.len();
    let mut min_of: Vec<u32> = (0..m as u32).collect();
    for i in 0..m as u32 {
        let r = find(&mut parent, i) as usize;
        if ids[i as usize] < ids[min_of[r] as usize] {
            min_of[r] = i;
        }
    }
    for s in &mut slots {
        if s.name != 0 {
            s.name = min_of[parent[s.name as usize - 1] as usize] + 1;
        }
    }
    LinkMap { slots, ids }
}


pub const T_VIEW: u32 = 0;
pub const T_CART: u32 = 1;
pub const T_PURCHASE: u32 = 2;
pub const T_INVALID: u32 = 255;

#[derive(Clone, Copy)]
pub struct Ev {
    eid: [u64; 2],
    user: [u64; 2],
    ingest: i64,
    ts: u32,
    pt: u32,
    cat: u32,
    etag: u8,
    utag: u8,
    chunk: u16,
}

#[derive(Clone, Copy)]
pub struct Rec {
    k: [u64; 2],
    ts: u32,
    pt: u32,
    cat: u32,
    tag: u8,
}

#[derive(Clone, Copy)]
pub struct Ck<'a> {
    k: [u64; 2],
    line: &'a u8,
    ts: u32,
    camp: u32,
    tag: u8,
}

pub struct Parsed<'a> {
    ev: Bins<Ev>,
    pub ck: Vec<Ck<'a>>,
    pub side: Vec<Vec<u8>>,
}
impl Parsed<'_> {
    pub fn new(nshard: usize) -> Self {
        Parsed { ev: Bins::new(nshard), ck: Vec::new(), side: vec![Vec::new(); nshard] }
    }
}

pub struct EvCtx<'m, 'a> {
    pub lo: i64,
    pub ws: i64,
    pub we: i64,
    pub products: &'m Map<B<'a>, u32>,
    pub unknown_cat: u32,
}

pub fn parse_events(c: B<'_>, chunk: u16, ctx: &EvCtx<'_, '_>, out: &mut Parsed<'_>) {
    let nshard = out.side.len();
    for_rows(c, |_, [eid, user, ts, ingest, typ, product, price]: [B; 7]| {
        if eid.is_empty() {
            return;
        }
        let Some(ingest) = parse_ts(ingest) else { return };
        let (etag, ek) = key_of(eid);
        let mut e = Ev { eid: ek, user: [0; 2], ingest, ts: 0, pt: T_INVALID << 24, cat: 0, etag, utag: 0, chunk };
        'v: {
            if user.is_empty() || product.is_empty() {
                break 'v;
            }
            let Some(t) = parse_ts(ts) else { break 'v };
            if t < ctx.ws || t >= ctx.we {
                break 'v;
            }
            let ty = match typ {
                b"view" => T_VIEW,
                b"cart" => T_CART,
                b"purchase" => T_PURCHASE,
                _ => break 'v,
            };
            let mut pr = 0u32;
            if ty == T_PURCHASE {
                let Some(p) = parse_price(price) else { break 'v };
                pr = p;
                e.cat = *ctx.products.get(product).unwrap_or(&ctx.unknown_cat);
            }
            if ingest - t > DAY_MS {
                break 'v;
            }
            (e.utag, e.user) = key_of(user);
            if e.utag == T_LONG {
                let side = &mut out.side[shard_of(khash(T_LONG, e.user), nshard)];
                side.extend_from_slice(&e.user[0].to_le_bytes());
                side.extend_from_slice(&e.user[1].to_le_bytes());
                side.extend_from_slice(&(user.len() as u32).to_le_bytes());
                side.extend_from_slice(user);
            }
            e.ts = (t - ctx.lo) as u32;
            e.pt = pr | (ty << 24);
        }
        out.ev.push(shard_of(khash(etag, ek), nshard), e);
    });
}

pub struct Routed<'a> {
    rec: Bins<Rec>,
    ck: Bins<Ck<'a>>,
    tab: Tab32,
    lose: Vec<u32>,
}
impl Routed<'_> {
    pub fn new(nshard: usize) -> Self {
        Routed { rec: Bins::new(nshard), ck: Bins::new(nshard), tab: Tab32::default(), lose: Vec::new() }
    }
}

const BATCH: usize = 32;

pub fn dedup_route(parsed: &[Parsed<'_>], s: usize, links: &LinkMap<'_>, nshard: usize, out: &mut Routed<'_>) {
    let total: usize = parsed.iter().map(|p| p.ev.len(s)).sum();
    let at = |mut i: usize| -> &Ev {
        for p in parsed {
            let n = p.ev.len(s);
            if i < n {
                return p.ev.get(s, i);
            }
            i -= n;
        }
        unreachable!()
    };
    out.tab.reset(total);
    out.lose.clear();
    let mut flat = 0u32;
    for p in parsed {
        for blk in p.ev.blocks(s) {
            for e in blk {
                let h = khash(e.etag, e.eid);
                match out.tab.find(h, |i| {
                    let o = at(i as usize);
                    o.eid == e.eid && o.etag == e.etag
                }) {
                    Ok((slot, i)) => {
                        let o = at(i as usize);
                        if e.ingest < o.ingest || (e.ingest == o.ingest && e.chunk < o.chunk) {
                            out.lose.push(i);
                            out.tab.set(slot, h, flat);
                        } else {
                            out.lose.push(flat);
                        }
                    }
                    Err(slot) => out.tab.set(slot, h, flat),
                }
                flat += 1;
            }
        }
    }
    out.lose.sort_unstable();
    let mut hs = [0u64; BATCH];
    let mut flat = 0u32;
    let mut li = 0usize;
    for p in parsed {
        for blk in p.ev.blocks(s) {
            for sub in blk.chunks(BATCH) {
                let mut keep = 0u32;
                for (i, e) in sub.iter().enumerate() {
                    flat += 1;
                    if li < out.lose.len() && out.lose[li] == flat - 1 {
                        li += 1;
                        continue;
                    }
                    if (e.pt >> 24) > T_PURCHASE {
                        continue;
                    }
                    hs[i] = khash(e.utag, e.user);
                    links.prefetch(hs[i]);
                    keep |= 1 << i;
                }
                while keep != 0 {
                    let i = keep.trailing_zeros() as usize;
                    keep &= keep - 1;
                    let e = &sub[i];
                    let (tag, k) = links.person(e.utag, e.user, hs[i]);
                    let h = if tag == T_LINK { khash(tag, k) } else { hs[i] };
                    out.rec.push(shard_of(h, nshard), Rec { k, ts: e.ts, pt: e.pt, cat: e.cat, tag });
                }
            }
        }
    }
}

pub fn parse_clicks<'a>(c: B<'a>, lo: i64, we: i64, campaigns: &Map<B<'_>, u32>, out: &mut Vec<Ck<'a>>) {
    for_rows(c, |line, [cid, user, camp, ts]: [B; 4]| {
        if cid.is_empty() || user.is_empty() {
            return;
        }
        let Some(t) = parse_ts(ts) else { return };
        if t < lo || t >= we {
            return;
        }
        let Some(&camp) = campaigns.get(camp) else { return };
        let (tag, k) = key_of(user);
        out.push(Ck { k, line: line, ts: (t - lo) as u32, camp, tag });
    });
}

pub fn route_clicks<'a>(v: &[Ck<'a>], links: &LinkMap<'_>, nshard: usize, out: &mut Routed<'a>) {
    let mut hs = [0u64; BATCH];
    for sub in v.chunks(BATCH) {
        for (i, c) in sub.iter().enumerate() {
            hs[i] = khash(c.tag, c.k);
            links.prefetch(hs[i]);
        }
        for (i, c) in sub.iter().enumerate() {
            let (tag, k) = links.person(c.tag, c.k, hs[i]);
            let h = if tag == T_LINK { khash(tag, k) } else { hs[i] };
            out.ck.push(shard_of(h, nshard), Ck { k, tag, ..*c });
        }
    }
}


pub const GAP_MS: i64 = 1_800_000;
pub const WEEK_MS: i64 = 7 * 86_400_000;

pub type Acc = Map<u64, [u64; 4]>;

#[inline]
pub fn key(camp: u32, day: i32) -> u64 {
    ((camp as u64) << 32) | (day as u32 as u64)
}
pub fn unkey(k: u64) -> (u32, i32) {
    ((k >> 32) as u32, k as u32 as i32)
}

struct Sess {
    start: i64,
    day: i32,
    rev: u64,
    purch: bool,
}

pub struct UserRow {
    pub person: u32,
    pub day: i32,
    pub sessions: u64,
    pub events: u64,
    pub revenue: u64,
    pub top: Option<u32>,
}

struct Scratch {
    sess: Vec<Sess>,
    starts: Vec<i64>,
    days: Vec<i32>,
    day_end: Vec<u32>,
    catsum: Vec<u64>,
    touched: Vec<u32>,
    ct: Vec<(u32, i64)>,
    win: Vec<u32>,
}

struct DayAcc {
    day: i32,
    sessions: u64,
    events: u64,
    revenue: u64,
}

fn flush_row(person: u32, d: &DayAcc, sc: &mut Scratch, rows: &mut Vec<UserRow>) {
    let mut top: Option<u32> = None;
    let mut best = 0u64;
    for &c in &sc.touched {
        let v = sc.catsum[c as usize];
        if top.is_none() || v > best || (v == best && c < top.unwrap()) {
            top = Some(c);
            best = v;
        }
        sc.catsum[c as usize] = 0;
    }
    sc.touched.clear();
    rows.push(UserRow { person, day: d.day, sessions: d.sessions, events: d.events, revenue: d.revenue, top });
}

struct PersonCtx<'s, 'a> {
    purch: &'s [(u32, u32)],
    cl: &'s [(u32, &'a u8)],
    lo: i64,
    organic: u32,
}

fn person(pid: u32, evs: &mut [u64], cks: &mut [u64], cx: &PersonCtx<'_, '_>, sc: &mut Scratch, rows: &mut Vec<UserRow>, acc: &mut Acc) {
    evs.sort_unstable();
    sc.sess.clear();
    let mut d = DayAcc { day: 0, sessions: 0, events: 0, revenue: 0 };
    let mut prev = 0i64;
    for (i, &e) in evs.iter().enumerate() {
        let ts = (e >> 32) as i64;
        if i == 0 || ts - prev > GAP_MS {
            let day = day_of(cx.lo + ts);
            if day != d.day {
                if i > 0 {
                    flush_row(pid, &d, sc, rows);
                }
                d = DayAcc { day, sessions: 0, events: 0, revenue: 0 };
            }
            d.sessions += 1;
            sc.sess.push(Sess { start: ts, day, rev: 0, purch: false });
        }
        prev = ts;
        d.events += 1;
        if e as u32 != 0 {
            let (price, cat) = cx.purch[e as u32 as usize - 1];
            let price = price as u64;
            let s = sc.sess.last_mut().unwrap();
            s.rev += price;
            s.purch = true;
            d.revenue += price;
            if sc.catsum[cat as usize] == 0 {
                sc.touched.push(cat);
            }
            sc.catsum[cat as usize] += price;
        }
    }
    flush_row(pid, &d, sc, rows);

    cks.sort_unstable();
    sc.win.clear();
    let mut i = 0;
    while i < cks.len() {
        let mut best = cx.cl[cks[i] as u32 as usize];
        let mut j = i + 1;
        while j < cks.len() && cks[j] >> 32 == cks[i] >> 32 {
            let c = cx.cl[cks[j] as u32 as usize];
            if unsafe { first(c.1) < first(best.1) } {
                best = c;
            }
            j += 1;
        }
        sc.win.resize(j, best.0);
        i = j;
    }
    credit(&sc.sess, cks, &sc.win, cx.organic, acc);
    if !cks.is_empty() {
        sc.starts.clear();
        sc.days.clear();
        sc.starts.extend(sc.sess.iter().map(|s| s.start));
        sc.days.extend(sc.sess.iter().map(|s| s.day));
        let n = sc.sess.len();
        sc.day_end.clear();
        sc.day_end.resize(n, 0);
        let mut end = n as u32;
        for i in (0..n).rev() {
            if i + 1 < n && sc.days[i + 1] != sc.days[i] {
                end = (i + 1) as u32;
            }
            sc.day_end[i] = end;
        }
        sc.ct.clear();
        sc.ct.extend(cks.iter().map(|&c| (cx.cl[c as u32 as usize].0, (c >> 32) as i64)));
        sc.ct.sort_unstable();
        assists(&sc.starts, &sc.days, &sc.day_end, &sc.ct, acc);
    }
}

#[derive(Default)]
struct ShardBufs<'a> {
    tab: Tab32,
    keys: Vec<(u8, [u64; 2])>,
    tmp: Vec<(u32, u64)>,
    off: Vec<u32>,
    pos: Vec<u32>,
    pe: Vec<u64>,
    purch: Vec<(u32, u32)>,
    cl: Vec<(u32, &'a u8)>,
    coff: Vec<u32>,
    pc: Vec<u64>,
}

pub struct Worker<'a> {
    sc: Scratch,
    bf: ShardBufs<'a>,
    pub name_off: Vec<u32>,
    pub name_data: Vec<u8>,
    pub rows: Vec<UserRow>,
    pub acc: Acc,
}
impl Worker<'_> {
    pub fn new(ncat: usize) -> Self {
        Worker {
            sc: Scratch { sess: vec![], starts: vec![], days: vec![], day_end: vec![], catsum: vec![0; ncat], touched: vec![], ct: vec![], win: vec![] },
            bf: ShardBufs::default(),
            name_off: vec![0],
            name_data: Vec::new(),
            rows: Vec::new(),
            acc: Acc::default(),
        }
    }
}

fn group(tmp: &[(u32, u64)], off: &mut [u32], pos: &mut Vec<u32>, out: &mut Vec<u64>) {
    let np = off.len() - 1;
    for i in 0..np {
        off[i + 1] += off[i];
    }
    pos.clear();
    pos.extend_from_slice(&off[..np]);
    out.clear();
    out.resize(tmp.len(), 0);
    for &(pid, k) in tmp {
        let q = &mut pos[pid as usize];
        out[*q as usize] = k;
        *q += 1;
    }
}

pub fn run_shard<'a>(routed: &[Routed<'a>], sides: &[Vec<Vec<u8>>], links: &LinkMap<'_>, p: usize, lo: i64, organic: u32, w: &mut Worker<'a>) {
    let Worker { sc, bf, name_off, name_data, rows, acc } = w;
    let n_ev: usize = routed.iter().map(|r| r.rec.len(p)).sum();
    bf.tab.reset(n_ev);
    bf.keys.clear();
    bf.tmp.clear();
    bf.purch.clear();
    bf.off.clear();
    bf.off.push(0);
    for r in routed {
        for blk in r.rec.blocks(p) {
            for e in blk {
                let h = khash(e.tag, e.k);
                let pid = match bf.tab.find(h, |i| bf.keys[i as usize] == (e.tag, e.k)) {
                    Ok((_, i)) => i,
                    Err(slot) => {
                        let i = bf.keys.len() as u32;
                        bf.keys.push((e.tag, e.k));
                        bf.off.push(0);
                        bf.tab.set(slot, h, i);
                        i
                    }
                };
                bf.off[pid as usize + 1] += 1;
                let mut k = (e.ts as u64) << 32;
                if e.pt >> 24 == T_PURCHASE {
                    bf.purch.push((e.pt & 0x00ff_ffff, e.cat));
                    k |= bf.purch.len() as u64;
                }
                bf.tmp.push((pid, k));
            }
        }
    }
    let np = bf.keys.len();
    group(&bf.tmp, &mut bf.off, &mut bf.pos, &mut bf.pe);
    bf.tmp.clear();
    bf.cl.clear();
    bf.coff.clear();
    bf.coff.resize(np + 1, 0);
    for r in routed {
        for blk in r.ck.blocks(p) {
            for c in blk {
                if let Ok((_, pid)) = bf.tab.find(khash(c.tag, c.k), |i| bf.keys[i as usize] == (c.tag, c.k)) {
                    bf.coff[pid as usize + 1] += 1;
                    bf.tmp.push((pid, (c.ts as u64) << 32 | bf.cl.len() as u64));
                    bf.cl.push((c.camp, c.line));
                }
            }
        }
    }
    group(&bf.tmp, &mut bf.coff, &mut bf.pos, &mut bf.pc);
    let cx = PersonCtx { purch: &bf.purch, cl: &bf.cl, lo, organic };
    let mut side: Option<Map<(u64, u64), &[u8]>> = None;
    for i in 0..np {
        let (tag, k) = bf.keys[i];
        match tag {
            T_SHORT => {
                let mut b = [0u8; 16];
                b[..8].copy_from_slice(&k[0].to_le_bytes());
                b[8..].copy_from_slice(&k[1].to_le_bytes());
                name_data.extend_from_slice(&b[..b[15] as usize]);
            }
            T_LONG => {
                let m = side.get_or_insert_with(|| {
                    let mut m = new_map(0);
                    for t in sides {
                        let mut b = &t[p][..];
                        while !b.is_empty() {
                            let n = r32(b, 16) as usize;
                            m.insert((r64(b, 0), r64(b, 8)), &b[20..20 + n]);
                            b = &b[20 + n..];
                        }
                    }
                    m
                });
                name_data.extend_from_slice(m[&(k[0], k[1])]);
            }
            T_LINK => name_data.extend_from_slice(links.ids[k[0] as usize]),
            _ => {
                name_data.push(tag);
                for word in k {
                    name_data.extend((0..16).map(|j| b"0123456789abcdef"[(word >> (60 - 4 * j)) as usize & 15]));
                }
            }
        }
        let pid = name_off.len() as u32 - 1;
        name_off.push(name_data.len() as u32);
        let evs = &mut bf.pe[bf.off[i] as usize..bf.off[i + 1] as usize];
        let cks = &mut bf.pc[bf.coff[i] as usize..bf.coff[i + 1] as usize];
        person(pid, evs, cks, &cx, sc, rows, acc);
    }
}


fn credit(sess: &[Sess], cks: &[u64], win: &[u32], organic: u32, acc: &mut Acc) {
    let n = cks.len();
    let (mut lo, mut hi) = (0usize, 0usize);
    for s in sess {
        while hi < n && (cks[hi] >> 32) as i64 <= s.start {
            hi += 1;
        }
        while lo < hi && ((cks[lo] >> 32) as i64) < s.start - WEEK_MS {
            lo += 1;
        }
        let camp = if hi > lo { win[hi - 1] } else { organic };
        let a = acc.entry(key(camp, s.day)).or_default();
        a[0] += 1;
        a[1] += s.purch as u64;
        a[2] += s.rev;
    }
}

fn assists(starts: &[i64], days: &[i32], day_end: &[u32], ct: &[(u32, i64)], acc: &mut Acc) {
    let n = ct.len();
    let mut flush = |camp: u32, a: i64, b: i64| {
        let lo = starts.partition_point(|&s| s < a);
        let hi = starts.partition_point(|&s| s <= b);
        let mut k = lo;
        while k < hi {
            let e = (day_end[k] as usize).min(hi);
            acc.entry(key(camp, days[k])).or_insert([0; 4])[3] += (e - k) as u64;
            k = e;
        }
    };
    let mut i = 0;
    while i < n {
        let camp = ct[i].0;
        let a = ct[i].1;
        let mut b = a + WEEK_MS;
        i += 1;
        while i < n && ct[i].0 == camp && ct[i].1 <= b {
            b = b.max(ct[i].1 + WEEK_MS);
            i += 1;
        }
        flush(camp, a, b);
    }
}
