use super::parse::{count_lines, day_of, first, for_rows, parse_price, parse_ts, B, DAY_MS};
use super::util::{mix, new_map, Map};
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::arch::x86_64::*;
use std::mem::MaybeUninit;

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
        if let Some(k) = hex32(b[1..].try_into().unwrap()) {
            return (b[0], k);
        }
    }
    (T_LONG, fingerprint(b))
}

#[inline]
fn hex32(b: &[u8; 32]) -> Option<[u64; 2]> {
    unsafe {
        let v = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
        let d = _mm256_sub_epi8(v, _mm256_set1_epi8(b'0' as i8));
        let a = _mm256_sub_epi8(v, _mm256_set1_epi8(b'a' as i8));
        let is_d = _mm256_cmpeq_epi8(_mm256_min_epu8(d, _mm256_set1_epi8(9)), d);
        let is_a = _mm256_cmpeq_epi8(_mm256_min_epu8(a, _mm256_set1_epi8(5)), a);
        if _mm256_movemask_epi8(_mm256_or_si256(is_d, is_a)) != -1 {
            return None;
        }
        let nib = _mm256_blendv_epi8(_mm256_add_epi8(a, _mm256_set1_epi8(10)), d, is_d);
        let pair = _mm256_maddubs_epi16(nib, _mm256_set1_epi16(0x0110));
        let bytes = _mm256_packus_epi16(pair, pair);
        Some([(_mm256_extract_epi64::<0>(bytes) as u64).swap_bytes(), (_mm256_extract_epi64::<2>(bytes) as u64).swap_bytes()])
    }
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
    unsafe { _mm_prefetch::<_MM_HINT_T0>(p as *const T as *const i8) }
}

const BLOCK: usize = 16 << 10;
const SLAB: usize = 16 << 20;
const STAGE: usize = 8;

extern "C" {
    fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
}

const MADV_DONTNEED: i32 = 4;
const MADV_HUGEPAGE: i32 = 14;
const MADV_POPULATE_READ: i32 = 22;
const MADV_POPULATE_WRITE: i32 = 23;

fn advise<T>(p: *const T, n: usize, advice: i32) {
    let a = (p as usize + 4095) & !4095;
    let e = (p as usize + n * std::mem::size_of::<T>()) & !4095;
    if e > a {
        unsafe { madvise(a as *mut u8, e - a, advice) };
    }
}

pub fn prefault(c: B<'_>) {
    advise(c.as_ptr(), c.len(), MADV_POPULATE_READ);
}

pub fn release(c: B<'_>) {
    advise(c.as_ptr(), c.len(), MADV_DONTNEED);
}

pub fn huge_pages(need: usize) -> bool {
    let free: usize = std::fs::read_to_string("/proc/buddyinfo")
        .unwrap_or_default()
        .lines()
        .flat_map(|l| l.split_ascii_whitespace().skip(4).enumerate().skip(9).map(|(o, n)| n.parse::<usize>().unwrap_or(0) << (12 + o)))
        .sum();
    free >= need
}

struct Arena {
    slabs: Vec<*mut u8>,
    used: usize,
    pool: Vec<*mut u8>,
    huge: bool,
}
unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Arena {
    fn new(huge: bool) -> Self {
        Arena { slabs: Vec::new(), used: 0, pool: Vec::new(), huge }
    }
    fn release(self) {
        for &slab in &self.slabs {
            advise(slab, SLAB, MADV_DONTNEED);
        }
    }
    fn block(&mut self) -> *mut u8 {
        if let Some(p) = self.pool.pop() {
            return p;
        }
        if self.used % SLAB == 0 {
            let layout = Layout::from_size_align(SLAB, 2 << 20).unwrap();
            let slab = unsafe { alloc(layout) };
            if slab.is_null() {
                handle_alloc_error(layout);
            }
            if self.huge {
                advise(slab, SLAB, MADV_HUGEPAGE);
            }
            self.slabs.push(slab);
            self.used = 0;
        }
        let p = unsafe { self.slabs[self.slabs.len() - 1].add(self.used) };
        if self.used % (2 << 20) == 0 {
            unsafe { madvise(p, 2 << 20, MADV_POPULATE_WRITE) };
        }
        self.used += BLOCK;
        p
    }
}

struct Bin<T> {
    at: *mut T,
    end: *mut T,
    staged: usize,
    blocks: usize,
}

struct Bins<T> {
    bins: Vec<Bin<T>>,
    stage: Vec<MaybeUninit<T>>,
    tab: Vec<*mut T>,
    stride: usize,
}
unsafe impl<T: Send> Send for Bins<T> {}
unsafe impl<T: Sync> Sync for Bins<T> {}

impl<T: Copy> Bins<T> {
    const PER: usize = BLOCK / std::mem::size_of::<T>() / STAGE * STAGE;

    fn new(n: usize) -> Self {
        let mut stage: Vec<MaybeUninit<T>> = Vec::new();
        stage.resize_with(n * STAGE, MaybeUninit::uninit);
        Bins { bins: (0..n).map(|_| Bin { at: std::ptr::null_mut(), end: std::ptr::null_mut(), staged: 0, blocks: 0 }).collect(), stage, tab: vec![std::ptr::null_mut(); n * 32], stride: 32 }
    }
    fn grow(&mut self, arena: &mut Arena, s: usize) {
        if self.bins[s].blocks == self.stride {
            let stride = self.stride * 2;
            let mut tab = vec![std::ptr::null_mut(); self.bins.len() * stride];
            for (new, old) in tab.chunks_mut(stride).zip(self.tab.chunks(self.stride)) {
                new[..old.len()].copy_from_slice(old);
            }
            self.tab = tab;
            self.stride = stride;
        }
        let b = &mut self.bins[s];
        b.at = arena.block() as *mut T;
        b.end = unsafe { b.at.add(Self::PER) };
        self.tab[s * self.stride + b.blocks] = b.at;
        b.blocks += 1;
    }
    fn list(&self, s: usize) -> &[*mut T] {
        &self.tab[s * self.stride..s * self.stride + self.bins[s].blocks]
    }
    #[inline]
    fn push(&mut self, arena: &mut Arena, s: usize, x: T) {
        let b = &mut self.bins[s];
        self.stage[s * STAGE + b.staged].write(x);
        b.staged += 1;
        if b.staged == STAGE {
            if b.at == b.end {
                self.grow(arena, s);
            }
            let b = &mut self.bins[s];
            let src = self.stage[s * STAGE..].as_ptr() as *const __m256i;
            for i in 0..STAGE * std::mem::size_of::<T>() / 32 {
                unsafe { _mm256_stream_si256((b.at as *mut __m256i).add(i), _mm256_loadu_si256(src.add(i))) };
            }
            b.at = unsafe { b.at.add(STAGE) };
            b.staged = 0;
        }
    }
    fn finish(&mut self, arena: &mut Arena) {
        for s in 0..self.bins.len() {
            if self.bins[s].staged == 0 {
                continue;
            }
            if self.bins[s].at == self.bins[s].end {
                self.grow(arena, s);
            }
            let b = &mut self.bins[s];
            unsafe {
                std::ptr::copy_nonoverlapping(self.stage[s * STAGE..].as_ptr() as *const T, b.at, b.staged);
                b.at = b.at.add(b.staged);
            }
            b.staged = 0;
        }
    }
    fn len(&self, s: usize) -> usize {
        match self.list(s).last() {
            Some(&p) => (self.bins[s].blocks - 1) * Self::PER + unsafe { self.bins[s].at.offset_from(p) } as usize,
            None => 0,
        }
    }
    fn blocks(&self, s: usize) -> impl Iterator<Item = &[T]> {
        let b = self.list(s);
        let last = self.len(s) - b.len().saturating_sub(1) * Self::PER;
        b.iter().enumerate().map(move |(j, &p)| unsafe { std::slice::from_raw_parts(p, if j + 1 == b.len() { last } else { Self::PER }) })
    }
    fn get(&self, s: usize, i: usize) -> &T {
        unsafe { &*self.list(s)[i / Self::PER].add(i % Self::PER) }
    }
}

#[derive(Default)]
struct Tab32 {
    slots: Vec<u32>,
    bits: u32,
}
impl Tab32 {
    fn reset(&mut self, n: usize, slots: usize) {
        self.bits = usize::BITS - n.leading_zeros();
        self.slots.clear();
        let slots = slots.next_power_of_two().max(16);
        if self.slots.capacity() < slots {
            extend(&mut self.slots, slots);
        }
        self.slots.resize(slots, 0);
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
    pub fn release(self) {
        advise(self.slots.as_ptr(), self.slots.len(), MADV_DONTNEED);
    }
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
    advise(v.as_ptr(), v.capacity(), MADV_POPULATE_WRITE);
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

pub fn build_links<'a>(parts: &[LinkPart<'a>], huge: bool) -> LinkMap<'a> {
    let n: usize = parts.iter().map(|p| p.len()).sum();
    let mask = (4 * n).next_power_of_two().max(16) - 1;
    let mut slots: Vec<Slot> = Vec::with_capacity(mask + 1);
    if huge {
        advise(slots.as_ptr(), mask + 1, MADV_HUGEPAGE);
    }
    advise(slots.as_ptr(), mask + 1, MADV_POPULATE_WRITE);
    slots.resize(mask + 1, Slot { k: [0; 2], tag: 0, name: 0 });
    let mut ids: Vec<B<'a>> = Vec::with_capacity(n + n / 2);
    let mut parent: Vec<u32> = Vec::with_capacity(n + n / 2);
    advise(ids.as_ptr(), ids.capacity(), MADV_POPULATE_WRITE);
    advise(parent.as_ptr(), parent.capacity(), MADV_POPULATE_WRITE);
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

pub struct Parsed {
    arena: Arena,
    ev: Bins<Ev>,
    side: Vec<Vec<u8>>,
}
impl Parsed {
    pub fn finish(&mut self) {
        self.ev.finish(&mut self.arena);
    }
    pub fn release(self) {
        self.arena.release();
    }
    pub fn new(nshard: usize, huge: bool) -> Self {
        Parsed { arena: Arena::new(huge), ev: Bins::new(nshard), side: vec![Vec::new(); nshard] }
    }
}

pub struct EvCtx<'m, 'a> {
    pub lo: i64,
    pub ws: i64,
    pub we: i64,
    pub products: &'m Map<B<'a>, u32>,
    pub unknown_cat: u32,
}

pub fn parse_events(c: B<'_>, chunk: u16, ctx: &EvCtx<'_, '_>, out: &mut Parsed) {
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
        out.ev.push(&mut out.arena, shard_of(khash(etag, ek), nshard), e);
    });
    unsafe { _mm_sfence() };
}

pub struct Routed<'a> {
    arena: Arena,
    rec: Bins<Rec>,
    ck: Bins<Ck<'a>>,
    tab: Tab32,
    lose: Vec<u32>,
    pend: Vec<Ck<'a>>,
}
impl Routed<'_> {
    pub fn finish(&mut self) {
        self.rec.finish(&mut self.arena);
        self.ck.finish(&mut self.arena);
    }
    pub fn release(self) {
        self.arena.release();
    }
    pub fn new(nshard: usize, huge: bool) -> Self {
        Routed { arena: Arena::new(huge), rec: Bins::new(nshard), ck: Bins::new(nshard), tab: Tab32::default(), lose: Vec::new(), pend: Vec::with_capacity(BATCH) }
    }
}

const BATCH: usize = 32;

pub fn dedup_route(parsed: &[Parsed], s: usize, links: &LinkMap<'_>, nshard: usize, out: &mut Routed<'_>) {
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
    out.tab.reset(total, 2 * total);
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
                    out.rec.push(&mut out.arena, shard_of(h, nshard), Rec { k, ts: e.ts, pt: e.pt, cat: e.cat, tag });
                }
            }
        }
    }
    for p in parsed {
        out.arena.pool.extend(p.ev.list(s).iter().map(|&b| b as *mut u8));
    }
    unsafe { _mm_sfence() };
}

pub struct CkCtx<'m, 'a> {
    pub lo: i64,
    pub we: i64,
    pub campaigns: &'m Map<B<'a>, u32>,
    pub links: &'m LinkMap<'a>,
}

pub fn parse_clicks<'a>(c: B<'a>, ctx: &CkCtx<'_, '_>, nshard: usize, out: &mut Routed<'a>) {
    let Routed { arena, ck, pend, .. } = out;
    for_rows(c, |line, [cid, user, camp, ts]: [B; 4]| {
        if cid.is_empty() || user.is_empty() {
            return;
        }
        let Some(t) = parse_ts(ts) else { return };
        if t < ctx.lo || t >= ctx.we {
            return;
        }
        let Some(&camp) = ctx.campaigns.get(camp) else { return };
        let (tag, k) = key_of(user);
        pend.push(Ck { k, line, ts: (t - ctx.lo) as u32, camp, tag });
        if pend.len() == BATCH {
            route_clicks(pend, ctx.links, nshard, arena, ck);
        }
    });
    route_clicks(pend, ctx.links, nshard, arena, ck);
    unsafe { _mm_sfence() };
}

fn route_clicks<'a>(pend: &mut Vec<Ck<'a>>, links: &LinkMap<'_>, nshard: usize, arena: &mut Arena, out: &mut Bins<Ck<'a>>) {
    let mut hs = [0u64; BATCH];
    for (i, c) in pend.iter().enumerate() {
        hs[i] = khash(c.tag, c.k);
        links.prefetch(hs[i]);
    }
    for (i, c) in pend.iter().enumerate() {
        let (tag, k) = links.person(c.tag, c.k, hs[i]);
        let h = if tag == T_LINK { khash(tag, k) } else { hs[i] };
        out.push(arena, shard_of(h, nshard), Ck { k, tag, ..*c });
    }
    pend.clear();
}


pub const GAP_MS: i64 = 1_800_000;
pub const WEEK_MS: i64 = 7 * 86_400_000;

pub struct Acc {
    day0: i32,
    ndays: usize,
    pub credit: Vec<(u32, u32, u64)>,
    pub assist: Vec<u32>,
}
impl Acc {
    #[inline]
    fn cell(&self, camp: u32, day: i32) -> usize {
        camp as usize * self.ndays + (day - self.day0) as usize
    }
}

struct Sess {
    start: i64,
    day: i32,
    rev: u64,
    purch: bool,
}

#[derive(Default)]
pub struct Rows {
    pub person: Vec<u32>,
    pub day: Vec<i32>,
    pub sessions: Vec<i64>,
    pub events: Vec<i64>,
    pub revenue: Vec<i64>,
    pub top: Vec<u32>,
}

const ROW_STEP: usize = 1 << 17;

fn extend<T>(v: &mut Vec<T>, n: usize) {
    v.reserve_exact(n);
    advise(unsafe { v.as_ptr().add(v.len()) }, v.capacity() - v.len(), MADV_POPULATE_WRITE);
}

struct Scratch {
    sess: Vec<Sess>,
    starts: Vec<i64>,
    days: Vec<i32>,
    day_end: Vec<u32>,
    catsum: Vec<u64>,
    touched: Vec<u32>,
    ct: Vec<(u32, i64)>,
}

struct DayAcc {
    day: i32,
    sessions: u64,
    events: u64,
    revenue: u64,
}

fn flush_row(person: u32, d: &DayAcc, sc: &mut Scratch, rows: &mut Rows) {
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
    if rows.person.len() == rows.person.capacity() {
        extend(&mut rows.person, ROW_STEP);
        extend(&mut rows.day, ROW_STEP);
        extend(&mut rows.sessions, ROW_STEP);
        extend(&mut rows.events, ROW_STEP);
        extend(&mut rows.revenue, ROW_STEP);
        extend(&mut rows.top, ROW_STEP);
    }
    rows.person.push(person);
    rows.day.push(d.day);
    rows.sessions.push(d.sessions as i64);
    rows.events.push(d.events as i64);
    rows.revenue.push(d.revenue as i64);
    rows.top.push(top.unwrap_or(u32::MAX));
}

struct PersonCtx<'s, 'a> {
    purch: &'s [(u32, u32)],
    cl: &'s [(u32, &'a u8)],
    lo: i64,
    organic: u32,
}

fn person(pid: u32, evs: &mut [u64], cks: &mut [u64], cx: &PersonCtx<'_, '_>, sc: &mut Scratch, rows: &mut Rows, acc: &mut Acc) {
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
    credit(&sc.sess, cks, cx, acc);
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
    pub rows: Rows,
    pub acc: Acc,
}
impl Worker<'_> {
    pub fn new(ncat: usize, ncamp: usize, day0: i32, ndays: usize) -> Self {
        Worker {
            sc: Scratch { sess: vec![], starts: vec![], days: vec![], day_end: vec![], catsum: vec![0; ncat], touched: vec![], ct: vec![] },
            bf: ShardBufs::default(),
            name_off: vec![0],
            name_data: Vec::new(),
            rows: Rows::default(),
            acc: Acc { day0, ndays, credit: vec![(0, 0, 0); ncamp * ndays], assist: vec![0; ncamp * ndays] },
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

pub fn run_shard<'a>(routed: &[Routed<'a>], parsed: &[Parsed], links: &LinkMap<'_>, p: usize, lo: i64, organic: u32, w: &mut Worker<'a>) {
    let Worker { sc, bf, name_off, name_data, rows, acc } = w;
    let n_ev: usize = routed.iter().map(|r| r.rec.len(p)).sum();
    bf.tab.reset(n_ev, n_ev / 4);
    bf.keys.clear();
    bf.tmp.clear();
    if bf.tmp.capacity() < n_ev {
        extend(&mut bf.tmp, n_ev + n_ev / 4);
    }
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
                        if e.tag == T_LINK {
                            prefetch(&links.ids[e.k[0] as usize]);
                        }
                        bf.keys.push((e.tag, e.k));
                        bf.off.push(0);
                        bf.tab.set(slot, h, i);
                        if bf.keys.len() * 2 > bf.tab.slots.len() {
                            bf.tab.reset(n_ev, bf.keys.len() * 4);
                            for (j, &(tag, k)) in bf.keys.iter().enumerate() {
                                let h = khash(tag, k);
                                let slot = bf.tab.find(h, |_| false).unwrap_err();
                                bf.tab.set(slot, h, j as u32);
                            }
                        }
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
    for &(tag, k) in &bf.keys {
        if tag == T_LINK {
            prefetch(&links.ids[k[0] as usize][0]);
        }
    }
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
                    for t in parsed {
                        let mut b = &t.side[p][..];
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


fn credit(sess: &[Sess], cks: &[u64], cx: &PersonCtx<'_, '_>, acc: &mut Acc) {
    let n = cks.len();
    let (mut lo, mut hi) = (0usize, 0usize);
    let mut camp = cx.organic;
    for s in sess {
        let h0 = hi;
        while hi < n && (cks[hi] >> 32) as i64 <= s.start {
            hi += 1;
        }
        while lo < hi && ((cks[lo] >> 32) as i64) < s.start - WEEK_MS {
            lo += 1;
        }
        if hi == lo {
            camp = cx.organic;
        } else if hi != h0 {
            let mut best = cx.cl[cks[hi - 1] as u32 as usize];
            let mut i = hi - 1;
            let mut mixed = false;
            while i > lo && cks[i - 1] >> 32 == cks[hi - 1] >> 32 {
                i -= 1;
                mixed |= cx.cl[cks[i] as u32 as usize].0 != best.0;
            }
            if mixed {
                for &c in &cks[i..hi - 1] {
                    let c = cx.cl[c as u32 as usize];
                    if unsafe { first(c.1) < first(best.1) } {
                        best = c;
                    }
                }
            }
            camp = best.0;
        }
        let c = acc.cell(camp, s.day);
        let a = &mut acc.credit[c];
        a.0 += 1;
        a.1 += s.purch as u32;
        a.2 += s.rev;
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
            let c = acc.cell(camp, days[k]);
            acc.assist[c] += (e - k) as u32;
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
