use super::util::{count_byte, eq_mask64, find_byte, find_sub};
use std::arch::x86_64::{_pdep_u64, _pext_u32, _pext_u64};
use std::cell::Cell;
use std::io;

pub type B<'a> = &'a [u8];

pub const DAY_MS: i64 = 86_400_000;

pub fn chunks<'a>(files: &[B<'a>], target: usize) -> Vec<B<'a>> {
    let target = target.max(1);
    let mut out = Vec::new();
    for &f in files {
        let body = match find_byte(f, b'\n') {
            Some(p) => &f[p + 1..],
            None => continue,
        };
        let mut s = 0;
        while s < body.len() {
            let mut e = s.saturating_add(target).min(body.len());
            if e < body.len() {
                e = match find_byte(&body[e..], b'\n') {
                    Some(p) => e + p + 1,
                    None => body.len(),
                };
            }
            out.push(&body[s..e]);
            s = e;
        }
    }
    out
}

pub fn chunk_target(files: &[B], ncpu: usize) -> usize {
    let total: usize = files.iter().map(|f| f.len()).sum();
    (total / (ncpu * 16).max(1)).clamp(1 << 20, 16 << 20)
}

#[inline]
pub fn count_lines(c: B) -> usize {
    count_byte(c, b'\n')
}

#[inline]
pub fn for_lines<'a>(chunk: B<'a>, mut f: impl FnMut(B<'a>)) {
    let n = chunk.len();
    let mut s = 0usize;
    let mut base = 0usize;
    while base + 64 <= n {
        let mut m = eq_mask64(&chunk[base..], b'\n');
        while m != 0 {
            let p = base + m.trailing_zeros() as usize;
            if p > s {
                f(&chunk[s..p]);
            }
            s = p + 1;
            m &= m - 1;
        }
        base += 64;
    }
    for p in base..n {
        if chunk[p] == b'\n' {
            if p > s {
                f(&chunk[s..p]);
            }
            s = p + 1;
        }
    }
    if s < n {
        f(&chunk[s..]);
    }
}

#[inline]
fn unquote(f: B, has_quote: bool) -> Option<B> {
    if !has_quote {
        return Some(f);
    }
    let n = f.len();
    if n >= 2 && f[0] == b'"' && f[n - 1] == b'"' && !f[1..n - 1].contains(&b'"') {
        Some(&f[1..n - 1])
    } else {
        None
    }
}

#[inline]
pub fn split<'a, const N: usize>(line: B<'a>) -> Option<[B<'a>; N]> {
    let mut out: [B<'a>; N] = [&[]; N];
    let mut k = 0usize;
    let mut start = 0usize;
    let mut q = false;
    for (i, &b) in line.iter().enumerate() {
        if b == b',' {
            if k + 1 >= N {
                return None;
            }
            out[k] = unquote(&line[start..i], q)?;
            k += 1;
            start = i + 1;
            q = false;
        } else if b == b'"' {
            q = true;
        }
    }
    if k + 1 != N {
        return None;
    }
    out[k] = unquote(&line[start..], q)?;
    Some(out)
}

const ROW_BUF: usize = 256;

#[inline]
pub fn for_rows<'a, const N: usize>(chunk: B<'a>, mut f: impl FnMut(&'a u8, [B<'a>; N])) {
    const { assert!(N >= 1 && N <= 8) };
    let n = chunk.len();
    let care = (!0u64 >> (64 - 8 * N)) & 0x0303_0303_0303_0303;
    let want = 1u64 << (8 * (N - 1));
    let mut pos = [usize::MAX; ROW_BUF + 80];
    let mut flags = [0u8; ROW_BUF + 80];
    let mut cnt = 1usize;
    let mut tail = [0u8; 64];
    let mut base = 0usize;
    let mut after_sep = 1u64;
    let mut after_nl = 1u64;
    let mut after_inner = 0u64;
    let mut open_carry = 0u64;
    let mut stray_carry = 0u64;
    let mut skip = false;
    let mut more = true;
    while more {
        while more && cnt <= ROW_BUF {
            let blk: &[u8] = if base + 64 <= n {
                &chunk[base..base + 64]
            } else {
                tail[..n - base].copy_from_slice(&chunk[base..]);
                tail[n - base] = b'\n';
                more = false;
                &tail
            };
            let nl = eq_mask64(blk, b'\n');
            let sep = nl | eq_mask64(blk, b',');
            let quote = eq_mask64(blk, b'"');
            let inner = quote & !(sep << 1 | after_sep);
            let closed = inner << 1 | after_inner;
            let (opened, c0) = (!sep).overflowing_add(quote ^ inner);
            let (opened, c1) = opened.overflowing_add(open_carry);
            let (stray, c2) = (!sep).overflowing_add(closed & !sep);
            let (stray, c3) = stray.overflowing_add(stray_carry);
            let bad = ((opened ^ closed) | stray) & sep | nl & (nl << 1 | after_nl);
            after_sep = sep >> 63;
            after_nl = nl >> 63;
            after_inner = inner >> 63;
            open_carry = (c0 | c1) as u64;
            stray_carry = (c2 | c3) as u64;
            let (mut nls, mut bads, mut quoted) = unsafe { (_pext_u64(nl, sep), _pext_u64(bad, sep), _pext_u64(closed, sep)) };
            let mut m = sep;
            let mut at = cnt;
            cnt += sep.count_ones() as usize;
            loop {
                let out: &mut [usize; 8] = (&mut pos[at..at + 8]).try_into().unwrap();
                for o in out {
                    unsafe { std::ptr::write_volatile(o, base + m.trailing_zeros() as usize) };
                    m &= m.wrapping_sub(1);
                }
                let fl = unsafe { _pdep_u64(nls, 0x0101_0101_0101_0101) | _pdep_u64(bads, 0x0202_0202_0202_0202) | _pdep_u64(quoted, 0x0404_0404_0404_0404) };
                flags[at..at + 8].copy_from_slice(&fl.to_le_bytes());
                if m == 0 {
                    break;
                }
                at += 8;
                nls >>= 8;
                bads >>= 8;
                quoted >>= 8;
            }
            base += 64;
        }
        let mut i = 1usize;
        if skip {
            while i < cnt && flags[i] & 1 == 0 {
                i += 1;
            }
            skip = i == cnt;
            i = cnt.min(i + 1);
        }
        while i + N <= cnt {
            let w = u64::from_le_bytes(flags[i..i + 8].try_into().unwrap());
            if w & care == want {
                let line = pos[i - 1].wrapping_add(1);
                let mut s = line;
                let mut out: [B<'a>; N] = [&[]; N];
                for (k, o) in out.iter_mut().enumerate() {
                    let q = (w >> (8 * k + 2)) as usize & 1;
                    let e = pos[i + k];
                    *o = unsafe { chunk.get_unchecked(s + q..e - q) };
                    s = e + 1;
                }
                f(unsafe { chunk.get_unchecked(line) }, out);
                i += N;
            } else {
                while i < cnt && flags[i] & 1 == 0 {
                    i += 1;
                }
                skip = i == cnt;
                i = cnt.min(i + 1);
            }
        }
        pos.copy_within(i - 1..i + 15, 0);
        flags.copy_within(i - 1..i + 15, 0);
        cnt -= i - 1;
    }
}

#[inline]
pub unsafe fn first<'a>(p: &'a u8) -> B<'a> {
    let p0 = p as *const u8;
    let mut q = p0;
    while *q != b',' {
        q = q.add(1);
    }
    strip(std::slice::from_raw_parts(p0, q.offset_from(p0) as usize))
}

#[inline]
fn strip(f: B) -> B {
    if !f.is_empty() && f[0] == b'"' {
        &f[1..f.len() - 1]
    } else {
        f
    }
}

#[inline]
fn d2(a: u8, b: u8) -> Option<i64> {
    if a.is_ascii_digit() && b.is_ascii_digit() {
        Some(((a - b'0') * 10 + (b - b'0')) as i64)
    } else {
        None
    }
}

pub fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

fn is_leap(y: i64) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

thread_local! {
    static DAYS: [Cell<(u64, u32, i64)>; 64] = const { [const { Cell::new((0, 1, 0)) }; 64] };
}

#[cold]
fn date(s: &[u8]) -> Option<i64> {
    if s[4] != b'-' || s[7] != b'-' || s[10] != b'T' {
        return None;
    }
    let y = d2(s[0], s[1])? * 100 + d2(s[2], s[3])?;
    let mo = d2(s[5], s[6])?;
    let d = d2(s[8], s[9])?;
    if !(1..=12).contains(&mo) || d < 1 {
        return None;
    }
    let dim = match mo {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        _ => {
            if is_leap(y) {
                29
            } else {
                28
            }
        }
    };
    if d > dim {
        return None;
    }
    Some(days_from_civil(y, mo, d) * DAY_MS)
}

#[inline(always)]
fn civil(s: &[u8]) -> Option<i64> {
    let k0 = u64::from_le_bytes(s[..8].try_into().unwrap());
    let k1 = u32::from_le_bytes(s[7..11].try_into().unwrap());
    let day = DAYS.with(|days| {
        let slot = &days[unsafe { _pext_u32(k1, 0x000f_0300) } as usize];
        let (a, b, ms) = slot.get();
        if a == k0 && b == k1 {
            return Some(ms);
        }
        let ms = date(s)?;
        slot.set((k0, k1, ms));
        Some(ms)
    })?;
    let x = u64::from_le_bytes(s[11..19].try_into().unwrap()) ^ 0x3030_3a30_303a_3030;
    if (x | x.wrapping_add(0x0606_0f06_060f_0606)) & 0xf0f0_f0f0_f0f0_f0f0 != 0 {
        return None;
    }
    let t = x.wrapping_mul(0xa01);
    if t.wrapping_add(0x4400_0044_0000_6800) & 0x8000_0080_0000_8000 != 0 {
        return None;
    }
    Some(day + ((t >> 8 & 255) * 3_600_000 + (t >> 32 & 255) * 60_000 + (t >> 56) * 1000) as i64)
}

const POW10: [i64; 9] = [1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000];

#[inline]
fn digits8(x: u64) -> i64 {
    let x = x.wrapping_mul(0xa01) >> 8 & 0x00ff_00ff_00ff_00ff;
    let x = x.wrapping_mul(0x64_0001) >> 16 & 0x0000_ffff_0000_ffff;
    (x.wrapping_mul(0x2710_0000_0001) >> 32) as i64
}

fn epoch(s: &[u8]) -> Option<i64> {
    if s.is_empty() || !s.iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let mut i = 0;
    while i < s.len() && s[i] == b'0' {
        i += 1;
    }
    let r = &s[i..];
    if r.len() > 18 {
        return None;
    }
    let mut v: i64 = 0;
    for &b in r {
        v = v * 10 + (b - b'0') as i64;
    }
    Some(v)
}

#[inline(always)]
pub fn parse_ts(s: &[u8]) -> Option<i64> {
    let n = s.len();
    match n {
        20 if s[19] == b'Z' => civil(s),
        25 if s[19] == b'+' || s[19] == b'-' => {
            if s[22] != b':' {
                return None;
            }
            let oh = d2(s[20], s[21])?;
            let om = d2(s[23], s[24])?;
            if oh > 23 || om > 59 {
                return None;
            }
            let off = (oh * 3600 + om * 60) * 1000;
            civil(s).map(|t| if s[19] == b'+' { t - off } else { t + off })
        }
        9..=16 => {
            let hi = u64::from_le_bytes(s[..8].try_into().unwrap()) ^ 0x3030_3030_3030_3030;
            let lo = u64::from_le_bytes(s[n - 8..].try_into().unwrap()) ^ 0x3030_3030_3030_3030;
            if (hi | lo | hi.wrapping_add(0x0606_0606_0606_0606) | lo.wrapping_add(0x0606_0606_0606_0606)) & 0xf0f0_f0f0_f0f0_f0f0 != 0 {
                return None;
            }
            Some(digits8(hi) * POW10[n - 8] + digits8(lo & (!0 << (8 * (16 - n)))))
        }
        _ => epoch(s),
    }
}

#[inline]
pub fn parse_price(s: &[u8]) -> Option<u32> {
    if s.is_empty() || !s.iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let mut i = 0;
    while i < s.len() && s[i] == b'0' {
        i += 1;
    }
    let r = &s[i..];
    if r.len() > 8 {
        return None;
    }
    let mut v: u32 = 0;
    for &b in r {
        v = v * 10 + (b - b'0') as u32;
    }
    if (1..=10_000_000).contains(&v) {
        Some(v)
    } else {
        None
    }
}

#[inline]
pub fn day_of(ts: i64) -> i32 {
    ts.div_euclid(DAY_MS) as i32
}

fn bad(msg: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

pub fn manifest(data: &[u8]) -> io::Result<(i64, i64)> {
    let get = |key: &[u8]| -> io::Result<i64> {
        let k = String::from_utf8_lossy(key).into_owned();
        let pos = find_sub(data, key).ok_or_else(|| bad(format!("manifest: no {k}")))?;
        let rest = &data[pos + key.len()..];
        let colon = find_byte(rest, b':').ok_or_else(|| bad(format!("manifest: no colon after {k}")))?;
        let rest = &rest[colon + 1..];
        let q1 = find_byte(rest, b'"').ok_or_else(|| bad(format!("manifest: no value for {k}")))?;
        let rest = &rest[q1 + 1..];
        let q2 = find_byte(rest, b'"').ok_or_else(|| bad(format!("manifest: unterminated {k}")))?;
        parse_ts(&rest[..q2]).ok_or_else(|| bad(format!("manifest: bad timestamp {}", String::from_utf8_lossy(&rest[..q2]))))
    };
    Ok((get(b"\"window_start\"")?, get(b"\"window_end\"")?))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn old_civil(s: &[u8]) -> Option<i64> {
        if s[4] != b'-' || s[7] != b'-' || s[10] != b'T' || s[13] != b':' || s[16] != b':' {
            return None;
        }
        let y = d2(s[0], s[1])? * 100 + d2(s[2], s[3])?;
        let mo = d2(s[5], s[6])?;
        let d = d2(s[8], s[9])?;
        let h = d2(s[11], s[12])?;
        let mi = d2(s[14], s[15])?;
        let se = d2(s[17], s[18])?;
        if !(1..=12).contains(&mo) || h > 23 || mi > 59 || se > 59 || d < 1 {
            return None;
        }
        let dim = match mo {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
            4 | 6 | 9 | 11 => 30,
            _ => {
                if is_leap(y) {
                    29
                } else {
                    28
                }
            }
        };
        if d > dim {
            return None;
        }
        Some((days_from_civil(y, mo, d) * 86_400 + h * 3600 + mi * 60 + se) * 1000)
    }

    fn old_ts(s: &[u8]) -> Option<i64> {
        if s.is_empty() {
            return None;
        }
        if s.iter().all(|b| b.is_ascii_digit()) {
            let mut i = 0;
            while i < s.len() && s[i] == b'0' {
                i += 1;
            }
            let r = &s[i..];
            if r.len() > 18 {
                return None;
            }
            let mut v: i64 = 0;
            for &b in r {
                v = v * 10 + (b - b'0') as i64;
            }
            return Some(v);
        }
        match s.len() {
            20 => {
                if s[19] != b'Z' {
                    return None;
                }
                old_civil(s)
            }
            25 => {
                let sign = match s[19] {
                    b'+' => 1,
                    b'-' => -1,
                    _ => return None,
                };
                if s[22] != b':' {
                    return None;
                }
                let oh = d2(s[20], s[21])?;
                let om = d2(s[23], s[24])?;
                if oh > 23 || om > 59 {
                    return None;
                }
                old_civil(s).map(|t| t - sign * (oh * 3600 + om * 60) * 1000)
            }
            _ => None,
        }
    }

    fn old_rows<const N: usize>(chunk: &[u8]) -> Vec<(usize, [(usize, usize); N])> {
        let at = |f: &[u8]| -> usize { f.as_ptr() as usize - chunk.as_ptr() as usize };
        let mut out = Vec::new();
        for line in chunk.split(|&b| b == b'\n') {
            if line.is_empty() {
                continue;
            }
            let fields: Vec<&[u8]> = line.split(|&b| b == b',').collect();
            if fields.len() != N {
                continue;
            }
            let mut row = [(0usize, 0usize); N];
            let mut ok = true;
            for (i, f) in fields.iter().enumerate() {
                let n = f.len();
                if !f.contains(&b'"') {
                    row[i] = (at(f), n);
                } else if n >= 2 && f[0] == b'"' && f[n - 1] == b'"' && !f[1..n - 1].contains(&b'"') {
                    row[i] = (at(f) + 1, n - 2);
                } else {
                    ok = false;
                }
            }
            if ok {
                out.push((at(line), row));
            }
        }
        out
    }

    fn new_rows<const N: usize>(chunk: &[u8]) -> Vec<(usize, [(usize, usize); N])> {
        let at = |p: *const u8| -> usize { p as usize - chunk.as_ptr() as usize };
        let mut out = Vec::new();
        for_rows::<N>(chunk, |line, fields| out.push((at(line), fields.map(|f| (at(f.as_ptr()), f.len())))));
        out
    }

    fn split_rows<const N: usize>(chunk: &[u8]) -> Vec<(usize, [(usize, usize); N])> {
        let at = |p: *const u8| -> usize { p as usize - chunk.as_ptr() as usize };
        let mut out = Vec::new();
        for_lines(chunk, |l| {
            if let Some(fields) = split::<N>(l) {
                out.push((at(l.as_ptr()), fields.map(|f| (at(f.as_ptr()), f.len()))));
            }
        });
        out
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
        fn pick(&mut self, set: &[u8]) -> u8 {
            set[self.below(set.len())]
        }
    }

    fn check_rows(chunk: &[u8]) {
        assert_eq!(new_rows::<1>(chunk), old_rows::<1>(chunk), "{:?}", String::from_utf8_lossy(chunk));
        assert_eq!(new_rows::<2>(chunk), old_rows::<2>(chunk), "{:?}", String::from_utf8_lossy(chunk));
        assert_eq!(new_rows::<4>(chunk), old_rows::<4>(chunk), "{:?}", String::from_utf8_lossy(chunk));
        assert_eq!(new_rows::<7>(chunk), old_rows::<7>(chunk), "{:?}", String::from_utf8_lossy(chunk));
        assert_eq!(new_rows::<8>(chunk), old_rows::<8>(chunk), "{:?}", String::from_utf8_lossy(chunk));
        assert_eq!(split_rows::<2>(chunk), old_rows::<2>(chunk), "{:?}", String::from_utf8_lossy(chunk));
        assert_eq!(split_rows::<7>(chunk), old_rows::<7>(chunk), "{:?}", String::from_utf8_lossy(chunk));
    }

    fn random_line(r: &mut Rng, out: &mut Vec<u8>) {
        const WORDS: [&[u8]; 12] = [
            b"e6d3t175y",
            b"u02423c3d84ab053af78764ce49f23b5c",
            b"2027-12-18T07:05:50-09:30",
            b"2027-12-19T08:16:10Z",
            b"1829203731000",
            b"purchase",
            b"p4837",
            b"",
            b"\"",
            b"\"\"",
            b"\r",
            b"\xef\xbc\x92 ",
        ];
        let shape = r.below(20);
        if shape == 0 {
            for _ in 0..r.below(4) {
                out.push(r.pick(b",\"\ra\xff"));
            }
            return;
        }
        let fields = match r.below(12) {
            0 => r.below(10),
            1 => 2,
            2 => 4,
            3 => 1,
            _ => 7,
        };
        for i in 0..fields {
            if i > 0 {
                out.push(b',');
            }
            let quoted = r.below(5) == 0;
            if quoted {
                out.push(b'"');
            }
            let words = if r.below(30) == 0 { 12 } else { 8 };
            out.extend_from_slice(WORDS[r.below(words)]);
            if shape == 1 && r.below(4) == 0 {
                for _ in 0..[70, 130, 5000][r.below(3)] {
                    out.push(r.pick(b"abc 0"));
                }
            }
            if r.below(60) == 0 {
                out.push(r.pick(b"\"\r \xc3"));
            }
            if quoted && r.below(80) != 0 {
                out.push(b'"');
            }
        }
    }

    #[test]
    fn rows_match_split() {
        let mut r = Rng(0x9e37_79b9_7f4a_7c15);
        let mut chunk: Vec<u8> = Vec::new();
        for round in 0..60_000 {
            chunk.clear();
            let lines = if round % 16 == 0 { 40 } else { r.below(6) };
            for _ in 0..lines {
                random_line(&mut r, &mut chunk);
                chunk.push(b'\n');
            }
            if r.below(3) == 0 {
                random_line(&mut r, &mut chunk);
            }
            for _ in 0..r.below(3) {
                if !chunk.is_empty() {
                    let at = r.below(chunk.len());
                    match r.below(3) {
                        0 => chunk[at] = r.pick(b",\"\n\r\xff0"),
                        1 => chunk.insert(at, r.pick(b",\"\n\r\xff0")),
                        _ => {
                            chunk.remove(at);
                        }
                    }
                }
            }
            check_rows(&chunk);
        }
        let mut r = Rng(77);
        for len in 0..600 {
            for _ in 0..40 {
                chunk.clear();
                for _ in 0..len {
                    chunk.push(r.pick(b",,\"\n\n\ra0"));
                }
                check_rows(&chunk);
            }
        }
    }

    #[test]
    fn rows() {
        let mut got: Vec<(u8, [Vec<u8>; 3])> = Vec::new();
        let text = b"a,\"b\",c\n\n\"\",,\"x y\"\r\nbad\",1,2\n\"\"\",1,2\n1,2\n1,2,3,4\n\",1,2\n\"q\"x,1,2\nlast,\"\",9";
        for_rows::<3>(text, |line, f| got.push((*line, f.map(|x| x.to_vec()))));
        let want: Vec<(u8, [Vec<u8>; 3])> = vec![(b'a', [b"a".to_vec(), b"b".to_vec(), b"c".to_vec()]), (b'l', [b"last".to_vec(), b"".to_vec(), b"9".to_vec()])];
        assert_eq!(got, want);
    }

    #[test]
    fn ts_matches_old() {
        let mut r = Rng(0x2545_f491_4f6c_dd1d);
        let mut s: Vec<u8> = Vec::new();
        for round in 0..6_000_000u32 {
            s.clear();
            let form = r.below(10);
            if form < 5 {
                let (y, mo, d) = match r.below(8) {
                    0 => (r.below(10_000), r.below(14), r.below(33)),
                    1 => (2024 + r.below(6), 2, 27 + r.below(4)),
                    _ => (2027, 11 + r.below(2), 1 + r.below(31)),
                };
                let (h, mi, se) = if r.below(20) == 0 { (r.below(26), r.below(62), r.below(62)) } else { (r.below(24), r.below(60), r.below(60)) };
                s.extend_from_slice(format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{se:02}").as_bytes());
                if form < 3 {
                    s.push(b'Z');
                } else {
                    let (oh, om) = if r.below(10) == 0 { (r.below(26), r.below(62)) } else { (r.below(24), r.below(60)) };
                    s.extend_from_slice(format!("{}{oh:02}:{om:02}", if r.below(2) == 0 { '+' } else { '-' }).as_bytes());
                }
            } else if form < 9 {
                for _ in 0..r.below(4) * r.below(4) {
                    s.push(b'0');
                }
                for _ in 0..[13, 13, 13, r.below(30)][r.below(4)] {
                    s.push(b'0' + r.below(10) as u8);
                }
            } else {
                for _ in 0..r.below(28) {
                    s.push(r.next() as u8);
                }
            }
            for _ in 0..[0, 0, 1, 1, 2, 5][round as usize % 6] {
                if !s.is_empty() {
                    let at = r.below(s.len());
                    match r.below(8) {
                        0 => s.insert(at, r.pick(b"0123456789-:TZ+ ")),
                        1 => {
                            s.remove(at);
                        }
                        2 => s[at] = r.next() as u8,
                        _ => s[at] = r.pick(b"0123456789-:TZtz+. /;\xd9\xa2"),
                    }
                }
            }
            assert_eq!(parse_ts(&s), old_ts(&s), "{:?}", String::from_utf8_lossy(&s));
        }
    }

    #[test]
    fn ts() {
        assert_eq!(parse_ts(b"2026-10-03T23:58:10Z"), Some(1791071890000));
        assert_eq!(parse_ts(b"2026-10-03T19:58:10-04:00"), Some(1791071890000));
        assert_eq!(parse_ts(b"1791071890000"), Some(1791071890000));
        assert_eq!(parse_ts(b"0001791071890000"), Some(1791071890000));
        assert_eq!(parse_ts(b"2026-10-03T23:58:10z"), None);
        assert_eq!(parse_ts(b"2026-10-03t23:58:10Z"), None);
        assert_eq!(parse_ts(b"2026-10-03 23:58:10Z"), None);
        assert_eq!(parse_ts(b"2026-02-29T00:00:00Z"), None);
        assert_eq!(parse_ts(b"2028-02-29T00:00:00Z").is_some(), true);
        assert_eq!(parse_ts(b"2026-10-03T19:58:10+24:00"), None);
        assert_eq!(parse_ts(b"2026-10-03T19:58:10+05:60"), None);
        assert_eq!(parse_ts(b"2026-10-03T19:58:10+0200"), None);
        assert_eq!(parse_ts(b"2026-10-03T19:58:10-00:00"), parse_ts(b"2026-10-03T19:58:10Z"));
        assert_eq!(parse_ts(b"2026-10-03T24:00:00Z"), None);
        assert_eq!(parse_ts(b"2026-10-03T23:59:60Z"), None);
        assert_eq!(parse_ts(b"1970-01-01T00:00:00Z"), Some(0));
        assert_eq!(parse_ts(b""), None);
        assert_eq!(parse_ts(b"86400000"), Some(86_400_000));
        assert_eq!(parse_ts(b"1791071890000.0"), None);
        assert_eq!(parse_ts(b"1.79e12"), None);
        assert_eq!(parse_ts(b"-5"), None);
        assert_eq!(parse_ts(b"179107189000\r"), None);
        assert_eq!(parse_ts(b"00000000000000000001"), Some(1));
        assert_eq!(parse_ts(b"00123456789012345678"), Some(123_456_789_012_345_678));
        assert_eq!(parse_ts(b"01234567890123456789"), None);
        assert_eq!(parse_ts(b"0000000000000000000000001"), Some(1));
        assert_eq!(parse_ts("179107189000٢".as_bytes()), None);
        assert_eq!(parse_ts("１７９１０７１８９００００".as_bytes()), None);
        assert_eq!(parse_price(b"0250"), Some(250));
        assert_eq!(parse_price(b"10000000"), Some(10_000_000));
        assert_eq!(parse_price(b"10000001"), None);
        assert_eq!(parse_price(b"0"), None);
        assert_eq!(split::<2>(b"\"a\",\"\""), Some([&b"a"[..], &b""[..]]));
        assert_eq!(split::<2>(b"a,b\""), None);
        assert_eq!(split::<2>(b"a,b,c"), None);
        assert_eq!(split::<2>(b"a"), None);
        let l = b"\"e1\",u 1,x,y";
        assert_eq!(unsafe { first(&l[0]) }, &b"e1"[..]);
        let l = b",\"\",x";
        assert_eq!(unsafe { first(&l[0]) }, &b""[..]);
    }
    #[test]
    fn lines() {
        let mut s = Vec::new();
        for i in 0..300 {
            s.extend_from_slice(format!("line{i}\n").as_bytes());
            if i % 7 == 0 {
                s.extend_from_slice(b"\n\n");
            }
        }
        s.extend_from_slice(b"tail");
        let mut got = Vec::new();
        for_lines(&s, |l| got.push(l.to_vec()));
        assert_eq!(got.len(), 301);
        assert_eq!(got[300], b"tail".to_vec());
        assert_eq!(count_lines(&s), 300 + 2 * 43);
        assert_eq!(find_byte(&s[1..], b'\n'), Some(4));
    }
}
