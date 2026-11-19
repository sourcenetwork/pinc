//! Byte-text helpers for the `UPnP` leg: a bounded writer, searching, and the few number and address forms HTTP and the
//! IGD's XML carry.
//!
//! Invariants: nothing reads past its slice, allocates or panics; the writer never writes past its buffer and reports
//! an overflow instead of truncating silently.

use core::net::Ipv4Addr;

/// A writer over a caller's buffer. An overflow sets `ok` to false and writes nothing more.
pub(crate) struct Out<'a> {
    buf: &'a mut [u8],
    n: usize,
    ok: bool,
}

impl<'a> Out<'a> {
    pub(crate) const fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, n: 0, ok: true }
    }

    pub(crate) fn put(&mut self, b: &[u8]) -> &mut Self {
        let end = self.n.saturating_add(b.len());
        match self.buf.get_mut(self.n..end) {
            Some(d) if self.ok => {
                d.copy_from_slice(b);
                self.n = end;
            }
            _ => self.ok = false,
        }
        self
    }

    /// A number in decimal.
    pub(crate) fn dec(&mut self, mut v: u32) -> &mut Self {
        let mut digits = [0u8; 10];
        let mut i = digits.len();
        loop {
            i -= 1;
            if let Some(d) = digits.get_mut(i) {
                // v % 10 < 10, so the cast keeps the value.
                *d = b'0' + (v % 10) as u8;
            }
            v /= 10;
            if v == 0 || i == 0 {
                break;
            }
        }
        self.put(digits.get(i..).unwrap_or_default())
    }

    /// An IPv4 address in dotted form.
    pub(crate) fn ip4(&mut self, ip: Ipv4Addr) -> &mut Self {
        let [a, b, c, d] = ip.octets();
        self.dec(a.into())
            .put(b".")
            .dec(b.into())
            .put(b".")
            .dec(c.into())
            .put(b".")
            .dec(d.into())
    }

    /// The length written, or `None` after an overflow.
    pub(crate) const fn done(&self) -> Option<usize> {
        if self.ok { Some(self.n) } else { None }
    }
}

/// Public wrappers over this module's items for the trace test; each calls the real item and nothing else.
#[cfg(feature = "trace")]
pub mod trace {
    use core::net::Ipv4Addr;

    use super::Out;

    /// Run `puts` through one `Out` over `buf`; the result of `done()`.
    pub fn out_run(buf: &mut [u8], puts: &[&[u8]]) -> Option<usize> {
        let mut o = Out::new(buf);
        for p in puts {
            o.put(p);
        }
        o.done()
    }

    /// `Out::new(buf).dec(v).done()`.
    pub fn out_dec(buf: &mut [u8], v: u32) -> Option<usize> {
        Out::new(buf).dec(v).done()
    }

    /// `Out::new(buf).ip4(ip).done()`.
    pub fn out_ip4(buf: &mut [u8], ip: Ipv4Addr) -> Option<usize> {
        Out::new(buf).ip4(ip).done()
    }

    /// `parse_u32`.
    pub fn parse_u32(b: &[u8]) -> Option<u32> {
        super::parse_u32(b)
    }

    /// `parse_ip4`.
    pub fn parse_ip4(b: &[u8]) -> Option<Ipv4Addr> {
        super::parse_ip4(b)
    }

    /// `find`.
    pub fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
        super::find(hay, needle)
    }

    /// `trim`.
    pub fn trim(b: &[u8]) -> &[u8] {
        super::trim(b)
    }

    /// `header`.
    pub fn header<'a>(head: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
        super::header(head, name)
    }

    /// `element`.
    pub fn element<'a>(body: &'a [u8], from: usize, name: &[u8]) -> Option<(&'a [u8], usize)> {
        super::element(body, from, name)
    }
}

/// The first position of `needle` in `hay`.
pub(crate) fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    hay.windows(needle.len()).position(|w| w == needle)
}

/// `b` without leading and trailing spaces and tabs.
pub(crate) fn trim(b: &[u8]) -> &[u8] {
    let start = b.iter().position(|c| *c != b' ' && *c != b'\t').unwrap_or(b.len());
    let end = b
        .iter()
        .rposition(|c| *c != b' ' && *c != b'\t')
        .map_or(start, |e| e + 1);
    b.get(start..end).unwrap_or_default()
}

/// A decimal number of one to ten digits that fits a `u32`; nothing else.
pub(crate) fn parse_u32(b: &[u8]) -> Option<u32> {
    if b.is_empty() || b.len() > 10 {
        return None;
    }
    let mut v: u64 = 0;
    for c in b {
        if !c.is_ascii_digit() {
            return None;
        }
        v = v * 10 + u64::from(c - b'0');
    }
    u32::try_from(v).ok()
}

/// A dotted IPv4 address: four decimal parts of at most three digits each, each at most 255.
pub(crate) fn parse_ip4(b: &[u8]) -> Option<Ipv4Addr> {
    let mut o = [0u8; 4];
    let mut parts = b.split(|c| *c == b'.');
    for d in &mut o {
        let p = parts.next()?;
        if p.len() > 3 {
            return None;
        }
        *d = u8::try_from(parse_u32(p)?).ok()?;
    }
    parts.next().is_none().then(|| Ipv4Addr::from(o))
}

/// The value of the HTTP header `name` in `head` (the lines before the empty line), trimmed.
pub(crate) fn header<'a>(head: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
    for line in head.split(|c| *c == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let Some(colon) = line.iter().position(|c| *c == b':') else {
            continue;
        };
        let (k, v) = line.split_at(colon);
        if trim(k).eq_ignore_ascii_case(name) {
            return Some(trim(v.get(1..).unwrap_or_default()));
        }
    }
    None
}

/// The text between `<name>` and the next `</name>` at or after `from`, with where the search may go on.
pub(crate) fn element<'a>(body: &'a [u8], from: usize, name: &[u8]) -> Option<(&'a [u8], usize)> {
    let hay = body.get(from..)?;
    let open = tag(hay, name, false)?;
    let start = open.1;
    let rest = hay.get(start..)?;
    let close = tag(rest, name, true)?;
    let text = rest.get(..close.0)?;
    Some((trim(text), from + start + close.1))
}

/// Where the tag `<name>` (or `</name>` when `closing`) starts and ends in `hay`; a namespace prefix (`<u:name>`) is
/// accepted.
fn tag(hay: &[u8], name: &[u8], closing: bool) -> Option<(usize, usize)> {
    let mut at = 0;
    while let Some(lt) = hay.get(at..).and_then(|h| h.iter().position(|c| *c == b'<')) {
        let s = at + lt;
        let gt = s + hay.get(s..)?.iter().position(|c| *c == b'>')?;
        let mut inner = hay.get(s + 1..gt)?;
        if closing {
            let Some(i) = inner.strip_prefix(b"/") else {
                at = gt;
                continue;
            };
            inner = i;
        }
        let inner = inner.split(u8::is_ascii_whitespace).next().unwrap_or_default();
        let local = inner
            .iter()
            .rposition(|c| *c == b':')
            .map_or(inner, |c| inner.get(c + 1..).unwrap_or_default());
        if local == name {
            return Some((s, gt + 1));
        }
        at = gt;
    }
    None
}
