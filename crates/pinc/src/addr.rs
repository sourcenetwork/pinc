//! Node ids as text and the address a peer is reached at.
//!
//! The text form of an Ed25519 node id is the lowercase hex of its 32-byte public key, 64 characters. Any other
//! algorithm adds its two-digit tag and a dot in front (`02.` for ECDSA P-256, and then the hex). A [`NodeAddr`] is a
//! node id with the direct addresses and relay URLs to try, and has a one-line text form: `<id>` or
//! `<id>@<item>,<item>` where an item is an `ip:port` or a relay URL (it contains `://`).
//!
//! Invariants: parsing never panics; printing then parsing returns the same value for a [`NodeAddr`] built through its
//! functions (a struct literal can hold what the text form cannot carry); the text of a node id holds no secret.

use alloc::borrow::ToOwned;
use alloc::string::String;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::fmt;
use core::net::SocketAddr;
use core::str::FromStr;

use crate::error::{Error, ErrorKind, Result};
use pinc_crypto::{IdentityAlg, NodeId};

/// The text form of a node id.
pub fn node_to_string(id: &NodeId) -> String {
    use core::fmt::Write as _;
    let mut s = String::with_capacity(67);
    if id.alg != IdentityAlg::Ed25519 {
        let _ = write!(s, "{:02x}.", id.alg.tag());
    }
    for b in id.bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

fn bad(what: &'static str) -> Error {
    Error::new(ErrorKind::Config, what)
}

/// Whether `s` is `len` characters of lowercase hex, the only text `node_to_string` prints.
fn is_lower_hex(s: &str, len: usize) -> bool {
    s.len() == len && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

/// Parse the text form of a node id: exactly what [`node_to_string`] prints, so one id has one text.
///
/// # Errors
/// [`crate::ErrorKind::Config`] if the text is not a node id.
pub fn node_from_str(s: &str) -> Result<NodeId> {
    let (alg, hex) = match s.split_once('.') {
        Some((tag, rest)) => {
            if !is_lower_hex(tag, 2) {
                return Err(bad("the node id has a bad algorithm tag"));
            }
            let t = u8::from_str_radix(tag, 16).map_err(|_| bad("the node id has a bad algorithm tag"))?;
            let alg = IdentityAlg::from_tag(t).ok_or_else(|| bad("the node id has an unknown algorithm"))?;
            if alg == IdentityAlg::Ed25519 {
                return Err(bad("an Ed25519 node id is written without a tag"));
            }
            (alg, rest)
        }
        None => (IdentityAlg::Ed25519, s),
    };
    if !is_lower_hex(hex, 64) {
        return Err(bad("a node id is 64 lowercase hex characters"));
    }
    let mut bytes = [0u8; 32];
    for (b, pair) in bytes.iter_mut().zip(hex.as_bytes().chunks(2)) {
        let p = core::str::from_utf8(pair).map_err(|_| bad("a node id is hex"))?;
        *b = u8::from_str_radix(p, 16).map_err(|_| bad("a node id is hex"))?;
    }
    Ok(NodeId { alg, bytes })
}

/// A node and where to try to reach it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NodeAddr {
    /// The node.
    pub node: NodeId,
    /// Socket addresses to dial directly.
    pub direct: Vec<SocketAddr>,
    /// Relay URLs the node can be reached through.
    pub relays: Vec<String>,
}

impl NodeAddr {
    /// A node with no hints: the discovery hook and the address book are tried.
    pub const fn new(node: NodeId) -> Self {
        Self {
            node,
            direct: Vec::new(),
            relays: Vec::new(),
        }
    }

    /// Add a direct address. An IPv6 flow label is dropped: it means nothing to a dial, and the text form has none.
    #[must_use]
    pub fn with_direct(mut self, mut addr: SocketAddr) -> Self {
        if let SocketAddr::V6(v6) = &mut addr {
            v6.set_flowinfo(0);
        }
        self.direct.push(addr);
        self
    }

    /// Add a relay URL.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the URL is empty, has no `://` or has a `,`: the text form could not give it
    /// back.
    pub fn with_relay(mut self, url: impl Into<String>) -> Result<Self> {
        let url = url.into();
        if url.is_empty() || !url.contains("://") || url.contains(',') {
            return Err(bad("a relay is a URL with a scheme and no comma"));
        }
        self.relays.push(url);
        Ok(self)
    }

    /// The one-line text form; [`NodeAddr::parse`] reads it back.
    ///
    /// ```
    /// use pinc::{NodeAddr, node_to_string};
    ///
    /// # fn main() -> pinc::Result<()> {
    /// let id = pinc::node_from_str(&"ab".repeat(32))?;
    /// let addr = NodeAddr::new(id).with_direct("10.0.0.7:4433".parse().unwrap());
    /// assert_eq!(addr.ticket(), format!("{}@10.0.0.7:4433", node_to_string(&id)));
    /// assert_eq!(NodeAddr::parse(&addr.ticket())?, addr);
    /// # Ok(())
    /// # }
    /// ```
    pub fn ticket(&self) -> String {
        let mut s = node_to_string(&self.node);
        let items: Vec<String> = self
            .direct
            .iter()
            .map(ToString::to_string)
            .chain(self.relays.iter().cloned())
            .collect();
        if !items.is_empty() {
            s.push('@');
            s.push_str(&items.join(","));
        }
        s
    }

    /// Parse the text form.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the text is not a node address.
    pub fn parse(s: &str) -> Result<Self> {
        let (id, rest) = s.split_once('@').map_or((s, ""), |(a, b)| (a, b));
        let mut out = Self::new(node_from_str(id)?);
        for item in rest.split(',').filter(|i| !i.is_empty()) {
            if item.contains("://") {
                out.relays.push(item.to_owned());
            } else {
                out.direct.push(
                    item.parse()
                        .map_err(|_| bad("an address in the ticket is not ip:port"))?,
                );
            }
        }
        Ok(out)
    }
}

impl From<NodeId> for NodeAddr {
    fn from(node: NodeId) -> Self {
        Self::new(node)
    }
}

impl fmt::Display for NodeAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.ticket())
    }
}

impl FromStr for NodeAddr {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use alloc::format;
    use alloc::vec;
    use core::net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6};

    use super::*;

    #[test]
    fn an_ed25519_id_has_one_text_and_other_algorithms_keep_their_tag() {
        let hex = "ab".repeat(32);
        assert!(node_from_str(&format!("01.{hex}")).is_err());
        let p256 = node_from_str(&format!("02.{hex}")).unwrap();
        assert_eq!(node_to_string(&p256), format!("02.{hex}"));
    }

    #[test]
    fn an_ipv6_address_with_a_flow_label_and_a_scope_survives_the_ticket() {
        let v6 = SocketAddrV6::new(Ipv6Addr::LOCALHOST, 9, 5, 2);
        let node = node_from_str(&"ab".repeat(32)).unwrap();
        let a = NodeAddr::new(node).with_direct(SocketAddr::V6(v6));
        assert_eq!(NodeAddr::parse(&a.ticket()).unwrap(), a);
        let kept = match a.direct.first() {
            Some(SocketAddr::V6(v)) => *v,
            other => unreachable!("{other:?}"),
        };
        assert_eq!((kept.flowinfo(), kept.scope_id()), (0, 2));
    }

    use crate::trace_util::{below, jb, mix, write_trace};
    use core::fmt::Write as _;

    fn id_of(tag: u8, bytes: [u8; 32]) -> NodeId {
        NodeId {
            alg: IdentityAlg::from_tag(tag).unwrap(),
            bytes,
        }
    }

    fn random_id(seed: &mut u64) -> NodeId {
        let mut bytes = [0u8; 32];
        for b in &mut bytes {
            *b = mix(seed).to_le_bytes()[0];
        }
        id_of(u8::try_from(1 + below(seed, 4)).unwrap(), bytes)
    }

    fn jnode(id: &NodeId) -> String {
        format!(r#"{{"alg":{},"bytes":{}}}"#, id.alg.tag(), jb(&id.bytes))
    }

    fn flow(a: &SocketAddr) -> u32 {
        if let SocketAddr::V6(v) = a { v.flowinfo() } else { 0 }
    }

    fn jaddr(a: &SocketAddr) -> String {
        format!(r#"{{"txt":{},"flow":{}}}"#, jb(a.to_string().as_bytes()), flow(a))
    }

    fn jval(v: &NodeAddr) -> String {
        let direct: Vec<String> = v.direct.iter().map(jaddr).collect();
        let relays: Vec<String> = v.relays.iter().map(|r| jb(r.as_bytes())).collect();
        format!(
            r#"{{"node":{},"direct":[{}],"relays":[{}]}}"#,
            jnode(&v.node),
            direct.join(","),
            relays.join(",")
        )
    }

    /// `t` with one byte of it replaced, deleted, or one inserted, from `alphabet`.
    fn mutate(seed: &mut u64, t: &str, alphabet: &[u8]) -> String {
        let mut b = t.as_bytes().to_vec();
        let c = alphabet[below(seed, alphabet.len())];
        match below(seed, 3) {
            0 if !b.is_empty() => {
                let k = below(seed, b.len());
                b[k] = c;
            }
            1 if !b.is_empty() => {
                b.remove(below(seed, b.len()));
            }
            _ => b.insert(below(seed, b.len() + 1), c),
        }
        String::from_utf8(b).unwrap()
    }

    fn parse_line(out: &mut String, s: &str) {
        let parsed = NodeAddr::parse(s);
        let (ok, v) = match &parsed {
            Ok(v) => (true, v.clone()),
            Err(_) => (false, NodeAddr::new(id_of(1, [0; 32]))),
        };
        let items = s.split_once('@').map_or("", |(_, r)| r);
        let cp: Vec<String> = items
            .split(',')
            .filter(|i| !i.is_empty() && !i.contains("://"))
            .map(|i| match i.parse::<SocketAddr>() {
                Ok(a) => format!(
                    r#"{{"t":{},"ok":true,"txt":{},"flow":{}}}"#,
                    jb(i.as_bytes()),
                    jb(a.to_string().as_bytes()),
                    flow(&a)
                ),
                Err(_) => format!(r#"{{"t":{},"ok":false,"txt":[],"flow":0}}"#, jb(i.as_bytes())),
            })
            .collect();
        writeln!(
            out,
            r#"{{"t":"addr","op":"parse","s":{},"ok":{ok},"v":{},"cp":[{}]}}"#,
            jb(s.as_bytes()),
            jval(&v),
            cp.join(",")
        )
        .unwrap();
    }

    fn ticket_line(out: &mut String, v: &NodeAddr) -> String {
        let t = v.ticket();
        writeln!(
            out,
            r#"{{"t":"addr","op":"ticket","v":{},"text":{}}}"#,
            jval(v),
            jb(t.as_bytes())
        )
        .unwrap();
        t
    }

    fn str_line(out: &mut String, s: &str) {
        let (ok, extra) = match node_from_str(s) {
            Ok(id) => (true, format!(r#","alg":{},"bytes":{}"#, id.alg.tag(), jb(&id.bytes))),
            Err(_) => (false, String::new()),
        };
        writeln!(
            out,
            r#"{{"t":"addr","op":"str","s":{},"ok":{ok}{extra}}}"#,
            jb(s.as_bytes())
        )
        .unwrap();
    }

    /// Every sequence of up to two indexes below `n`.
    fn seqs(n: usize) -> Vec<Vec<usize>> {
        let mut all = vec![vec![]];
        let mut frontier = all.clone();
        for _ in 0..2 {
            frontier = frontier
                .iter()
                .flat_map(|s| (0..n).map(move |i| [s.clone(), vec![i]].concat()))
                .collect();
            all.extend(frontier.iter().cloned());
        }
        all
    }

    /// Node id text, `node_from_str`, `with_relay`, tickets and their parses, as the model reads them.
    #[test]
    #[allow(clippy::too_many_lines, reason = "one recorded run")]
    fn trace_addr() {
        let mut out = String::new();
        let hex = "ab".repeat(32);
        let mut seed = 1u64;

        let mut ids = Vec::new();
        for tag in 1..=4u8 {
            ids.push(id_of(tag, [0; 32]));
            ids.push(id_of(tag, [0xff; 32]));
            ids.push(id_of(tag, core::array::from_fn(|i| u8::try_from(i).unwrap())));
            ids.extend((0..8).map(|_| {
                let mut id = random_id(&mut seed);
                id.alg = IdentityAlg::from_tag(tag).unwrap();
                id
            }));
        }
        for id in &ids {
            let text = node_to_string(id);
            assert_eq!(node_from_str(&text).unwrap(), *id);
            writeln!(
                out,
                r#"{{"t":"addr","op":"id","alg":{},"bytes":{},"text":{}}}"#,
                id.alg.tag(),
                jb(&id.bytes),
                jb(text.as_bytes())
            )
            .unwrap();
        }

        let mut mid = hex.clone().into_bytes();
        mid[32] = b'A';
        let hexes = [
            hex.clone(),
            hex.to_uppercase(),
            hex[1..].to_owned(),
            format!("{hex}a"),
            format!("+{}", &hex[1..]),
            format!("g{}", &hex[1..]),
            String::from_utf8(mid).unwrap(),
        ];
        for tag in ["", "00.", "01.", "02.", "04.", "05.", "0a.", "0A.", "1.", "+1."] {
            for h in &hexes {
                str_line(&mut out, &format!("{tag}{h}"));
            }
        }
        for s in [".".to_owned(), format!(".{hex}"), String::new()] {
            str_line(&mut out, &s);
        }
        assert!(node_from_str(&format!("01.{hex}")).is_err());
        for _ in 0..2000 {
            let id = random_id(&mut seed);
            let m = mutate(&mut seed, &node_to_string(&id), b"0123456789abcdefABCDEF.+-g@ ");
            str_line(&mut out, &m);
        }

        let id = id_of(1, [7; 32]);
        let mut urls = vec![String::new()];
        let mut frontier = urls.clone();
        for _ in 0..4 {
            frontier = frontier
                .iter()
                .flat_map(|u| "h:/,@".chars().map(move |c| format!("{u}{c}")))
                .collect();
            urls.extend(frontier.iter().cloned());
        }
        assert_eq!(urls.len(), 781);
        for u in &urls {
            let ok = NodeAddr::new(id).with_relay(u.clone()).is_ok();
            writeln!(out, r#"{{"t":"addr","op":"relay","u":{},"ok":{ok}}}"#, jb(u.as_bytes())).unwrap();
        }

        let directs: [SocketAddr; 3] = [
            SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 5)),
            SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::LOCALHOST, 2, 0, 0)),
            SocketAddr::V6(SocketAddrV6::new(Ipv6Addr::LOCALHOST, 2, 1, 0)),
        ];
        let relays = ["h://", "://@", "h://h", "wss://r.example:443/x"];
        let mut values = Vec::new();
        for node in [id_of(1, [7; 32]), id_of(2, [9; 32])] {
            for d in seqs(directs.len()) {
                for r in seqs(relays.len()) {
                    let mut v = NodeAddr::new(node);
                    for &i in &d {
                        v = v.with_direct(directs[i]);
                    }
                    for &i in &r {
                        v = v.with_relay(relays[i]).unwrap();
                    }
                    assert_eq!(NodeAddr::parse(&v.ticket()).unwrap(), v);
                    values.push(v);
                }
            }
        }
        for raw in [vec![""], vec!["h"], vec!["h://,h"]] {
            let mut v = NodeAddr::new(id);
            v.relays.extend(raw.into_iter().map(ToOwned::to_owned));
            values.push(v);
        }
        for _ in 0..500 {
            let mut v = NodeAddr::new(random_id(&mut seed));
            for _ in 0..below(&mut seed, 4) {
                let port = u16::try_from(below(&mut seed, 65536)).unwrap();
                let o = mix(&mut seed).to_le_bytes();
                v.direct.push(if below(&mut seed, 2) == 0 {
                    SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(o[0], o[1], o[2], o[3]), port))
                } else {
                    let fl = if below(&mut seed, 2) == 0 {
                        0
                    } else {
                        u32::try_from(below(&mut seed, 1 << 31)).unwrap()
                    };
                    let ip = Ipv6Addr::new(u16::from(o[0]), 0, 0, u16::from(o[1]), 0, 0, 0, u16::from(o[2]));
                    SocketAddr::V6(SocketAddrV6::new(ip, port, fl, 0))
                });
            }
            for _ in 0..below(&mut seed, 4) {
                v.relays.push(relays[below(&mut seed, relays.len())].to_owned());
            }
            values.push(v);
        }
        let tickets: Vec<String> = values.iter().map(|v| ticket_line(&mut out, v)).collect();
        for t in &tickets {
            parse_line(&mut out, t);
        }
        for _ in 0..2000 {
            let t = &tickets[below(&mut seed, tickets.len())];
            let m = mutate(&mut seed, t, b"0123456789abcdef.:,@/[]h");
            parse_line(&mut out, &m);
        }
        write_trace("facade_addr.ndjson", &out);
    }
}
