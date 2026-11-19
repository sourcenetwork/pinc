//! Node ids as text and the address a peer is reached at.
//!
//! The text form of an Ed25519 node id is the lowercase hex of its 32-byte public key, 64 characters. Any other
//! algorithm adds its tag and a dot in front (`01.` and then the hex). A [`NodeAddr`] is a node id with the direct
//! addresses and relay URLs to try, and has a one-line text form: `<id>` or `<id>@<item>,<item>` where an item is an
//! `ip:port` or a relay URL (it contains `://`).
//!
//! Invariants: parsing never panics; printing then parsing returns the same value; the text of a node id holds no
//! secret.

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
            (
                IdentityAlg::from_tag(t).ok_or_else(|| bad("the node id has an unknown algorithm"))?,
                rest,
            )
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

    /// Add a direct address.
    #[must_use]
    pub fn with_direct(mut self, addr: SocketAddr) -> Self {
        self.direct.push(addr);
        self
    }

    /// Add a relay URL.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the URL is empty, has no `://` or has a `,`: the text form could not give it back.
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
