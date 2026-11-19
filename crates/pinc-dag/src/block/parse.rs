//! Zero-copy, strict parsing of a block.

use core::cmp::Ordering;

use pinc_wire::cbor::{Decoder, Item, MapReader};

use super::BlockError;
use crate::cid::{CidList, CidRef, cmp_text};

/// A parsed block borrowing its input. See the [module](super) for what is validated.
#[derive(Debug, Clone)]
pub struct BlockRef<'a> {
    delta: &'a [u8],
    heads: CidList<'a>,
    links: LinkList<'a>,
    encryption: Option<CidRef<'a>>,
    signature: Option<CidRef<'a>>,
}

/// One named link of a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinkRef<'a> {
    /// The link name, usually a field name.
    pub name: &'a str,
    /// The linked block.
    pub cid: CidRef<'a>,
}

/// Iterator over the head CIDs of a block, in order.
pub type Heads<'a> = CidList<'a>;

/// Iterator over the named links of a block, in order.
pub type Links<'a> = LinkList<'a>;

/// A validated array of links, iterated in place.
#[derive(Debug, Clone)]
pub struct LinkList<'a> {
    dec: Decoder<'a>,
    left: u64,
}

impl<'a> BlockRef<'a> {
    /// Parse and validate a whole block.
    ///
    /// # Errors
    /// [`BlockError::Wire`] and [`BlockError::Cid`] for malformed bytes, [`BlockError::TrailingBytes`],
    /// [`BlockError::MissingDelta`], [`BlockError::Malformed`] for a field of the wrong kind, and
    /// [`BlockError::Unordered`] for heads or links that are out of order or duplicated.
    pub fn parse(bytes: &'a [u8]) -> Result<Self, BlockError> {
        let mut dec = Decoder::new(bytes);
        let mut map = MapReader::new(&mut dec)?;
        let mut delta = None;
        let mut heads = CidList::empty();
        let mut links = LinkList::empty();
        let (mut encryption, mut signature) = (None, None);
        while let Some(key) = map.next_key(&mut dec)? {
            match key {
                "delta" => {
                    let start = dec.position();
                    dec.skip_value()?;
                    delta = bytes.get(start..dec.position());
                }
                "heads" => {
                    heads = if skip_null(&mut dec)? {
                        CidList::empty()
                    } else {
                        CidList::read(&mut dec, bytes)?
                    };
                    check_ascending(heads.clone(), "heads", cmp_text)?;
                }
                "links" => {
                    links = if skip_null(&mut dec)? {
                        LinkList::empty()
                    } else {
                        LinkList::read(&mut dec, bytes)?
                    };
                    check_ascending(links.clone(), "links", |a, b| {
                        cmp_text(a.cid, b.cid).then_with(|| a.name.cmp(b.name))
                    })?;
                }
                "signature" => signature = read_optional_cid(&mut dec)?,
                "encryption" => encryption = read_optional_cid(&mut dec)?,
                _ => dec.skip_value()?,
            }
        }
        if !dec.is_empty() {
            return Err(BlockError::TrailingBytes);
        }
        Ok(Self {
            delta: delta.ok_or(BlockError::MissingDelta)?,
            heads,
            links,
            encryption,
            signature,
        })
    }

    /// The raw DAG-CBOR bytes of the delta item.
    pub const fn delta(&self) -> &'a [u8] {
        self.delta
    }

    /// The head CIDs, sorted by CID text.
    pub fn heads(&self) -> Heads<'a> {
        self.heads.clone()
    }

    /// The named links, sorted by CID text and then name.
    pub fn links(&self) -> Links<'a> {
        self.links.clone()
    }

    /// The CID of the encryption block, if any.
    pub const fn encryption(&self) -> Option<CidRef<'a>> {
        self.encryption
    }

    /// The CID of the signature block, if any.
    pub const fn signature(&self) -> Option<CidRef<'a>> {
        self.signature
    }

    /// The heads, then the link targets: the edges of the history DAG (`DefraDB`'s `AllLinks`).
    pub fn all_links(&self) -> impl Iterator<Item = CidRef<'a>> + use<'a> {
        self.heads().chain(self.links().map(|l| l.cid))
    }

    /// Every CID this block refers to: [`BlockRef::all_links`], then the signature and encryption CIDs.
    pub fn references(&self) -> impl Iterator<Item = CidRef<'a>> + use<'a> {
        self.all_links().chain(self.signature).chain(self.encryption)
    }
}

/// Consume a `null` if it is next; report whether it was.
fn skip_null(dec: &mut Decoder<'_>) -> Result<bool, BlockError> {
    let mut probe = *dec;
    if matches!(probe.next_item()?, Item::Null) {
        *dec = probe;
        return Ok(true);
    }
    Ok(false)
}

fn read_optional_cid<'a>(dec: &mut Decoder<'a>) -> Result<Option<CidRef<'a>>, BlockError> {
    if skip_null(dec)? {
        return Ok(None);
    }
    Ok(Some(CidRef::read_cbor(dec)?))
}

/// Require `items` to be strictly ascending under `cmp`.
fn check_ascending<T: Copy, I: Iterator<Item = T>>(
    items: I,
    what: &'static str,
    cmp: impl Fn(T, T) -> Ordering,
) -> Result<(), BlockError> {
    let mut prev = None;
    for item in items {
        if prev.is_some_and(|p| cmp(p, item) != Ordering::Less) {
            return Err(BlockError::Unordered(what));
        }
        prev = Some(item);
    }
    Ok(())
}

impl<'a> LinkList<'a> {
    const fn empty() -> Self {
        Self {
            dec: Decoder::new(&[]),
            left: 0,
        }
    }

    fn read(dec: &mut Decoder<'a>, whole: &'a [u8]) -> Result<Self, BlockError> {
        let Item::Array(count) = dec.next_item()? else {
            return Err(BlockError::Malformed("links is not an array"));
        };
        let start = dec.position();
        for _ in 0..count {
            read_link(dec)?;
        }
        let items = whole.get(start..dec.position()).ok_or(BlockError::Malformed("links"))?;
        Ok(Self {
            dec: Decoder::new(items),
            left: count,
        })
    }

    /// How many links remain.
    pub const fn len(&self) -> u64 {
        self.left
    }

    /// Whether no links remain.
    pub const fn is_empty(&self) -> bool {
        self.left == 0
    }
}

/// Read one `{"link": CID, "name": text}` map; unknown keys are skipped as `DefraDB` does.
fn read_link<'a>(dec: &mut Decoder<'a>) -> Result<LinkRef<'a>, BlockError> {
    let mut map = MapReader::new(dec)?;
    let (mut cid, mut name) = (None, None);
    while let Some(key) = map.next_key(dec)? {
        match key {
            "link" => cid = Some(CidRef::read_cbor(dec)?),
            "name" => match dec.next_item()? {
                Item::Text(t) => name = Some(t),
                _ => return Err(BlockError::Malformed("link name is not text")),
            },
            _ => dec.skip_value()?,
        }
    }
    match (cid, name) {
        (Some(cid), Some(name)) => Ok(LinkRef { name, cid }),
        _ => Err(BlockError::Malformed("link needs a link and a name")),
    }
}

impl<'a> Iterator for LinkList<'a> {
    type Item = LinkRef<'a>;

    fn next(&mut self) -> Option<LinkRef<'a>> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        // The items were validated by `read`, so a failure cannot happen; it ends the iteration if it ever did.
        let link = read_link(&mut self.dec).ok();
        if link.is_none() {
            self.left = 0;
        }
        link
    }
}
