//! The bundle store of delay-tolerant delivery for a VINC node program: the host side of `vinc_node::DtnApp`. The
//! node composes the layer itself (forwarder, custody book, ledger, transfers); the host gives it the store, the keys
//! every node derives from its name, and the contact windows a scenario sets. A scenario can also keep the store in a
//! directory, so a program started again resumes from it, and corrupt this node's copy of what it keeps.
//!
//! Invariants: a store that is off holds nothing and refuses every bundle; a bundle is kept whole or not at all, on
//! disk too; a corruption is applied only when the scenario asks for it, and only to this node's own copy.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use vinc_crypto::provider::Provider;
use vinc_crypto::{Keypair, NodeId, Software};
use vinc_dtn::forward::Policy;
use vinc_dtn::head::BundleId;
use vinc_dtn::seal::RecipientKeys;
use vinc_node::{DtnApp, Recipient};

use super::core::{keypair, node_id};
use crate::node::data::seed32;
use crate::node::proto::{Contact, DtnInit};

/// The keys a node opens bundles with, derived from its name, so a sender needs only the destination's name.
pub struct Opener {
    /// The published keys.
    pub keys: RecipientKeys,
    dk: <Software as Provider>::KemDecapsKey,
    xs: <Software as Provider>::X25519Secret,
}

/// The bundle keys of the node called `name`.
///
/// # Errors
/// The node's identity could not be made.
pub fn opener(name: &str) -> Result<Opener, String> {
    let p = Software;
    let (dk, ek) = p.kem_keygen(&seed32(name, "vinc-dtn-kem-d"), &seed32(name, "vinc-dtn-kem-z"));
    let xs = p.x25519_secret(&seed32(name, "vinc-dtn-x25519"));
    Ok(Opener {
        keys: RecipientKeys {
            node: node_id(name)?,
            epoch: 1,
            kem_ek: p.kem_encaps_key_bytes(&ek),
            x25519: p.x25519_public(&xs),
        },
        dk,
        xs,
    })
}

/// The hex of `b`.
pub fn hex(b: &[u8]) -> String {
    use std::fmt::Write as _;
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

fn unhex(s: &str) -> Option<[u8; 32]> {
    let mut out = [0u8; 32];
    if s.len() != 64 {
        return None;
    }
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// A contact window: the peer, and when it opens and closes in milliseconds after the start.
type Span = ([u8; 32], u64, u64);

struct On {
    key: Keypair,
    open: Opener,
    init: DtnInit,
    bundles: BTreeMap<BundleId, (Vec<u8>, Vec<u8>)>,
    records: BTreeMap<BundleId, Vec<u8>>,
    /// The start the windows count from and the windows; none for every peer, always.
    contacts: Option<(u64, Vec<Span>)>,
    bytes: u64,
    peak: u64,
}

/// The bundle store of a node: off unless the scenario turned delay-tolerant delivery on for it.
#[derive(Default)]
pub struct DtnStore(Option<Box<On>>);

impl DtnStore {
    /// The store of the node called `name`, loaded from its directory when `init` keeps one there.
    ///
    /// # Errors
    /// The node's keys could not be made or its kept store could not be read.
    pub fn new(name: &str, init: DtnInit) -> Result<Self, String> {
        let mut on = On {
            key: keypair(name)?,
            open: opener(name)?,
            init,
            bundles: BTreeMap::new(),
            records: BTreeMap::new(),
            contacts: None,
            bytes: 0,
            peak: 0,
        };
        if let Some(dir) = on.init.dir.clone() {
            std::fs::create_dir_all(&dir).map_err(|e| format!("the bundle store {dir} could not be made: {e}"))?;
            on.load(Path::new(&dir))?;
        }
        Ok(Self(Some(Box::new(on))))
    }

    /// Whether delay-tolerant delivery is on.
    pub fn is_on(&self) -> bool {
        self.0.is_some()
    }

    /// Whether the store holds records a restarted node resumes from.
    pub fn has_records(&self) -> bool {
        self.0.as_ref().is_some_and(|o| !o.records.is_empty())
    }

    /// The most sealed bytes held at once, and the ledger's budget.
    pub fn peak_and_budget(&self) -> (u64, u64) {
        self.0.as_ref().map_or((0, 0), |o| (o.peak, o.init.budget))
    }

    /// Set the contact windows, counted from the wall clock `t0_ms`; none for every peer, always.
    ///
    /// # Errors
    /// A window names a peer with no identity.
    pub fn set_contacts(&mut self, t0_ms: u64, windows: Option<&[Contact]>) -> Result<(), String> {
        let Some(on) = self.0.as_mut() else {
            return Err("delay-tolerant delivery is not on for this node".into());
        };
        on.contacts = match windows {
            None => None,
            Some(ws) => Some((
                t0_ms,
                ws.iter()
                    .map(|w| node_id(&w.peer).map(|id| (id.bytes, w.from_ms, w.to_ms)))
                    .collect::<Result<_, _>>()?,
            )),
        };
        Ok(())
    }
}

impl On {
    fn dir(&self) -> Option<PathBuf> {
        self.init.dir.as_deref().map(PathBuf::from)
    }

    fn load(&mut self, dir: &Path) -> Result<(), String> {
        let err = |e: std::io::Error| format!("the bundle store {} could not be read: {e}", dir.display());
        for entry in std::fs::read_dir(dir).map_err(err)? {
            let path = entry.map_err(err)?.path();
            let (Some(stem), Some(ext)) = (
                path.file_stem().and_then(|s| s.to_str()).and_then(unhex),
                path.extension().and_then(|s| s.to_str()),
            ) else {
                continue;
            };
            let data = std::fs::read(&path).map_err(err)?;
            let id = BundleId(stem);
            match ext {
                "b" => {
                    let Some((len, rest)) = data.split_first_chunk::<8>() else {
                        continue;
                    };
                    let Some((sealed, outboard)) = usize::try_from(u64::from_le_bytes(*len))
                        .ok()
                        .and_then(|n| (n <= rest.len()).then(|| rest.split_at(n)))
                    else {
                        continue;
                    };
                    self.bytes += sealed.len() as u64;
                    self.bundles.insert(id, (sealed.to_vec(), outboard.to_vec()));
                }
                "r" => {
                    let mut rec = data;
                    // A held record ends with the bundle's signed head: flip its last byte.
                    if self.init.tamper_heads
                        && rec.get(1) == Some(&0)
                        && let Some(last) = rec.last_mut()
                    {
                        *last ^= 0x01;
                    }
                    self.records.insert(id, rec);
                }
                _ => {}
            }
        }
        self.peak = self.bytes;
        Ok(())
    }

    fn write(&self, id: &BundleId, ext: &str, parts: &[&[u8]]) -> bool {
        let Some(dir) = self.dir() else { return true };
        let path = dir.join(format!("{}.{ext}", hex(&id.0)));
        let tmp = dir.join(format!("{}.{ext}.tmp", hex(&id.0)));
        std::fs::write(&tmp, parts.concat())
            .and_then(|()| std::fs::rename(&tmp, &path))
            .is_ok()
    }

    /// Add `more` to the end of a file; a crash may leave a torn tail, which the node's restore ignores.
    fn append(&self, id: &BundleId, ext: &str, more: &[u8]) {
        use std::io::Write as _;
        let Some(dir) = self.dir() else { return };
        let path = dir.join(format!("{}.{ext}", hex(&id.0)));
        if let Ok(mut f) = std::fs::OpenOptions::new().append(true).open(path) {
            let _ = f.write_all(more);
        }
    }

    fn unlink(&self, id: &BundleId, ext: &str) {
        if let Some(dir) = self.dir() {
            let _ = std::fs::remove_file(dir.join(format!("{}.{ext}", hex(&id.0))));
        }
    }
}

impl DtnApp<Software> for DtnStore {
    fn signer(&self) -> Option<&Keypair> {
        self.0.as_ref().map(|o| &o.key)
    }

    fn recipient(&self) -> Option<Recipient<'_, Software>> {
        self.0.as_ref().map(|o| Recipient {
            own: &o.open.keys,
            kem_dk: &o.open.dk,
            x25519: &o.open.xs,
        })
    }

    fn put(&mut self, id: &BundleId, sealed: &[u8], outboard: &[u8]) -> bool {
        let Some(on) = self.0.as_mut() else { return false };
        let mut sealed = sealed.to_vec();
        if on.init.tamper_slices {
            // Every symbol is at least 1 KiB: one flipped byte per KiB corrupts each of them.
            for b in sealed.iter_mut().step_by(1024) {
                *b ^= 0x01;
            }
        }
        if on.init.tamper_one_slice
            && let Some(b) = sealed.first_mut()
        {
            // The first byte is in symbol 0, the first data symbol of the first erasure block.
            *b ^= 0x01;
        }
        let len = (sealed.len() as u64).to_le_bytes();
        if !on.write(id, "b", &[&len, &sealed, outboard]) {
            return false;
        }
        on.bytes += sealed.len() as u64;
        on.peak = on.peak.max(on.bytes);
        if let Some((old, _)) = on.bundles.insert(*id, (sealed, outboard.to_vec())) {
            on.bytes -= old.len() as u64;
        }
        true
    }

    fn get(&self, id: &BundleId) -> Option<(&[u8], &[u8])> {
        let (s, o) = self.0.as_ref()?.bundles.get(id)?;
        Some((s.as_slice(), o.as_slice()))
    }

    fn remove(&mut self, id: &BundleId) {
        if let Some(on) = self.0.as_mut()
            && let Some((s, _)) = on.bundles.remove(id)
        {
            on.bytes -= s.len() as u64;
            on.unlink(id, "b");
        }
    }

    fn budget(&self) -> u64 {
        self.0.as_ref().map_or(0, |o| o.init.budget)
    }

    fn policy(&self) -> Policy {
        self.0.as_ref().map_or(
            Policy {
                retry_ms: 10_000,
                max_sends: 4,
            },
            |o| Policy {
                retry_ms: o.init.retry_ms,
                max_sends: o.init.max_sends,
            },
        )
    }

    fn in_contact(&self, peer: &NodeId, wall_ms: u64) -> bool {
        let Some((t0, ws)) = self.0.as_ref().and_then(|o| o.contacts.as_ref()) else {
            return true;
        };
        ws.iter()
            .any(|(p, a, b)| *p == peer.bytes && t0 + a <= wall_ms && wall_ms < t0 + b)
    }

    fn next_contact_change(&self, wall_ms: u64) -> Option<u64> {
        let (t0, ws) = self.0.as_ref()?.contacts.as_ref()?;
        ws.iter()
            .flat_map(|(_, a, b)| [t0 + a, t0 + b])
            .filter(|e| *e > wall_ms)
            .min()
    }

    fn save_record(&mut self, id: &BundleId, record: &[u8]) {
        if let Some(on) = self.0.as_mut() {
            on.write(id, "r", &[record]);
            on.records.insert(*id, record.to_vec());
        }
    }

    fn append_record(&mut self, id: &BundleId, more: &[u8]) {
        if let Some(on) = self.0.as_mut()
            && let Some(rec) = on.records.get_mut(id)
        {
            rec.extend_from_slice(more);
            on.append(id, "r", more);
        }
    }

    fn drop_record(&mut self, id: &BundleId) {
        if let Some(on) = self.0.as_mut()
            && on.records.remove(id).is_some()
        {
            on.unlink(id, "r");
        }
    }

    fn record_at(&self, n: usize) -> Option<(BundleId, &[u8])> {
        self.0
            .as_ref()?
            .records
            .iter()
            .nth(n)
            .map(|(id, r)| (*id, r.as_slice()))
    }
}
