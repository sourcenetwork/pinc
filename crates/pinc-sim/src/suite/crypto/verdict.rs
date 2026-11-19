//! The security verdicts: what the harvest-now-decrypt-later and the compromising adversary know, nonce reuse,
//! plaintext payload on the wire, third-party bytes and amplification.
//!
//! The knowledge rules are the reference harness's, applied to the terms the ledger recorded: the HNDL adversary
//! knows every `Dh` term, the adversary chosen terms, and a `KemSs` only if its decapsulation key is compromised; the
//! classical adversary after a compromise knows the compromised terms, and a `Dh` iff one of its private terms is
//! compromised; a `Hkdf` is known iff it has secret inputs and all of them are known.
//!
//! What the runner must feed: [`Registry::scan_wire`] with every datagram a node puts on the wire (its sender and the
//! bytes as they cross the network); [`Registry::note_compromise`] at the compromise time with the identity seed and
//! the bytes of the node's exported state; the virtual time in [`Registry::now`] before each call into a node; and
//! to [`Registry::sec_verdict`] the amplification ledger, one `(bytes received from, bytes sent to)` pair per
//! unvalidated source address, which only the simulator can count.

use std::collections::BTreeSet;

use super::payload::{MsgId, PayloadKind, mix};
use super::registry::{PayloadKey, Registry, Term, TermId};

/// A reuse of one AEAD key and nonce for different content.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NonceReuse {
    /// The node that sealed the second message.
    pub node: usize,
    /// Virtual time of the second seal.
    pub at_ns: u64,
}

/// One compromise: the terms the adversary learned from a node at a time.
#[derive(Debug, Clone)]
pub(super) struct Compromise {
    pub(super) time: u64,
    pub(super) node: usize,
    pub(super) terms: BTreeSet<TermId>,
}

/// What a seal reads from the plaintext before encrypting it.
pub(super) struct PreSeal {
    has_payload: bool,
    content: u64,
    len: u64,
}

/// The first payload seen unencrypted on the wire.
#[derive(Debug, Clone, Copy)]
pub(super) struct PlaintextSeen {
    pub(super) sender: usize,
    pub(super) at_ns: u64,
}

/// The first offending key or event of a check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Finding {
    /// The key's term, when the finding is about a key.
    pub term: Option<TermId>,
    /// The node involved.
    pub node: usize,
    /// Virtual time of the key's first payload, or of the event.
    pub at_ns: u64,
}

/// What a datagram shows to someone on the path.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct WireScan {
    /// Application payload is visible in the datagram bytes.
    pub plaintext_payload: bool,
    /// The datagram carries an AEAD tag made by another node, or another node's message payload.
    pub third_party: bool,
    /// The messages whose payload blocks are visible, in order of appearance.
    pub payload_msgs: Vec<MsgId>,
}

/// The outcome of the security checks of a run; every field empty or false is a pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SecReport {
    /// A payload key a harvest-now-decrypt-later adversary can compute.
    pub hndl: Option<Finding>,
    /// A payload key used before a compromise that the compromising adversary can compute.
    pub forward_secrecy: Option<Finding>,
    /// Payload bytes seen unencrypted on the wire.
    pub plaintext_payload: Option<Finding>,
    /// Reused (key, nonce) pairs with different content, at most 16.
    pub nonce_reuse: Vec<NonceReuse>,
    /// A payload key whose derivation the ledger did not see completely: the verdict cannot be trusted for it.
    pub unknown_provenance: Option<Finding>,
    /// More than three times the received bytes were sent to an unvalidated address.
    pub amplification: bool,
    /// Seals under keys of unknown provenance, of any content (informational: where the tracking is incomplete).
    pub unknown_key_seals: u64,
}

impl SecReport {
    /// The gate messages of the failed checks, in the reference's order.
    pub fn failures(&self) -> Vec<&'static str> {
        let mut out = Vec::new();
        let mut push = |on: bool, msg: &'static str| {
            if on {
                out.push(msg);
            }
        };
        push(
            self.hndl.is_some(),
            "payload readable by the harvest-now-decrypt-later adversary",
        );
        push(
            self.forward_secrecy.is_some(),
            "sessions before a key compromise are readable (forward secrecy)",
        );
        push(
            self.plaintext_payload.is_some(),
            "payload sent in plaintext on the wire",
        );
        push(
            !self.nonce_reuse.is_empty(),
            "AEAD nonce reused under one key with different content",
        );
        push(
            self.amplification,
            "more than 3x the received bytes sent to an unvalidated address",
        );
        push(
            self.unknown_provenance.is_some(),
            "payload sealed under a key whose derivation was not tracked",
        );
        out
    }

    /// No check failed.
    pub fn clean(&self) -> bool {
        self.failures().is_empty()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Hndl,
    Classical,
}

/// Per term: can the adversary compute it? One pass in id order, which is a topological order of the terms.
fn knowledge(terms: &[Term], mode: Mode, compromised: &BTreeSet<TermId>) -> Vec<bool> {
    let mut known = vec![false; terms.len()];
    for (i, t) in terms.iter().enumerate() {
        let hit = |x: &TermId| compromised.contains(x);
        known[i] = compromised.contains(&(i as TermId))
            || match t {
                Term::DhAdv | Term::KemAdv => true,
                Term::Dh(a, b) => mode == Mode::Hndl || hit(a) || hit(b),
                Term::KemSs { owner, .. } => hit(owner),
                Term::Hkdf { inputs, .. } => inputs.iter().all(|&j| known[j as usize]),
                Term::Rand(_) | Term::XSk(_) | Term::KemSk(_) | Term::KemRej(..) | Term::Unknown(_) => false,
            };
    }
    known
}

fn finding(k: &PayloadKey) -> Finding {
    Finding {
        term: Some(k.term),
        node: k.node,
        at_ns: k.first_ns,
    }
}

/// A cheap 64-bit fold of `bytes`, 8 bytes at a time, to compare plaintexts of equal (key, nonce).
fn fold64(seed: u64, bytes: &[u8]) -> u64 {
    let mut h = seed ^ bytes.len() as u64;
    let (words, rest) = bytes.as_chunks::<8>();
    for c in words {
        h = (h ^ u64::from_le_bytes(*c))
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .rotate_left(29);
    }
    for &b in rest {
        h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01B3);
    }
    mix(h)
}

impl Registry {
    /// The adversary compromised `node` at `now`: it learned every registered secret that occurs in the identity
    /// seed or in the bytes of the node's exported state.
    pub fn note_compromise(&self, node: usize, now: u64, identity_seed: &[u8], exported_state: &[u8]) {
        let mut st = self.st.borrow_mut();
        let mut terms = st.scan_all(identity_seed);
        terms.extend(st.scan_all(exported_state));
        st.compromises.push(Compromise { time: now, node, terms });
    }

    /// The terms learned by the compromises so far, as `(time, node, terms)`.
    pub fn compromises(&self) -> Vec<(u64, usize, Vec<TermId>)> {
        let st = self.st.borrow();
        st.compromises
            .iter()
            .map(|c| (c.time, c.node, c.terms.iter().copied().collect()))
            .collect()
    }

    /// Read what a seal needs from the plaintext before the cipher overwrites it.
    pub(super) fn pre_seal(&self, aad: &[u8], plain: &[u8]) -> PreSeal {
        PreSeal {
            has_payload: self.has_blocks(plain),
            content: fold64(fold64(0x5EA1, aad), plain),
            len: plain.len() as u64,
        }
    }

    /// Record a seal: nonce reuse, the tag's maker, payload under the key, the key's use and the work.
    pub(super) fn record_seal(&self, node: usize, key: TermId, nonce: &[u8; 12], pre: &PreSeal, tag: &[u8; 16]) {
        let lo = u64::from_le_bytes([
            nonce[0], nonce[1], nonce[2], nonce[3], nonce[4], nonce[5], nonce[6], nonce[7],
        ]);
        let hi = u64::from(u32::from_le_bytes([nonce[8], nonce[9], nonce[10], nonce[11]]));
        let fp = mix(u64::from(key) ^ mix(lo ^ mix(hi)));
        let now = self.now.get();
        let mut st = self.st.borrow_mut();
        match st.nonce_use.get(&fp) {
            None => {
                st.nonce_use.insert(fp, pre.content);
            }
            Some(&prev) if prev != pre.content && st.nonce_reuse.len() < 16 => {
                st.nonce_reuse.push(NonceReuse { node, at_ns: now });
            }
            Some(_) => {}
        }
        let tag_key = u64::from_le_bytes([tag[0], tag[1], tag[2], tag[3], tag[4], tag[5], tag[6], tag[7]]);
        st.note_tag(tag_key, node as u32);
        if pre.has_payload {
            st.payload_keys.entry(key).or_insert(PayloadKey {
                term: key,
                first_ns: now,
                node,
            });
        }
        *st.key_seals.entry(u64::from(key)).or_insert(0) += 1;
        let w = st.work_mut(node);
        w.aead += 1;
        w.aead_bytes += pre.len;
    }

    /// What the datagram `datagram`, sent by node `sender`, shows on the wire. The first plaintext payload is kept
    /// for [`Registry::sec_verdict`].
    pub fn scan_wire(&self, sender: usize, datagram: &[u8]) -> WireScan {
        let mut scan = WireScan::default();
        for (msg, _) in self.find_blocks(datagram) {
            if !scan.payload_msgs.contains(&msg) {
                scan.payload_msgs.push(msg);
            }
        }
        scan.plaintext_payload = !scan.payload_msgs.is_empty();
        scan.third_party = scan.payload_msgs.iter().any(|&m| {
            self.msg_meta(m)
                .is_some_and(|meta| meta.kind == PayloadKind::Msg && meta.creator != sender)
        });
        let now = self.now.get();
        let mut st = self.st.borrow_mut();
        if scan.plaintext_payload && st.plaintext.is_none() {
            st.plaintext = Some(PlaintextSeen { sender, at_ns: now });
        }
        if !scan.third_party && !st.tags.is_empty() {
            scan.third_party = datagram.windows(8).any(|w| {
                let k = u64::from_le_bytes([w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]);
                st.tag_maker(k).is_some_and(|maker| maker as usize != sender)
            });
        }
        scan
    }

    /// Decide the security checks. `amplification` has one `(bytes received from, bytes sent to)` pair per
    /// unvalidated source address.
    pub fn sec_verdict(&self, amplification: impl IntoIterator<Item = (u64, u64)>) -> SecReport {
        let unknown = self.unknown_flags();
        let st = self.st.borrow();
        let mut report = SecReport {
            plaintext_payload: st.plaintext.map(|p| Finding {
                term: None,
                node: p.sender,
                at_ns: p.at_ns,
            }),
            nonce_reuse: st.nonce_reuse.clone(),
            amplification: amplification.into_iter().any(|(rx, tx)| tx > 3 * rx.max(1)),
            ..SecReport::default()
        };
        let none = BTreeSet::new();
        let hndl = knowledge(&st.terms, Mode::Hndl, &none);
        report.hndl = st.payload_keys.values().find(|k| hndl[k.term as usize]).map(finding);
        report.unknown_provenance = st.payload_keys.values().find(|k| unknown[k.term as usize]).map(finding);
        for c in &st.compromises {
            let known = knowledge(&st.terms, Mode::Classical, &c.terms);
            if let Some(k) = st
                .payload_keys
                .values()
                .find(|k| k.first_ns < c.time && known[k.term as usize])
            {
                report.forward_secrecy = Some(finding(k));
                break;
            }
        }
        report.unknown_key_seals = st
            .key_seals
            .iter()
            .filter(|(k, _)| unknown.get(**k as usize).copied().unwrap_or(false))
            .map(|(_, n)| *n)
            .sum();
        report
    }
}
