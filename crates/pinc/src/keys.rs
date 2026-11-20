//! The node's keys: an identity in a key store that the engine owns, and the prekeys that stay in software.
//!
//! The identity key lives in a [`KeyStore`] the engine owns outright: signing takes `&mut`, and both the engine (the
//! handshake) and the application (signing its own messages, as a request to the engine) sign, one at a time on the
//! engine's task, so no lock is needed. The ML-KEM prekeys always live in the engine's own [`SoftwareStore`], as a TPM
//! cannot hold them; the two newest generations are kept so a handshake that began under the old prekey still
//! completes. The seeds of a prekey are drawn from the identity's store, so a host that seeds that store from its own
//! entropy gets prekeys from it too.
//!
//! Invariants: no private key leaves a store; a rotated-out prekey is removed, which zeroizes it, and the seeds of a
//! prekey are zeroized once the key is made; errors name the failed operation and never a key.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;

use pinc_crypto::{IdentityAlg, Keypair, NodeId, Provider, Software};
use pinc_keystore::{KeyHandle, KeyStore, SoftwareStore};
use pinc_security::{KeyHandle as WireHandle, LocalIdentity, PrekeyInfo};
use zeroize::Zeroizing;

use crate::error::{Error, ErrorKind, Result};

/// The handle the handshake uses for the identity key.
const IDENTITY: WireHandle = WireHandle(0);
/// How long a prekey serves new dials: 10 minutes.
pub(crate) const PREKEY_LIFE: u64 = 600_000_000_000;
/// How many handshakes one prekey serves before it is replaced.
pub(crate) const PREKEY_USES: u32 = 64;

/// The node's identity: a key in a store, and the public facts about it.
pub struct Identity<S = SoftwareStore> {
    store: S,
    handle: KeyHandle,
    node: NodeId,
    public: Rc<[u8]>,
    /// The seed of the software key the broadcast layer signs with, when the identity was made from a seed this crate
    /// holds; given up once, by [`take_signer`](Self::take_signer). A key pair is far larger than a seed.
    seed: Option<[u8; 32]>,
}

impl<S> core::fmt::Debug for Identity<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Identity")
            .field("alg", &self.node.alg)
            .finish_non_exhaustive()
    }
}

fn key_error(_: pinc_keystore::KeyStoreError) -> Error {
    Error::new(ErrorKind::Config, "the key store refused the request")
}

impl Identity {
    /// The identity of the Ed25519 key made from `seed`, held in a new in-memory store. Only with the `std` feature.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store cannot start or the seed is refused.
    #[cfg(feature = "std")]
    pub fn from_seed(seed: &[u8; 32]) -> Result<Self> {
        Self::in_store(SoftwareStore::new().map_err(key_error)?, seed)
    }

    /// As `from_seed`, in a store whose random bytes come from a generator seeded with `entropy`:
    /// for a host without an operating system. The host gives fresh entropy at every start; the same entropy gives
    /// the same store keys and nonces.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the seed is refused.
    pub fn from_seed_with(seed: &[u8; 32], entropy: &[u8; 32]) -> Result<Self> {
        Self::in_store(SoftwareStore::from_entropy(*entropy), seed)
    }

    /// A new Ed25519 identity from operating system randomness, held in a new in-memory store. Only with the `std`
    /// feature.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the operating system has no randomness or the store cannot start.
    #[cfg(feature = "std")]
    pub fn generate() -> Result<Self> {
        Self::generate_in(SoftwareStore::new().map_err(key_error)?)
    }

    /// A new Ed25519 identity whose seed and store come from a generator seeded with `entropy`: for a host without an
    /// operating system. The host gives fresh entropy at every start; the same entropy gives the same identity, store
    /// keys and nonces.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the generator cannot give the seed.
    pub fn generate_with(entropy: &[u8; 32]) -> Result<Self> {
        Self::generate_in(SoftwareStore::from_entropy(*entropy))
    }

    /// A new identity whose seed is drawn from `store`, which then holds the key.
    pub(crate) fn generate_in(mut store: SoftwareStore) -> Result<Self> {
        let mut seed = Zeroizing::new([0u8; 32]);
        store.random(seed.as_mut_slice()).map_err(key_error)?;
        Self::in_store(store, &seed)
    }

    /// The identity of the Ed25519 key made from `seed`, held in `store`.
    pub(crate) fn in_store(mut store: SoftwareStore, seed: &[u8; 32]) -> Result<Self> {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, seed)
            .map_err(|_| Error::config("the identity seed is not valid"))?;
        let handle = store.insert(kp);
        let mut id = Self::from_store(store, handle)?;
        id.seed = Some(*seed);
        Ok(id)
    }
}

impl<S: KeyStore> Identity<S> {
    /// The identity of the key `handle` in `store`.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store does not hold an identity key under `handle`.
    pub fn from_store(store: S, handle: KeyHandle) -> Result<Self> {
        let (alg, public) = store.public(&handle).map_err(key_error)?;
        let node = NodeId::from_public(alg, &public).map_err(|_| Error::config("the identity key is not valid"))?;
        Ok(Self {
            store,
            handle,
            node,
            public: public.into(),
            seed: None,
        })
    }

    /// The software key the node's broadcast layer signs with, given up once: `None` for an identity that lives in a
    /// key store the crate cannot take a key out of, or after the key was taken.
    pub(crate) fn take_signer(&mut self) -> Option<Box<Keypair>> {
        let mut seed = self.seed.take()?;
        let key = Keypair::from_seed(IdentityAlg::Ed25519, &seed).ok().map(Box::new);
        seed.fill(0);
        key
    }

    /// The node id.
    pub const fn node_id(&self) -> NodeId {
        self.node
    }

    /// The public key bytes.
    pub fn public_key(&self) -> &[u8] {
        &self.public
    }

    /// Sign `msg` with the identity key.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store fails.
    pub fn sign(&mut self, msg: &[u8]) -> Result<Vec<u8>> {
        self.store
            .sign(&self.handle, msg)
            .map(pinc_keystore::Signature::into_bytes)
            .map_err(key_error)
    }

    /// Seal `plain` for storage at rest with the key store; only a store holding the same sealing key opens it.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store fails.
    pub fn seal(&mut self, plain: &[u8]) -> Result<Vec<u8>> {
        self.store.seal(plain).map_err(key_error)
    }

    /// Open bytes made by [`seal`](Self::seal).
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the bytes were altered or sealed by another store.
    pub fn unseal(&mut self, sealed: &[u8]) -> Result<Vec<u8>> {
        self.store.unseal(sealed).map(|z| z.to_vec()).map_err(key_error)
    }

    /// Mix `entropy` into the generator of the identity's store, for a host that runs a relay part without an
    /// endpoint and keeps the identity it shares with it fresh. A store with a source of its own ignores it.
    pub fn refresh(&mut self, entropy: &[u8; 32]) {
        self.refresh_with(&mut |out| {
            *out = *entropy;
            true
        });
    }

    /// Offer the store fresh entropy through `fresh`, which a store with a source of its own never calls.
    pub(crate) fn refresh_with(&mut self, fresh: &mut dyn FnMut(&mut [u8; 32]) -> bool) {
        self.store.refresh(fresh);
    }

    /// Fill `out` with random bytes from the store.
    pub(crate) fn random(&mut self, out: &mut [u8]) -> Result<()> {
        self.store.random(out).map_err(key_error)
    }

    pub(crate) fn local(&self) -> Result<LocalIdentity> {
        LocalIdentity::new(self.node.alg, &self.public, IDENTITY)
            .map_err(|_| Error::config("the identity key is not valid"))
    }
}

/// The engine's prekeys: the newest and the one before.
pub(crate) struct Prekeys {
    store: SoftwareStore,
    held: Vec<(u64, KeyHandle)>,
    next: u64,
    rotate_at: u64,
    /// Handshakes the newest prekey has served.
    used: u32,
}

impl Prekeys {
    /// Prekeys held in a store made from `entropy`, which only holds the keys.
    pub(crate) fn new(entropy: [u8; 32]) -> Self {
        Self {
            store: SoftwareStore::from_entropy(entropy),
            held: Vec::new(),
            next: 1,
            rotate_at: 0,
            used: 0,
        }
    }

    /// A new prekey to set on the endpoint, its two seeds drawn through `random`; drops all but the previous one.
    pub(crate) fn rotate(&mut self, now: u64, random: &mut dyn FnMut(&mut [u8]) -> Result<()>) -> Result<PrekeyInfo> {
        let mut d = Zeroizing::new([0u8; 32]);
        let mut z = Zeroizing::new([0u8; 32]);
        random(d.as_mut_slice())?;
        random(z.as_mut_slice())?;
        let (dk, ek) = Software.kem_keygen(&d, &z);
        let h = self.store.insert_kem(dk);
        let ek = Software.kem_encaps_key_bytes(&ek);
        let gen_id = self.next;
        self.next += 1;
        self.held.push((gen_id, h));
        while self.held.len() > 2 {
            let (_, old) = self.held.remove(0);
            self.store.remove(&old);
        }
        self.rotate_at = now.saturating_add(PREKEY_LIFE);
        self.used = 0;
        Ok(PrekeyInfo::new(ek, WireHandle(gen_id)))
    }

    /// Whether the newest prekey is past its lifetime or has served [`PREKEY_USES`] handshakes.
    pub(crate) const fn due(&self, now: u64) -> bool {
        now >= self.rotate_at || self.used >= PREKEY_USES
    }

    pub(crate) fn decapsulate(&mut self, key: WireHandle, ct: &[u8]) -> Option<pinc_crypto::Secret<32>> {
        if key.0 == self.next.saturating_sub(1) {
            self.used = self.used.saturating_add(1);
        }
        let (_, h) = self.held.iter().find(|(g, _)| *g == key.0)?;
        self.store.decapsulate(h, ct).ok()
    }
}

#[cfg(test)]
impl Prekeys {
    /// The generations held (oldest first), `next`, `rotate_at` and `used`.
    pub(crate) fn view(&self) -> (Vec<u64>, u64, u64, u32) {
        (
            self.held.iter().map(|(g, _)| *g).collect(),
            self.next,
            self.rotate_at,
            self.used,
        )
    }
}

/// Whether a wire handle names the identity key.
pub(crate) const fn is_identity(key: WireHandle) -> bool {
    key.0 == IDENTITY.0
}

/// What the trace tests of the prekeys share: the output file and the word encoding.
#[cfg(test)]
pub(crate) mod trace_out {
    use alloc::format;
    use alloc::string::String;

    /// A `u64` as the four 16-bit limbs the trace models read, least significant first.
    pub(crate) fn limbs(v: u64) -> String {
        format!(
            "[{},{},{},{}]",
            v & 0xffff,
            (v >> 16) & 0xffff,
            (v >> 32) & 0xffff,
            v >> 48
        )
    }

    /// Append `lines` to `prekeys.ndjson` under `PINC_TRACE_DIR`, in one write; nothing when the variable is unset.
    #[allow(clippy::unwrap_used, reason = "tests assert")]
    pub(crate) fn append(lines: &str) {
        use std::io::Write as _;
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            let mut f = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(std::path::Path::new(&dir).join("prekeys.ndjson"))
                .unwrap();
            f.write_all(lines.as_bytes()).unwrap();
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use alloc::format;
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;
    use core::fmt::Write as _;

    use super::*;

    #[test]
    fn a_prekey_is_replaced_after_64_handshakes_or_its_lifetime() {
        let mut p = Prekeys::new([5; 32]);
        let mut store = SoftwareStore::from_entropy([1; 32]);
        let mut os = |out: &mut [u8]| store.random(out).map_err(key_error);
        assert!(p.due(0), "no prekey yet");
        p.rotate(1, &mut os).unwrap();
        assert!(!p.due(2));
        let newest = WireHandle(1);
        for _ in 0..PREKEY_USES - 1 {
            let _ = p.decapsulate(newest, &[]);
        }
        assert!(!p.due(2), "63 handshakes");
        let _ = p.decapsulate(newest, &[]);
        assert!(p.due(2), "the 64th");
        p.rotate(3, &mut os).unwrap();
        assert!(!p.due(4), "a new prekey starts at zero");
        // A handshake that began under the previous prekey does not count against the new one.
        let _ = p.decapsulate(newest, &[]);
        assert!(!p.due(4));
        assert!(p.due(3 + PREKEY_LIFE), "its lifetime");
    }

    /// A `random` that replays `stream`, 32 bytes at a time.
    fn replay(stream: &[u8]) -> impl FnMut(&mut [u8]) -> Result<()> + '_ {
        let mut at = 0;
        move |out| {
            out.copy_from_slice(&stream[at..at + out.len()]);
            at += out.len();
            Ok(())
        }
    }

    #[test]
    fn a_prekey_follows_the_bytes_drawn_for_it() {
        let key = |stream: &[u8]| Prekeys::new([1; 32]).rotate(1, &mut replay(stream)).unwrap();
        let a: Vec<u8> = (0..64).collect();
        let mut b = a.clone();
        b[0] ^= 1;
        let (first, again, other) = (key(&a), key(&a), key(&b));
        assert_eq!(first.encaps_key(), again.encaps_key());
        assert_ne!(first.encaps_key(), other.encaps_key());
    }

    #[cfg(feature = "std")]
    #[test]
    fn an_operating_system_identity_is_not_offered_fresh_entropy() {
        let mut id = Identity::from_seed(&[2; 32]).unwrap();
        let mut asked = 0;
        id.refresh_with(&mut |_| {
            asked += 1;
            true
        });
        assert_eq!(asked, 0);
        let mut seeded = Identity::generate_with(&[3; 32]).unwrap();
        seeded.refresh_with(&mut |_| {
            asked += 1;
            true
        });
        assert_eq!(asked, 1);
    }

    #[test]
    fn the_same_entropy_gives_the_same_identity_and_other_entropy_another() {
        let node = |e: u8| Identity::generate_with(&[e; 32]).unwrap().node_id();
        assert_eq!(node(1), node(1));
        assert_ne!(node(1), node(2));
        let seeded = |e: u8| Identity::from_seed_with(&[9; 32], &[e; 32]).unwrap().node_id();
        assert_eq!(seeded(1), seeded(2));
    }

    /// A small generator for the seeded runs (the crate's unit tests cannot use `pinc_tests`).
    struct SplitMix64(u64);

    impl SplitMix64 {
        fn next_u64(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
    }

    /// A `Prekeys` beside a reference written from its documentation; every call is checked against the reference
    /// and recorded.
    struct Run {
        p: Prekeys,
        store: SoftwareStore,
        held: Vec<u64>,
        next: u64,
        at: u64,
        used: u32,
        infos: Vec<(u64, PrekeyInfo)>,
        out: String,
    }

    impl Run {
        fn new(k: u8) -> Self {
            let mut r = Self {
                p: Prekeys::new([k; 32]),
                store: SoftwareStore::from_entropy([k; 32]),
                held: Vec::new(),
                next: 1,
                at: 0,
                used: 0,
                infos: Vec::new(),
                out: String::new(),
            };
            r.event("new", "");
            r
        }

        fn st(&self) -> String {
            let held: Vec<String> = self.held.iter().map(ToString::to_string).collect();
            format!(
                r#"{{"held":[{}],"next":{},"at":{},"used":{}}}"#,
                held.join(","),
                self.next,
                trace_out::limbs(self.at),
                self.used
            )
        }

        /// Check the state against the reference, then record the event with the state after it.
        fn event(&mut self, op: &str, fields: &str) {
            let (held, next, at, used) = self.p.view();
            assert_eq!(
                (held, next, at, used),
                (self.held.clone(), self.next, self.at, self.used)
            );
            assert!(next < 1 << 31 && used < 1 << 31, "a number past what the model reads");
            let st = self.st();
            writeln!(self.out, r#"{{"t":"pk","op":"{op}"{fields},"st":{st}}}"#).unwrap();
        }

        /// `rotate`; `fail` is the draw (1 or 2) that the host's source refuses.
        fn rot(&mut self, now: u64, fail: Option<u32>) {
            let mut draws = 0;
            let store = &mut self.store;
            let mut random = |out: &mut [u8]| {
                draws += 1;
                if fail == Some(draws) {
                    Err(key_error(pinc_keystore::KeyStoreError::Entropy))
                } else {
                    store.random(out).map_err(key_error)
                }
            };
            let res = self.p.rotate(now, &mut random);
            let mut gen_id = 0;
            match res {
                Ok(info) => {
                    assert!(fail.is_none());
                    gen_id = info.handle().0;
                    assert_eq!(gen_id, self.next, "the handle is the new generation");
                    self.held.push(self.next);
                    while self.held.len() > 2 {
                        self.held.remove(0);
                    }
                    self.at = now.saturating_add(PREKEY_LIFE);
                    self.used = 0;
                    self.next += 1;
                    self.infos.push((gen_id, info));
                }
                Err(_) => assert!(fail.is_some()),
            }
            let fields = format!(
                r#","now":{},"ok":{},"res":{},"gen":{gen_id}"#,
                trace_out::limbs(now),
                fail.is_none(),
                gen_id != 0
            );
            self.event("rot", &fields);
        }

        fn due(&mut self, now: u64) {
            let r = self.p.due(now);
            assert_eq!(r, now >= self.at || self.used >= PREKEY_USES);
            writeln!(
                self.out,
                r#"{{"t":"pk","op":"due","now":{},"r":{r}}}"#,
                trace_out::limbs(now)
            )
            .unwrap();
        }

        /// `decapsulate` of generation `h`, with a real encapsulation when `valid` and the generation was issued.
        fn dec(&mut self, h: u64, valid: bool) {
            let info = self.infos.iter().find(|(g, _)| *g == h).map(|(_, i)| i.clone());
            let (ct, want) = match info.filter(|_| valid) {
                Some(info) => {
                    let ek = Software.kem_encaps_key(info.encaps_key()).unwrap();
                    let m = [h.to_le_bytes()[0] ^ 0x5a; 32];
                    let (ct, secret) = Software.kem_encapsulate(&ek, &m).unwrap();
                    (Software.kem_ciphertext_bytes(&ct).to_vec(), Some(*secret.expose()))
                }
                None => (Vec::new(), None),
            };
            if h == self.next.saturating_sub(1) {
                self.used = self.used.saturating_add(1);
            }
            let answered = want.is_some() && self.held.contains(&h);
            let got = self.p.decapsulate(WireHandle(h), &ct);
            assert_eq!(got.is_some(), answered, "answered exactly when held and valid");
            if let Some(secret) = got {
                assert_eq!(Some(*secret.expose()), want, "the encapsulated secret");
            }
            let fields = format!(r#","h":{h},"valid":{},"ans":{answered}"#, want.is_some());
            self.event("dec", &fields);
        }
    }

    const TOP_START: u64 = u64::MAX - PREKEY_LIFE;

    #[test]
    fn trace_prekeys() {
        let mut out = String::new();
        let mut r = Run::new(1);
        r.due(0);
        r.dec(0, false);
        r.dec(1, false);
        r.rot(0, None);
        for now in [0, 1, PREKEY_LIFE - 1, PREKEY_LIFE] {
            r.due(now);
        }
        for _ in 0..63 {
            r.dec(1, true);
        }
        r.due(1);
        r.dec(1, true);
        r.due(1);
        r.dec(0, false);
        r.rot(3, None);
        r.dec(1, true);
        r.due(4);
        r.rot(5, Some(1));
        r.rot(5, Some(2));
        r.rot(6, None);
        r.dec(1, true);
        r.dec(2, true);
        r.dec(3, true);
        r.dec(4, false);
        r.rot(1_000_000_000_000, None);
        r.due(5);
        r.rot(5, None);
        r.rot(TOP_START, None);
        r.due(u64::MAX - 1);
        r.due(u64::MAX);
        r.rot(u64::MAX - 1, None);
        r.rot(u64::MAX, None);
        r.due(u64::MAX);
        r.rot(0, None);
        out.push_str(&r.out);
        for seed in 1..=8u64 {
            let mut r = Run::new(u8::try_from(seed).unwrap());
            let mut rng = SplitMix64(seed);
            let mut last = 0u64;
            for _ in 0..200 {
                let now = match rng.next_u64() % 14 {
                    0 => 0,
                    1 => 1,
                    2 => 2,
                    3 => PREKEY_LIFE - 1,
                    4 => PREKEY_LIFE,
                    5 => PREKEY_LIFE + 1,
                    6 => TOP_START - 1,
                    7 => TOP_START,
                    8 => u64::MAX - 1,
                    9 => u64::MAX,
                    10 => last,
                    11 => last.saturating_sub(1),
                    12 => last.saturating_add(1),
                    _ => last.saturating_add(rng.next_u64() % 1_000_000_000_000),
                };
                last = now;
                match rng.next_u64() % 8 {
                    0 | 1 => {
                        let fail =
                            (rng.next_u64().is_multiple_of(8)).then(|| 1 + u32::from(rng.next_u64().is_multiple_of(2)));
                        r.rot(now, fail);
                    }
                    2..=5 => {
                        let h = rng.next_u64() % (r.next + 2);
                        r.dec(h, !rng.next_u64().is_multiple_of(4));
                    }
                    _ => r.due(now),
                }
            }
            out.push_str(&r.out);
        }
        trace_out::append(&out);
    }
}
