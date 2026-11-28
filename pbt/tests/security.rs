//! `pinc-security`: the handshake state machines fed generated schedules of their real flights (dropped,
//! duplicated, reordered, cut, bit-flipped, replayed to a second responder) and garbage, with delayed key answers
//! and loss timers; the record layer; the client ticket store.
//!
//! Where the expected behaviour comes from:
//! - `initiator` module doc: "a Reply or a resume Reply that fails any check before that (its key share, its AEAD,
//!   the sealed block, the identity in it, the signature) is dropped as [`Failure::Authentication`] and the machine
//!   waits for the real one ... Only a failure after the responder authenticated, or of the host's own key
//!   operation, is fatal"; "the Finish ... goes out only after the responder's signature verified and its node id
//!   equals the dialed one"; "A fatal failure stops the machine and is reported once as an event";
//! - `responder` module doc: "it is established only when the initiator's Finish authenticated (full handshake) or
//!   when the ticket's binder verified (resumption). A ticket is removed from the store only after its binder
//!   verified ... and an exact replay of a good Hello finds the ticket gone and is rejected";
//! - `tests/sec_common.rs` `assert_same_keys`: what two established sides agree on;
//! - `record`: "a number is never sealed twice under one key"; the AEAD rejects any change of packet, header, number
//!   or key ("The tag does not match: the packet, its header, its number or the key is wrong");
//! - `tickets`: `export` writes "the newest at most `max` unexpired tickets", `restore` stores "every entry that has
//!   not expired by `now`", and `take` hands a ticket out once.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    missing_docs
)]

use ephyra::prelude::*;
use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::{Aead, Capabilities, CryptoError, Drbg, IdentityAlg, Keypair, NodeId, Provider, Secret, Software};
use pinc_pbt::bytes;
use pinc_security::{
    AlpnList, ClientTickets, ConnId, CreditRecord, Env, Established, Event, Failure, Initiator, InitiatorParams,
    KeyHandle, LocalIdentity, Output, PacketKey, PrekeyPolicy, RecordError, Responder, ResponderConfig,
    ResponderStores, SoftKeys, SoftPrekeys,
};

/// [`Software`] with a chosen answer to "does AES-GCM run on hardware", so both AEADs are reached (as in
/// `tests/sec_common.rs`).
#[derive(Debug, Clone, Copy)]
struct Caps(Software, bool);

impl Provider for Caps {
    type AeadKey = <Software as Provider>::AeadKey;
    type HpKey = <Software as Provider>::HpKey;
    type X25519Secret = <Software as Provider>::X25519Secret;
    type KemEncapsKey = <Software as Provider>::KemEncapsKey;
    type KemDecapsKey = <Software as Provider>::KemDecapsKey;
    type KemCiphertext = <Software as Provider>::KemCiphertext;

    fn capabilities(&self) -> Capabilities {
        Capabilities {
            aes_gcm_hw: self.1,
            chacha20_simd: false,
        }
    }
    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<Self::AeadKey, CryptoError> {
        self.0.aead_key(alg, key)
    }
    fn seal(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError> {
        self.0.seal(key, nonce, aad, buf)
    }
    fn open(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError> {
        self.0.open(key, nonce, aad, buf, tag)
    }
    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<Self::HpKey, CryptoError> {
        self.0.hp_key(alg, key)
    }
    fn hp_mask(&self, key: &Self::HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN] {
        self.0.hp_mask(key, sample)
    }
    fn sha256(&self, data: &[u8]) -> [u8; 32] {
        self.0.sha256(data)
    }
    fn x25519_secret(&self, seed: &[u8; 32]) -> Self::X25519Secret {
        self.0.x25519_secret(seed)
    }
    fn x25519_public(&self, secret: &Self::X25519Secret) -> [u8; 32] {
        self.0.x25519_public(secret)
    }
    fn x25519_dh(&self, secret: &Self::X25519Secret, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError> {
        self.0.x25519_dh(secret, peer)
    }
    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (Self::KemDecapsKey, Self::KemEncapsKey) {
        self.0.kem_keygen(d, z)
    }
    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<Self::KemEncapsKey, CryptoError> {
        self.0.kem_encaps_key(bytes)
    }
    fn kem_encaps_key_bytes(&self, ek: &Self::KemEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN] {
        self.0.kem_encaps_key_bytes(ek)
    }
    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<Self::KemCiphertext, CryptoError> {
        self.0.kem_ciphertext(bytes)
    }
    fn kem_ciphertext_bytes(&self, ct: &Self::KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN] {
        self.0.kem_ciphertext_bytes(ct)
    }
    fn kem_encapsulate(
        &self,
        ek: &Self::KemEncapsKey,
        m: &[u8; 32],
    ) -> Result<(Self::KemCiphertext, Secret<32>), CryptoError> {
        self.0.kem_encapsulate(ek, m)
    }
    fn kem_decapsulate(&self, dk: &Self::KemDecapsKey, ct: &Self::KemCiphertext) -> Result<Secret<32>, CryptoError> {
        self.0.kem_decapsulate(dk, ct)
    }
}

const ALPN: &[u8] = b"pinc/1";
const T0: u64 = 1_000_000_000_000;
type Stores = ResponderStores<8, 16>;

struct Party {
    kp: Keypair,
    id: LocalIdentity,
}

fn party(alg: IdentityAlg, tag: u8) -> Party {
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    Party { kp, id }
}

/// How the run starts.
#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Setup {
    #[ephyra(gen = algs())]
    i_alg: u8,
    #[ephyra(gen = algs())]
    r_alg: u8,
    i_hw: bool,
    r_hw: bool,
    /// 0: a full handshake; 1: the short Initial to a responder that cached the prekey (after one full handshake);
    /// 2: the short Initial to a responder that did not; 3: resumption with a ticket of an earlier session.
    #[ephyra(gen = gens::int(0u8..=3))]
    mode: u8,
    /// Whether the host allows short Initials on resends.
    short_ok: bool,
    #[ephyra(gen = gens::int(0u8..=4))]
    tickets_per_session: u8,
}

/// One event of the run. `side` false is toward the responder, true toward the initiator.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    /// Deliver a message in flight (an index into the queue: reordering).
    Deliver(bool, #[ephyra(gen = gens::int(0u8..=7))] u8),
    /// Deliver the oldest message in flight.
    DeliverFirst(bool),
    Drop(bool, #[ephyra(gen = gens::int(0u8..=7))] u8),
    Dup(bool, #[ephyra(gen = gens::int(0u8..=7))] u8),
    /// Flip bits of one byte of a message in flight.
    Flip(
        bool,
        #[ephyra(gen = gens::int(0u8..=7))] u8,
        #[ephyra(gen = gens::int(0u16..=4000))] u16,
        #[ephyra(gen = gens::int(1u8..=255))] u8,
    ),
    /// Cut a message in flight.
    Cut(bool, #[ephyra(gen = gens::int(0u8..=7))] u8, #[ephyra(gen = gens::int(0u16..=4000))] u16),
    /// Hand a side a message of a known type byte with random contents, or a real message with bytes appended.
    Garbage(bool, #[ephyra(gen = gens::int(0u8..=9))] u8, #[ephyra(gen = bytes(120))] Vec<u8>),
    Extend(bool, #[ephyra(gen = gens::int(0u8..=7))] u8, #[ephyra(gen = bytes(8))] Vec<u8>),
    /// Hand a side again a message the other side sent earlier.
    Replay(bool, #[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Hand an earlier message toward the responder to a fresh responder sharing the stores (an attacker replays the
    /// first flight to another connection of the same node).
    ReplayFresh(#[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Answer a side's outstanding key request now.
    Keys(bool),
    /// A side's loss timer.
    Retransmit(bool),
    /// The transport received a 1-RTT packet: the side sheds what the handshake no longer needs.
    Shed(bool),
    /// Time passes (seconds): past a prekey's lifetime, past a ticket's.
    Clock(#[ephyra(gen = gens::pick_from(vec![1u64, 60, 601, 86_401]))] u64),
}

fn runs() -> impl Gen<Value = (Setup, Vec<Op>)> {
    (ephyra::any::<Setup>(), gens::vec(ephyra::any::<Op>()).len(0..=50))
}

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

/// Mostly the fast algorithms; the post-quantum ones (large keys and signatures) now and then.
fn algs() -> impl Gen<Value = u8> {
    gens::frequency(vec![(6, gens::int(0u8..=1).boxed()), (1, gens::int(2u8..=3).boxed())])
}

#[derive(Default)]
struct Seen {
    established: Vec<Established>,
    failed: Vec<Failure>,
}

struct Net {
    ip: Party,
    rp: Party,
    i_prov: Caps,
    r_prov: Caps,
    i_drbg: Drbg,
    r_drbg: Drbg,
    now: u64,
    prekeys: SoftPrekeys<Caps>,
    stores: Box<Stores>,
    i: Initiator,
    r: Responder,
    fresh: Vec<Responder>,
    to_r: Vec<Vec<u8>>,
    to_i: Vec<Vec<u8>>,
    hist_r: Vec<Vec<u8>>,
    hist_i: Vec<Vec<u8>>,
    i_seen: Seen,
    r_seen: Seen,
    fresh_seen: Vec<Seen>,
    /// A message was changed or made up: completion is not owed.
    tainted: bool,
    resume: bool,
}

fn responder(rp: &Party, tickets: u8) -> Responder {
    let mut cfg = ResponderConfig::new(
        rp.id,
        ConnId::new(b"respond0").unwrap(),
        AlpnList::new(&[ALPN, b"pinc/2"]).unwrap(),
    );
    cfg.tickets_per_session = tickets;
    Responder::new(cfg)
}

fn record(seen: &mut Seen, e: Event) {
    match e {
        Event::Established(x) => seen.established.push(x),
        Event::Failed(f) => seen.failed.push(f),
        Event::EarlyKeys(_) | Event::ResumeRejected => {}
    }
}

/// Drain one machine's outputs into `to` (and `hist`), its events into `seen`. Key requests stay outstanding until a
/// `Keys` step.
macro_rules! drain {
    ($m:expr, $to:expr, $hist:expr, $seen:expr) => {{
        for _ in 0..16 {
            match $m.poll_output() {
                Some(Output::Send { data, .. }) => {
                    $to.push(data.to_vec());
                    $hist.push(data.to_vec());
                }
                Some(Output::Event(e)) => record(&mut $seen, e),
                Some(Output::Key(_)) => {}
                None => break,
            }
        }
    }};
}

impl Net {
    fn new(s: &Setup) -> Self {
        let i_prov = Caps(Software, s.i_hw);
        let r_prov = Caps(Software, s.r_hw);
        let mut i_drbg = Drbg::new(&[0x11; 32]);
        let mut r_drbg = Drbg::new(&[0x33; 32]);
        let ip = party(ALGS[usize::from(s.i_alg)], 0x21);
        let rp = party(ALGS[usize::from(s.r_alg)], 0x22);
        let now = T0;
        let mut prekeys = SoftPrekeys::new(
            &mut Env {
                provider: &i_prov,
                now,
                drbg: &mut i_drbg,
            },
            PrekeyPolicy::default(),
        )
        .unwrap();
        let mut stores: Box<Stores> = Box::default();
        let mut client: ClientTickets<16> = ClientTickets::new();
        // An earlier, clean full handshake when the mode needs what it leaves behind.
        if s.mode == 1 || s.mode == 3 {
            let (ie, re) = clean_handshake(&ip, &rp, &i_prov, &r_prov, &mut i_drbg, &mut r_drbg, &mut prekeys, &mut stores);
            client.accept_batch(&ie, &re.tickets, now);
        }
        let mut env = Env {
            provider: &i_prov,
            now,
            drbg: &mut i_drbg,
        };
        let prekey = prekeys.acquire(&mut env).unwrap();
        let dial = rp.id.node_id();
        let ticket = if s.mode == 3 { client.take(&dial, ALPN, now) } else { None };
        let resume = ticket.is_some();
        let mut i = Initiator::new(
            &mut env,
            InitiatorParams {
                peer: dial,
                alpn: ALPN,
                scid: ConnId::new(b"initiat0").unwrap(),
                identity: &ip.id,
                prekey: &prekey,
                peer_has_prekey: s.mode == 1 || s.mode == 2,
                ticket,
                credit: CreditRecord::NONE,
            },
        )
        .unwrap();
        if s.short_ok {
            i.set_short_until(u64::MAX);
        }
        let r = responder(&rp, s.tickets_per_session);
        let mut n = Self {
            ip,
            rp,
            i_prov,
            r_prov,
            i_drbg,
            r_drbg,
            now,
            prekeys,
            stores,
            i,
            r,
            fresh: Vec::new(),
            to_r: Vec::new(),
            to_i: Vec::new(),
            hist_r: Vec::new(),
            hist_i: Vec::new(),
            i_seen: Seen::default(),
            r_seen: Seen::default(),
            fresh_seen: Vec::new(),
            tainted: false,
            resume,
        };
        drain!(n.i, n.to_r, n.hist_r, n.i_seen);
        n
    }

    fn to_i_side(&mut self, m: &[u8]) {
        let mut env = Env {
            provider: &self.i_prov,
            now: self.now,
            drbg: &mut self.i_drbg,
        };
        let _ = self.i.handle(&mut env, m);
        drain!(self.i, self.to_r, self.hist_r, self.i_seen);
    }

    fn to_r_side(&mut self, m: &[u8]) {
        let mut env = Env {
            provider: &self.r_prov,
            now: self.now,
            drbg: &mut self.r_drbg,
        };
        let _ = self.r.handle(&mut env, &mut self.stores, m);
        drain!(self.r, self.to_i, self.hist_i, self.r_seen);
    }

    fn keys(&mut self, to_i: bool) {
        if to_i {
            let mut env = Env {
                provider: &self.i_prov,
                now: self.now,
                drbg: &mut self.i_drbg,
            };
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.ip.kp)),
                prekeys: Some(&self.prekeys),
            };
            let _ = self.i.answer_soft(&mut env, &soft);
            drain!(self.i, self.to_r, self.hist_r, self.i_seen);
        } else {
            let mut env = Env {
                provider: &self.r_prov,
                now: self.now,
                drbg: &mut self.r_drbg,
            };
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &self.rp.kp)),
                prekeys: None,
            };
            let _ = self.r.answer_soft(&mut env, &soft);
            drain!(self.r, self.to_i, self.hist_i, self.r_seen);
        }
    }

    fn deliver(&mut self, to_i: bool, m: &[u8]) {
        if to_i {
            self.to_i_side(m);
        } else {
            self.to_r_side(m);
        }
    }

    fn queue(&mut self, to_i: bool) -> &mut Vec<Vec<u8>> {
        if to_i { &mut self.to_i } else { &mut self.to_r }
    }

    fn step(&mut self, op: &Op) {
        match op {
            Op::Deliver(s, k) => {
                let q = self.queue(*s);
                if !q.is_empty() {
                    let m = q.remove(usize::from(*k) % q.len());
                    self.deliver(*s, &m);
                }
            }
            Op::DeliverFirst(s) => {
                let q = self.queue(*s);
                if !q.is_empty() {
                    let m = q.remove(0);
                    self.deliver(*s, &m);
                }
            }
            Op::Drop(s, k) => {
                let q = self.queue(*s);
                if !q.is_empty() {
                    let at = usize::from(*k) % q.len();
                    q.remove(at);
                }
            }
            Op::Dup(s, k) => {
                let q = self.queue(*s);
                if !q.is_empty() && q.len() < 32 {
                    let m = q[usize::from(*k) % q.len()].clone();
                    q.push(m);
                }
            }
            Op::Flip(s, k, at, x) => {
                if let Some(m) = pick(self.queue(*s), *k).filter(|m| !m.is_empty()) {
                    let i = usize::from(*at) % m.len();
                    m[i] ^= x;
                    self.tainted = true;
                }
            }
            Op::Cut(s, k, len) => {
                if let Some(m) = pick(self.queue(*s), *k).filter(|m| !m.is_empty()) {
                    let n = usize::from(*len) % m.len();
                    m.truncate(n);
                    self.tainted = true;
                }
            }
            Op::Extend(s, k, tail) => {
                if let Some(m) = pick(self.queue(*s), *k).filter(|_| !tail.is_empty()) {
                    m.extend_from_slice(tail);
                    self.tainted = true;
                }
            }
            Op::Garbage(s, ty, body) => {
                let mut m = vec![*ty];
                m.extend_from_slice(body);
                self.tainted = true;
                self.deliver(*s, &m);
            }
            Op::Replay(s, k) => {
                let hist = if *s { &self.hist_i } else { &self.hist_r };
                if !hist.is_empty() {
                    let m = hist[usize::from(*k) % hist.len()].clone();
                    self.deliver(*s, &m);
                }
            }
            Op::ReplayFresh(k) => {
                if !self.hist_r.is_empty() && self.fresh.len() < 3 {
                    let m = self.hist_r[usize::from(*k) % self.hist_r.len()].clone();
                    let mut r = responder(&self.rp, 1);
                    let mut seen = Seen::default();
                    let mut sink = Vec::new();
                    let mut env = Env {
                        provider: &self.r_prov,
                        now: self.now,
                        drbg: &mut self.r_drbg,
                    };
                    let _ = r.handle(&mut env, &mut self.stores, &m);
                    let soft = SoftKeys {
                        signer: Some((KeyHandle(1), &self.rp.kp)),
                        prekeys: None,
                    };
                    for _ in 0..4 {
                        if !matches!(r.answer_soft(&mut env, &soft), Ok(true)) {
                            break;
                        }
                    }
                    let mut hist = Vec::new();
                    drain!(r, sink, hist, seen);
                    self.fresh.push(r);
                    self.fresh_seen.push(seen);
                }
            }
            Op::Keys(s) => self.keys(*s),
            Op::Retransmit(s) => {
                if *s {
                    self.r.retransmit();
                    drain!(self.r, self.to_i, self.hist_i, self.r_seen);
                } else {
                    let mut env = Env {
                        provider: &self.i_prov,
                        now: self.now,
                        drbg: &mut self.i_drbg,
                    };
                    let _ = self.i.retransmit(&mut env);
                    drain!(self.i, self.to_r, self.hist_r, self.i_seen);
                }
            }
            Op::Clock(secs) => self.now = self.now.saturating_add(secs * 1_000_000_000),
            Op::Shed(s) => {
                // The transport sheds "once the transport knows the peer has the session (it received a 1-RTT
                // packet)": both sides must hold the session's keys (0-RTT packets do not count).
                let both = !self.r_seen.established.is_empty() && !self.i_seen.established.is_empty();
                if *s && both {
                    self.r.shed();
                } else if !*s && both {
                    self.i.shed();
                }
            }
        }
        if self.to_r.len() > 64 {
            self.to_r.drain(..32);
        }
        if self.to_i.len() > 64 {
            self.to_i.drain(..32);
        }
        self.hist_i.truncate(64);
        self.hist_r.truncate(64);
        self.check();
    }

    fn check(&self) {
        let i_node = self.ip.id.node_id();
        let r_node = self.rp.id.node_id();
        assert!(self.i_seen.established.len() <= 1, "the initiator was established twice");
        assert!(self.r_seen.established.len() <= 1, "the responder was established twice");
        assert!(self.i_seen.failed.len() <= 1, "the initiator reported its failure twice");
        assert!(self.r_seen.failed.len() <= 1, "the responder reported its failure twice");
        // Only a failure after the responder authenticated, or of the host's own key operation, is fatal: the
        // honest responder never sends what fails after it authenticated, and the keys never fail here.
        assert!(self.i_seen.failed.is_empty(), "the initiator failed: {:?}", self.i_seen.failed);
        if let Some(ie) = self.i_seen.established.first() {
            assert_eq!(ie.peer, r_node, "the initiator is established with another node");
        }
        let responders = std::iter::once(&self.r_seen).chain(self.fresh_seen.iter());
        let mut resumed = 0;
        for seen in responders {
            let Some(re) = seen.established.first() else { continue };
            assert_eq!(re.peer, i_node, "a responder is established with another node");
            if re.resumed {
                resumed += 1;
            } else {
                // A full handshake ends at the responder with the initiator's Finish, which goes out with the
                // initiator's session.
                let ie = self.i_seen.established.first();
                assert!(ie.is_some(), "a responder completed a full handshake the initiator never finished");
            }
            if let Some(ie) = self.i_seen.established.first()
                && (!re.resumed || ie.resumed)
            {
                same_keys(ie, re);
            }
        }
        assert!(resumed <= 1, "one ticket resumed {resumed} sessions");
    }

    /// Every flight delivered in order, keys answered and timers run, a bounded number of times.
    fn settle(&mut self) {
        for _ in 0..12 {
            self.keys(true);
            self.keys(false);
            while !self.to_r.is_empty() || !self.to_i.is_empty() {
                if !self.to_r.is_empty() {
                    let m = self.to_r.remove(0);
                    self.to_r_side(&m);
                    self.keys(false);
                }
                if !self.to_i.is_empty() {
                    let m = self.to_i.remove(0);
                    self.to_i_side(&m);
                    self.keys(true);
                }
                if self.hist_i.len() + self.hist_r.len() > 400 {
                    break;
                }
            }
            if !self.i_seen.established.is_empty() && !self.r_seen.established.is_empty() {
                break;
            }
            self.step(&Op::Retransmit(false));
            self.step(&Op::Retransmit(true));
        }
        self.check();
    }
}

fn pick(q: &mut [Vec<u8>], k: u8) -> Option<&mut Vec<u8>> {
    let n = q.len();
    (n > 0).then_some(()).and_then(move |()| q.get_mut(usize::from(k) % n))
}

fn same_keys(i: &Established, r: &Established) {
    assert_eq!(i.traffic.aead, r.traffic.aead, "the sides chose different AEADs");
    assert_eq!(i.traffic.send, r.traffic.recv, "initiator send key differs from responder receive key");
    assert_eq!(i.traffic.recv, r.traffic.send, "initiator receive key differs from responder send key");
    assert_eq!(i.resume, r.resume, "the resumption secrets differ");
    assert_eq!(i.alpn, r.alpn, "the ALPNs differ");
    assert_eq!(i.cid_secret, r.cid_secret, "the connection-id secrets differ");
    assert_eq!(i.resumed, r.resumed, "one side resumed, the other did not");
}

#[allow(clippy::too_many_arguments)]
fn clean_handshake(
    ip: &Party,
    rp: &Party,
    i_prov: &Caps,
    r_prov: &Caps,
    i_drbg: &mut Drbg,
    r_drbg: &mut Drbg,
    prekeys: &mut SoftPrekeys<Caps>,
    stores: &mut Stores,
) -> (Established, Established) {
    let mut ei = Env {
        provider: i_prov,
        now: T0,
        drbg: i_drbg,
    };
    let prekey = prekeys.acquire(&mut ei).unwrap();
    let mut i = Initiator::new(
        &mut ei,
        InitiatorParams {
            peer: rp.id.node_id(),
            alpn: ALPN,
            scid: ConnId::new(b"initiat0").unwrap(),
            identity: &ip.id,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            credit: CreditRecord::NONE,
        },
    )
    .unwrap();
    let mut r = responder(rp, 2);
    let mut er = Env {
        provider: r_prov,
        now: T0,
        drbg: r_drbg,
    };
    let (mut ie, mut re) = (None, None);
    let (mut to_r, mut to_i) = (Vec::new(), Vec::new());
    let mut sink = Vec::new();
    let (mut si, mut sr) = (Seen::default(), Seen::default());
    drain!(i, to_r, sink, si);
    for _ in 0..16 {
        for m in core::mem::take(&mut to_r) {
            let _ = r.handle(&mut er, stores, &m);
            for _ in 0..4 {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &rp.kp)),
                    prekeys: None,
                };
                if !matches!(r.answer_soft(&mut er, &soft), Ok(true)) {
                    break;
                }
            }
            drain!(r, to_i, sink, sr);
        }
        for m in core::mem::take(&mut to_i) {
            let _ = i.handle(&mut ei, &m);
            for _ in 0..4 {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &ip.kp)),
                    prekeys: Some(&*prekeys),
                };
                if !matches!(i.answer_soft(&mut ei, &soft), Ok(true)) {
                    break;
                }
            }
            drain!(i, to_r, sink, si);
        }
        if ie.is_none() {
            ie = si.established.pop();
        }
        if re.is_none() {
            re = sr.established.pop();
        }
        if ie.is_some() && re.is_some() {
            break;
        }
    }
    (ie.unwrap(), re.unwrap())
}

#[ephyra::test(gen = runs(), tests = 400)]
fn handshake_under_a_hostile_schedule(run: (Setup, Vec<Op>)) {
    let (setup, ops) = run;
    let mut n = Net::new(&setup);
    for op in &ops {
        n.step(op);
    }
    let tainted = n.tainted;
    n.settle();
    // With only loss, duplication, reordering and replays, the handshake completes once the network delivers.
    if !tainted {
        assert!(
            !n.i_seen.established.is_empty(),
            "the initiator did not complete over a clean network (resume {})",
            n.resume
        );
        assert!(!n.r_seen.established.is_empty(), "the responder did not complete over a clean network");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Records.

/// A packet: number, header bytes, payload.
fn packets() -> impl Gen<Value = Vec<(u64, Vec<u8>, Vec<u8>)>> {
    gens::vec((gens::int(1u64..=1000), bytes(24), bytes(200))).len(1..=12)
}

fn secret(tag: u8) -> Secret<32> {
    Secret::new([tag; 32])
}

#[ephyra::test(gen = (gens::bool(), packets(), gens::int(0usize..=4096), gens::int(1u8..=255)), tests = 2000)]
fn a_record_opens_once_sealed_and_never_after_a_change(x: (bool, Vec<(u64, Vec<u8>, Vec<u8>)>, usize, u8)) {
    let (aes, pkts, at, bit) = x;
    let p = Caps(Software, true);
    let aead = if aes { Aead::Aes128Gcm } else { Aead::ChaCha20Poly1305 };
    let mut tx = PacketKey::from_secret(&p, aead, &secret(7)).unwrap();
    let mut rx = PacketKey::from_secret(&p, aead, &secret(7)).unwrap();
    let mut other = PacketKey::from_secret(&p, aead, &secret(8)).unwrap();
    let mut pn = 0u64;
    let mut last: Option<u64> = None;
    for (gap, aad, payload) in &pkts {
        pn += gap;
        // A number at or below the last sealed is refused, and nothing is sealed then.
        if let Some(l) = last {
            let mut b = payload.clone();
            assert_eq!(tx.seal(&p, l, aad, &mut b), Err(RecordError::NotIncreasing));
            assert_eq!(&b, payload, "a refused seal changed the buffer");
        }
        let mut ct = payload.clone();
        let tag = tx.seal(&p, pn, aad, &mut ct).unwrap();
        last = Some(pn);
        // It opens under the same secret, number and header.
        let mut pt = ct.clone();
        assert_eq!(rx.open(&p, pn, aad, &mut pt, &tag), Ok(()));
        assert_eq!(&pt, payload, "the record did not decrypt to what was sealed");
        // One bit anywhere in header, ciphertext or tag, the number, or the key: refused, buffer left as is.
        let total = aad.len() + ct.len() + tag.len();
        let i = at % total;
        let (mut aad2, mut ct2, mut tag2) = (aad.clone(), ct.clone(), tag);
        if i < aad.len() {
            aad2[i] ^= bit;
        } else if i < aad.len() + ct.len() {
            ct2[i - aad.len()] ^= bit;
        } else {
            tag2[i - aad.len() - ct.len()] ^= bit;
        }
        let before = ct2.clone();
        assert_eq!(rx.open(&p, pn, &aad2, &mut ct2, &tag2), Err(RecordError::Authentication));
        assert_eq!(ct2, before, "a refused open changed the buffer");
        let mut ct3 = ct.clone();
        assert_eq!(rx.open(&p, pn ^ u64::from(bit), aad, &mut ct3, &tag), Err(RecordError::Authentication));
        let mut ct4 = ct.clone();
        assert_eq!(other.open(&p, pn, aad, &mut ct4, &tag), Err(RecordError::Authentication));
    }
    assert_eq!(tx.sealed(), pkts.len() as u64);
    let _ = &mut other;
}

#[ephyra::test(gen = (gens::bool(), gens::vec(gens::int(1u8..=3)).len(1..=20)), tests = 300)]
fn rolled_keys_agree_on_both_sides_and_differ_from_every_earlier_generation(x: (bool, Vec<u8>)) {
    let (aes, dhs) = x;
    let p = Caps(Software, true);
    let aead = if aes { Aead::Aes128Gcm } else { Aead::ChaCha20Poly1305 };
    let mut a = PacketKey::from_secret(&p, aead, &secret(1)).unwrap();
    let mut b = PacketKey::from_secret(&p, aead, &secret(1)).unwrap();
    let mut olds = Vec::new();
    for (n, d) in dhs.iter().enumerate() {
        let dh = secret(*d);
        let next = a.rolled(&p, &dh).unwrap();
        olds.push(core::mem::replace(&mut a, next));
        b = b.rolled(&p, &dh).unwrap();
        assert_eq!(a.generation(), n as u32 + 1);
        let mut ct = b"payload".to_vec();
        let tag = a.seal(&p, 1, b"h", &mut ct).unwrap();
        let sealed = ct.clone();
        assert_eq!(b.open(&p, 1, b"h", &mut ct, &tag), Ok(()), "the peer cannot open after the roll");
        for old in &mut olds {
            let mut c = sealed.clone();
            assert_eq!(old.open(&p, 1, b"h", &mut c, &tag), Err(RecordError::Authentication), "an earlier key opens");
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Client tickets: export then restore gives back the unexpired tickets.

#[ephyra::test(gen = (gens::int(1usize..=6), gens::int(0usize..=8), gens::int(0u64..=200_000)), tests = 60)]
fn ticket_export_then_restore_keeps_the_newest_unexpired(x: (usize, usize, u64)) {
    let (sessions, max, later_s) = x;
    let setup = Setup {
        i_alg: 0,
        r_alg: 0,
        i_hw: true,
        r_hw: true,
        mode: 0,
        short_ok: false,
        tickets_per_session: 4,
    };
    let base = Net::new(&setup);
    let (ip, rp) = (base.ip, base.rp);
    let (i_prov, r_prov) = (base.i_prov, base.r_prov);
    let (mut i_drbg, mut r_drbg) = (base.i_drbg, base.r_drbg);
    let mut prekeys = base.prekeys;
    let mut stores = base.stores;
    let mut client: ClientTickets<16> = ClientTickets::new();
    // Every session is with the same peer: each batch replaces the peer's ticket, so at most one is held.
    for _ in 0..sessions {
        let (ie, re) = clean_handshake(&ip, &rp, &i_prov, &r_prov, &mut i_drbg, &mut r_drbg, &mut prekeys, &mut stores);
        client.accept_batch(&ie, &re.tickets, T0);
    }
    let held = client.len();
    let mut out = vec![0u8; 2 + max * pinc_security::tickets::MAX_EXPORT_ENTRY_LEN];
    let n = client.export(T0, max, &mut out).unwrap();
    let now = T0 + later_s * 1_000_000_000;
    let mut back: ClientTickets<16> = ClientTickets::new();
    let restored = back.restore(&out[..n], now).unwrap();
    // A ticket of this run lives 86 400 s at most, so by `now` it either expired or is still whole.
    assert!(restored <= held.min(max), "restored {restored} of {held} held, max {max}");
    assert_eq!(back.len(), restored);
    let dial: NodeId = rp.id.node_id();
    let t1 = back.take(&dial, ALPN, now);
    assert_eq!(t1.is_some(), restored > 0, "a restored ticket cannot be taken");
    assert!(back.take(&dial, ALPN, now).is_none(), "a ticket was taken twice");
}
