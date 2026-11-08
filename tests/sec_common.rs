//! Scaffolding shared by the security tests: a capability-overriding provider, fixtures and an in-memory network.
#![allow(
    dead_code,
    clippy::many_single_char_names,
    clippy::trivially_copy_pass_by_ref,
    clippy::range_plus_one,
    clippy::assert_is_empty,
    clippy::needless_pass_by_value,
    clippy::similar_names,
    clippy::items_after_statements,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::type_complexity
)]

use std::collections::VecDeque;

use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{Aead, Capabilities, CryptoError, Drbg, IdentityAlg, Keypair, NodeId, Provider, Secret, Software};
use vinc_security::{AlpnList, ConnId};
use vinc_security::{
    ClientTickets, Env, Established, Event, Failure, Initiator, InitiatorParams, KeyHandle, LocalIdentity, Output,
    PrekeyPolicy, Responder, ResponderConfig, ResponderStores, SoftKeys, SoftPrekeys,
};

/// Run `f` on a thread with a large stack: ML-DSA-65 keys and working state are tens of KiB.
pub(crate) fn big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// [`Software`] with a chosen answer to "does AES-GCM run on hardware", so both AEADs are testable anywhere.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Caps(pub Software, pub bool);

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

pub(crate) const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];
pub(crate) const ALPN: &[u8] = b"vinc/1";
pub(crate) const ALPN_B: &[u8] = b"vinc/2";
pub(crate) const T0: u64 = 1_000_000_000_000;

pub(crate) fn keypair(alg: IdentityAlg, tag: u8) -> Keypair {
    Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap()
}

pub(crate) struct Party {
    pub kp: Keypair,
    pub id: LocalIdentity,
}

pub(crate) fn party(alg: IdentityAlg, tag: u8) -> Party {
    let kp = keypair(alg, tag);
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    Party { kp, id }
}

pub(crate) const PK: usize = 8;
pub(crate) const TK: usize = 512;

/// One initiator, one responder and everything they share across handshakes.
pub(crate) struct World {
    pub ip: Party,
    pub rp: Party,
    pub i_prov: Caps,
    pub r_prov: Caps,
    pub i_drbg: Drbg,
    pub r_drbg: Drbg,
    pub now: u64,
    pub prekeys: SoftPrekeys<Caps>,
    pub stores: ResponderStores<PK, TK>,
    pub client: ClientTickets<512>,
    pub r_alpns: Vec<&'static [u8]>,
    pub tickets_per_session: u8,
    pub token: Vec<u8>,
}

impl World {
    pub fn new(i_alg: IdentityAlg, r_alg: IdentityAlg, i_hw: bool, r_hw: bool) -> Self {
        let i_prov = Caps(Software, i_hw);
        let mut i_drbg = Drbg::new(&[0x11; 32]);
        let now = T0;
        let prekeys = {
            let mut env = Env {
                provider: &i_prov,
                now,
                drbg: &mut i_drbg,
            };
            SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap()
        };
        Self {
            ip: party(i_alg, 0x21),
            rp: party(r_alg, 0x22),
            i_prov,
            r_prov: Caps(Software, r_hw),
            i_drbg,
            r_drbg: Drbg::new(&[0x33; 32]),
            now,
            prekeys,
            stores: ResponderStores::default(),
            client: ClientTickets::new(),
            r_alpns: vec![ALPN, ALPN_B],
            tickets_per_session: 1,
            token: Vec::new(),
        }
    }

    /// The node id the initiator dials: the responder's.
    pub fn dial(&self) -> NodeId {
        self.rp.id.node_id()
    }

    pub fn initiator_with(&mut self, dial: NodeId, alpn: &[u8], peer_has_prekey: bool, ticket: bool) -> Initiator {
        let mut env = Env {
            provider: &self.i_prov,
            now: self.now,
            drbg: &mut self.i_drbg,
        };
        let prekey = self.prekeys.acquire(&mut env).unwrap();
        let ticket = if ticket {
            self.client.take(&dial, alpn, self.now)
        } else {
            None
        };
        Initiator::new(
            &mut env,
            InitiatorParams {
                peer: dial,
                alpn,
                scid: ConnId::new(b"initiat0").unwrap(),
                identity: &self.ip.id,
                prekey: &prekey,
                peer_has_prekey,
                token: &self.token,
                ticket,
            },
        )
        .unwrap()
    }

    pub fn initiator(&mut self) -> Initiator {
        let dial = self.dial();
        self.initiator_with(dial, ALPN, false, false)
    }

    pub fn responder(&self) -> Responder {
        let mut cfg = ResponderConfig::new(
            self.rp.id,
            ConnId::new(b"respond0").unwrap(),
            AlpnList::new(&self.r_alpns).unwrap(),
        );
        cfg.tickets_per_session = self.tickets_per_session;
        Responder::new(cfg)
    }

    /// Run the two machines against each other in memory, optionally altering one message in flight.
    pub fn run(&mut self, i: &mut Initiator, r: &mut Responder, tamper: Option<&Tamper>) -> Outcome {
        let mut out = Outcome::default();
        let mut to_r: VecDeque<Vec<u8>> = VecDeque::new();
        let mut to_i: VecDeque<Vec<u8>> = VecDeque::new();
        let Self {
            ip,
            rp,
            i_prov,
            r_prov,
            i_drbg,
            r_drbg,
            now,
            prekeys,
            stores,
            ..
        } = self;
        let mut env_i = Env {
            provider: &*i_prov,
            now: *now,
            drbg: i_drbg,
        };
        let mut env_r = Env {
            provider: &*r_prov,
            now: *now,
            drbg: r_drbg,
        };
        let soft_i = SoftKeys {
            signer: Some((KeyHandle(1), &ip.kp)),
            prekeys: Some(&*prekeys),
        };
        let soft_r = SoftKeys {
            signer: Some((KeyHandle(1), &rp.kp)),
            prekeys: None,
        };
        let mut sent = 0usize;
        macro_rules! drain {
            ($m:expr, $env:expr, $soft:expr, $dst:expr, $events:expr, $errs:expr) => {{
                for _ in 0..8 {
                    match $m.answer_soft(&mut $env, &$soft) {
                        Ok(true) => {}
                        Ok(false) => break,
                        Err(e) => {
                            $errs.push(e);
                            break;
                        }
                    }
                }
                while let Some(o) = $m.poll_output() {
                    match o {
                        Output::Send { data, .. } => {
                            out.msgs.push(data.to_vec());
                            let bytes = match tamper {
                                Some(t) if t.msg == sent => (t.apply)(data),
                                _ => data.to_vec(),
                            };
                            sent += 1;
                            $dst.push_back(bytes);
                        }
                        Output::Event(e) => $events.push(e),
                        Output::Key(_) => {}
                    }
                }
            }};
        }
        drain!(i, env_i, soft_i, to_r, out.i_events, out.i_errs);
        for _ in 0..64 {
            if to_r.is_empty() && to_i.is_empty() {
                break;
            }
            while let Some(m) = to_r.pop_front() {
                if let Err(e) = r.handle(&mut env_r, stores, &m) {
                    out.r_errs.push(e);
                }
                drain!(r, env_r, soft_r, to_i, out.r_events, out.r_errs);
            }
            while let Some(m) = to_i.pop_front() {
                if let Err(e) = i.handle(&mut env_i, &m) {
                    out.i_errs.push(e);
                }
                drain!(i, env_i, soft_i, to_r, out.i_events, out.i_errs);
            }
        }
        out
    }

    /// Hand the initiator `n` more tickets for the session `out` established (as the responder would over the
    /// protected channel), `4` at a time.
    pub fn mint_tickets(&mut self, out: &Outcome, n: usize) {
        let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
        let mut env = Env {
            provider: &self.r_prov,
            now: self.now,
            drbg: &mut self.r_drbg,
        };
        for _ in 0..n.div_ceil(4) {
            let batch = self.stores.tickets.issue_batch(&mut env, r, 4, 86_400).unwrap();
            let mut bytes = [0u8; 81];
            let len = batch.encode(&mut bytes).unwrap();
            self.client.accept_bytes(i, &bytes[..len], self.now).unwrap();
        }
    }

    /// A full handshake with default parameters, asserting it established on both sides.
    pub fn full(&mut self) -> Outcome {
        let mut i = self.initiator();
        let mut r = self.responder();
        let out = self.run(&mut i, &mut r, None);
        assert!(out.both_established(), "{:?} {:?}", out.i_errs, out.r_errs);
        let (ie, re) = (out.i_est().unwrap(), out.r_est().unwrap());
        self.client.accept_batch(ie, &re.tickets, self.now);
        out
    }
}

/// Alter the message with the given index (in the order messages are sent).
pub(crate) struct Tamper {
    pub msg: usize,
    pub apply: Box<dyn Fn(&[u8]) -> Vec<u8>>,
}

impl Tamper {
    pub fn flip(msg: usize, byte: usize) -> Self {
        Self {
            msg,
            apply: Box::new(move |m| {
                let mut v = m.to_vec();
                v[byte] ^= 0x01;
                v
            }),
        }
    }
    pub fn truncate(msg: usize, len: usize) -> Self {
        Self {
            msg,
            apply: Box::new(move |m| m[..len].to_vec()),
        }
    }
    pub fn extend(msg: usize) -> Self {
        Self {
            msg,
            apply: Box::new(|m| {
                let mut v = m.to_vec();
                v.push(0);
                v
            }),
        }
    }
    pub fn custom(msg: usize, f: impl Fn(&mut Vec<u8>) + 'static) -> Self {
        Self {
            msg,
            apply: Box::new(move |m| {
                let mut v = m.to_vec();
                f(&mut v);
                v
            }),
        }
    }
}

#[derive(Default)]
pub(crate) struct Outcome {
    pub msgs: Vec<Vec<u8>>,
    pub i_events: Vec<Event>,
    pub r_events: Vec<Event>,
    pub i_errs: Vec<Failure>,
    pub r_errs: Vec<Failure>,
}

impl Outcome {
    pub fn i_est(&self) -> Option<&Established> {
        self.i_events.iter().find_map(|e| match e {
            Event::Established(x) => Some(x),
            _ => None,
        })
    }
    pub fn r_est(&self) -> Option<&Established> {
        self.r_events.iter().find_map(|e| match e {
            Event::Established(x) => Some(x),
            _ => None,
        })
    }
    pub fn both_established(&self) -> bool {
        self.i_est().is_some() && self.r_est().is_some()
    }
    pub fn i_failed(&self) -> Option<Failure> {
        self.i_events.iter().find_map(|e| match e {
            Event::Failed(f) => Some(*f),
            _ => None,
        })
    }
    pub fn r_failed(&self) -> Option<Failure> {
        self.r_events.iter().find_map(|e| match e {
            Event::Failed(f) => Some(*f),
            _ => None,
        })
    }
    pub fn i_early(&self) -> Option<&vinc_security::EarlyKeys> {
        self.i_events.iter().find_map(|e| match e {
            Event::EarlyKeys(x) => Some(x),
            _ => None,
        })
    }
    pub fn r_early(&self) -> Option<&vinc_security::EarlyKeys> {
        self.r_events.iter().find_map(|e| match e {
            Event::EarlyKeys(x) => Some(x),
            _ => None,
        })
    }
    /// The message types in the order sent.
    pub fn types(&self) -> Vec<u8> {
        self.msgs.iter().map(|m| m[0]).collect()
    }
}

/// Both sides derived the same keys.
pub(crate) fn assert_same_keys(i: &Established, r: &Established) {
    assert_eq!(i.traffic.aead, r.traffic.aead);
    assert_eq!(i.traffic.send, r.traffic.recv);
    assert_eq!(i.traffic.recv, r.traffic.send);
    assert_ne!(i.traffic.send, i.traffic.recv);
    assert_eq!(i.resume, r.resume);
    assert_eq!(i.alpn, r.alpn);
}

/// `from` seals a short-header packet with header protection; `to` removes it and opens it.
pub(crate) fn send_packet(pa: &Caps, pb: &Caps, from: &Established, to: &Established, pn: u64, payload: &[u8]) {
    let mut tx = from.traffic.send_keys(pa).unwrap();
    let mut rx = to.traffic.recv_keys(pb).unwrap();
    let pn_len = 2usize;
    let mut header = vec![0x40 | (pn_len as u8 - 1)];
    header.extend_from_slice(&(pn as u16).to_be_bytes());
    let mut body = payload.to_vec();
    let tag = tx.packet.seal(pa, pn, &header, &mut body).unwrap();
    body.extend_from_slice(&tag);
    let mut packet = header.clone();
    packet.extend_from_slice(&body);
    let sample: [u8; 16] = packet[4..20].try_into().unwrap();
    let (first, rest) = packet.split_first_mut().unwrap();
    tx.header
        .protect(pa, first, &mut rest[..pn_len], &sample, false)
        .unwrap();
    // Receive.
    let sample: [u8; 16] = packet[4..20].try_into().unwrap();
    let (first, rest) = packet.split_first_mut().unwrap();
    let n = rx.header.unprotect(pb, first, rest, &sample, false).unwrap();
    assert_eq!(n, pn_len);
    assert_eq!(&packet[..1 + pn_len], header.as_slice());
    let (aad, ct) = packet.split_at(1 + pn_len);
    let (ct, tag) = ct.split_at(ct.len() - 16);
    let mut plain = ct.to_vec();
    rx.packet
        .open(pb, pn, aad, &mut plain, tag.try_into().unwrap())
        .unwrap();
    assert_eq!(plain, payload);
}

/// Application data flows in both directions.
pub(crate) fn assert_data_flows(pi: &Caps, pr: &Caps, i: &Established, r: &Established) {
    let payload = [0x5au8; 64];
    send_packet(pi, pr, i, r, 7, &payload);
    send_packet(pr, pi, r, i, 9, &payload);
}
