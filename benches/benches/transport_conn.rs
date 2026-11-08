//! Benchmarks of the `vinc-transport` connection: bulk throughput between two connections in memory with each AEAD at
//! 0% and 1% loss, handshake to first byte, and the cost per packet of sending and of receiving in steady state.
//!
//! The two connections exchange datagrams directly, with no delay and a seeded loss draw; virtual time advances 50
//! microseconds per round so the round-trip estimate and the pacer have something to work with. The numbers are the
//! cost of the transport and the crypto on this machine, not of a network.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::many_single_char_names,
    clippy::cast_precision_loss
)]

use std::hint::black_box;
use std::time::{Duration, Instant};

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{Aead, Capabilities, CryptoError, Drbg, IdentityAlg, Keypair, Provider, Secret, Software};
use vinc_security::{AlpnList, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys};
use vinc_transport::conn::{ClientParams, Config, Connection, Event, PathId, PathInfo, Resources, ServerParams};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};

const ALPN: &[u8] = b"vinc/1";
const MIB: usize = 1 << 20;

/// [`Software`] with a chosen answer to "does AES-GCM run on hardware", so both AEADs can be measured anywhere.
#[derive(Clone, Copy)]
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

type Conn<'a> = Connection<'a, Caps, NoSource, 16, 257, 512, 2>;
type Table = Streams<NoSource, 16, 257>;

/// Storage a connection borrows.
struct Store {
    streams: Box<Table>,
    loss: LossEstimate,
    pool: Option<BufferPool<'static>>,
}

impl Store {
    fn new(client: bool, chunks: usize) -> Self {
        let streams = Box::new(Table::new(&stream::Config::new(client), &BufferPool::new_boxed(chunks)));
        Self {
            streams,
            loss: LossEstimate::new(),
            pool: Some(BufferPool::new_boxed(chunks)),
        }
    }
    fn resources(&mut self) -> Resources<'_, NoSource, 16, 257> {
        Resources {
            pool: self.pool.take().unwrap(),
            streams: &mut self.streams,
            loss: &self.loss,
        }
    }
}

/// Keys and randomness of one side.
struct Side {
    prov: Caps,
    drbg: Drbg,
    kp: Keypair,
    prekeys: Option<SoftPrekeys<Caps>>,
}

/// Both ends of a connection and the loop that moves datagrams between them.
struct Rig<'a> {
    a: Conn<'a>,
    b: Conn<'a>,
    sa: Side,
    sb: Side,
    stores: Box<ResponderStores<4, 16>>,
    now: u64,
    rng: u64,
    loss_ppm: u64,
    abuf: Vec<u8>,
    bbuf: Vec<u8>,
    packets_a: u64,
    packets_b: u64,
}

impl<'a> Rig<'a> {
    /// A pair that has not started its handshake. `hw` picks AES-128-GCM (true) or ChaCha20-Poly1305 (false).
    fn new(a_store: &'a mut Store, b_store: &'a mut Store, hw: bool, loss_ppm: u64) -> Self {
        let alg = IdentityAlg::Ed25519;
        let prov = Caps(Software, hw);
        let kp_a = Keypair::from_seed(alg, &vec![0x21; alg.seed_len()]).unwrap();
        let kp_b = Keypair::from_seed(alg, &vec![0x22; alg.seed_len()]).unwrap();
        let id_a = LocalIdentity::from_keypair(&kp_a, KeyHandle(1)).unwrap();
        let id_b = LocalIdentity::from_keypair(&kp_b, KeyHandle(1)).unwrap();
        let (mut da, mut db) = (Drbg::new(&[1; 32]), Drbg::new(&[2; 32]));
        let mut env_a = Env {
            provider: &prov,
            now: 1_000_000_000_000,
            drbg: &mut da,
        };
        let mut prekeys = SoftPrekeys::new(&mut env_a, PrekeyPolicy::default()).unwrap();
        let prekey = prekeys.acquire(&mut env_a).unwrap();
        let mut cfg = Config::new();
        cfg.max_gso = 1;
        let a = Conn::client(
            cfg,
            ClientParams {
                peer: id_b.node_id(),
                alpn: ALPN,
                identity: &id_a,
                prekey: &prekey,
                peer_has_prekey: false,
                token: &[],
                ticket: None,
                path: PathId(1),
                path_info: PathInfo::default(),
            },
            a_store.resources(),
            &mut env_a,
        )
        .unwrap();
        let mut env_b = Env {
            provider: &prov,
            now: 1_000_000_000_000,
            drbg: &mut db,
        };
        let b = Conn::server(
            cfg,
            &ServerParams {
                identity: id_b,
                alpns: AlpnList::new(&[ALPN]).unwrap(),
                tickets_per_session: 1,
                ticket_lifetime_s: 86_400,
            },
            b_store.resources(),
            &mut env_b,
        )
        .unwrap();
        Self {
            a,
            b,
            sa: Side {
                prov,
                drbg: da,
                kp: kp_a,
                prekeys: Some(prekeys),
            },
            sb: Side {
                prov,
                drbg: db,
                kp: kp_b,
                prekeys: None,
            },
            stores: Box::default(),
            now: 1_000_000_000_000,
            rng: 0x9E37_79B9_7F4A_7C15,
            loss_ppm,
            abuf: vec![0; 65_536],
            bbuf: vec![0; 65_536],
            packets_a: 0,
            packets_b: 0,
        }
    }

    fn lost(&mut self) -> bool {
        self.rng ^= self.rng << 13;
        self.rng ^= self.rng >> 7;
        self.rng ^= self.rng << 17;
        self.loss_ppm > 0 && self.rng % 1_000_000 < self.loss_ppm
    }

    /// Serve the handshake's key requests on both sides.
    fn serve_keys(&mut self) {
        for is_a in [true, false] {
            let (conn, side) = if is_a {
                (&mut self.a, &mut self.sa)
            } else {
                (&mut self.b, &mut self.sb)
            };
            let mut want = false;
            while let Some(ev) = conn.poll_event() {
                want |= matches!(ev, Event::KeyRequest(_));
            }
            if want {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &side.kp)),
                    prekeys: side.prekeys.as_ref(),
                };
                let mut env = Env {
                    provider: &side.prov,
                    now: self.now,
                    drbg: &mut side.drbg,
                };
                while conn.answer_soft(&mut env, &soft).unwrap_or(false) {}
            }
        }
    }

    /// One round: each side sends what it has and the other receives it. Returns whether anything moved. Time spent in
    /// `poll_transmit` of the sender `a` and in `handle_datagram` of the receiver `b` is added to `send` and `recv`.
    fn round(&mut self, send: &mut Duration, recv: &mut Duration) -> bool {
        self.now += 50_000;
        let mut moved = false;
        loop {
            let t = Instant::now();
            let tx = {
                let mut env = Env {
                    provider: &self.sa.prov,
                    now: self.now,
                    drbg: &mut self.sa.drbg,
                };
                self.a.poll_transmit(&mut env, &mut self.abuf)
            };
            *send += t.elapsed();
            let Some(tx) = tx else { break };
            moved = true;
            self.packets_a += 1;
            if self.lost() {
                continue;
            }
            let t = Instant::now();
            let mut env = Env {
                provider: &self.sb.prov,
                now: self.now,
                drbg: &mut self.sb.drbg,
            };
            self.b
                .handle_datagram_with(&mut env, &mut self.stores, PathId(2), &mut self.abuf[..tx.len])
                .ok();
            *recv += t.elapsed();
        }
        loop {
            let tx = {
                let mut env = Env {
                    provider: &self.sb.prov,
                    now: self.now,
                    drbg: &mut self.sb.drbg,
                };
                self.b.poll_transmit(&mut env, &mut self.bbuf)
            };
            let Some(tx) = tx else { break };
            moved = true;
            self.packets_b += 1;
            if self.lost() {
                continue;
            }
            let mut env = Env {
                provider: &self.sa.prov,
                now: self.now,
                drbg: &mut self.sa.drbg,
            };
            self.a
                .handle_datagram(&mut env, PathId(1), &mut self.bbuf[..tx.len])
                .ok();
        }
        self.serve_keys();
        for (conn, side) in [(&mut self.a, &mut self.sa), (&mut self.b, &mut self.sb)] {
            if conn.poll_timeout().is_some_and(|t| t <= self.now) {
                let mut env = Env {
                    provider: &side.prov,
                    now: self.now,
                    drbg: &mut side.drbg,
                };
                conn.handle_timeout(&mut env);
            }
        }
        moved
    }

    fn connect(&mut self) {
        let (mut s, mut r) = (Duration::ZERO, Duration::ZERO);
        for _ in 0..20_000 {
            self.round(&mut s, &mut r);
            if self.a.is_connected() && self.b.is_connected() {
                return;
            }
        }
        panic!("the handshake did not complete");
    }

    /// Move `bytes` from `a` to `b` on a new unidirectional stream and drain it.
    fn transfer(&mut self, bytes: usize, chunk: &[u8], send: &mut Duration, recv: &mut Duration) {
        let id = self.a.open_uni().unwrap();
        let (mut off, mut got, mut finished) = (0usize, 0usize, false);
        while got < bytes {
            while off < bytes {
                let want = chunk.len().min(bytes - off);
                let k = self.a.write(id, &chunk[..want]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            if off == bytes && !finished {
                self.a.finish(id).unwrap();
                finished = true;
            }
            self.round(send, recv);
            let mut env = Env {
                provider: &self.sb.prov,
                now: self.now,
                drbg: &mut self.sb.drbg,
            };
            while let Some(c) = self.b.read_chunk(id) {
                let n = c.len();
                got += n;
                self.b.consume(&mut env, id, n).unwrap();
            }
        }
    }
}

fn bench_throughput(c: &mut Criterion) {
    let mut g = c.benchmark_group("conn_throughput");
    g.sample_size(10);
    g.throughput(Throughput::Bytes(8 * MIB as u64));
    let chunk = vec![0xa5u8; 64 * 1024];
    for (name, hw) in [("aes128gcm", true), ("chacha20poly1305", false)] {
        for (loss, ppm) in [("0pct", 0u64), ("1pct", 10_000)] {
            let (mut sa, mut sb) = (Store::new(true, 512), Store::new(false, 512));
            let mut rig = Rig::new(&mut sa, &mut sb, hw, ppm);
            rig.connect();
            let (mut s, mut r) = (Duration::ZERO, Duration::ZERO);
            g.bench_function(format!("{name}_{loss}_8MiB"), |b| {
                b.iter(|| rig.transfer(8 * MIB, black_box(&chunk), &mut s, &mut r));
            });
        }
    }
    g.finish();
}

fn bench_handshake(c: &mut Criterion) {
    let mut g = c.benchmark_group("conn_handshake");
    g.sample_size(20);
    g.bench_function("to_first_byte", |b| {
        b.iter_batched(
            || (Store::new(true, 64), Store::new(false, 64)),
            |(mut sa, mut sb)| {
                let mut rig = Rig::new(&mut sa, &mut sb, true, 0);
                rig.connect();
                let id = rig.a.open_bi().unwrap();
                rig.a.write(id, b"x").unwrap();
                let (mut s, mut r) = (Duration::ZERO, Duration::ZERO);
                for _ in 0..100 {
                    rig.round(&mut s, &mut r);
                    if rig.b.read_chunk(id).is_some() {
                        break;
                    }
                }
                assert!(rig.b.read_chunk(id).is_some());
            },
            BatchSize::PerIteration,
        );
    });
    g.finish();
}

/// Cost per packet of `poll_transmit` (build, seal, protect) and of `handle_datagram` (unprotect, open, process).
fn bench_per_packet(c: &mut Criterion) {
    let mut g = c.benchmark_group("conn_per_packet");
    let chunk = vec![0xa5u8; 64 * 1024];
    let (mut sa, mut sb) = (Store::new(true, 512), Store::new(false, 512));
    let mut rig = Rig::new(&mut sa, &mut sb, true, 0);
    rig.connect();
    for _ in 0..200 {
        let (mut s, mut r) = (Duration::ZERO, Duration::ZERO);
        rig.transfer(MIB, &chunk, &mut s, &mut r);
    }
    for which in ["send", "receive"] {
        g.bench_function(which, |b| {
            b.iter_custom(|iters| {
                let (mut s, mut r) = (Duration::ZERO, Duration::ZERO);
                let start = rig.packets_a;
                while rig.packets_a - start < iters {
                    rig.transfer(MIB, &chunk, &mut s, &mut r);
                }
                let packets = (rig.packets_a - start).max(1);
                let total = if which == "send" { s } else { r };
                total.mul_f64(iters as f64 / packets as f64)
            });
        });
    }
    g.finish();
}

criterion_group!(benches, bench_throughput, bench_handshake, bench_per_packet);
criterion_main!(benches);
