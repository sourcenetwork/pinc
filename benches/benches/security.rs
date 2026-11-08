//! Benchmarks of `vinc-security`: the handshakes end to end in memory, and per-packet record protection.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::large_stack_arrays,
    clippy::too_many_lines
)]

use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use vinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, Provider, Secret, Software};
use vinc_security::message::MAX_MESSAGE_LEN;
use vinc_security::{
    AlpnList, ConnId, Env, Established, Event, HeaderKey, Initiator, InitiatorParams, KeyHandle, Limits, LocalIdentity,
    Output, PacketKey, PrekeyPolicy, Responder, ResponderConfig, ResponderStores, SoftKeys, SoftPrekeys, Ticket,
};

const ALPN: &[u8] = b"vinc/1";

/// Both ends of a connection and everything they keep between handshakes.
struct Rig {
    p: Software,
    i_kp: Keypair,
    r_kp: Keypair,
    i_id: LocalIdentity,
    r_id: LocalIdentity,
    prekeys: SoftPrekeys<Software>,
    i_drbg: Drbg,
    r_drbg: Drbg,
    stores: Box<ResponderStores<4, 64>>,
}

impl Rig {
    fn new(alg: IdentityAlg) -> Self {
        let p = Software;
        let seed = vec![7u8; alg.seed_len()];
        let (i_kp, r_kp) = (
            Keypair::from_seed(alg, &seed).unwrap(),
            Keypair::from_seed(alg, &vec![8u8; alg.seed_len()]).unwrap(),
        );
        let (i_id, r_id) = (
            LocalIdentity::from_keypair(&i_kp, KeyHandle(1)).unwrap(),
            LocalIdentity::from_keypair(&r_kp, KeyHandle(1)).unwrap(),
        );
        let mut i_drbg = Drbg::new(&[1; 32]);
        let policy = PrekeyPolicy {
            lifetime_ns: u64::MAX,
            max_uses: u32::MAX,
        };
        let prekeys = SoftPrekeys::new(
            &mut Env {
                provider: &p,
                now: 0,
                drbg: &mut i_drbg,
            },
            policy,
        )
        .unwrap();
        Self {
            p,
            i_kp,
            r_kp,
            i_id,
            r_id,
            prekeys,
            i_drbg,
            r_drbg: Drbg::new(&[2; 32]),
            stores: Box::default(),
        }
    }

    /// One handshake, end to end in memory; `short` tries the short Initial, `ticket` resumes.
    fn handshake(&mut self, short: bool, ticket: Option<Ticket>) -> (Established, Established) {
        let Self {
            p,
            i_kp,
            r_kp,
            i_id,
            r_id,
            prekeys,
            i_drbg,
            r_drbg,
            stores,
        } = self;
        let mut env_i = Env {
            provider: &*p,
            now: 1,
            drbg: i_drbg,
        };
        let mut env_r = Env {
            provider: &*p,
            now: 1,
            drbg: r_drbg,
        };
        let prekey = prekeys.acquire(&mut env_i).unwrap();
        let mut i = Initiator::new(
            &mut env_i,
            InitiatorParams {
                peer: r_id.node_id(),
                alpn: ALPN,
                scid: ConnId::new(b"initiat0").unwrap(),
                identity: i_id,
                prekey: &prekey,
                peer_has_prekey: short,
                token: &[],
                ticket,
            },
        )
        .unwrap();
        let mut r = Responder::new(ResponderConfig::new(
            *r_id,
            ConnId::new(b"respond0").unwrap(),
            AlpnList::new(&[ALPN]).unwrap(),
        ));
        let soft_i = SoftKeys {
            signer: Some((KeyHandle(1), &*i_kp)),
            prekeys: Some(&*prekeys),
        };
        let soft_r = SoftKeys {
            signer: Some((KeyHandle(1), &*r_kp)),
            prekeys: None,
        };
        let (mut to_r, mut to_i) = ([0u8; MAX_MESSAGE_LEN], [0u8; MAX_MESSAGE_LEN]);
        let (mut len_r, mut len_i) = (0usize, 0usize);
        let (mut est_i, mut est_r) = (None, None);
        for _ in 0..8 {
            while i.answer_soft(&mut env_i, &soft_i).unwrap() {}
            while let Some(o) = i.poll_output() {
                match o {
                    Output::Send { data, .. } => {
                        len_r = data.len();
                        to_r[..len_r].copy_from_slice(data);
                    }
                    Output::Event(Event::Established(e)) => est_i = Some(e),
                    _ => {}
                }
            }
            if len_r > 0 {
                r.handle(&mut env_r, stores, &to_r[..len_r]).unwrap();
                len_r = 0;
                while r.answer_soft(&mut env_r, &soft_r).unwrap() {}
                while let Some(o) = r.poll_output() {
                    match o {
                        Output::Send { data, .. } => {
                            len_i = data.len();
                            to_i[..len_i].copy_from_slice(data);
                        }
                        Output::Event(Event::Established(e)) => est_r = Some(e),
                        _ => {}
                    }
                }
            }
            if len_i > 0 {
                i.handle(&mut env_i, &to_i[..len_i]).unwrap();
                len_i = 0;
                continue;
            }
            if est_i.is_some() && est_r.is_none() {
                continue;
            }
            break;
        }
        (est_i.unwrap(), est_r.unwrap())
    }
}

fn bench_handshakes(c: &mut Criterion) {
    let mut g = c.benchmark_group("handshake");
    for (name, alg) in [("ed25519", IdentityAlg::Ed25519), ("hybrid", IdentityAlg::Hybrid)] {
        let mut rig = Rig::new(alg);
        g.bench_function(format!("full_{name}"), |b| {
            b.iter(|| black_box(rig.handshake(false, None)));
        });
        // Warm the responder's prekey cache, then use the short Initial.
        let (i_est, r_est) = rig.handshake(false, None);
        g.bench_function(format!("prekey_short_{name}"), |b| {
            b.iter(|| black_box(rig.handshake(true, None)));
        });
        // Resumption: every iteration needs a fresh single-use ticket, which the unmeasured setup issues.
        let rig = std::cell::RefCell::new(rig);
        g.bench_function(format!("resume_{name}"), |b| {
            b.iter_batched(
                || {
                    let mut rig = rig.borrow_mut();
                    let Rig {
                        p,
                        r_id,
                        r_drbg,
                        stores,
                        ..
                    } = &mut *rig;
                    let mut client = vinc_security::ClientTickets::<1>::new();
                    let mut env = Env {
                        provider: &*p,
                        now: 1,
                        drbg: r_drbg,
                    };
                    let batch = stores.tickets.issue_batch(&mut env, &r_est, 1, 3600).unwrap();
                    client.accept_batch(&i_est, &batch, 1);
                    client.take(&r_id.node_id(), ALPN, 1).unwrap()
                },
                |ticket| black_box(rig.borrow_mut().handshake(false, Some(ticket))),
                BatchSize::PerIteration,
            );
        });
    }
    g.finish();
}

fn bench_records(c: &mut Criterion) {
    let p = Software;
    let limits = Limits {
        aes_gcm_packets: u64::MAX,
        chacha_failures: u64::MAX,
    };
    for (name, aead) in [
        ("chacha20poly1305", Aead::ChaCha20Poly1305),
        ("aes128gcm", Aead::Aes128Gcm),
    ] {
        let secret = Secret::new([5u8; 32]);
        let mut tx = PacketKey::from_secret(&p, aead, &secret).unwrap().with_limits(limits);
        let mut rx = PacketKey::from_secret(&p, aead, &secret).unwrap().with_limits(limits);
        let hk = HeaderKey::from_secret(&p, aead, &secret).unwrap();
        let mut g = c.benchmark_group(format!("record_{name}"));
        g.throughput(Throughput::Bytes(1452));
        // A short-header packet: first byte, a 4-byte packet number, then the payload and its tag.
        let header = [0x43u8, 0, 0, 0, 1];
        let mut payload = vec![7u8; 1452 - header.len() - 16];
        g.bench_function("seal_and_protect_1452", |b| {
            b.iter(|| {
                let tag = tx.seal(&p, black_box(1), &header, &mut payload).unwrap();
                let mut head = header;
                let sample: [u8; 16] = payload[..16].try_into().unwrap();
                let (first, pn) = head.split_first_mut().unwrap();
                hk.protect(&p, first, pn, &sample, false).unwrap();
                black_box((head, tag));
            });
        });
        let mut ct = vec![7u8; payload.len()];
        let tag = tx.seal(&p, 1, &header, &mut ct).unwrap();
        let mut masked = header;
        let sample: [u8; 16] = ct[..16].try_into().unwrap();
        let (first, pn) = masked.split_first_mut().unwrap();
        hk.protect(&p, first, pn, &sample, false).unwrap();
        // `open` decrypts in place, so each run starts from a fresh copy of the ciphertext.
        g.bench_function("unprotect_and_open_1452", |b| {
            b.iter_batched_ref(
                || (ct.clone(), masked),
                |(buf, head)| {
                    let (first, pn) = head.split_first_mut().unwrap();
                    let n = hk.unprotect(&p, first, pn, &sample, false).unwrap();
                    rx.open(&p, 1, &header, buf, &tag).unwrap();
                    black_box(n);
                },
                BatchSize::SmallInput,
            );
        });
        g.finish();
    }
    let _ = p.capabilities();
}

criterion_group!(benches, bench_handshakes, bench_records);
criterion_main!(benches);
