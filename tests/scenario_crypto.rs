//! The instrumented crypto of the scenario suite: recognisable payload, provenance of every key of a real handshake,
//! and the security verdicts, including the cases where they must fail.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::type_complexity,
    clippy::many_single_char_names,
    missing_docs
)]

#[path = "crypto_support/net.rs"]
mod net;

use net::{Host, Net, ancestry, has};
use vinc_core::{Command, Event, Role, Value};
use vinc_crypto::{Aead, Provider, Software, expand, extract};
use vinc_security::{labels, roll_secret};
use vinc_sim::suite::crypto::{BLOCK_LEN, DeviceCosts, MsgId, PayloadKind, Registry, Term, Tracked, Work};
use vinc_tests::{ALPN_A, SEC_NS, SplitMix64, big_stack};

// ---------------------------------------------------------------- payload

fn random_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

/// The block indices a reader can recognise in the bytes `offset..offset + span` of a body of `len` bytes.
fn visible_blocks(len: u64, offset: u64, span: u64) -> Vec<u32> {
    let end = (offset + span).min(len);
    (0..len.div_ceil(BLOCK_LEN as u64))
        .filter(|&b| {
            let start = b * BLOCK_LEN as u64;
            let valid = (len - start).min(BLOCK_LEN as u64);
            let visible = valid.min(end.saturating_sub(start));
            start >= offset && start < end && visible >= 20
        })
        .map(|b| b as u32)
        .collect()
}

#[test]
fn fill_is_deterministic_and_ranges_agree_with_the_whole() {
    let reg = Registry::new(7);
    let m = reg.new_msg(3, PayloadKind::Msg, 5000);
    let other = reg.new_msg(4, PayloadKind::Value, 5000);
    assert_eq!((m, other), (MsgId(1), MsgId(2)));
    assert_eq!(reg.creator_of(m), Some(3));
    assert_eq!(reg.kind_of(other), Some(PayloadKind::Value));
    assert_eq!(reg.creator_of(MsgId(99)), None);
    let mut whole = vec![0u8; 5000];
    reg.fill(m, 0, &mut whole).unwrap();
    let mut again = vec![0u8; 5000];
    let twin = Registry::new(7);
    twin.fill(twin.new_msg(3, PayloadKind::Msg, 5000), 0, &mut again)
        .unwrap();
    assert_eq!(whole, again, "same seed and id, same bytes");
    let mut diff = vec![0u8; 5000];
    reg.fill(other, 0, &mut diff).unwrap();
    assert_ne!(whole, diff);
    let mut rng = SplitMix64::new(5);
    for _ in 0..500 {
        let off = rng.next_u64() % 5000;
        let n = (rng.next_u64() % (5000 - off + 1)) as usize;
        let mut part = vec![0u8; n];
        reg.fill(m, off, &mut part).unwrap();
        assert_eq!(part, whole[off as usize..off as usize + n]);
    }
    assert!(reg.fill(m, 4990, &mut [0u8; 11]).is_err());
    assert!(reg.fill(MsgId(9), 0, &mut [0u8; 1]).is_err());
    assert!(reg.fill(m, u64::MAX, &mut [0u8; 1]).is_err());
}

#[test]
fn blocks_are_found_at_every_alignment_and_never_in_noise() {
    let reg = Registry::new(11);
    let len = 5000u64;
    let m = reg.new_msg(0, PayloadKind::Value, len);
    let mut body = vec![0u8; len as usize];
    reg.fill(m, 0, &mut body).unwrap();
    let mut rng = SplitMix64::new(9);
    for align in 0..=130usize {
        for (offset, span) in [
            (0u64, 1200u64),
            (17, 1200),
            (64, 900),
            (130, 300),
            (4000, 1000),
            (4980, 20),
            (4992, 8),
        ] {
            let mut buf = random_bytes(&mut rng, align);
            buf.extend_from_slice(&body[offset as usize..(offset + span).min(len) as usize]);
            buf.extend(random_bytes(&mut rng, 37));
            let mut got: Vec<u32> = reg
                .find_blocks(&buf)
                .map(|(id, idx)| {
                    assert_eq!(id, m);
                    idx
                })
                .collect();
            got.sort_unstable();
            assert_eq!(
                got,
                visible_blocks(len, offset, span),
                "align {align} offset {offset} span {span}"
            );
        }
    }
    let mut found = 0;
    for _ in 0..2000 {
        found += reg.find_blocks(&random_bytes(&mut rng, 1200)).count();
    }
    assert_eq!(found, 0, "noise must not look like payload");
    // A header copied onto the wrong body is not a block: the rest has to match.
    let mut forged = body[..BLOCK_LEN].to_vec();
    forged[25] ^= 1;
    assert_eq!(reg.find_blocks(&forged).count(), 0);
}

#[test]
fn a_message_shorter_than_a_header_holds_no_block() {
    let reg = Registry::new(1);
    let m = reg.new_msg(0, PayloadKind::Msg, 19);
    let mut b = vec![0u8; 19];
    reg.fill(m, 0, &mut b).unwrap();
    assert!(!reg.has_blocks(&b));
}

// ---------------------------------------------------------------- a real network of tracked endpoints

#[test]
fn a_real_handshake_and_exchange_have_known_keys_and_clean_verdicts() {
    big_stack(|| {
        let mut net = Net::new(2026);
        let (a, b) = (net.add(), net.add());
        let reg = net.reg;
        let (sa, sb) = net.connect(a, b);

        let m1 = reg.new_msg(a, PayloadKind::Msg, 20_000);
        net.send_msg(a, sa, m1, 20_000);
        net.expect_msg(b, m1, 20_000);
        let m2 = reg.new_msg(b, PayloadKind::Msg, 9_000);
        net.send_msg(b, sb, m2, 9_000);
        net.expect_msg(a, m2, 9_000);
        net.run_for(SEC_NS);

        // Every key that sealed payload has a term, built from both a Diffie-Hellman and a KEM secret.
        let keys = reg.payload_keys();
        assert!(keys.len() >= 2, "{keys:?}");
        for k in &keys {
            assert!(!reg.is_unknown(k.term), "payload key {} of unknown provenance", k.term);
            assert!(
                has(reg, k.term, |t| matches!(t, Term::Dh(..))),
                "no Dh under key {}",
                k.term
            );
            assert!(
                has(reg, k.term, |t| matches!(t, Term::KemSs { .. })),
                "no KEM secret under key {}",
                k.term
            );
        }
        let v = reg.sec_verdict([(100, 200)]);
        assert!(v.clean(), "{v:?}");
        assert_eq!(
            v.unknown_key_seals, 0,
            "a key that sealed something has no tracked derivation: {v:?}"
        );
        assert!(net.log.datagrams > 20);
        assert_eq!((net.log.plaintext, net.log.third_party), (0, 0), "{:?}", net.log);

        // A compromise of node a after the exchange: what its exported state holds does not open the session.
        let now = net.now;
        let mut state = vec![0u8; vinc_core::state_len(8)];
        let n = net.hosts[a].ep.export_state(now, &mut state).unwrap();
        reg.note_compromise(a, now, &net.hosts[a].identity_seed, &state[..n]);
        let comp = reg.compromises();
        assert_eq!(comp.len(), 1);
        let v = reg.sec_verdict([]);
        assert!(v.clean(), "{v:?}");
        // Node b's prekey seed is exported state too: with it the KEM secrets of b's sessions are known, and the
        // classical adversary still lacks the ephemeral Diffie-Hellman.
        let seed_b = [&net.hosts[b].identity_seed[..], &[][..]].concat();
        reg.note_compromise(b, now, &seed_b, &[]);
        assert!(reg.sec_verdict([]).clean());
        eprintln!("{} payload keys, {} terms", keys.len(), reg.payload_keys().len());
    });
}

#[test]
fn without_the_derivation_hook_the_keys_are_reported_unknown_not_clean() {
    big_stack(|| {
        let mut net = Net::untraced(5);
        let (a, b) = (net.add(), net.add());
        let (sa, _) = net.connect(a, b);
        let m = net.reg.new_msg(a, PayloadKind::Msg, 5_000);
        net.send_msg(a, sa, m, 5_000);
        net.expect_msg(b, m, 5_000);
        let v = net.reg.sec_verdict([]);
        assert!(v.unknown_provenance.is_some() && !v.clean(), "{v:?}");
        assert!(v.unknown_key_seals > 0);
    });
}

#[test]
fn resumption_with_early_data_keeps_every_key_tracked() {
    big_stack(|| {
        let mut net = Net::new(77);
        let (a, b) = (net.add(), net.add());
        let reg = net.reg;
        let (sa, _) = net.connect(a, b);
        net.run_for(SEC_NS);
        let first = reg.payload_keys().len();
        let m0 = reg.new_msg(a, PayloadKind::Msg, 3_000);
        net.send_msg(a, sa, m0, 3_000);
        net.expect_msg(b, m0, 3_000);
        let before = reg.payload_keys().len();
        assert!(before > first);
        // Node a restarts with its saved state; the next dial resumes and carries payload as early data.
        let now = net.now;
        assert!(!net.hosts[a].ep.tickets().is_empty(), "no ticket was issued");
        let mut state = vec![0u8; vinc_core::state_len(8)];
        let n = net.hosts[a].ep.export_state(now, &mut state).unwrap();
        net.hosts[a].cmd(now, Command::Close { session: sa, error: 0 });
        net.run_for(SEC_NS);
        net.hosts[a] = Host::new(reg, a, net.now);
        net.hosts[a].ep.restore_state(net.now, &state[..n]).unwrap();
        let (peer, to, now) = (net.hosts[b].node, net.hosts[b].addr, net.now);
        let na = net.hosts[a]
            .events
            .iter()
            .filter(|e| matches!(e, Event::Connected { .. }))
            .count();
        let rep = net.hosts[a].cmd(
            now,
            Command::Connect {
                node: peer,
                alpn: ALPN_A,
                addrs: &[to],
                role: Role::Other,
            },
        );
        let Value::Session(s2) = rep.value else { panic!() };
        let m1 = reg.new_msg(a, PayloadKind::Msg, 2_000);
        net.send_msg(a, s2, m1, 2_000);
        net.dial_done(a, b, na);
        net.expect_msg(b, m1, 2_000);
        let conn: Vec<_> = net.hosts[a]
            .events
            .iter()
            .filter(|e| matches!(e, Event::Connected { .. }))
            .collect();
        assert!(
            conn.iter().any(|e| matches!(e, Event::Connected { resumed: true, .. })),
            "the second dial did not resume: {conn:?}"
        );
        assert!(
            reg.payload_keys().len() > before,
            "the resumed session sealed no payload"
        );
        let v = reg.sec_verdict([]);
        assert!(v.clean(), "{v:?}");
        for k in reg.payload_keys() {
            assert!(!reg.is_unknown(k.term), "key {} of unknown provenance", k.term);
        }
        assert_eq!(v.unknown_key_seals, 0, "{v:?}");
        assert_eq!((net.log.plaintext, net.log.third_party), (0, 0));
    });
}

// ---------------------------------------------------------------- direct provider paths and the verdicts that must fail

fn provider_pair(seed: u64) -> (&'static Registry, Tracked, Tracked) {
    let reg = Registry::leak(seed);
    reg.install();
    (reg, Tracked::new(reg, 0, Software), Tracked::new(reg, 1, Software))
}

/// Seal `msg` (all of it) under `key` with `nonce` and return the datagram `ciphertext || tag`.
fn seal_msg(p: &Tracked, key: &<Tracked as Provider>::AeadKey, nonce: u8, msg: MsgId, len: usize) -> Vec<u8> {
    let mut buf = vec![0u8; len];
    p.registry().fill(msg, 0, &mut buf).unwrap();
    let tag = p.seal(key, &[nonce; 12], b"hdr", &mut buf).unwrap();
    buf.extend_from_slice(&tag);
    buf
}

fn key_from(p: &Tracked, secret: &[u8; 32]) -> <Tracked as Provider>::AeadKey {
    let mut k = [0u8; 32];
    expand(secret, labels::PACKET_KEY, &[], &mut k);
    p.aead_key(Aead::ChaCha20Poly1305, &k).unwrap()
}

/// Node 0 and 1 run a Diffie-Hellman between a static key of node 1 and an ephemeral key of node 0.
fn static_ephemeral(p0: &Tracked, p1: &Tracked) -> (<Tracked as Provider>::X25519Secret, [u8; 32]) {
    let eph = p0.x25519_secret(&[0x11; 32]);
    let eph_pk = p0.x25519_public(&eph);
    let stat = p1.x25519_secret(&[0x22; 32]);
    let stat_pk = p1.x25519_public(&stat);
    let a = p0.x25519_dh(&eph, &stat_pk).unwrap();
    let b = p1.x25519_dh(&stat, &eph_pk).unwrap();
    assert_eq!(a.expose(), b.expose());
    (stat, *a.expose())
}

#[test]
fn a_key_from_x25519_alone_is_readable_by_the_hndl_adversary() {
    let (reg, p0, p1) = provider_pair(1);
    let (_stat, dh) = static_ephemeral(&p0, &p1);
    let m = reg.new_msg(0, PayloadKind::Msg, 3000);
    reg.now.set(1000);
    let key = key_from(&p0, &dh);
    seal_msg(&p0, &key, 1, m, 3000);
    let v = reg.sec_verdict([]);
    let f = v.hndl.expect("an X25519-only key must be reported");
    assert_eq!((f.node, f.at_ns, f.term), (0, 1000, Some(key.term())));
    assert!(v.forward_secrecy.is_none() && v.unknown_provenance.is_none() && v.nonce_reuse.is_empty());
    assert!(!v.clean());
}

/// The hybrid derivation of the schedule over a Diffie-Hellman and a KEM secret; returns the packet key secret.
fn hybrid_key(reg: &'static Registry, p0: &Tracked, p1: &Tracked) -> ([u8; 32], [u8; 32], [u8; 32]) {
    let (stat, dh) = static_ephemeral(p0, p1);
    let _ = stat;
    let (d, z) = ([0x33; 32], [0x44; 32]);
    let (dk, ek) = p1.kem_keygen(&d, &z);
    let (ct, ss) = p0.kem_encapsulate(&ek, &[0x55; 32]).unwrap();
    let ss1 = p1.kem_decapsulate(&dk, &ct).unwrap();
    assert_eq!(ss.expose(), ss1.expose());
    let mut ikm = [0u8; 64];
    ikm[..32].copy_from_slice(ss.expose());
    ikm[32..].copy_from_slice(&dh);
    let ck = extract(&[9; 32], &ikm);
    let mut secret = [0u8; 32];
    expand(&ck, labels::APPLICATION_INITIATOR, b"th", &mut secret);
    let _ = reg;
    (secret, [0x22; 32], {
        let mut s = [0u8; 32];
        s.copy_from_slice(&d);
        s
    })
}

#[test]
fn a_hybrid_key_is_safe_from_hndl_and_from_a_classical_compromise_of_the_static_key() {
    let (reg, p0, p1) = provider_pair(2);
    let (secret, static_seed, _) = hybrid_key(reg, &p0, &p1);
    let m = reg.new_msg(0, PayloadKind::Msg, 3000);
    reg.now.set(1000);
    let key = key_from(&p0, &secret);
    seal_msg(&p0, &key, 1, m, 3000);
    // The static key of node 1 leaks later: the ephemeral one is gone, so the session stays closed.
    reg.note_compromise(1, 2000, &static_seed, &[]);
    assert_eq!(reg.compromises()[0].2.len(), 1);
    let v = reg.sec_verdict([]);
    assert!(v.clean(), "{v:?}");
    assert!(has(reg, key.term(), |t| matches!(t, Term::KemSs { .. })));
}

#[test]
fn a_compromised_long_term_secret_that_a_key_derives_from_breaks_forward_secrecy() {
    // Key from Diffie-Hellman only, static key compromised after first use: forward secrecy fails (and HNDL too).
    let (reg, p0, p1) = provider_pair(3);
    let (_stat, dh) = static_ephemeral(&p0, &p1);
    let m = reg.new_msg(0, PayloadKind::Msg, 3000);
    reg.now.set(1000);
    let key = key_from(&p0, &dh);
    seal_msg(&p0, &key, 1, m, 3000);
    reg.note_compromise(1, 2000, &[0x22; 32], &[]);
    let v = reg.sec_verdict([]);
    let f = v
        .forward_secrecy
        .expect("compromised static key must break forward secrecy");
    assert_eq!((f.node, f.at_ns), (0, 1000));

    // The same compromise before the key was first used does not count against it.
    let (reg, p0, p1) = provider_pair(4);
    let (_stat, dh) = static_ephemeral(&p0, &p1);
    let m = reg.new_msg(0, PayloadKind::Msg, 3000);
    reg.now.set(1000);
    let key = key_from(&p0, &dh);
    seal_msg(&p0, &key, 1, m, 3000);
    reg.note_compromise(1, 500, &[0x22; 32], &[]);
    assert!(reg.sec_verdict([]).forward_secrecy.is_none());

    // A hybrid key breaks classically only when the KEM key leaks as well; HNDL stays clean either way.
    let (reg, p0, p1) = provider_pair(5);
    let (secret, static_seed, d) = hybrid_key(reg, &p0, &p1);
    let m = reg.new_msg(0, PayloadKind::Msg, 3000);
    reg.now.set(1000);
    let key = key_from(&p0, &secret);
    seal_msg(&p0, &key, 1, m, 3000);
    let state = [&static_seed[..], &d[..], &[0x44; 32][..]].concat();
    reg.note_compromise(1, 2000, &[], &state);
    let v = reg.sec_verdict([]);
    assert!(v.forward_secrecy.is_some(), "{v:?}");
    assert!(v.hndl.is_none(), "{v:?}");
}

#[test]
fn a_reused_key_and_nonce_is_reported_only_for_different_content() {
    let (reg, p0, _p1) = provider_pair(6);
    let key = key_from(&p0, &[7; 32]);
    let m1 = reg.new_msg(0, PayloadKind::Msg, 200);
    let m2 = reg.new_msg(0, PayloadKind::Msg, 200);
    reg.now.set(55);
    seal_msg(&p0, &key, 1, m1, 200);
    seal_msg(&p0, &key, 2, m2, 200);
    seal_msg(&p0, &key, 1, m1, 200);
    assert!(
        reg.sec_verdict([]).nonce_reuse.is_empty(),
        "same content, or a new nonce, is no reuse"
    );
    seal_msg(&p0, &key, 1, m2, 200);
    let v = reg.sec_verdict([]);
    assert_eq!(v.nonce_reuse.len(), 1);
    assert_eq!((v.nonce_reuse[0].node, v.nonce_reuse[0].at_ns), (0, 55));
    assert!(v.failures().iter().any(|f| f.contains("nonce")));
    for _ in 0..40 {
        seal_msg(&p0, &key, 1, m2, 200);
        let m3 = reg.new_msg(0, PayloadKind::Msg, 200);
        seal_msg(&p0, &key, 1, m3, 200);
    }
    assert_eq!(reg.sec_verdict([]).nonce_reuse.len(), 16, "at most 16 cases are kept");
}

#[test]
fn payload_on_the_wire_is_plaintext_and_foreign_tags_are_third_party() {
    let (reg, p0, _p1) = provider_pair(7);
    let m = reg.new_msg(0, PayloadKind::Msg, 3000);
    let val = reg.new_msg(0, PayloadKind::Value, 3000);
    let mut dg = random_bytes(&mut SplitMix64::new(1), 300);
    let mut body = vec![0u8; 700];
    reg.fill(m, 100, &mut body).unwrap();
    dg.extend_from_slice(&body);
    dg.extend(random_bytes(&mut SplitMix64::new(2), 200));
    reg.now.set(9);
    let s = reg.scan_wire(0, &dg);
    assert!(s.plaintext_payload && !s.third_party);
    assert_eq!(s.payload_msgs, vec![m]);
    assert!(reg.scan_wire(1, &dg).third_party, "another node's message in the clear");
    let mut vbody = vec![0u8; 700];
    reg.fill(val, 0, &mut vbody).unwrap();
    assert!(!reg.scan_wire(1, &vbody).third_party, "a value is not a message");
    let v = reg.sec_verdict([]);
    let f = v.plaintext_payload.unwrap();
    assert_eq!((f.node, f.at_ns), (0, 9));
    assert!(v.failures().iter().any(|f| f.contains("plaintext")));

    // A sealed datagram shows no payload; its tag belongs to its maker.
    let (reg, p0b, _) = provider_pair(8);
    let _ = p0;
    let key = key_from(&p0b, &[3; 32]);
    let m = reg.new_msg(0, PayloadKind::Msg, 1100);
    let mut sealed = random_bytes(&mut SplitMix64::new(3), 17);
    sealed.extend(seal_msg(&p0b, &key, 1, m, 1100));
    let own = reg.scan_wire(0, &sealed);
    assert_eq!((own.plaintext_payload, own.third_party), (false, false));
    assert!(
        reg.scan_wire(1, &sealed).third_party,
        "a tag made by node 0, carried by node 1"
    );
    assert!(reg.sec_verdict([]).plaintext_payload.is_none());
}

#[test]
fn a_key_of_unknown_provenance_that_seals_payload_fails_the_verdict() {
    let (reg, p0, _p1) = provider_pair(9);
    let key = p0.aead_key(Aead::ChaCha20Poly1305, &[0xAB; 32]).unwrap();
    let m = reg.new_msg(0, PayloadKind::Msg, 500);
    // Sealing something else under it is only counted.
    let other = reg.new_msg(0, PayloadKind::Msg, 10);
    let mut small = [0u8; 10];
    reg.fill(other, 0, &mut small).unwrap();
    seal_msg(&p0, &key, 1, other, 10);
    let v = reg.sec_verdict([]);
    assert!(v.unknown_provenance.is_none() && v.unknown_key_seals == 1);
    seal_msg(&p0, &key, 2, m, 500);
    let v = reg.sec_verdict([]);
    assert!(v.unknown_provenance.is_some() && !v.clean(), "{v:?}");
    assert!(v.hndl.is_none(), "an unknown key is not claimed to be known");
}

#[test]
fn a_derivation_from_an_untracked_input_is_unknown_and_taints_what_follows() {
    let (reg, p0, _p1) = provider_pair(10);
    // A prk the ledger never saw.
    let mut k = [0u8; 32];
    expand(&[0x99; 32], labels::PACKET_KEY, &[], &mut k);
    let t = reg.term_of(&k).unwrap();
    assert!(reg.is_unknown(t));
    // Mixing it with a tracked secret keeps the taint.
    let sk = p0.x25519_secret(&[1; 32]);
    let _ = p0.x25519_public(&sk);
    let mut ikm = [0u8; 64];
    ikm[..32].copy_from_slice(&k);
    ikm[32..].copy_from_slice(&[1; 32]);
    let ck = extract(&[5; 32], &ikm);
    assert!(reg.is_unknown(reg.term_of(&ck).unwrap()));
}

#[test]
fn a_key_roll_chains_the_old_secret_and_the_fresh_dh() {
    let (reg, p0, p1) = provider_pair(11);
    let (secret, _, _) = hybrid_key(reg, &p0, &p1);
    let before = reg.term_of(&secret).unwrap();
    let e0 = p0.x25519_secret(&[0x61; 32]);
    let e1 = p1.x25519_secret(&[0x62; 32]);
    let pk1 = p1.x25519_public(&e1);
    let dh = p0.x25519_dh(&e0, &pk1).unwrap();
    let rolled = roll_secret(&vinc_crypto::Secret::new(secret), &dh);
    let t = reg.term_of(rolled.expose()).unwrap();
    assert!(!reg.is_unknown(t));
    let Term::Hkdf { inputs, .. } = reg.term(t).unwrap() else {
        panic!()
    };
    assert!(inputs.iter().any(|&i| ancestry(reg, i).contains(&before)));
    assert!(has(reg, t, |x| matches!(x, Term::Dh(..))));
}

#[test]
fn encapsulating_to_an_unowned_key_gives_the_adversary_the_secret() {
    let (reg, p0, p1) = provider_pair(12);
    // A key whose decapsulation side the ledger never saw: build it with the base provider.
    let (_dk, ek) = Software.kem_keygen(&[1; 32], &[2; 32]);
    let ek = p0.kem_encaps_key(&Software.kem_encaps_key_bytes(&ek)).unwrap();
    let (_ct, ss) = p0.kem_encapsulate(&ek, &[3; 32]).unwrap();
    assert_eq!(reg.term(reg.term_of(ss.expose()).unwrap()), Some(Term::KemAdv));
    // A forged ciphertext decapsulated by a real key is a rejection, known to nobody.
    let (dk, _) = p1.kem_keygen(&[7; 32], &[8; 32]);
    let forged = p1.kem_ciphertext(&[0x5A; 1088]).unwrap();
    let rej = p1.kem_decapsulate(&dk, &forged).unwrap();
    assert!(matches!(
        reg.term(reg.term_of(rej.expose()).unwrap()),
        Some(Term::KemRej(..))
    ));
    // A peer key nobody owns is an adversary-chosen Diffie-Hellman.
    let sk = p0.x25519_secret(&[4; 32]);
    let out = p0.x25519_dh(&sk, &[9; 32]).unwrap();
    assert_eq!(reg.term(reg.term_of(out.expose()).unwrap()), Some(Term::DhAdv));
}

#[test]
fn amplification_above_three_times_is_reported() {
    let reg = Registry::new(0);
    assert!(reg.sec_verdict([(1000, 3000), (0, 3)]).clean());
    assert!(reg.sec_verdict([(1000, 3001)]).amplification);
    assert!(reg.sec_verdict([(0, 4)]).amplification);
}

#[test]
fn work_is_counted_per_call_and_charged_with_the_device_constants() {
    let (reg, p0, p1) = provider_pair(13);
    let _ = p1;
    reg.take_work(0, &DeviceCosts::CLOUD);
    let key = key_from(&p0, &[1; 32]);
    let m = reg.new_msg(0, PayloadKind::Msg, 1000);
    seal_msg(&p0, &key, 1, m, 1000);
    let mut buf = vec![0u8; 100];
    let tag = p0.seal(&key, &[2; 12], b"", &mut buf).unwrap();
    p0.open(&key, &[2; 12], b"", &mut buf, &tag).unwrap();
    let sk = p0.x25519_secret(&[1; 32]);
    let _ = p0.x25519_public(&sk);
    let _ = p0.sha256(&[0u8; 1000]);
    reg.note_sign(0, 100);
    reg.note_verify(0, 200);
    let w = reg.peek_work(0);
    assert_eq!(
        w,
        Work {
            aead: 3,
            aead_bytes: 1000 + 100 + 116,
            hash_bytes: 1000 + 300,
            x25519: 1,
            hkdf: 1,
            sign: 1,
            verify: 1,
            ..Work::default()
        }
    );
    let c = DeviceCosts::CLOUD;
    let want = 3.0 * c.aead + 1216.0 * c.aead_b + 1300.0 * c.hash_b + c.x25519 + c.hkdf + c.sign + c.verify;
    let ns = reg.take_work(0, &c);
    let ns = u32::try_from(ns).unwrap();
    assert!((f64::from(ns) - want).abs() < 1.0, "{ns} vs {want}");
    assert_eq!(reg.peek_work(0), Work::default());
    assert_eq!(reg.take_work(0, &c), 0);
    // The browser is twice the desktop, a slow CPU multiplies everything, the remainder is carried.
    assert_eq!(DeviceCosts::BROWSER, DeviceCosts::DESKTOP.scaled(2.0));
    assert_eq!(DeviceCosts::named("phone"), Some(DeviceCosts::PHONE));
    assert!(DeviceCosts::named("toaster").is_none());
    let mut total = 0;
    for _ in 0..10 {
        reg.note_verify(2, 0);
        total += reg.take_work(2, &DeviceCosts::CLOUD.scaled(0.00001));
    }
    assert_eq!(total, 5, "10 x 0.5 ns, the remainder carried");
}

#[test]
fn scanning_a_datagram_is_cheap() {
    let (reg, p0, _p1) = provider_pair(14);
    let key = key_from(&p0, &[1; 32]);
    for i in 0..200_000u32 {
        let mut buf = [0u8; 40];
        buf[..4].copy_from_slice(&i.to_le_bytes());
        let mut nonce = [0u8; 12];
        nonce[..4].copy_from_slice(&i.to_le_bytes());
        p0.seal(&key, &nonce, b"", &mut buf).unwrap();
    }
    let dg = random_bytes(&mut SplitMix64::new(4), 1200);
    let t = std::time::Instant::now();
    let n = 2000;
    for _ in 0..n {
        assert!(!reg.scan_wire(1, &dg).third_party);
    }
    let per = t.elapsed().as_nanos() / n;
    let t = std::time::Instant::now();
    for _ in 0..n {
        assert!(!reg.has_blocks(&dg));
    }
    eprintln!("has_blocks: {} ns", t.elapsed().as_nanos() / n);
    eprintln!("scan_wire of 1200 B with 200000 tags registered: {per} ns");
    assert!(per < 1_000_000);
}
