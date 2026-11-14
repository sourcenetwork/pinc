//! Trace generation for the protected carrier: seeded runs of a real dialer and a real listener
//! (`vinc_connect::carrier::session::ProtectedCarrier`) wired through two byte streams, recorded as ndjson
//! (`connect_carrier.ndjson`) for the TLA+ trace check (`TraceConnectCarrier.tla`) and the Lean replay
//! (`Vinc/TraceConnectCarrier.lean`).
//!
//! A run handshakes over the streams with reads, transmits and polls of random sizes and in random order, then seals
//! frames and raw bytes on both ends and carries them across. Some runs are attacked: a length of 0, one over the
//! handshake limit, one over the record limit or one of at most a tag, garbage, the dialer's first message sent again
//! and again to a listener whose host does not transmit (the handshake output fills up), a record dropped, replayed,
//! moved after the next one, with a flipped bit, reflected back to its sender, or cut at the end of the stream. The
//! seals cover the encoder's refusals (a frame that does not encode, a buffer too short for the frame or for the tag),
//! empty and over-long bytes, and seals before the handshake and after the end, and key answers nobody asked for. Every
//! call is one event with what the code answered and the state the public API shows (`free`, `pending_transmit`,
//! `key_request`).
//!
//! The stream each end receives is written at the start of the run as its units: the offset and the value of each
//! length (split by the lengths, from the start, as a reader does), and for a unit whose bytes are exactly the `k`-th
//! record the other end sealed, `k` and whether its plaintext decodes as a frame. The models take the stream from that
//! table and predict every answer from it.
//!
//! The test checks by itself: every sealed unit is the 2-byte length `n + 16` then `n + 16` bytes; every frame
//! delivered is, byte for byte, the next frame the other end sealed; the handshake bytes each end transmits split into
//! units of their length.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    clippy::large_stack_frames,
    clippy::needless_pass_by_value,
    clippy::cast_possible_wrap,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_connect::carrier::session::{self, ALPN, CarrierError, IN_LEN, MAX_UNIT_LEN, OUT_LEN, Poll, ProtectedCarrier};
use vinc_connect::carrier::{Frame, FrameError, MAX_FRAME_LEN, MAX_PACKET_LEN};
use vinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_security::message::MAX_MESSAGE_LEN;
use vinc_security::{
    ConnId, CreditRecord, Env, InitiatorParams, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys,
    SoftPrekeys,
};
use vinc_tests::SplitMix64;

const NOW: u64 = 1_000_000_000_000;
const TAG: usize = Aead::TAG_LEN;

fn err_tag(e: CarrierError) -> &'static str {
    match e {
        CarrierError::Handshake(_) => "Handshake",
        CarrierError::UnitSize => "UnitSize",
        CarrierError::Authentication => "Authentication",
        CarrierError::KeyLimit => "KeyLimit",
        CarrierError::NotOpen => "NotOpen",
        CarrierError::NoKeyRequest => "NoKeyRequest",
        CarrierError::OutputFull => "OutputFull",
        CarrierError::NoRoom => "NoRoom",
        CarrierError::Frame(_) => "Frame",
        CarrierError::Record(_) => "Record",
        CarrierError::Closed => "Closed",
    }
}

/// A poll or key answer without borrows: the result name, the frame bytes for a frame.
fn owned(r: Result<Poll<'_>, CarrierError>) -> (&'static str, Option<Vec<u8>>) {
    match r {
        Ok(Poll::Idle) => ("idle", None),
        Ok(Poll::Handshake) => ("hs", None),
        Ok(Poll::KeyRequest) => ("kreq", None),
        Ok(Poll::Open(_)) => ("open", None),
        Ok(Poll::Frame(f)) => {
            let mut b = vec![0u8; MAX_FRAME_LEN];
            let n = f.encode(&mut b).unwrap();
            b.truncate(n);
            ("frame", Some(b))
        }
        Err(e) => (err_tag(e), None),
    }
}

fn nid(tag: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [tag; 32],
    }
}

/// One end: the carrier, its keys and generator, and the stream it receives.
struct End {
    name: &'static str,
    c: Box<ProtectedCarrier<Software>>,
    kp: Keypair,
    drbg: Drbg,
    prekeys: Option<SoftPrekeys<Software>>,
    stores: ResponderStores<4, 4>,
    /// The bytes this end's host offers, in order.
    wire: Vec<u8>,
    /// How many of them the carrier took.
    fed: usize,
    /// The units this end sealed: the unit, whether its plaintext decodes as a frame, the plaintext.
    sealed: Vec<(Vec<u8>, bool, Vec<u8>)>,
    /// Records this end opened so far (frames and dropped frames).
    opened: usize,
    /// Every handshake byte this end transmitted.
    sent_hs: Vec<u8>,
}

struct Run {
    prov: Software,
    ev: Vec<String>,
    id: u32,
}

impl Run {
    fn push(&mut self, s: &str) {
        self.ev.push(format!(r#"{{"t":"cca","run":{},{s}}}"#, self.id));
    }
}

fn ends(rng: &mut SplitMix64) -> (End, End) {
    let prov = Software;
    let ckp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x31; 32]).unwrap();
    let rkp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x32; 32]).unwrap();
    let mut seed = [0u8; 32];
    rng.fill(&mut seed);
    let mut cd = Drbg::new(&seed);
    rng.fill(&mut seed);
    let rd = Drbg::new(&seed);
    let cid = LocalIdentity::from_keypair(&ckp, KeyHandle(1)).unwrap();
    let rid = LocalIdentity::from_keypair(&rkp, KeyHandle(1)).unwrap();
    let mut env = Env {
        provider: &prov,
        now: NOW,
        drbg: &mut cd,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let client = ProtectedCarrier::dial(
        &mut env,
        InitiatorParams {
            peer: rkp.node_id(),
            alpn: ALPN,
            scid: ConnId::new(b"client00").unwrap(),
            identity: &cid,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            credit: CreditRecord::NONE,
        },
    )
    .unwrap();
    let relay = ProtectedCarrier::accept(session::responder_config(rid, ConnId::new(b"relay000").unwrap()).unwrap());
    let mk = |name, c, kp, drbg, prekeys| End {
        name,
        c: Box::new(c),
        kp,
        drbg,
        prekeys,
        stores: ResponderStores::default(),
        wire: Vec::new(),
        fed: 0,
        sealed: Vec::new(),
        opened: 0,
        sent_hs: Vec::new(),
    };
    (mk("d", client, ckp, cd, Some(prekeys)), mk("a", relay, rkp, rd, None))
}

fn state(e: &End) -> String {
    format!(
        r#""free":{},"pend":{},"kr":{}"#,
        e.c.free(),
        e.c.pending_transmit(),
        e.c.key_request().is_some()
    )
}

fn recv(run: &mut Run, e: &mut End, n: usize) {
    let end = (e.fed + n).min(e.wire.len());
    let off = e.fed;
    let took = e.c.receive(&e.wire[off..end]);
    assert!(took <= end - off);
    e.fed += took;
    let s = format!(
        r#""op":"recv","side":"{}","off":{off},"len":{},"took":{took},{}"#,
        e.name,
        end - off,
        state(e)
    );
    run.push(&s);
}

/// One poll; the frames are checked against what the other end sealed.
fn poll(run: &mut Run, e: &mut End, peer_sealed: &[(Vec<u8>, bool, Vec<u8>)]) -> &'static str {
    let pend0 = e.c.pending_transmit();
    let (res, frame) = {
        let mut env = Env {
            provider: &run.prov,
            now: NOW,
            drbg: &mut e.drbg,
        };
        owned(e.c.poll(&mut env, &mut e.stores))
    };
    let grow = e.c.pending_transmit() - pend0;
    if res == "frame" || res == "Frame" {
        let want = &peer_sealed[e.opened];
        assert_eq!(
            res == "frame",
            want.1,
            "the record decodes exactly when its plaintext is a frame"
        );
        if let Some(f) = &frame {
            assert_eq!(f, &want.2, "the frame delivered is the next frame the other end sealed");
        }
        e.opened += 1;
    }
    let s = format!(
        r#""op":"poll","side":"{}","res":"{res}","grow":{grow},{}"#,
        e.name,
        state(e)
    );
    run.push(&s);
    res
}

fn answer(run: &mut Run, e: &mut End) -> &'static str {
    let pend0 = e.c.pending_transmit();
    let res = {
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &e.kp)),
            prekeys: e.prekeys.as_ref(),
        };
        let mut env = Env {
            provider: &run.prov,
            now: NOW,
            drbg: &mut e.drbg,
        };
        owned(e.c.answer_soft(&mut env, &soft)).0
    };
    let grow = e.c.pending_transmit() - pend0;
    let s = format!(
        r#""op":"ans","side":"{}","res":"{res}","grow":{grow},{}"#,
        e.name,
        state(e)
    );
    run.push(&s);
    res
}

/// A poll, and the answers to every key request it leads to, as a software host does.
fn poll_ans(run: &mut Run, e: &mut End, peer_sealed: &[(Vec<u8>, bool, Vec<u8>)]) -> &'static str {
    let mut r = poll(run, e, peer_sealed);
    while r == "kreq" {
        r = answer(run, e);
    }
    r
}

/// Transmit at most `cap` handshake bytes onto `to`'s stream.
fn transmit(run: &mut Run, e: &mut End, to: &mut Vec<u8>, cap: usize) {
    let mut b = vec![0u8; cap];
    let n = e.c.transmit(&mut b);
    to.extend_from_slice(&b[..n]);
    e.sent_hs.extend_from_slice(&b[..n]);
    let s = format!(r#""op":"tx","side":"{}","cap":{cap},"n":{n},{}"#, e.name, state(e));
    run.push(&s);
}

/// The frames a run seals: small ones mostly, a few at the limits, and some that do not encode.
fn frame_of<'a>(rng: &mut SplitMix64, pkt: &'a [u8]) -> Frame<'a> {
    match rng.next_u64() % 6 {
        0 => Frame::Ping,
        1 => Frame::Pong,
        2 => Frame::Send {
            dst: nid(3),
            flag: 1,
            packet: pkt,
        },
        3 => Frame::Recv {
            src: nid(4),
            flag: 2,
            packet: pkt,
        },
        _ => Frame::SelfSend { packet: pkt },
    }
}

/// What the frame encoder does in a buffer of `len` bytes: "ok", "wire" (too short) or "frame" (refused).
fn encodes(f: &Frame<'_>, len: usize) -> &'static str {
    match f.encode(&mut vec![0u8; len]) {
        Ok(_) => "ok",
        Err(FrameError::Wire(_)) => "wire",
        Err(_) => "frame",
    }
}

/// Seal on `e` (a frame, or raw bytes) into a buffer of a chosen size; a sealed unit is returned.
fn seal(run: &mut Run, rng: &mut SplitMix64, e: &mut End) -> Option<Vec<u8>> {
    let bytes = rng.next_u64().is_multiple_of(3);
    let plen_pick = match rng.next_u64() % 16 {
        0 => 0,
        1 => MAX_PACKET_LEN + 1,
        2 => MAX_PACKET_LEN,
        3..=5 => 1 + (rng.next_u64() % 600) as usize,
        _ => 1 + (rng.next_u64() % 40) as usize,
    };
    let mut pkt = vec![0u8; plen_pick];
    rng.fill(&mut pkt);
    let f = frame_of(rng, &pkt);
    // the plaintext: raw bytes, or the frame's encoding (empty for a frame that does not encode)
    let plain: Vec<u8> = if bytes {
        let len = match rng.next_u64() % 10 {
            0 => 0,
            1 => MAX_FRAME_LEN + 1,
            2 => MAX_FRAME_LEN,
            3 => MAX_FRAME_LEN - (rng.next_u64() % 4) as usize,
            _ => 1 + (rng.next_u64() % 64) as usize,
        };
        let mut p = vec![0u8; len];
        rng.fill(&mut p);
        if rng.next_u64().is_multiple_of(2) && !p.is_empty() {
            p[0] = 5; // a PING type byte: decodes only alone
            if rng.next_u64().is_multiple_of(2) {
                p.truncate(1);
            }
        }
        p
    } else {
        let mut b = vec![0u8; MAX_FRAME_LEN];
        match f.encode(&mut b) {
            Ok(n) => {
                b.truncate(n);
                b
            }
            Err(_) => Vec::new(),
        }
    };
    let mut cap = 2 + plain.len() + TAG;
    match rng.next_u64() % 12 {
        0 => cap -= 1 + (rng.next_u64() % (TAG as u64)) as usize, // short of the tag
        1 => cap = rng.next_u64() as usize % 2,                   // not even the length
        2 => cap = 2 + plain.len().saturating_sub(1),             // short of the plaintext
        _ => {}
    }
    let mut out = vec![0u8; cap];
    let (how, fe, r) = if bytes {
        ("bytes", "ok", e.c.seal_bytes(&run.prov, &plain, &mut out))
    } else {
        // the encoder's outcome in the body the carrier gives it, out[2..]
        let fe = if cap < 2 { "ok" } else { encodes(&f, cap - 2) };
        ("frame", fe, e.c.seal(&run.prov, &f, &mut out))
    };
    let plen = plain.len();
    let (res, n) = match r {
        Ok(n) => ("ok", n),
        Err(err) => (err_tag(err), 0),
    };
    let s = format!(
        r#""op":"seal","side":"{}","how":"{how}","plen":{plen},"cap":{cap},"fe":"{fe}","res":"{res}","n":{n},{}"#,
        e.name,
        state(e)
    );
    run.push(&s);
    if res != "ok" {
        return None;
    }
    out.truncate(n);
    assert_eq!(n, 2 + plen + TAG, "a unit is the length, the ciphertext and the tag");
    assert_eq!(usize::from(u16::from_be_bytes([out[0], out[1]])), plen + TAG);
    let fok = Frame::decode(&plain).is_ok();
    e.sealed.push((out.clone(), fok, plain));
    Some(out)
}

/// The units of a stream from its start, split by their lengths as a reader splits them.
fn table(wire: &[u8], peer_sealed: &[(Vec<u8>, bool, Vec<u8>)]) -> String {
    let mut units = Vec::new();
    let mut o = 0usize;
    while o + 2 <= wire.len() {
        let h = usize::from(u16::from_be_bytes([wire[o], wire[o + 1]]));
        let (mut g, mut f) = (-1i64, false);
        if o + 2 + h <= wire.len()
            && let Some(k) = peer_sealed.iter().position(|s| s.0[..] == wire[o..o + 2 + h])
        {
            g = k as i64;
            f = peer_sealed[k].1;
        }
        units.push(format!("[{o},{h},{g},{f}]"));
        if h == 0 {
            break;
        }
        o += 2 + h;
    }
    units.join(",")
}

/// The handshake bytes an end transmitted split into whole units of their length (the last may be cut).
fn check_hs_units(sent: &[u8]) {
    let mut o = 0;
    while o + 2 <= sent.len() {
        let h = usize::from(u16::from_be_bytes([sent[o], sent[o + 1]]));
        assert!(
            h > 0 && h <= MAX_MESSAGE_LEN,
            "a handshake unit has the length of its message"
        );
        o += 2 + h;
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Attack {
    None,
    HsJunk,
    DupInitial,
    Drop,
    Replay,
    Swap,
    Flip,
    Reflect,
    Junk,
    CutEnd,
    AnswerOpen,
}

fn one_run(rng: &mut SplitMix64, id: u32, attack: Attack) -> Vec<String> {
    let (mut d, mut a) = ends(rng);
    let mut run = Run {
        prov: Software,
        ev: Vec::new(),
        id,
    };
    let k = format!(
        r#""k":{{"inl":{IN_LEN},"maxm":{MAX_MESSAGE_LEN},"maxu":{MAX_UNIT_LEN},"tag":{TAG},"outn":{OUT_LEN},"maxf":{MAX_FRAME_LEN}}}"#
    );
    for e in [&d, &a] {
        let kind = if e.name == "d" { "dial" } else { "accept" };
        let s = format!(r#""op":"init","side":"{}","kind":"{kind}",{k},{}"#, e.name, state(e));
        run.push(&s);
    }
    // a seal before the handshake
    if rng.next_u64().is_multiple_of(3) {
        let _ = seal(&mut run, rng, &mut d);
    }
    let read = |rng: &mut SplitMix64| match rng.next_u64() % 8 {
        0 => 1,
        1 => 2,
        2 => 3 + (rng.next_u64() % 20) as usize,
        3 => 100 + (rng.next_u64() % 1000) as usize,
        _ => IN_LEN + 10,
    };
    let txcap = |rng: &mut SplitMix64| match rng.next_u64() % 4 {
        0 => 1 + (rng.next_u64() % 300) as usize,
        _ => OUT_LEN,
    };

    // ---- the handshake ----
    match attack {
        Attack::HsJunk => {
            let h: u16 = match rng.next_u64() % 4 {
                0 => 0,
                1 => (MAX_MESSAGE_LEN + 1) as u16,
                2 => u16::MAX,
                _ => 3,
            };
            if rng.next_u64().is_multiple_of(2) {
                a.wire.extend_from_slice(&h.to_be_bytes());
                a.wire.extend_from_slice(&[0x55; 3]);
            } else {
                // the junk after the dialer's first message
                transmit(&mut run, &mut d, &mut a.wire, OUT_LEN);
                a.wire.extend_from_slice(&h.to_be_bytes());
                let mut g = vec![0u8; 8];
                rng.fill(&mut g);
                a.wire.extend_from_slice(&g);
            }
        }
        Attack::DupInitial => {
            transmit(&mut run, &mut d, &mut a.wire, OUT_LEN);
            let init = a.wire.clone();
            for _ in 0..12 {
                a.wire.extend_from_slice(&init);
            }
            // the listener's host reads and polls without transmitting until it ends
            for _ in 0..400 {
                if a.c.is_ended() || a.fed == a.wire.len() {
                    break;
                }
                let n = read(rng);
                recv(&mut run, &mut a, n);
                while poll_ans(&mut run, &mut a, &d.sealed) == "hs" {}
            }
        }
        _ => {}
    }
    for _ in 0..600 {
        if (d.c.is_open() && a.c.is_open()) || d.c.is_ended() || a.c.is_ended() {
            break;
        }
        match rng.next_u64() % 6 {
            0 if d.c.pending_transmit() > 0 => {
                let cap = txcap(rng);
                transmit(&mut run, &mut d, &mut a.wire, cap);
            }
            1 if a.c.pending_transmit() > 0 => {
                let cap = txcap(rng);
                transmit(&mut run, &mut a, &mut d.wire, cap);
            }
            2 if d.fed < d.wire.len() => {
                let n = read(rng);
                recv(&mut run, &mut d, n);
            }
            3 if a.fed < a.wire.len() => {
                let n = read(rng);
                recv(&mut run, &mut a, n);
            }
            4 => {
                let _ = poll_ans(&mut run, &mut d, &a.sealed);
            }
            5 => {
                let _ = poll_ans(&mut run, &mut a, &d.sealed);
            }
            _ => {}
        }
    }
    check_hs_units(&d.sent_hs);
    check_hs_units(&a.sent_hs);

    // ---- records ----
    let steps = 20 + (rng.next_u64() % 40) as usize;
    let attack_at = (rng.next_u64() % steps as u64) as usize;
    let mut held: Option<(bool, Vec<u8>)> = None; // a unit moved after the next one: (toward a, bytes)
    for step in 0..steps {
        match rng.next_u64() % 8 {
            0..=2 => {
                let from_d = rng.next_u64().is_multiple_of(2);
                let (src, dst) = if from_d { (&mut d, &mut a) } else { (&mut a, &mut d) };
                if let Some(u) = seal(&mut run, rng, src) {
                    let act = if step >= attack_at { attack } else { Attack::None };
                    match act {
                        Attack::Drop => {}
                        Attack::Replay => {
                            dst.wire.extend_from_slice(&u);
                            dst.wire.extend_from_slice(&u);
                        }
                        Attack::Swap if held.is_none() => held = Some((from_d, u)),
                        Attack::Flip => {
                            let mut v = u.clone();
                            let i = 2 + (rng.next_u64() as usize % (v.len() - 2));
                            v[i] ^= 1 << (rng.next_u64() % 8);
                            dst.wire.extend_from_slice(&v);
                        }
                        Attack::Reflect => src.wire.extend_from_slice(&u),
                        Attack::Junk => {
                            let h: u16 = match rng.next_u64() % 4 {
                                0 => 0,
                                1 => (MAX_UNIT_LEN + 1) as u16,
                                2 => (rng.next_u64() % (TAG as u64 + 1)) as u16,
                                _ => u16::MAX,
                            };
                            dst.wire.extend_from_slice(&h.to_be_bytes());
                            dst.wire.extend_from_slice(&[0xaa; 20]);
                        }
                        Attack::CutEnd => {
                            let cut = 1 + rng.next_u64() as usize % (u.len() - 1);
                            dst.wire.extend_from_slice(&u[..cut]);
                        }
                        _ => {
                            dst.wire.extend_from_slice(&u);
                            if let Some((to_a, h)) = held.take() {
                                if to_a == from_d {
                                    dst.wire.extend_from_slice(&h);
                                } else {
                                    src.wire.extend_from_slice(&h);
                                }
                            }
                        }
                    }
                    if act == Attack::CutEnd {
                        // nothing more follows the cut record on that stream
                        break;
                    }
                }
            }
            3 | 4 => {
                let to_a = rng.next_u64().is_multiple_of(2);
                let n = read(rng);
                if to_a {
                    recv(&mut run, &mut a, n);
                } else {
                    recv(&mut run, &mut d, n);
                }
            }
            5 if attack == Attack::AnswerOpen && step >= attack_at => {
                let _ = answer(&mut run, &mut a);
            }
            _ => {
                if rng.next_u64().is_multiple_of(2) {
                    let _ = poll(&mut run, &mut a, &d.sealed);
                } else {
                    let _ = poll(&mut run, &mut d, &a.sealed);
                }
            }
        }
    }
    // the hosts drain what they have, then a few calls on whatever state is left (ended carriers included)
    for _ in 0..3 {
        while a.fed < a.wire.len() || d.fed < d.wire.len() {
            let before = (a.fed, d.fed);
            recv(&mut run, &mut a, IN_LEN);
            while !matches!(poll(&mut run, &mut a, &d.sealed), "idle") && !a.c.is_ended() {}
            recv(&mut run, &mut d, IN_LEN);
            while !matches!(poll(&mut run, &mut d, &a.sealed), "idle") && !d.c.is_ended() {}
            if before == (a.fed, d.fed) {
                break;
            }
        }
    }
    let _ = poll(&mut run, &mut a, &d.sealed);
    let _ = poll(&mut run, &mut d, &a.sealed);
    if rng.next_u64().is_multiple_of(2) {
        let _ = seal(&mut run, rng, &mut a);
        let mut sink = Vec::new();
        transmit(&mut run, &mut a, &mut sink, OUT_LEN);
        let _ = answer(&mut run, &mut d);
    }

    // the stream tables first, then the calls
    let mut out = Vec::new();
    for (e, peer) in [(&d, &a), (&a, &d)] {
        out.push(format!(
            r#"{{"t":"cca","run":{id},"op":"stream","side":"{}","units":[{}]}}"#,
            e.name,
            table(&e.wire, &peer.sealed)
        ));
    }
    out.extend(run.ev);
    out
}

#[test]
fn carrier_calls_match_the_models() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut rng = SplitMix64::new(0x4343_4101);
            let attacks = [
                Attack::None,
                Attack::HsJunk,
                Attack::DupInitial,
                Attack::Drop,
                Attack::Replay,
                Attack::Swap,
                Attack::Flip,
                Attack::Reflect,
                Attack::Junk,
                Attack::CutEnd,
                Attack::AnswerOpen,
            ];
            let mut all = String::new();
            for id in 1..=110u32 {
                let attack = attacks[(id as usize) % attacks.len()];
                for line in one_run(&mut rng, id, attack) {
                    let _ = writeln!(all, "{line}");
                }
            }
            if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(std::path::Path::new(&dir).join("connect_carrier.ndjson"), &all).unwrap();
            }
            for want in [
                r#""res":"frame""#,
                r#""res":"Frame""#,
                r#""res":"Authentication""#,
                r#""res":"UnitSize""#,
                r#""res":"OutputFull""#,
                r#""res":"NoRoom""#,
                r#""res":"NotOpen""#,
                r#""res":"Closed""#,
                r#""res":"Handshake""#,
                r#""res":"NoKeyRequest""#,
                r#""res":"kreq""#,
                r#""res":"open""#,
                r#""fe":"wire""#,
                r#""fe":"frame""#,
            ] {
                assert!(all.contains(want), "no event with {want}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
