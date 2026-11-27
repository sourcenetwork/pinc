//! `pinc-security`, second pass: the handshake message codecs under hostile bytes, and the two state machines fed
//! forged or mangled messages and a key host that answers late, twice, wrongly or not at all, with the oracle the
//! first pass (`security.rs`) left out: after the hostile part, an honest network still completes the handshake.
//!
//! Where the expected behaviour comes from:
//! - `message` module doc: "The parsers are strict: a wrong type, a length out of range, a missing byte or a trailing
//!   byte is an error, and nothing panics", with the layout table (every field fixed-size or length-prefixed, so a
//!   message that parses re-encodes to the same bytes); `keyroll`: "A request is 33 bytes, an answer 42 to 50";
//!   `TicketBatch`: "Wire form: `count(1) <= 4`, then `count` entries".
//! - `initiator` module doc: "a Reply or a resume Reply that fails any check before that ... is dropped as
//!   [`Failure::Authentication`] and the machine waits for the real one ... Only a failure after the responder
//!   authenticated, or of the host's own key operation, is fatal"; `message`: "A reject is not authenticated: forging
//!   one only forces the fallback handshake".
//! - `responder` module doc: "A message the responder cannot place is dropped with an error and changes nothing";
//!   `Failure::DifferentFirst`: "the held one was damaged or forged on the way, so the host may start the session
//!   again from this one"; `pinc-core` `rx` module doc, the host this models: "a first flight that every holder says
//!   differs from its own gets a half-open session of its own under the same id, up to four holders, so a forged
//!   flight never displaces the first", and "a long packet is offered to each holder, oldest first, until one owns
//!   it".
//! - `Initiator::on_key_response` / `Responder::on_key_response`: "[`Failure::UnexpectedKeyResponse`] (nothing
//!   changes) if no request of that kind is outstanding"; `keys` module doc: the host answers "whenever the host has
//!   it, so a slow device never blocks the state machine"; `Failure::KeyOperation`: "The host failed or refused a key
//!   operation" (fatal, `Failure::is_fatal`).
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    missing_docs
)]

use std::collections::VecDeque;

use ephyra::prelude::*;
use ephyra::{check_generator, check_shrinker};
use pinc_crypto::identity::MAX_SIGNATURE_LEN;
use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, Secret, Software};
use pinc_pbt::{bytes, mostly_valid};
use pinc_security::keyroll::Rekey;
use pinc_security::message::{
    Finish, IdSig, Initial, MAX_SEALED_LEN, MessageType, PrekeyField, Reject, Reply, ResumeHello, ResumeReply,
};
use pinc_security::{
    AeadSet, AlpnList, ClientTickets, ConnId, CreditRecord, Env, Established, Event, Failure, Initiator,
    InitiatorParams, KeyHandle, KeyRequest, KeyResponse, LocalIdentity, Output, PrekeyInfo, PrekeyPolicy, Responder,
    ResponderConfig, ResponderStores, SoftKeys, SoftPrekeys, TicketBatch, TicketEntry, VERSION,
};
use pinc_wire::{WireError, Writer};

// ---------------------------------------------------------------------------------------------------------------
// The codecs.

fn arr<const N: usize>(g: &mut Source) -> [u8; N] {
    core::array::from_fn(|_| g.int(0u8..=255))
}

fn some_bytes(g: &mut Source, n: usize) -> Vec<u8> {
    (0..n).map(|_| g.int(0u8..=255)).collect()
}

fn cid(g: &mut Source) -> ConnId {
    let n = *g.pick(&[0usize, 1, 4, 8, 16, 19, 20]);
    let n = if g.bool() { n } else { g.int(0usize..=20) };
    ConnId::new(&some_bytes(g, n)).unwrap()
}

fn alpn(g: &mut Source) -> Vec<u8> {
    let n = if g.bool() { *g.pick(&[1usize, 6, 31, 32]) } else { g.int(1usize..=32) };
    some_bytes(g, n)
}

fn credit(g: &mut Source) -> CreditRecord {
    CreditRecord::decode(&arr::<6>(g))
}

fn aead(g: &mut Source) -> Aead {
    if g.bool() { Aead::Aes128Gcm } else { Aead::ChaCha20Poly1305 }
}

fn version(g: &mut Source) -> u8 {
    if g.bool_with(0.8) { VERSION } else { g.int(0u8..=255) }
}

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

/// The length of a sealed identity and signature of a real algorithm (with the credit record of a Reply), or any
/// length the parser takes.
fn sealed(g: &mut Source) -> Vec<u8> {
    let alg = ALGS[g.index(4)];
    let real = 1 + 2 + alg.public_key_len() + 2 + alg.signature_len() + 6 + Aead::TAG_LEN;
    let n = match g.int(0u8..=3) {
        0 => real,
        1 => real - 6,
        2 => *g.pick(&[Aead::TAG_LEN, MAX_SEALED_LEN]),
        _ => g.int(Aead::TAG_LEN..=MAX_SEALED_LEN),
    };
    some_bytes(g, n)
}

fn batch(g: &mut Source) -> TicketBatch {
    let mut b = TicketBatch::new();
    for _ in 0..g.int(0usize..=4) {
        b.push(TicketEntry {
            tid: arr(g),
            lifetime_s: g.int(0u32..=u32::MAX),
        });
    }
    b
}

fn write_with(f: impl FnOnce(&mut Writer<'_>) -> Result<(), WireError>) -> Result<Vec<u8>, WireError> {
    let mut buf = vec![0u8; 8192];
    let mut w = Writer::new(&mut buf);
    f(&mut w)?;
    Ok(w.written().to_vec())
}

/// The kinds of message, in the order of [`valid_message`].
const KINDS: [&str; 12] = [
    "initial",
    "short initial",
    "prekey reject",
    "reply",
    "finish",
    "resume hello",
    "resume reply",
    "resume reject",
    "id-sig of a reply",
    "id-sig of a finish",
    "ticket batch",
    "rekey",
];

/// One valid message of a kind drawn first: every field in its documented range, the lengths at their edges often.
fn valid_message(g: &mut Source) -> (u8, Vec<u8>) {
    let kind = g.int(0u8..=11);
    let bytes = match kind {
        0 | 1 => {
            let a = alpn(g);
            let pk = some_bytes(g, KEM_ENCAPS_KEY_LEN);
            let pk: &[u8; KEM_ENCAPS_KEY_LEN] = pk.as_slice().try_into().unwrap();
            let h: [u8; 32] = arr(g);
            let m = Initial {
                version: version(g),
                dcid: cid(g),
                scid: cid(g),
                alpn: &a,
                aead_offer: AeadSet::from_bits(g.int(1u8..=3)).unwrap(),
                e: arr(g),
                prekey: if kind == 0 { PrekeyField::Full(pk) } else { PrekeyField::Hash(&h) },
                credit: credit(g),
            };
            write_with(|w| m.write(w))
        },
        2 | 7 => {
            let ty = if kind == 2 { MessageType::PrekeyReject } else { MessageType::ResumeReject };
            let m = Reject { echo: arr(g) };
            write_with(|w| m.write(w, ty))
        },
        3 => {
            let ct = some_bytes(g, KEM_CIPHERTEXT_LEN);
            let s = sealed(g);
            let m = Reply {
                scid: cid(g),
                aead: aead(g),
                e: arr(g),
                ct: ct.as_slice().try_into().unwrap(),
                sealed: &s,
            };
            write_with(|w| m.write(w))
        },
        4 => {
            let s = sealed(g);
            write_with(|w| Finish { sealed: &s }.write(w))
        },
        5 => {
            let a = alpn(g);
            let m = ResumeHello {
                version: version(g),
                dcid: cid(g),
                scid: cid(g),
                alpn: &a,
                aead: aead(g),
                tid: arr(g),
                e: arr(g),
                binder: arr(g),
                credit: credit(g),
            };
            write_with(|w| m.write(w))
        },
        6 => {
            let m = ResumeReply {
                scid: cid(g),
                e: arr(g),
                tickets: batch(g),
                credit: credit(g),
                confirm: arr(g),
            };
            write_with(|w| m.write(w))
        },
        8 | 9 => {
            let alg = ALGS[g.index(4)];
            let pk = some_bytes(g, alg.public_key_len());
            let sig = some_bytes(g, alg.signature_len());
            let m = IdSig {
                alg,
                public_key: &pk,
                signature: &sig,
                credit: (kind == 8).then(|| credit(g)),
            };
            write_with(|w| m.write(w))
        },
        10 => {
            let b = batch(g);
            write_with(|w| b.write(w))
        },
        _ => {
            let answer = g.bool();
            let bits = g.int(0u32..=63);
            let switch_pn = if bits == 0 { 0 } else { g.int(0u64..=(1u64 << bits) - 1) };
            // A request carries the sender's roll count; one past 2^63 - 1 does not encode.
            let roll = if answer { 0 } else { [0, 63, 64, 127, 128, 1 << 62, (1 << 63) - 1, 1 << 63][g.index(8)] };
            let mut m = Rekey {
                answer,
                share: arr(g),
                echo: if answer { arr(g) } else { [0; 8] },
                switch_pn: if answer { switch_pn } else { 0 },
                roll,
            };
            let written = write_with(|w| m.write(w));
            if roll == 1 << 63 {
                assert!(written.is_err(), "a roll of 2^63 was encoded");
                m.roll = 0;
                write_with(|w| m.write(w))
            } else {
                written
            }
        },
    };
    (kind, bytes.unwrap())
}

/// Every parser of the crate's wire formats, run on `m`; for each one that accepts it, its name and what writing the
/// parsed value gives back.
fn reencode_all(m: &[u8]) -> Vec<(&'static str, Result<Vec<u8>, WireError>)> {
    let mut out = Vec::new();
    if let Ok(x) = Initial::parse(m) {
        let name = if matches!(x.prekey, PrekeyField::Full(_)) { KINDS[0] } else { KINDS[1] };
        out.push((name, write_with(|w| x.write(w))));
    }
    for (name, ty) in [(KINDS[2], MessageType::PrekeyReject), (KINDS[7], MessageType::ResumeReject)] {
        if let Ok(x) = Reject::parse(m, ty) {
            out.push((name, write_with(|w| x.write(w, ty))));
        }
    }
    if let Ok(x) = Reply::parse(m) {
        out.push((KINDS[3], write_with(|w| x.write(w))));
    }
    if let Ok(x) = Finish::parse(m) {
        out.push((KINDS[4], write_with(|w| x.write(w))));
    }
    if let Ok(x) = ResumeHello::parse(m) {
        out.push((KINDS[5], write_with(|w| x.write(w))));
    }
    if let Ok(x) = ResumeReply::parse(m) {
        out.push((KINDS[6], write_with(|w| x.write(w))));
    }
    for (name, with_credit) in [(KINDS[8], true), (KINDS[9], false)] {
        if let Ok(x) = IdSig::parse(m, with_credit) {
            out.push((name, write_with(|w| x.write(w))));
        }
    }
    if let Ok(x) = TicketBatch::parse(m) {
        out.push((KINDS[10], write_with(|w| x.write(w))));
    }
    if let Ok(x) = Rekey::decode(m) {
        out.push((KINDS[11], write_with(|w| x.write(w))));
    }
    out
}

fn valid_messages() -> impl Gen<Value = (u8, Vec<u8>)> {
    valid_message
}

/// The message generator reaches every kind, and its values and shrinks stay valid: each parses as its kind.
#[test]
fn the_message_generator_is_valid_and_shrinks_valid() {
    let parses = |x: &(u8, Vec<u8>)| reencode_all(&x.1).iter().any(|(n, _)| *n == KINDS[usize::from(x.0)]);
    check_generator(&Config::default().tests(3000), valid_messages(), parses).assert_passed();
    check_shrinker(&Config::default().tests(300), valid_messages(), parses, |x| x.1.len() as u64).assert_passed();
    let mut seen = [false; 12];
    let mut g = Source::new(7, 64);
    for _ in 0..2000 {
        seen[usize::from(valid_message(&mut g).0)] = true;
    }
    assert!(seen.iter().all(|s| *s), "the generator misses a kind: {seen:?}");
}

/// A valid message parses as its own kind, writes back to the same bytes, and no strict prefix of it and no
/// extension of it by one byte parses as that kind ("a missing byte or a trailing byte is an error").
#[ephyra::test(gen = valid_messages(), tests = 3000)]
fn a_valid_message_parses_back_to_its_bytes_and_nothing_shorter_or_longer_does(x: (u8, Vec<u8>)) {
    let (kind, m) = x;
    let name = KINDS[usize::from(kind)];
    let back = reencode_all(&m);
    let mine = back.iter().find(|(n, _)| *n == name);
    assert!(mine.is_some(), "a valid {name} did not parse: {m:?}");
    let (_, again) = mine.unwrap();
    assert_eq!(again.as_ref().ok(), Some(&m), "a {name} did not write back to the bytes it was parsed from");
    for cut in [0, 1, m.len() / 2, m.len().saturating_sub(1)] {
        if cut < m.len() {
            let shorter = reencode_all(&m[..cut]);
            assert!(!shorter.iter().any(|(n, _)| *n == name), "a {name} cut to {cut} bytes still parsed");
        }
    }
    let mut longer = m.clone();
    longer.push(0);
    assert!(!reencode_all(&longer).iter().any(|(n, _)| *n == name), "a {name} with a trailing byte parsed");
}

/// No byte string panics a parser, and whatever any parser accepts writes back to exactly the bytes it read: a length
/// field that made a parser skip or reuse bytes would show as a different encoding.
#[ephyra::test(gen = mostly_valid(|g: &mut Source| valid_message(g).1), tests = 20_000)]
fn every_parser_is_total_and_canonical_on_hostile_bytes(m: Vec<u8>) {
    for (name, again) in reencode_all(&m) {
        ephyra::signature(name);
        assert_eq!(again.as_ref().ok(), Some(&m), "the {name} parser accepted bytes it does not write back");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The state machines between an honest network and a forger.

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

fn responder(p: &Party) -> Responder {
    let mut cfg = ResponderConfig::new(p.id, ConnId::new(b"respond0").unwrap(), AlpnList::new(&[ALPN]).unwrap());
    cfg.tickets_per_session = 2;
    Responder::new(cfg)
}

/// How the run starts.
#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Setup {
    #[ephyra(gen = algs())]
    i_alg: u8,
    #[ephyra(gen = algs())]
    r_alg: u8,
    /// 0: a full handshake; 1: the short Initial to a responder that cached the prekey; 2: the short Initial to one
    /// that did not; 3: resumption with a ticket of an earlier session.
    #[ephyra(gen = gens::int(0u8..=3))]
    mode: u8,
    /// Whether the host allows short Initials on resends.
    short_ok: bool,
}

/// Mostly the fast algorithms; the post-quantum ones now and then.
fn algs() -> impl Gen<Value = u8> {
    gens::frequency(vec![(8, gens::int(0u8..=1).boxed()), (1, gens::int(2u8..=3).boxed())])
}

/// One change to a message, as `pinc_pbt::mangle` makes them, kept as data so it shrinks and applies to whatever
/// message the run holds at that point.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Edit {
    Flip(#[ephyra(gen = pos())] u16, #[ephyra(gen = gens::int(0u8..=7))] u8),
    Set(#[ephyra(gen = pos())] u16, u8),
    Cut(#[ephyra(gen = pos())] u16),
    Dup(#[ephyra(gen = pos())] u16, #[ephyra(gen = gens::int(1u8..=8))] u8),
    Insert(#[ephyra(gen = pos())] u16, u8),
    Extreme(#[ephyra(gen = pos())] u16, #[ephyra(gen = gens::int(0u8..=14))] u8),
    Extend(#[ephyra(gen = bytes(8))] Vec<u8>),
}

/// A position in a message: half the time in the first 64 bytes, where the version, the ids, the ALPN, the cipher
/// and the ticket id sit, so an edit reaches a check past the parser instead of only the sealed part.
fn pos() -> impl Gen<Value = u16> {
    gens::frequency(vec![(1, gens::int(0u16..=63).boxed()), (1, gens::int(0u16..=4000).boxed())])
}

const EXTREMES: [u8; 15] = [0x00, 0x01, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x3f, 0x40, 0x7f, 0x80, 0xbf, 0xc0, 0xfe, 0xff];

fn apply(m: &[u8], edits: &[Edit]) -> Vec<u8> {
    let mut out = m.to_vec();
    for e in edits {
        if out.is_empty() {
            break;
        }
        let n = out.len();
        let at = |p: &u16| usize::from(*p) % n;
        match e {
            Edit::Flip(p, b) => out[at(p)] ^= 1 << b,
            Edit::Set(p, v) => out[at(p)] = *v,
            Edit::Cut(p) => out.truncate(at(p)),
            Edit::Dup(p, k) => {
                let i = at(p);
                let run: Vec<u8> = out[i..(i + usize::from(*k)).min(n)].to_vec();
                out.splice(i..i, run);
            },
            Edit::Insert(p, v) => out.insert(at(p), *v),
            Edit::Extreme(p, k) => out[at(p)] = EXTREMES[usize::from(*k)],
            Edit::Extend(tail) => out.extend_from_slice(tail),
        }
    }
    out
}

/// One event of the run. Deliveries of the honest network are in order and lossless; the forger adds messages.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    /// Deliver the oldest message the initiator sent.
    ToR,
    /// Deliver the oldest message a responder sent.
    ToI,
    /// The hosts answer the key requests outstanding now (until then the machines wait: a slow host).
    KeysI,
    KeysR,
    /// The loss timers.
    TimerI,
    TimerR,
    /// Hand the initiator a forgery: 0 the last message a responder sent, 1 the answer of an impostor (another node,
    /// which can build a Reply that opens, or a reject with the right echo) to one of the initiator's first flights,
    /// 2 an earlier message a responder sent; then the edits.
    ForgeI(
        #[ephyra(gen = gens::int(0u8..=2))] u8,
        #[ephyra(gen = gens::int(0u8..=15))] u8,
        #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(0..=3))] Vec<Edit>,
    ),
    /// Hand the responders a forgery: 0 an earlier message of the initiator, 1 one of its first flights; then the edits.
    ForgeR(
        #[ephyra(gen = gens::int(0u8..=1))] u8,
        #[ephyra(gen = gens::int(0u8..=15))] u8,
        #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(0..=3))] Vec<Edit>,
    ),
    /// A message of a known type byte with random contents (true: to the initiator).
    Garbage(bool, #[ephyra(gen = gens::int(0u8..=9))] u8, #[ephyra(gen = bytes(120))] Vec<u8>),
}

/// How a key host answers the request outstanding now.
#[derive(Clone, Copy, Debug, ephyra::Arbitrary)]
enum How {
    /// Right.
    Soft,
    /// `KeyResponse::Failed`.
    Failed,
    /// The answer of the other kind of request.
    WrongKind,
    /// A wrong shared secret, or a signature of random bytes of the right length.
    WrongValue,
    /// A signature of the right algorithm by another key.
    OtherSigner,
    /// A signature of the wrong length.
    ShortSig,
    /// The right answer delivered twice.
    Twice,
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum HostOp {
    Net(Op),
    Host(bool, How),
}

struct Holder {
    m: Responder,
    est: Option<Established>,
    ests: usize,
    failed: Vec<Failure>,
    /// It sent a Reply or a resume Reply.
    replied: bool,
}

fn drain_r(h: &mut Holder, to_i: &mut VecDeque<Vec<u8>>, hist: &mut Vec<Vec<u8>>) {
    for _ in 0..16 {
        match h.m.poll_output() {
            Some(Output::Send { data, .. }) => {
                if matches!(data.first(), Some(4 | 7)) {
                    h.replied = true;
                }
                to_i.push_back(data.to_vec());
                hist.push(data.to_vec());
            },
            Some(Output::Event(Event::Established(e))) => {
                h.ests += 1;
                h.est = Some(e);
            },
            Some(Output::Event(Event::Failed(f))) => h.failed.push(f),
            Some(Output::Event(_) | Output::Key(_)) => {},
            None => break,
        }
    }
}

fn is_first(m: &[u8]) -> bool {
    matches!(
        MessageType::of(m),
        Ok(MessageType::Initial | MessageType::ShortInitial | MessageType::ResumeHello)
    )
}

fn first_dcid(m: &[u8]) -> Option<ConnId> {
    match MessageType::of(m).ok()? {
        MessageType::Initial | MessageType::ShortInitial => Initial::parse(m).ok().map(|i| i.dcid),
        MessageType::ResumeHello => ResumeHello::parse(m).ok().map(|h| h.dcid),
        _ => None,
    }
}

fn same_session(a: &Established, b: &Established) -> bool {
    a.cid_secret == b.cid_secret
}

fn same_keys(i: &Established, r: &Established) {
    assert_eq!(i.traffic.aead, r.traffic.aead, "the sides chose different AEADs");
    assert_eq!(i.traffic.send, r.traffic.recv, "initiator send key differs from responder receive key");
    assert_eq!(i.traffic.recv, r.traffic.send, "initiator receive key differs from responder send key");
    assert_eq!(i.resume, r.resume, "the resumption secrets differ");
    assert_eq!(i.resumed, r.resumed, "one side resumed, the other did not");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Req {
    Sign(IdentityAlg),
    Decap,
}

fn pending(r: Option<KeyRequest<'_>>) -> Option<(Req, Vec<u8>, KeyHandle)> {
    match r? {
        KeyRequest::Sign { key, alg, message } => Some((Req::Sign(alg), message.to_vec(), key)),
        KeyRequest::Decapsulate { key, ct } => Some((Req::Decap, ct.to_vec(), key)),
    }
}

struct World {
    ip: Party,
    rp: Party,
    /// The impostor: another node, same algorithm as the responder.
    xp: Party,
    prov: Software,
    i_drbg: Drbg,
    r_drbg: Drbg,
    x_drbg: Drbg,
    now: u64,
    prekeys: SoftPrekeys<Software>,
    stores: Box<Stores>,
    i: Initiator,
    i_est: Vec<Established>,
    i_failed: Vec<Failure>,
    /// The destination id of the current table of holders.
    dcid: Option<ConnId>,
    holders: Vec<Holder>,
    /// The tables of the other destination ids.
    others: Vec<(ConnId, Vec<Holder>)>,
    retired: Vec<Holder>,
    to_r: VecDeque<Vec<u8>>,
    to_i: VecDeque<Vec<u8>>,
    hist_r: Vec<Vec<u8>>,
    hist_i: Vec<Vec<u8>>,
    firsts: Vec<Vec<u8>>,
    /// An honest first flight found the table full of forged holders (the documented cap of four).
    blocked: bool,
    /// The key host answered in a way that ends the handshake (a failure, a bad signature).
    fatal_host: bool,
}

impl World {
    fn new(s: &Setup) -> Self {
        let i_alg = ALGS[usize::from(s.i_alg)];
        let r_alg = ALGS[usize::from(s.r_alg)];
        let prov = Software;
        let mut i_drbg = Drbg::new(&[0x11; 32]);
        let prekeys = SoftPrekeys::new(
            &mut Env {
                provider: &prov,
                now: T0,
                drbg: &mut i_drbg,
            },
            PrekeyPolicy::default(),
        )
        .unwrap();
        let mut w = Self {
            ip: party(i_alg, 0x21),
            rp: party(r_alg, 0x22),
            xp: party(r_alg, 0x23),
            prov,
            i_drbg,
            r_drbg: Drbg::new(&[0x33; 32]),
            x_drbg: Drbg::new(&[0x55; 32]),
            now: T0,
            prekeys,
            stores: Box::default(),
            i: placeholder(),
            i_est: Vec::new(),
            i_failed: Vec::new(),
            dcid: None,
            holders: Vec::new(),
            others: Vec::new(),
            retired: Vec::new(),
            to_r: VecDeque::new(),
            to_i: VecDeque::new(),
            hist_r: Vec::new(),
            hist_i: Vec::new(),
            firsts: Vec::new(),
            blocked: false,
            fatal_host: false,
        };
        if s.mode == 1 || s.mode == 3 {
            w.restart(None, false, false);
            // An earlier, clean session leaves the prekey cached and a ticket behind.
            w.settle();
            let ie = w.i_est.first().cloned().expect("a clean first session did not complete at the initiator");
            let re = w.responder_session(&ie).expect("a clean first session did not complete at the responder");
            let mut client: ClientTickets<4> = ClientTickets::new();
            client.accept_batch(&ie, &re.tickets, T0);
            let ticket = if s.mode == 3 { client.take(&w.rp.id.node_id(), ALPN, T0) } else { None };
            assert!(s.mode != 3 || ticket.is_some(), "the first session left no ticket");
            w.restart(ticket, s.mode == 1, s.short_ok);
        } else {
            w.restart(None, s.mode == 2, s.short_ok);
        }
        w
    }

    /// A new initiator (and a new network), keeping the responder's stores and the prekeys.
    fn restart(&mut self, ticket: Option<pinc_security::Ticket>, peer_has_prekey: bool, short_ok: bool) {
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.i_drbg,
        };
        let prekey: PrekeyInfo = self.prekeys.acquire(&mut env).unwrap();
        self.i = Initiator::new(
            &mut env,
            InitiatorParams {
                peer: self.rp.id.node_id(),
                alpn: ALPN,
                scid: ConnId::new(b"initiat0").unwrap(),
                identity: &self.ip.id,
                prekey: &prekey,
                peer_has_prekey,
                ticket,
                credit: CreditRecord::new(1 << 20, 16, 1200),
            },
        )
        .unwrap();
        if short_ok {
            self.i.set_short_until(u64::MAX);
        }
        self.i_est.clear();
        self.i_failed.clear();
        self.dcid = None;
        self.holders.clear();
        self.others.clear();
        self.retired.clear();
        self.to_r.clear();
        self.to_i.clear();
        self.hist_r.clear();
        self.hist_i.clear();
        self.firsts.clear();
        self.blocked = false;
        self.fatal_host = false;
        self.drain_i();
    }

    fn drain_i(&mut self) {
        for _ in 0..16 {
            match self.i.poll_output() {
                Some(Output::Send { data, .. }) => {
                    if is_first(data) {
                        self.firsts.push(data.to_vec());
                    }
                    self.to_r.push_back(data.to_vec());
                    self.hist_r.push(data.to_vec());
                },
                Some(Output::Event(Event::Established(e))) => self.i_est.push(e),
                Some(Output::Event(Event::Failed(f))) => self.i_failed.push(f),
                Some(Output::Event(_) | Output::Key(_)) => {},
                None => break,
            }
        }
    }

    fn to_i_side(&mut self, m: &[u8]) {
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.i_drbg,
        };
        let _ = self.i.handle(&mut env, m);
        self.drain_i();
    }

    /// Make the table of destination id `to` the current one, keeping the current one under its id.
    fn switch(&mut self, to: Option<ConnId>) {
        if self.dcid == to {
            return;
        }
        let cur = std::mem::take(&mut self.holders);
        if let Some(c) = self.dcid {
            self.others.push((c, cur));
        }
        self.dcid = to;
        if let Some(i) = self.others.iter().position(|(c, _)| Some(*c) == to) {
            self.holders = self.others.remove(i).1;
        }
    }

    /// Deliver `m` as the endpoint does: a first flight goes to the holders of its destination id, any other message
    /// to the session the initiator is in (the current table); it is offered to each holder, oldest first, until one
    /// owns it; a first flight every holder says differs from its own gets a holder of its own, up to four. Only an
    /// honest first flight moves the initiator to another table.
    fn to_r_side(&mut self, m: &[u8], honest: bool) {
        let before = self.dcid;
        if let Some(d) = first_dcid(m) {
            self.switch(Some(d));
        }
        self.deliver_r(m, honest);
        if !honest {
            self.switch(before);
        }
    }

    fn deliver_r(&mut self, m: &[u8], honest: bool) {
        let mut owned = false;
        let mut all_different = !self.holders.is_empty();
        for h in &mut self.holders {
            let mut env = Env {
                provider: &self.prov,
                now: self.now,
                drbg: &mut self.r_drbg,
            };
            let r = h.m.handle(&mut env, &mut self.stores, m);
            drain_r(h, &mut self.to_i, &mut self.hist_i);
            match r {
                Ok(()) => {
                    owned = true;
                    break;
                },
                Err(Failure::DifferentFirst) => {},
                Err(_) => all_different = false,
            }
        }
        // A session that ended leaves the table.
        let (gone, kept): (Vec<Holder>, Vec<Holder>) =
            std::mem::take(&mut self.holders).into_iter().partition(|h| !h.failed.is_empty());
        self.holders = kept;
        self.retired.extend(gone);
        if owned || !is_first(m) || !(self.holders.is_empty() || all_different) {
            return;
        }
        if self.holders.len() >= 4 {
            self.blocked |= honest;
            return;
        }
        let mut h = Holder {
            m: responder(&self.rp),
            est: None,
            ests: 0,
            failed: Vec::new(),
            replied: false,
        };
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.r_drbg,
        };
        let _ = h.m.handle(&mut env, &mut self.stores, m);
        drain_r(&mut h, &mut self.to_i, &mut self.hist_i);
        if h.failed.is_empty() {
            self.holders.push(h);
        } else {
            self.retired.push(h);
        }
    }

    fn keys_i(&mut self) {
        self.host_i(How::Soft);
    }

    fn keys_r(&mut self) {
        for k in 0..self.holders.len() {
            self.host_r(k, How::Soft);
        }
    }

    /// The initiator's host answers the outstanding request as `how` says, and the result is checked against what
    /// the documentation promises for that answer.
    fn host_i(&mut self, how: How) {
        let before = pending(self.i.pending_key_request());
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.i_drbg,
        };
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let r = match (how, &before) {
            (How::Soft, _) => {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &self.ip.kp)),
                    prekeys: Some(&self.prekeys),
                };
                self.i.answer_soft(&mut env, &soft).map(|_| ())
            },
            (_, None) => {
                let r = self.i.on_key_response(&mut env, KeyResponse::Failed);
                assert!(
                    matches!(r, Err(Failure::UnexpectedKeyResponse | Failure::Closed)),
                    "the initiator took an answer with no request outstanding: {r:?}"
                );
                r
            },
            (How::Twice, Some((req, msg, key))) => {
                let first = match req {
                    Req::Sign(_) => {
                        let n = self.ip.kp.sign(msg, &mut sig).unwrap();
                        self.i.on_key_response(&mut env, KeyResponse::Signature(&sig[..n]))
                    },
                    Req::Decap => {
                        let ct: &[u8; KEM_CIPHERTEXT_LEN] = msg.as_slice().try_into().unwrap();
                        let ss = self.prekeys.decapsulate(&self.prov, *key, ct).unwrap();
                        let r1 = self.i.on_key_response(&mut env, KeyResponse::SharedSecret(ss.clone()));
                        let r2 = self.i.on_key_response(&mut env, KeyResponse::SharedSecret(ss));
                        assert_eq!(r2, Err(Failure::UnexpectedKeyResponse), "a repeated shared secret was taken");
                        r1
                    },
                };
                if matches!(req, Req::Sign(_)) {
                    let n = self.ip.kp.sign(msg, &mut sig).unwrap();
                    let again = self.i.on_key_response(&mut env, KeyResponse::Signature(&sig[..n]));
                    assert!(
                        matches!(again, Err(Failure::UnexpectedKeyResponse | Failure::Closed)),
                        "a repeated signature was taken: {again:?}"
                    );
                }
                first
            },
            (How::Failed, Some(_)) => {
                let r = self.i.on_key_response(&mut env, KeyResponse::Failed);
                assert_eq!(r, Err(Failure::KeyOperation), "a failed key operation");
                self.fatal_host = true;
                r
            },
            (How::WrongKind, Some((req, ..))) => {
                let r = match req {
                    Req::Sign(_) => self.i.on_key_response(&mut env, KeyResponse::SharedSecret(Secret::new([9; 32]))),
                    Req::Decap => self.i.on_key_response(&mut env, KeyResponse::Signature(&[7; 64])),
                };
                assert_eq!(r, Err(Failure::UnexpectedKeyResponse), "an answer of the wrong kind");
                let after = pending(self.i.pending_key_request());
                assert_eq!(after, before, "an answer of the wrong kind changed the request");
                r
            },
            (How::WrongValue, Some((Req::Decap, ..))) => {
                let r = self.i.on_key_response(&mut env, KeyResponse::SharedSecret(Secret::new([0x5a; 32])));
                // The Reply does not open under a wrong secret: it is dropped, and the real one is waited for.
                assert_eq!(r, Err(Failure::Authentication), "a wrong shared secret");
                r
            },
            (How::WrongValue | How::OtherSigner, Some((Req::Sign(alg), msg, _))) => {
                let n = if matches!(how, How::OtherSigner) {
                    party(*alg, 0x99).kp.sign(msg, &mut sig).unwrap()
                } else {
                    alg.signature_len()
                };
                self.fatal_host = true;
                self.i.on_key_response(&mut env, KeyResponse::Signature(&sig[..n]))
            },
            (How::OtherSigner, Some((Req::Decap, ..))) => {
                let r = self.i.on_key_response(&mut env, KeyResponse::SharedSecret(Secret::new([0x3c; 32])));
                assert_eq!(r, Err(Failure::Authentication), "a shared secret of another prekey");
                r
            },
            (How::ShortSig, Some((Req::Sign(_), ..))) => {
                let r = self.i.on_key_response(&mut env, KeyResponse::Signature(&[1, 2, 3]));
                assert_eq!(r, Err(Failure::KeyOperation), "a signature of the wrong length");
                self.fatal_host = true;
                r
            },
            (How::ShortSig, Some((Req::Decap, ..))) => Ok(()),
        };
        let _ = r;
        self.drain_i();
    }

    /// As [`World::host_i`], for holder `k`. A responder only ever asks for a signature.
    fn host_r(&mut self, k: usize, how: How) {
        let Some(h) = self.holders.get_mut(k) else { return };
        let before = pending(h.m.pending_key_request());
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.r_drbg,
        };
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        match (how, &before) {
            (How::Soft, _) => {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &self.rp.kp)),
                    prekeys: None,
                };
                let _ = h.m.answer_soft(&mut env, &soft);
            },
            (_, None) => {
                let r = h.m.on_key_response(&mut env, KeyResponse::Failed);
                assert!(
                    matches!(r, Err(Failure::UnexpectedKeyResponse | Failure::Closed)),
                    "a responder took an answer with no request outstanding: {r:?}"
                );
            },
            (_, Some((Req::Decap, ..))) => panic!("a responder asked to decapsulate"),
            (How::Twice, Some((_, msg, _))) => {
                let n = self.rp.kp.sign(msg, &mut sig).unwrap();
                let first = h.m.on_key_response(&mut env, KeyResponse::Signature(&sig[..n]));
                assert_eq!(first, Ok(()), "the right signature was refused");
                let again = h.m.on_key_response(&mut env, KeyResponse::Signature(&sig[..n]));
                assert_eq!(again, Err(Failure::UnexpectedKeyResponse), "a repeated signature was taken");
            },
            (How::Failed, Some(_)) => {
                let r = h.m.on_key_response(&mut env, KeyResponse::Failed);
                assert_eq!(r, Err(Failure::KeyOperation), "a failed key operation");
                self.fatal_host = true;
            },
            (How::WrongKind, Some(_)) => {
                let r = h.m.on_key_response(&mut env, KeyResponse::SharedSecret(Secret::new([9; 32])));
                assert_eq!(r, Err(Failure::UnexpectedKeyResponse), "an answer of the wrong kind");
                assert_eq!(pending(h.m.pending_key_request()), before, "an answer of the wrong kind changed the request");
            },
            (How::WrongValue | How::OtherSigner, Some((Req::Sign(alg), msg, _))) => {
                let n = if matches!(how, How::OtherSigner) {
                    party(*alg, 0x98).kp.sign(msg, &mut sig).unwrap()
                } else {
                    alg.signature_len()
                };
                let r = h.m.on_key_response(&mut env, KeyResponse::Signature(&sig[..n]));
                assert_eq!(r, Ok(()), "a signature of the right length was refused");
                self.fatal_host = true;
            },
            (How::ShortSig, Some(_)) => {
                let r = h.m.on_key_response(&mut env, KeyResponse::Signature(&[1, 2, 3]));
                assert_eq!(r, Err(Failure::KeyOperation), "a signature of the wrong length");
                self.fatal_host = true;
            },
        }
        drain_r(h, &mut self.to_i, &mut self.hist_i);
    }

    fn timer_i(&mut self) {
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.i_drbg,
        };
        let _ = self.i.retransmit(&mut env);
        self.drain_i();
    }

    fn timer_r(&mut self) {
        for h in &mut self.holders {
            h.m.retransmit();
            drain_r(h, &mut self.to_i, &mut self.hist_i);
        }
    }

    /// What an impostor node answers to the first flight `m`.
    fn impostor(&mut self, m: &[u8]) -> Option<Vec<u8>> {
        let mut x = responder(&self.xp);
        let mut stores: Box<Stores> = Box::default();
        let mut env = Env {
            provider: &self.prov,
            now: self.now,
            drbg: &mut self.x_drbg,
        };
        let _ = x.handle(&mut env, &mut stores, m);
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &self.xp.kp)),
            prekeys: None,
        };
        let _ = x.answer_soft(&mut env, &soft);
        for _ in 0..8 {
            match x.poll_output() {
                Some(Output::Send { data, .. }) => return Some(data.to_vec()),
                Some(_) => {},
                None => break,
            }
        }
        None
    }

    fn step(&mut self, op: &Op) {
        match op {
            Op::ToR => {
                if let Some(m) = self.to_r.pop_front() {
                    self.to_r_side(&m, true);
                }
            },
            Op::ToI => {
                if let Some(m) = self.to_i.pop_front() {
                    self.to_i_side(&m);
                }
            },
            Op::KeysI => self.keys_i(),
            Op::KeysR => self.keys_r(),
            Op::TimerI => self.timer_i(),
            Op::TimerR => self.timer_r(),
            Op::ForgeI(src, k, edits) => {
                let base = match src {
                    0 => self.hist_i.last().cloned(),
                    1 => {
                        let n = self.firsts.len();
                        let first = (n > 0).then(|| self.firsts[usize::from(*k) % n].clone());
                        first.and_then(|f| self.impostor(&f))
                    },
                    _ => {
                        let n = self.hist_i.len();
                        (n > 0).then(|| self.hist_i[usize::from(*k) % n].clone())
                    },
                };
                if let Some(b) = base {
                    self.to_i_side(&apply(&b, edits));
                }
            },
            Op::ForgeR(src, k, edits) => {
                let pool = if *src == 0 { &self.hist_r } else { &self.firsts };
                let n = pool.len();
                if n > 0 {
                    let m = apply(&pool[usize::from(*k) % n], edits);
                    self.to_r_side(&m, false);
                }
            },
            Op::Garbage(to_i, ty, body) => {
                let mut m = vec![*ty];
                m.extend_from_slice(body);
                if *to_i {
                    self.to_i_side(&m);
                } else {
                    self.to_r_side(&m, false);
                }
            },
        }
        self.check();
    }

    fn all_holders(&self) -> impl Iterator<Item = &Holder> {
        self.holders
            .iter()
            .chain(self.others.iter().flat_map(|(_, t)| t.iter()))
            .chain(self.retired.iter())
    }

    /// The responder's side of the session the initiator holds, if a responder holds it.
    fn responder_session(&self, ie: &Established) -> Option<Established> {
        self.all_holders()
            .filter_map(|h| h.est.as_ref())
            .find(|re| same_session(ie, re))
            .cloned()
    }

    fn check(&self) {
        assert!(self.i_est.len() <= 1, "the initiator was established twice");
        assert!(self.i_failed.len() <= 1, "the initiator reported its failure twice");
        if self.fatal_host {
            assert!(
                self.i_failed.iter().all(|f| *f == Failure::KeyOperation),
                "the initiator failed for another reason than its host: {:?}",
                self.i_failed
            );
        } else {
            assert!(self.i_failed.is_empty(), "the initiator failed: {:?}", self.i_failed);
        }
        let i_node = self.ip.id.node_id();
        let r_node = self.rp.id.node_id();
        if let Some(ie) = self.i_est.first() {
            assert_eq!(ie.peer, r_node, "the initiator is established with another node");
        }
        let mut matching = 0;
        for h in self.all_holders() {
            assert!(h.ests <= 1, "a responder was established twice");
            assert!(h.failed.len() <= 1, "a responder reported its failure twice");
            if h.replied && !h.failed.is_empty() {
                // After its Reply a responder only fails on what the initiator's host signed.
                assert!(
                    self.fatal_host && matches!(h.failed[0], Failure::KeyOperation | Failure::BadSignature),
                    "a responder that replied failed: {:?}",
                    h.failed
                );
            }
            let Some(re) = &h.est else { continue };
            assert_eq!(re.peer, i_node, "a responder is established with another node");
            let ie = self.i_est.first();
            if !re.resumed {
                // The Finish goes out with the initiator's session: a full handshake that ended here ended there too.
                assert!(ie.is_some(), "a responder completed a full handshake the initiator never finished");
            }
            if let Some(ie) = ie
                && same_session(ie, re)
            {
                same_keys(ie, re);
                matching += 1;
            }
        }
        assert!(matching <= 1, "{matching} responders hold the initiator's session");
    }

    fn complete(&self) -> bool {
        self.i_est.first().is_some_and(|ie| self.responder_session(ie).is_some())
    }

    /// The honest network delivers everything, the hosts answer at once and the timers run, a bounded number of times.
    fn settle(&mut self) {
        for _ in 0..16 {
            for _ in 0..96 {
                self.keys_i();
                self.keys_r();
                if let Some(m) = self.to_r.pop_front() {
                    self.to_r_side(&m, true);
                } else if let Some(m) = self.to_i.pop_front() {
                    self.to_i_side(&m);
                } else {
                    break;
                }
                self.check();
            }
            if self.complete() {
                break;
            }
            self.timer_i();
            self.timer_r();
            self.check();
        }
        self.check();
    }
}

/// A machine to fill the field until `restart` builds the real one.
fn placeholder() -> Initiator {
    let p = Software;
    let mut drbg = Drbg::new(&[0; 32]);
    let mut env = Env {
        provider: &p,
        now: T0,
        drbg: &mut drbg,
    };
    let me = party(IdentityAlg::Ed25519, 1);
    let prekey = PrekeyInfo::new([0; KEM_ENCAPS_KEY_LEN], KeyHandle(0));
    Initiator::new(
        &mut env,
        InitiatorParams {
            peer: me.id.node_id(),
            alpn: ALPN,
            scid: ConnId::default(),
            identity: &me.id,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            credit: CreditRecord::NONE,
        },
    )
    .unwrap()
}

fn hostile_runs() -> impl Gen<Value = (Setup, Vec<Op>)> {
    (ephyra::any::<Setup>(), gens::vec(ephyra::any::<Op>()).len(0..=40))
}

/// Forged, mangled and replayed messages to both sides at any point of the handshake, then an honest network: the
/// handshake completes with both sides holding the same keys, and a side never fails or completes on a forgery. The
/// first pass stopped owing completion once any message was changed; this owes it always, except when an honest
/// first flight met a table of four forged holders.
#[ephyra::test(gen = hostile_runs(), tests = 300)]
fn after_any_forgery_an_honest_network_still_completes_the_handshake(run: (Setup, Vec<Op>)) {
    let (setup, ops) = run;
    let mut w = World::new(&setup);
    for op in &ops {
        w.step(op);
    }
    w.settle();
    if !w.blocked {
        assert!(!w.i_est.is_empty(), "the initiator did not complete after the forgeries (mode {})", setup.mode);
        assert!(w.complete(), "no responder holds the initiator's session (mode {})", setup.mode);
    }
}

fn host_runs() -> impl Gen<Value = (Setup, Vec<HostOp>)> {
    (ephyra::any::<Setup>(), gens::vec(ephyra::any::<HostOp>()).len(0..=40))
}

/// A key host that answers late, twice, with the wrong kind, with a wrong value, or not at all, mixed with forgeries:
/// each answer gets the result its documentation states, a side ends either established with the right keys or
/// failed with the host's reason, and when no answer was of a kind that ends the handshake (a failure, a wrong
/// signature), the honest network still completes it.
#[ephyra::test(gen = host_runs(), tests = 300)]
fn a_misbehaving_key_host_fails_the_handshake_loudly_or_changes_nothing(run: (Setup, Vec<HostOp>)) {
    let (setup, ops) = run;
    let mut w = World::new(&setup);
    for op in &ops {
        match op {
            HostOp::Net(op) => w.step(op),
            HostOp::Host(true, how) => {
                w.host_i(*how);
                w.check();
            },
            HostOp::Host(false, how) => {
                w.host_r(0, *how);
                w.check();
            },
        }
    }
    w.settle();
    if !w.blocked && !w.fatal_host {
        assert!(!w.i_est.is_empty(), "the initiator did not complete after a recoverable host (mode {})", setup.mode);
        assert!(w.complete(), "no responder holds the initiator's session (mode {})", setup.mode);
    }
}
