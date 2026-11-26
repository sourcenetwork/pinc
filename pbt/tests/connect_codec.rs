//! `pinc-connect`: every codec that reads bytes from the network, and the batch builder.
//!
//! Where the expected behaviour comes from:
//! - `carrier::frame`: "A decode never accepts trailing bytes after a fixed-size frame, an empty packet, a nested
//!   batch, an unknown type or an unknown identity tag", `Frame::encode` refuses "a field the decoder would refuse",
//!   and the `BatchBuilder` rules: "at most [`BATCH_MAX_FRAMES`] frames and [`BATCH_MAX_BYTES`] bytes of frames, and a
//!   long-header packet is never batched ... One frame alone is emitted without a batch header."
//! - `relay::datagram`: "A decode never accepts trailing bytes after a fixed-size datagram, an empty packet, or an
//!   unknown type", and `encode`: "nothing is returned for a datagram the decoder would refuse".
//! - `record`: "[`Record::parse`] accepts exactly what [`sign`] produces (no trailing bytes, no unknown tag, no
//!   over-long list); [`Record::verify`] is the only way a record counts as authentic, and it checks both the key to
//!   node id binding and the signature. Nothing here allocates or panics."
//! - `ticket`: "[`Ticket::parse`] accepts exactly what [`Ticket::encode`] writes (no trailing bytes, no reserved bit,
//!   no unknown version); the text form round-trips", read back "in either case".
//! - `local`: "[`Beacon::parse`] accepts exactly what [`sign`] writes; a beacon that does not verify is never returned
//!   as a candidate."
//! - `relay::sleep`: `Notice::parse` refuses "anything [`sign`] would not produce".
//!
//! "Accepts exactly what the encoder produces" is checked as: whatever a decoder accepts, the encoder given the
//! decoded value writes back byte for byte (mangled valid encodings reach the deep paths of each decoder). The crate
//! root says the crate "never panics on any input", so every decoder is fed those bytes too.

use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr};

use ephyra::prelude::*;
use ephyra::check_generator;
use pinc_connect::carrier::frame::MAX_NOTICE_LEN;
use pinc_connect::carrier::{
    BATCH_MAX_BYTES, BATCH_MAX_FRAMES, BatchBuilder, DnsAnswer, Frame, MAX_FRAME_LEN, MAX_PACKET_LEN, Offer,
};
use pinc_connect::local::{self, Beacon};
use pinc_connect::record::{self, MAX_RECORD_LEN, Reach, Record, RecordFields};
use pinc_connect::relay::datagram::{Datagram, MAX_TUNNEL_DATAGRAM};
use pinc_connect::relay::sleep::{self, Notice};
use pinc_connect::ticket::{self, Ticket};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};
use pinc_pbt::mostly_valid;

const ALGS: [IdentityAlg; 4] = [IdentityAlg::Ed25519, IdentityAlg::EcdsaP256, IdentityAlg::MlDsa65, IdentityAlg::Hybrid];

fn byte() -> ephyra::BoxGen<u8> {
    gens::frequency(vec![(4, gens::int(0u8..=255).boxed()), (1, gens::pick_from(vec![0u8, 0x7f, 0x80, 0xff]).boxed())])
        .boxed()
}

/// Bytes of a length in `lo..=hi`, the two ends drawn often.
fn sized(lo: usize, hi: usize) -> ephyra::BoxGen<Vec<u8>> {
    gens::frequency(vec![
        (4, gens::vec(byte()).len(lo..=hi.min(lo + 64)).boxed()),
        (1, gens::vec(byte()).len(lo..=hi).boxed()),
        (1, gens::vec(byte()).len(hi..=hi).boxed()),
        (1, gens::vec(byte()).len(lo..=lo).boxed()),
    ])
    .boxed()
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Nid(#[ephyra(gen = gens::int(0usize..=3))] usize, #[ephyra(gen = gens::vec(byte()).len(32..=32))] Vec<u8>);

impl Nid {
    fn id(&self) -> NodeId {
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&self.1);
        NodeId { alg: ALGS[self.0 % 4], bytes }
    }
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Addr {
    V4(#[ephyra(gen = gens::vec(byte()).len(4..=4))] Vec<u8>, #[ephyra(gen = gens::edges(0u16..=u16::MAX))] u16),
    V6(#[ephyra(gen = gens::vec(byte()).len(16..=16))] Vec<u8>, #[ephyra(gen = gens::int(0u16..=u16::MAX))] u16),
}

impl Addr {
    fn addr(&self) -> SocketAddr {
        match self {
            Self::V4(o, p) => SocketAddr::new(Ipv4Addr::new(o[0], o[1], o[2], o[3]).into(), *p),
            Self::V6(o, p) => {
                let mut b = [0u8; 16];
                b.copy_from_slice(o);
                SocketAddr::new(Ipv6Addr::from(b).into(), *p)
            },
        }
    }
}

fn packet() -> ephyra::BoxGen<Vec<u8>> {
    sized(1, MAX_PACKET_LEN)
}

fn alias() -> ephyra::BoxGen<u8> {
    gens::frequency(vec![(3, gens::int(0u8..=31).boxed()), (1, gens::pick_from(vec![0u8, 31]).boxed())]).boxed()
}

/// A carrier frame other than a batch, every field in its valid range.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum FSpec {
    Ping,
    Pong,
    Send(Nid, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    Recv(Nid, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    SendNew(Nid, #[ephyra(gen = alias())] u8, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    SendAlias(#[ephyra(gen = alias())] u8, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    RecvNew(Nid, #[ephyra(gen = alias())] u8, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    RecvAlias(#[ephyra(gen = alias())] u8, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    Publish(#[ephyra(gen = sized(1, MAX_RECORD_LEN))] Vec<u8>),
    SelfSend(#[ephyra(gen = packet())] Vec<u8>),
    SelfRecv(#[ephyra(gen = packet())] Vec<u8>),
    DnsQuery(Nid),
    DnsReply(Nid, #[ephyra(gen = gens::int(0u8..=2))] u8, #[ephyra(gen = sized(1, MAX_RECORD_LEN))] Vec<u8>),
    Forward(Nid, Nid, #[ephyra(gen = byte())] u8, #[ephyra(gen = packet())] Vec<u8>),
    Sync(#[ephyra(gen = sized(1, MAX_RECORD_LEN))] Vec<u8>),
    Sleep(#[ephyra(gen = sized(1, MAX_NOTICE_LEN))] Vec<u8>),
}

fn answer(status: u8, body: &[u8]) -> DnsAnswer<'_> {
    match status {
        0 => DnsAnswer::Absent,
        1 => DnsAnswer::Record(body),
        _ => DnsAnswer::TooLarge,
    }
}

impl FSpec {
    fn frame(&self) -> Frame<'_> {
        match self {
            Self::Ping => Frame::Ping,
            Self::Pong => Frame::Pong,
            Self::Send(d, flag, p) => Frame::Send { dst: d.id(), flag: *flag, packet: p },
            Self::Recv(s, flag, p) => Frame::Recv { src: s.id(), flag: *flag, packet: p },
            Self::SendNew(d, alias, flag, p) => Frame::SendNew { dst: d.id(), alias: *alias, flag: *flag, packet: p },
            Self::SendAlias(alias, flag, p) => Frame::SendAlias { alias: *alias, flag: *flag, packet: p },
            Self::RecvNew(s, alias, flag, p) => Frame::RecvNew { src: s.id(), alias: *alias, flag: *flag, packet: p },
            Self::RecvAlias(alias, flag, p) => Frame::RecvAlias { alias: *alias, flag: *flag, packet: p },
            Self::Publish(r) => Frame::Publish { record: r },
            Self::SelfSend(p) => Frame::SelfSend { packet: p },
            Self::SelfRecv(p) => Frame::SelfRecv { packet: p },
            Self::DnsQuery(p) => Frame::DnsQuery { peer: p.id() },
            Self::DnsReply(p, status, r) => Frame::DnsReply { peer: p.id(), answer: answer(*status, r) },
            Self::Forward(s, d, flag, p) => Frame::Forward { src: s.id(), dst: d.id(), flag: *flag, packet: p },
            Self::Sync(r) => Frame::Sync { record: r },
            Self::Sleep(n) => Frame::Sleep { notice: n },
        }
    }
}

fn enc(f: &Frame<'_>) -> Vec<u8> {
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = f.encode(&mut b).expect("a valid frame encodes");
    b.truncate(n);
    b
}

#[ephyra::test(gen = ephyra::any::<FSpec>(), tests = 4000)]
fn frame_decode_inverts_encode(spec: FSpec) {
    let f = spec.frame();
    let bytes = enc(&f);
    assert_eq!(Frame::decode(&bytes), Ok(f), "decode of the encoding");
    let mut exact = vec![0u8; bytes.len()];
    assert_eq!(f.encode(&mut exact), Ok(bytes.len()), "encode into a buffer of exactly its length");
    let mut short = vec![0u8; bytes.len() - 1];
    assert!(f.encode(&mut short).is_err(), "encode into a buffer one byte short succeeded");
}

/// Batches built by the builder, the record bytes the carrier sends: the frames in order, as the builder grouped
/// them, each group one record. The builder's rules are the model: a frame it refuses starts the next group, and a
/// long-header frame goes alone.
fn records_of(specs: &[FSpec]) -> Vec<(Vec<u8>, Vec<usize>)> {
    let mut out = Vec::new();
    let mut buf = vec![0u8; MAX_FRAME_LEN];
    let mut b = BatchBuilder::new(&mut buf);
    let mut group: Vec<usize> = Vec::new();
    let mut used = 0usize;
    for (i, s) in specs.iter().enumerate() {
        let f = s.frame();
        let n = enc(&f).len();
        let long = f.is_long_header();
        let want_added = !long && group.len() < BATCH_MAX_FRAMES && used + n <= BATCH_MAX_BYTES;
        let got = b.offer(&f).expect("a valid frame is never an error with a full-size buffer");
        assert_eq!(got == Offer::Added, want_added, "offer of frame {i} ({n} bytes, long header {long}) with {} frames, {used} bytes held", group.len());
        if got == Offer::Added {
            group.push(i);
            used += n;
            continue;
        }
        if let Some(rec) = b.finish().expect("finish") {
            out.push((rec.to_vec(), std::mem::take(&mut group)));
        }
        used = 0;
        b = BatchBuilder::new(&mut buf);
        if long {
            out.push((enc(&f), vec![i]));
        } else {
            assert_eq!(b.offer(&f), Ok(Offer::Added), "an empty batch refused frame {i}");
            group.push(i);
            used = n;
        }
    }
    if let Some(rec) = b.finish().expect("finish") {
        out.push((rec.to_vec(), group));
    }
    out
}

#[ephyra::test(gen = gens::vec(ephyra::any::<FSpec>()).len(0..=90), tests = 600)]
fn batches_hold_the_frames_in_order_within_the_limits(specs: Vec<FSpec>) {
    let mut seen = Vec::new();
    for (rec, group) in records_of(&specs) {
        let f = Frame::decode(&rec).expect("a built record decodes");
        assert_eq!(enc(&f), rec, "a built record is canonical");
        match f {
            Frame::Batch(batch) => {
                assert!(group.len() >= 2, "a batch of {} frames", group.len());
                assert!(batch.len() <= BATCH_MAX_FRAMES);
                let inner: Vec<Frame<'_>> = batch.frames().collect();
                assert_eq!(inner.len(), group.len(), "the batch holds the frames offered");
                let total: usize = inner.iter().map(|f| enc(f).len()).sum();
                assert!(total <= BATCH_MAX_BYTES, "a batch of {total} bytes");
                for (f, i) in inner.iter().zip(&group) {
                    assert!(!f.is_long_header(), "a long-header packet was batched");
                    assert_eq!(*f, specs[*i].frame(), "frame {i} came out of the batch changed");
                }
            },
            f => {
                assert_eq!(group.len(), 1, "a single record for {} frames", group.len());
                assert_eq!(f, specs[group[0]].frame(), "a lone frame came out changed");
            },
        }
        seen.extend(group);
    }
    assert_eq!(seen, (0..specs.len()).collect::<Vec<_>>(), "every frame went out once, in order");
}

fn frame_or_batch_bytes(g: &mut Source) -> Vec<u8> {
    if g.bool_with(0.3) {
        let specs: Vec<FSpec> = g.draw(&gens::vec(ephyra::any::<FSpec>()).len(2..=8));
        if let Some((rec, _)) = records_of(&specs).into_iter().next() {
            return rec;
        }
    }
    let spec: FSpec = g.draw(&ephyra::any::<FSpec>());
    enc(&spec.frame())
}

#[ephyra::test(gen = mostly_valid(frame_or_batch_bytes), tests = 20_000)]
fn frame_decode_accepts_only_what_encode_writes(bytes: Vec<u8>) {
    let Ok(f) = Frame::decode(&bytes) else { return };
    assert_eq!(enc(&f), bytes, "decode accepted bytes that encode does not write for {f:?}");
    if let Frame::Batch(b) = f {
        assert_eq!(b.frames().count(), b.len(), "a decoded batch yields fewer frames than it counts");
        for inner in b.frames() {
            assert!(!matches!(inner, Frame::Batch(_)), "a nested batch was accepted");
        }
    }
}

/// A control datagram, every field in its valid range.
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum DSpec {
    Qad(#[ephyra(gen = gens::vec(byte()).len(8..=8))] Vec<u8>),
    Qadr(#[ephyra(gen = gens::vec(byte()).len(8..=8))] Vec<u8>, Addr),
    DnsQuery(Nid),
    DnsReply(Nid, #[ephyra(gen = gens::int(0u8..=2))] u8, #[ephyra(gen = sized(1, MAX_RECORD_LEN))] Vec<u8>),
    Sleep(#[ephyra(gen = sized(1, MAX_NOTICE_LEN))] Vec<u8>),
    Spl(Nid, #[ephyra(gen = byte())] u8, #[ephyra(gen = sized(1, MAX_TUNNEL_DATAGRAM - 35))] Vec<u8>),
    Spu(Nid, #[ephyra(gen = byte())] u8, #[ephyra(gen = sized(1, MAX_TUNNEL_DATAGRAM - 35))] Vec<u8>),
}

impl DSpec {
    fn datagram(&self) -> Datagram<'_> {
        let nonce = |v: &[u8]| <[u8; 8]>::try_from(v).unwrap_or([0; 8]);
        match self {
            Self::Qad(n) => Datagram::Qad { nonce: nonce(n) },
            Self::Qadr(n, a) => Datagram::Qadr { nonce: nonce(n), addr: a.addr() },
            Self::DnsQuery(p) => Datagram::DnsQuery { peer: p.id() },
            Self::DnsReply(p, s, r) => Datagram::DnsReply { peer: p.id(), answer: answer(*s, r) },
            Self::Sleep(n) => Datagram::Sleep { notice: n },
            Self::Spl(s, flag, p) => Datagram::Spl { src: s.id(), flag: *flag, packet: p },
            Self::Spu(d, flag, p) => Datagram::Spu { dst: d.id(), flag: *flag, packet: p },
        }
    }
}

fn denc(d: &Datagram<'_>) -> Vec<u8> {
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = d.encode(&mut b).expect("a valid datagram encodes");
    b.truncate(n);
    b
}

#[ephyra::test(gen = ephyra::any::<DSpec>(), tests = 4000)]
fn datagram_decode_inverts_encode(spec: DSpec) {
    let d = spec.datagram();
    let bytes = denc(&d);
    assert_eq!(Datagram::decode(&bytes), Ok(d));
    let mut short = vec![0u8; bytes.len() - 1];
    assert!(d.encode(&mut short).is_err(), "encode into a buffer one byte short succeeded");
}

#[ephyra::test(gen = mostly_valid(|g: &mut Source| denc(&g.draw(&ephyra::any::<DSpec>()).datagram())), tests = 20_000)]
fn datagram_decode_accepts_only_what_encode_writes(bytes: Vec<u8>) {
    let Ok(d) = Datagram::decode(&bytes) else { return };
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = d.encode(&mut b);
    assert!(n.is_ok(), "a decoded datagram does not encode: {d:?}: {n:?}");
    assert_eq!(b.get(..n.unwrap_or(0)), Some(&bytes[..]), "decode accepted bytes that encode does not write");
}

fn keypair(alg: usize, tag: u8) -> Keypair {
    let alg = ALGS[alg % 4];
    Keypair::from_seed(alg, &vec![tag + 1; alg.seed_len()]).expect("a seed of the algorithm's length")
}

/// The algorithm of a signer: post-quantum keys are slow to make and sign with, so they are drawn rarely.
fn alg_index() -> ephyra::BoxGen<usize> {
    gens::frequency(vec![(8, gens::constant(0usize).boxed()), (3, gens::constant(1usize).boxed()), (1, gens::int(2usize..=3).boxed())])
        .boxed()
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct RecSpec {
    #[ephyra(gen = alg_index())]
    alg: usize,
    #[ephyra(gen = gens::int(0u8..=3))]
    key: u8,
    home: Nid,
    #[ephyra(gen = gens::frequency(vec![(1, gens::edges(0u64..=u64::MAX).boxed()), (2, gens::int(0u64..=u64::MAX).boxed())]))]
    seq: u64,
    #[ephyra(gen = gens::int(1u8..=5))]
    reach: u8,
    #[ephyra(gen = gens::vec(ephyra::any::<Addr>()).len(0..=record::MAX_ADDRS))]
    addrs: Vec<Addr>,
    #[ephyra(gen = sized(0, record::MAX_HINT_LEN))]
    hints: Vec<u8>,
}

fn reach(tag: u8) -> Reach {
    match tag {
        1 => Reach::Public,
        2 => Reach::PortMapped,
        3 => Reach::Nat,
        4 => Reach::Cgnat,
        _ => Reach::UdpBlocked,
    }
}

impl RecSpec {
    fn sign(&self) -> (Keypair, Vec<u8>) {
        let kp = keypair(self.alg, self.key);
        let addrs: Vec<SocketAddr> = self.addrs.iter().map(Addr::addr).collect();
        let fields = RecordFields { home: self.home.id(), seq: self.seq, reach: reach(self.reach), addrs: &addrs, hints: &self.hints };
        let mut out = vec![0u8; MAX_RECORD_LEN];
        let n = record::sign(&kp, &fields, &mut out).expect("a valid record signs");
        out.truncate(n);
        (kp, out)
    }
}

/// The bytes [`record::prepare`] and [`record::finish`] write for a parsed record, with the key and signature the
/// layout puts last: the canonical encoding of what was parsed.
fn record_again(r: &Record<'_>, bytes: &[u8]) -> Vec<u8> {
    let (pk_len, sig_len) = (r.node.alg.public_key_len(), r.node.alg.signature_len());
    let signed = bytes.len() - sig_len;
    let pk = &bytes[signed - pk_len..signed];
    let addrs: Vec<SocketAddr> = r.addrs().collect();
    let fields = RecordFields { home: r.home, seq: r.seq, reach: r.reach, addrs: &addrs, hints: r.hints };
    let mut out = vec![0u8; MAX_RECORD_LEN];
    let at = record::prepare(&r.node, pk, &fields, &mut out).expect("a parsed record prepares");
    let n = record::finish(&mut out, at, &bytes[signed..]).expect("a parsed record finishes");
    out.truncate(n);
    out
}

#[ephyra::test(gen = (ephyra::any::<RecSpec>(), gens::int(0usize..=usize::MAX), gens::int(0u8..=7)), tests = 600)]
fn a_record_verifies_as_signed_and_no_changed_bit_verifies(case: (RecSpec, usize, u8)) {
    let (spec, at, bit) = case;
    let (kp, bytes) = spec.sign();
    let r = Record::parse_verified(&bytes);
    assert!(r.is_ok(), "a signed record is refused: {r:?}");
    let Ok(r) = r else { return };
    assert_eq!(r.node, kp.node_id());
    assert_eq!((r.home, r.seq, r.reach, r.hints), (spec.home.id(), spec.seq, reach(spec.reach), &spec.hints[..]));
    assert_eq!(r.addrs().collect::<Vec<_>>(), spec.addrs.iter().map(Addr::addr).collect::<Vec<_>>());
    assert_eq!(record_again(&r, &bytes), bytes, "the parsed record does not write back");
    let mut bad = bytes.clone();
    let i = at % bad.len();
    bad[i] ^= 1 << bit;
    assert!(Record::parse_verified(&bad).is_err(), "a record with bit {bit} of byte {i} flipped still verifies");
}

fn record_bytes(g: &mut Source) -> Vec<u8> {
    g.draw(&ephyra::any::<RecSpec>()).sign().1
}

#[ephyra::test(gen = mostly_valid(record_bytes), tests = 3000)]
fn record_parse_accepts_only_what_sign_writes(bytes: Vec<u8>) {
    let Ok(r) = Record::parse(&bytes) else { return };
    assert_eq!(record_again(&r, &bytes), bytes, "parse accepted bytes that prepare and finish do not write");
    let _ = r.verify();
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct TicketSpec {
    node: Nid,
    home: Option<Nid>,
    #[ephyra(gen = gens::vec(ephyra::any::<Addr>()).len(0..=ticket::MAX_ADDRS))]
    addrs: Vec<Addr>,
}

impl TicketSpec {
    fn ticket(&self) -> Ticket {
        let mut t = Ticket::new(self.node.id());
        if let Some(h) = &self.home {
            t = t.with_home(h.id());
        }
        for a in &self.addrs {
            t = t.with_addr(a.addr()).expect("at most four addresses");
        }
        t
    }
}

fn tenc(t: &Ticket) -> Vec<u8> {
    let mut b = [0u8; ticket::MAX_LEN];
    let n = t.encode(&mut b).expect("a ticket encodes");
    b[..n].to_vec()
}

fn ttext(t: &Ticket) -> Vec<u8> {
    let mut b = [0u8; ticket::MAX_TEXT];
    let n = t.to_text(&mut b).expect("a ticket fits its longest text");
    b[..n].to_vec()
}

#[ephyra::test(gen = ephyra::any::<TicketSpec>(), tests = 4000)]
fn a_ticket_round_trips_in_binary_and_in_text_of_either_case(spec: TicketSpec) {
    let t = spec.ticket();
    let bin = tenc(&t);
    assert_eq!(Ticket::parse(&bin), Ok(t));
    let text = ttext(&t);
    assert!(text.iter().all(|c| c.is_ascii_lowercase() || (b'2'..=b'7').contains(c)), "text outside the alphabet");
    assert_eq!(text.len(), (bin.len() * 8).div_ceil(5), "base32 without padding has ceil(8n / 5) symbols");
    assert_eq!(Ticket::from_text(&text), Ok(t));
    assert_eq!(Ticket::from_text(&text.to_ascii_uppercase()), Ok(t), "the upper-case text");
}

#[ephyra::test(gen = mostly_valid(|g: &mut Source| tenc(&g.draw(&ephyra::any::<TicketSpec>()).ticket())), tests = 20_000)]
fn ticket_parse_accepts_only_what_encode_writes(bytes: Vec<u8>) {
    let Ok(t) = Ticket::parse(&bytes) else { return };
    assert_eq!(tenc(&t), bytes, "parse accepted bytes that encode does not write");
}

#[ephyra::test(gen = mostly_valid(|g: &mut Source| ttext(&g.draw(&ephyra::any::<TicketSpec>()).ticket())), tests = 20_000)]
fn ticket_text_accepts_only_what_to_text_writes(text: Vec<u8>) {
    let Ok(t) = Ticket::from_text(&text) else { return };
    assert_eq!(ttext(&t), text.to_ascii_lowercase(), "from_text accepted a text that to_text does not write");
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct BeaconSpec {
    #[ephyra(gen = alg_index())]
    alg: usize,
    #[ephyra(gen = gens::int(0u8..=3))]
    key: u8,
    #[ephyra(gen = gens::edges(0u64..=u64::MAX))]
    seq: u64,
    #[ephyra(gen = gens::vec(ephyra::any::<Addr>()).len(0..=local::MAX_ADDRS))]
    addrs: Vec<Addr>,
    #[ephyra(gen = sized(0, local::MAX_HINT))]
    hint: Vec<u8>,
}

fn beacon_bytes(s: &BeaconSpec) -> Vec<u8> {
    let kp = keypair(s.alg, s.key);
    let addrs: Vec<SocketAddr> = s.addrs.iter().map(Addr::addr).collect();
    let mut out = vec![0u8; local::MAX_LEN];
    let n = local::sign(&kp, s.seq, &addrs, &s.hint, &mut out).expect("a valid beacon signs");
    out.truncate(n);
    out
}

#[ephyra::test(gen = mostly_valid(|g: &mut Source| beacon_bytes(&g.draw(&ephyra::any::<BeaconSpec>()))), tests = 3000)]
fn beacon_parse_accepts_only_what_sign_writes(bytes: Vec<u8>) {
    let Ok(b) = Beacon::parse(&bytes) else { return };
    let (pk_len, sig_len) = (b.node.alg.public_key_len(), b.node.alg.signature_len());
    let signed = bytes.len() - sig_len;
    let addrs: Vec<SocketAddr> = b.addrs().collect();
    let mut out = vec![0u8; local::MAX_LEN];
    let at = local::prepare(&b.node, &bytes[signed - pk_len..signed], b.seq, &addrs, b.hint, &mut out).expect("prepare");
    let n = local::finish(&mut out, at, &bytes[signed..]).expect("finish");
    assert_eq!(&out[..n], &bytes[..], "parse accepted bytes that sign does not write");
    if b.verify().is_ok() {
        assert!(Beacon::parse_verified(&bytes).is_ok());
    }
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct NoticeSpec {
    #[ephyra(gen = alg_index())]
    alg: usize,
    #[ephyra(gen = gens::int(0u8..=3))]
    key: u8,
    relay: Nid,
    #[ephyra(gen = gens::edges(0u64..=u64::MAX))]
    ts: u64,
}

#[ephyra::test(gen = (ephyra::any::<NoticeSpec>(), gens::int(0usize..=usize::MAX), gens::int(0u8..=7)), tests = 600)]
fn a_notice_verifies_for_its_relay_only_and_no_changed_bit_verifies(case: (NoticeSpec, usize, u8)) {
    let (s, at, bit) = case;
    let kp = keypair(s.alg, s.key);
    let relay = s.relay.id();
    let mut out = vec![0u8; sleep::MAX_LEN];
    let n = sleep::sign(&kp, &relay, s.ts, &mut out).expect("a notice signs");
    out.truncate(n);
    let p = Notice::parse(&out);
    assert!(p.is_ok(), "a signed notice does not parse: {p:?}");
    let Ok(p) = p else { return };
    assert_eq!((p.node, p.ts_ms), (kp.node_id(), s.ts));
    assert!(p.verify(&relay).is_ok(), "a notice does not verify for its relay");
    let mut other = relay;
    other.bytes[0] ^= 1;
    assert!(p.verify(&other).is_err(), "a notice verifies for another relay");
    let mut bad = out.clone();
    let i = at % bad.len();
    bad[i] ^= 1 << bit;
    assert!(!Notice::parse(&bad).is_ok_and(|q| q.verify(&relay).is_ok()), "a notice with bit {bit} of byte {i} flipped still verifies");
}

/// The frame and datagram generators make only values their encoder takes (their shrinkers are the derived ones).
#[test]
fn the_codec_generators_stay_valid() {
    let frame_ok = |s: &FSpec| {
        let mut b = vec![0u8; MAX_FRAME_LEN];
        s.frame().encode(&mut b).is_ok()
    };
    check_generator(&Config::default().tests(2000), ephyra::any::<FSpec>(), frame_ok).assert_passed();
    let dgram_ok = |s: &DSpec| {
        let mut b = vec![0u8; MAX_FRAME_LEN];
        s.datagram().encode(&mut b).is_ok()
    };
    check_generator(&Config::default().tests(2000), ephyra::any::<DSpec>(), dgram_ok).assert_passed();
    let ticket_ok = |s: &TicketSpec| s.addrs.len() <= ticket::MAX_ADDRS;
    check_generator(&Config::default().tests(2000), ephyra::any::<TicketSpec>(), ticket_ok).assert_passed();
}

/// One message or control frame of a WebSocket stream: a binary message cut into fragments, each control frame
/// sent after `after` fragments of the message it interrupts (RFC 6455 section 5.4 lets control frames sit between
/// fragments).
#[derive(Clone, Debug, ephyra::Arbitrary)]
enum WsOp {
    Message(#[ephyra(gen = gens::vec(ws_len()).len(1..=4))] Vec<usize>, #[ephyra(gen = gens::vec(ws_control()).len(0..=2))] Vec<(usize, u8, usize)>),
}

fn ws_len() -> ephyra::BoxGen<usize> {
    let max = pinc_connect::carrier::ws::MAX_PAYLOAD;
    gens::frequency(vec![
        (6, gens::int(0usize..=200).boxed()),
        (2, gens::pick_from(vec![0usize, 1, 125, 126, 127, 65_535, max - 1, max].into_iter().filter(|n| *n <= max).collect()).boxed()),
        (1, gens::int(0usize..=max).boxed()),
    ])
    .boxed()
}

/// A control frame: (fragments before it, kind 0 ping, 1 pong, 2 close without a code, 3 close with a code, length).
fn ws_control() -> ephyra::BoxGen<(usize, u8, usize)> {
    (gens::int(0usize..=3), gens::int(0u8..=3), gens::frequency(vec![(3, gens::int(0usize..=10).boxed()), (1, gens::int(0usize..=125).boxed())])).boxed()
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Seen {
    Data(Vec<u8>),
    Ping(Vec<u8>),
    Pong(Vec<u8>),
    Close(Option<u16>),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct WsCase {
    client: bool,
    #[ephyra(gen = gens::vec(ephyra::any::<WsOp>()).len(0..=6))]
    ops: Vec<WsOp>,
    #[ephyra(gen = gens::vec(gens::frequency(vec![(3, gens::int(1usize..=8).boxed()), (2, gens::int(1usize..=300).boxed()), (1, gens::int(1usize..=20_000).boxed())])).len(0..=40))]
    cuts: Vec<usize>,
    #[ephyra(gen = gens::int(0u32..=u32::MAX))]
    key: u32,
}

/// The stream the sender writes for `case` and the frames the receiver must report, in order.
fn ws_stream(case: &WsCase) -> (Vec<u8>, Vec<Seen>) {
    use pinc_connect::carrier::ws::{self, MAX_HEADER, Opcode};
    let mut stream = Vec::new();
    let mut want = Vec::new();
    let mut n = 0u32;
    let mut put = |stream: &mut Vec<u8>, op: Opcode, payload: &[u8], fin: bool| {
        n = n.wrapping_add(1);
        let mask = case.client.then(|| (case.key ^ n.wrapping_mul(0x9e37_79b9)).to_be_bytes());
        let mut out = vec![0u8; payload.len() + MAX_HEADER];
        let len = ws::encode(op, payload, mask, &mut out).expect("a valid frame encodes");
        if !fin {
            out[0] &= 0x7f;
        }
        stream.extend_from_slice(&out[..len]);
    };
    for WsOp::Message(frags, controls) in &case.ops {
        for (i, len) in frags.iter().enumerate() {
            for &(after, kind, clen) in controls.iter().filter(|c| c.0 == i) {
                let body: Vec<u8> = (0..clen).map(|j| (j as u8) ^ kind).collect();
                match kind {
                    0 => (put(&mut stream, Opcode::Ping, &body, true), want.push(Seen::Ping(body))),
                    1 => (put(&mut stream, Opcode::Pong, &body, true), want.push(Seen::Pong(body))),
                    2 => (put(&mut stream, Opcode::Close, &[], true), want.push(Seen::Close(None))),
                    _ => {
                        let code = 1000 + (after as u16) * 7 + clen as u16;
                        let mut b = code.to_be_bytes().to_vec();
                        b.extend(body.iter().take(123));
                        (put(&mut stream, Opcode::Close, &b, true), want.push(Seen::Close(Some(code))))
                    },
                };
            }
            let body: Vec<u8> = (0..*len).map(|j| (j as u8).wrapping_mul(31) ^ (i as u8)).collect();
            let op = if i == 0 { Opcode::Binary } else { Opcode::Continuation };
            put(&mut stream, op, &body, i + 1 == frags.len());
            want.push(Seen::Data(body));
        }
    }
    (stream, want)
}

/// Feed `stream` to a decoder in pieces of the `cuts` sizes, as a host reading a socket does: the frames reported,
/// the error that closed the stream if any, and the bytes left waiting for more.
fn ws_feed(
    stream: &[u8],
    cuts: &[usize],
    client: bool,
) -> (Vec<Seen>, Option<pinc_connect::carrier::ws::WsError>, usize) {
    use pinc_connect::carrier::ws::{Decoder, Role, WsFrame};
    let mut dec = Decoder::new(if client { Role::Client } else { Role::Server });
    let mut buf: Vec<u8> = Vec::new();
    let mut got = Vec::new();
    let mut at = 0usize;
    let mut cuts = cuts.iter().copied().chain(std::iter::repeat(usize::MAX));
    while at < stream.len() {
        let take = cuts.next().unwrap_or(usize::MAX).min(stream.len() - at);
        buf.extend_from_slice(&stream[at..at + take]);
        at += take;
        // Each round removes at least the two header bytes of a frame, so the loop ends within the stream.
        for _ in 0..=stream.len() / 2 {
            match dec.decode(&mut buf) {
                Err(e) => return (got, Some(e), buf.len()),
                Ok(None) => break,
                Ok(Some((f, used))) => {
                    got.push(match f {
                        WsFrame::Data(p) => Seen::Data(p.to_vec()),
                        WsFrame::Ping(p) => Seen::Ping(p.to_vec()),
                        WsFrame::Pong(p) => Seen::Pong(p.to_vec()),
                        WsFrame::Close(c) => Seen::Close(c),
                    });
                    assert!(used >= 2 && used <= buf.len(), "a frame of {used} bytes in a buffer of {}", buf.len());
                    buf.drain(..used);
                },
            }
        }
    }
    (got, None, buf.len())
}

#[ephyra::test(gen = ephyra::any::<WsCase>(), tests = 1500)]
fn ws_decoder_reports_every_frame_however_the_stream_is_cut(case: WsCase) {
    let (stream, want) = ws_stream(&case);
    let (got, err, left) = ws_feed(&stream, &case.cuts, case.client);
    assert_eq!(err, None, "a valid stream refused after {} frames", got.len());
    assert_eq!(left, 0, "bytes left undecoded");
    assert_eq!(got, want);
}

/// A mangled stream (what any peer can send) decodes to the same frames and the same error, read whole or in pieces:
/// the decoder's answer depends on the bytes, never on how they arrived.
#[ephyra::test(gen = (ephyra::any::<WsCase>(), gens::vec((gens::int(0usize..=usize::MAX), gens::int(0u8..=4), byte())).len(1..=4)), tests = 3000)]
fn ws_decoder_answers_the_same_for_a_mangled_stream_however_it_is_cut(input: (WsCase, Vec<(usize, u8, u8)>)) {
    let (case, edits) = input;
    let (mut stream, _) = ws_stream(&case);
    for (at, kind, v) in edits {
        let i = if stream.is_empty() { 0 } else { at % stream.len() };
        match kind {
            0 if !stream.is_empty() => stream[i] ^= 1 << (v % 8),
            1 if !stream.is_empty() => stream[i] = v,
            2 => stream.truncate(i),
            3 => stream.insert(i, v),
            _ if !stream.is_empty() => {
                stream.remove(i);
            },
            _ => {},
        }
    }
    let whole = ws_feed(&stream, &[], case.client);
    let cut = ws_feed(&stream, &case.cuts, case.client);
    assert_eq!(cut.0, whole.0, "the frames differ when the stream is cut");
    assert_eq!(cut.1, whole.1, "the error differs when the stream is cut");
}
