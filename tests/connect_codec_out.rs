//! The writer of the wire format trace of `pinc-connect` (`trace_connect_codec`): the tags of the errors, the JSON of a
//! byte sequence and the recorder that runs one call of the real decoder or encoder and appends its event.
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
    clippy::type_complexity,
    unreachable_pub
)]

use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use crate::connect_common::node_bytes;
use pinc_connect::carrier::frame::{DnsAnswer, Frame, FrameError, MAX_FRAME_LEN};
use pinc_connect::client::punch;
use pinc_connect::local::{self, Beacon, BeaconError};
use pinc_connect::record::{self, Record, RecordError, RecordFields};
use pinc_connect::relay::datagram::{Datagram, DatagramError};
use pinc_connect::relay::sleep::{self, Notice, SleepError};
use pinc_connect::ticket::{Ticket, TicketError};
use pinc_crypto::NodeId;
use pinc_wire::WireError;

pub fn wtag(e: WireError) -> String {
    match e {
        WireError::Truncated { needed } => format!("trunc:{needed}"),
        WireError::BufferTooSmall { needed } => format!("small:{needed}"),
        WireError::VarintTooLong => "vlong".into(),
        WireError::VarintOverflow => "vover".into(),
        WireError::VarintNonMinimal => "vnonmin".into(),
        WireError::NonCanonical(s) => format!("noncanon:{s}"),
        WireError::Unexpected(s) => format!("unexpected:{s}"),
        WireError::DepthExceeded => "depth".into(),
    }
}

pub fn ftag(e: FrameError) -> String {
    match e {
        FrameError::Wire(w) => wtag(w),
        FrameError::UnknownType(t) => format!("type:{t}"),
        FrameError::Trailing => "trailing".into(),
        FrameError::Alias(a) => format!("alias:{a}"),
        FrameError::PacketSize => "packet".into(),
        FrameError::BodySize => "body".into(),
        FrameError::Status(s) => format!("status:{s}"),
        FrameError::Batch(w) => format!("batch:{w}"),
        FrameError::NoRoom => "noroom".into(),
    }
}

pub fn rtag(e: RecordError) -> String {
    match e {
        RecordError::Wire(w) => wtag(w),
        RecordError::Magic => "magic".into(),
        RecordError::Reach(t) => format!("reach:{t}"),
        RecordError::AddrTag(t) => format!("addrtag:{t}"),
        RecordError::TooManyAddrs => "toomany".into(),
        RecordError::HintsTooLong => "hints".into(),
        RecordError::Trailing => "trailing".into(),
        RecordError::Signature(_) => "sig".into(),
    }
}

pub fn dtag(e: DatagramError) -> String {
    match e {
        DatagramError::UnknownType(t) => format!("type:{t}"),
        DatagramError::Frame(f) => format!("frame/{}", ftag(f)),
        DatagramError::Addr(r) => format!("addr/{}", rtag(r)),
        DatagramError::Trailing => "trailing".into(),
        DatagramError::PacketSize => "packet".into(),
    }
}

pub fn ttag(e: TicketError) -> String {
    match e {
        TicketError::Version(v) => format!("version:{v}"),
        TicketError::Flags(f) => format!("flags:{f}"),
        TicketError::Wire(w) => wtag(w),
        TicketError::Addr(r) => format!("taddr/{}", rtag(r)),
        TicketError::Text => "text".into(),
        TicketError::TooManyAddrs => "toomany".into(),
    }
}

pub fn btag(e: BeaconError) -> String {
    match e {
        BeaconError::Wire(w) => wtag(w),
        BeaconError::Magic => "magic".into(),
        BeaconError::Addr(r) => format!("baddr/{}", rtag(r)),
        BeaconError::TooLong => "toolong".into(),
        BeaconError::Trailing => "trailing".into(),
        BeaconError::Signature => "sig".into(),
    }
}

pub fn stag(e: SleepError) -> String {
    match e {
        SleepError::Wire(w) => wtag(w),
        SleepError::Signature(_) => "sig".into(),
        SleepError::Skew => "skew".into(),
        SleepError::UnknownNode => "unknown".into(),
        SleepError::WrongSender => "sender".into(),
    }
}

pub fn jb(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 4 + 2);
    s.push('[');
    for (i, x) in b.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

pub fn jbs(bs: &[Vec<u8>]) -> String {
    format!("[{}]", bs.iter().map(|b| jb(b)).collect::<Vec<_>>().join(","))
}

pub fn addr_bytes(a: &SocketAddr) -> Vec<u8> {
    let mut v = Vec::new();
    match a.ip() {
        IpAddr::V4(ip) => {
            v.push(4);
            v.extend_from_slice(&ip.octets());
        }
        IpAddr::V6(ip) => {
            v.push(6);
            v.extend_from_slice(&ip.octets());
        }
    }
    v.extend_from_slice(&a.port().to_be_bytes());
    v
}

pub fn enc(f: &Frame<'_>) -> Vec<u8> {
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = f.encode(&mut b).unwrap();
    b.truncate(n);
    b
}

pub fn answer_parts(peer: &NodeId, a: &DnsAnswer<'_>) -> Vec<Vec<u8>> {
    let mut v = vec![node_bytes(peer).to_vec()];
    match a {
        DnsAnswer::Absent => v.push(vec![0]),
        DnsAnswer::Record(r) => {
            v.push(vec![1]);
            v.push(r.to_vec());
        }
        DnsAnswer::TooLarge => v.push(vec![2]),
    }
    v
}

/// The type byte and the fields of a frame, as byte sequences.
pub fn parts(f: &Frame<'_>) -> (u8, Vec<Vec<u8>>) {
    let n = |x: &NodeId| node_bytes(x).to_vec();
    let ty = f.kind();
    let fs = match *f {
        Frame::Send { dst, flag, packet } => vec![n(&dst), vec![flag], packet.to_vec()],
        Frame::Recv { src, flag, packet } => vec![n(&src), vec![flag], packet.to_vec()],
        Frame::SendNew {
            dst,
            alias,
            flag,
            packet,
        } => vec![n(&dst), vec![alias], vec![flag], packet.to_vec()],
        Frame::RecvNew {
            src,
            alias,
            flag,
            packet,
        } => vec![n(&src), vec![alias], vec![flag], packet.to_vec()],
        Frame::SendAlias { alias, flag, packet } | Frame::RecvAlias { alias, flag, packet } => {
            vec![vec![alias], vec![flag], packet.to_vec()]
        }
        Frame::Publish { record } | Frame::Sync { record } => vec![record.to_vec()],
        Frame::Ping | Frame::Pong => vec![],
        Frame::SelfSend { packet } | Frame::SelfRecv { packet } => vec![packet.to_vec()],
        Frame::Batch(b) => b.frames().map(|m| enc(&m)).collect(),
        Frame::DnsQuery { peer } => vec![n(&peer)],
        Frame::DnsReply { peer, answer } => answer_parts(&peer, &answer),
        Frame::Forward { src, dst, flag, packet } => vec![n(&src), n(&dst), vec![flag], packet.to_vec()],
        Frame::Sleep { notice } => vec![notice.to_vec()],
    };
    (ty, fs)
}

pub fn dgram_parts(d: &Datagram<'_>) -> (u8, Vec<Vec<u8>>) {
    let n = |x: &NodeId| node_bytes(x).to_vec();
    match *d {
        Datagram::Qad { nonce } => (1, vec![nonce.to_vec()]),
        Datagram::Qadr { nonce, addr } => (2, vec![nonce.to_vec(), addr_bytes(&addr)]),
        Datagram::DnsQuery { peer } => (3, vec![n(&peer)]),
        Datagram::DnsReply { peer, answer } => (4, answer_parts(&peer, &answer)),
        Datagram::Sleep { notice } => (6, vec![notice.to_vec()]),
        Datagram::Spl { src, flag, packet } => (8, vec![n(&src), vec![flag], packet.to_vec()]),
        Datagram::Spu { dst, flag, packet } => (9, vec![n(&dst), vec![flag], packet.to_vec()]),
    }
}

pub struct Out {
    pub lines: Vec<String>,
}

impl Out {
    pub fn fdec(&mut self, b: &[u8]) {
        match Frame::decode(b) {
            Ok(f) => {
                let (ty, fs) = parts(&f);
                assert_eq!(enc(&f), b, "a decoded frame re-encodes to its input");
                self.lines
                    .push(format!(r#"{{"t":"fdec","b":{},"ty":{ty},"fs":{}}}"#, jb(b), jbs(&fs)));
            }
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"fdec","b":{},"err":"{}"}}"#, jb(b), ftag(e))),
        }
    }

    pub fn fenc(&mut self, f: &Frame<'_>, cap: usize) {
        let (ty, fs) = parts(f);
        let mut out = vec![0u8; cap];
        match f.encode(&mut out) {
            Ok(n) => self.lines.push(format!(
                r#"{{"t":"fenc","ty":{ty},"fs":{},"cap":{cap},"b":{}}}"#,
                jbs(&fs),
                jb(&out[..n])
            )),
            Err(e) => self.lines.push(format!(
                r#"{{"t":"fenc","ty":{ty},"fs":{},"cap":{cap},"err":"{}"}}"#,
                jbs(&fs),
                ftag(e)
            )),
        }
    }

    pub fn ddec(&mut self, b: &[u8]) {
        match Datagram::decode(b) {
            Ok(d) => {
                let (ty, fs) = dgram_parts(&d);
                let mut out = vec![0u8; b.len() + 8];
                let n = d.encode(&mut out).unwrap();
                assert_eq!(&out[..n], b, "a decoded datagram re-encodes to its input");
                self.lines
                    .push(format!(r#"{{"t":"ddec","b":{},"ty":{ty},"fs":{}}}"#, jb(b), jbs(&fs)));
            }
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"ddec","b":{},"err":"{}"}}"#, jb(b), dtag(e))),
        }
    }

    pub fn denc(&mut self, d: &Datagram<'_>, cap: usize) {
        let (ty, fs) = dgram_parts(d);
        let mut out = vec![0u8; cap];
        match d.encode(&mut out) {
            Ok(n) => self.lines.push(format!(
                r#"{{"t":"denc","ty":{ty},"fs":{},"cap":{cap},"b":{}}}"#,
                jbs(&fs),
                jb(&out[..n])
            )),
            Err(e) => self.lines.push(format!(
                r#"{{"t":"denc","ty":{ty},"fs":{},"cap":{cap},"err":"{}"}}"#,
                jbs(&fs),
                dtag(e)
            )),
        }
    }

    pub fn rdec(&mut self, b: &[u8]) {
        match Record::parse(b) {
            Ok(r) => {
                let addrs: Vec<Vec<u8>> = r.addrs().map(|a| addr_bytes(&a)).collect();
                self.lines.push(format!(
                    r#"{{"t":"rdec","b":{},"node":{},"home":{},"seq":{},"reach":{},"addrs":{},"hints":{}}}"#,
                    jb(b),
                    jb(&node_bytes(&r.node)),
                    jb(&node_bytes(&r.home)),
                    jb(&r.seq.to_be_bytes()),
                    r.reach as u8,
                    jbs(&addrs),
                    jb(r.hints)
                ));
            }
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"rdec","b":{},"err":"{}"}}"#, jb(b), rtag(e))),
        }
    }

    pub fn rprep(&mut self, node: &NodeId, pk: &[u8], f: &RecordFields<'_>, cap: usize) {
        let addrs: Vec<Vec<u8>> = f.addrs.iter().map(addr_bytes).collect();
        let head = format!(
            r#"{{"t":"rprep","node":{},"home":{},"seq":{},"reach":{},"addrs":{},"hints":{},"pk":{},"cap":{cap}"#,
            jb(&node_bytes(node)),
            jb(&node_bytes(&f.home)),
            jb(&f.seq.to_be_bytes()),
            f.reach as u8,
            jbs(&addrs),
            jb(f.hints),
            jb(pk)
        );
        let mut out = vec![0u8; cap];
        match record::prepare(node, pk, f, &mut out) {
            Ok(n) => self.lines.push(format!(r#"{head},"b":{}}}"#, jb(&out[..n]))),
            Err(e) => self.lines.push(format!(r#"{head},"err":"{}"}}"#, rtag(e))),
        }
    }

    pub fn bdec(&mut self, b: &[u8]) {
        match Beacon::parse(b) {
            Ok(r) => {
                let addrs: Vec<Vec<u8>> = r.addrs().map(|a| addr_bytes(&a)).collect();
                self.lines.push(format!(
                    r#"{{"t":"bdec","b":{},"node":{},"seq":{},"addrs":{},"hint":{}}}"#,
                    jb(b),
                    jb(&node_bytes(&r.node)),
                    jb(&r.seq.to_be_bytes()),
                    jbs(&addrs),
                    jb(r.hint)
                ));
            }
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"bdec","b":{},"err":"{}"}}"#, jb(b), btag(e))),
        }
    }

    pub fn bprep(&mut self, node: &NodeId, pk: &[u8], seq: u64, addrs: &[SocketAddr], hint: &[u8], cap: usize) {
        let ab: Vec<Vec<u8>> = addrs.iter().map(addr_bytes).collect();
        let head = format!(
            r#"{{"t":"bprep","node":{},"seq":{},"addrs":{},"hint":{},"pk":{},"cap":{cap}"#,
            jb(&node_bytes(node)),
            jb(&seq.to_be_bytes()),
            jbs(&ab),
            jb(hint),
            jb(pk)
        );
        let mut out = vec![0u8; cap];
        match local::prepare(node, pk, seq, addrs, hint, &mut out) {
            Ok(n) => self.lines.push(format!(r#"{head},"b":{}}}"#, jb(&out[..n]))),
            Err(e) => self.lines.push(format!(r#"{head},"err":"{}"}}"#, btag(e))),
        }
    }

    pub fn sdec(&mut self, b: &[u8]) {
        match Notice::parse(b) {
            Ok(n) => self.lines.push(format!(
                r#"{{"t":"sdec","b":{},"node":{},"ts":{}}}"#,
                jb(b),
                jb(&node_bytes(&n.node)),
                jb(&n.ts_ms.to_be_bytes())
            )),
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"sdec","b":{},"err":"{}"}}"#, jb(b), stag(e))),
        }
    }

    pub fn sprep(&mut self, node: &NodeId, pk: &[u8], ts: u64, cap: usize) {
        let head = format!(
            r#"{{"t":"sprep","node":{},"ts":{},"pk":{},"cap":{cap}"#,
            jb(&node_bytes(node)),
            jb(&ts.to_be_bytes()),
            jb(pk)
        );
        let mut out = vec![0u8; cap];
        match sleep::prepare(node, pk, ts, &mut out) {
            Ok(n) => self.lines.push(format!(r#"{head},"b":{}}}"#, jb(&out[..n]))),
            Err(e) => self.lines.push(format!(r#"{head},"err":"{}"}}"#, stag(e))),
        }
    }

    pub fn smsg(&mut self, relay: &NodeId, node: &NodeId, ts: u64) {
        let m = sleep::message(relay, node, ts).unwrap();
        self.lines.push(format!(
            r#"{{"t":"smsg","relay":{},"node":{},"ts":{},"b":{}}}"#,
            jb(&node_bytes(relay)),
            jb(&node_bytes(node)),
            jb(&ts.to_be_bytes()),
            jb(&m)
        ));
    }

    pub fn tdec(&mut self, b: &[u8]) {
        match Ticket::parse(b) {
            Ok(t) => {
                let addrs: Vec<Vec<u8>> = t.addrs().map(|a| addr_bytes(&a)).collect();
                let home = t.home.map_or_else(Vec::new, |h| node_bytes(&h).to_vec());
                let mut out = [0u8; 200];
                let n = t.encode(&mut out).unwrap();
                assert_eq!(&out[..n], b, "a decoded ticket re-encodes to its input");
                self.lines.push(format!(
                    r#"{{"t":"tdec","b":{},"node":{},"home":{},"addrs":{}}}"#,
                    jb(b),
                    jb(&node_bytes(&t.node)),
                    jb(&home),
                    jbs(&addrs)
                ));
            }
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"tdec","b":{},"err":"{}"}}"#, jb(b), ttag(e))),
        }
    }

    pub fn tenc(&mut self, t: &Ticket, cap: usize) {
        let addrs: Vec<Vec<u8>> = t.addrs().map(|a| addr_bytes(&a)).collect();
        let home = t.home.map_or_else(Vec::new, |h| node_bytes(&h).to_vec());
        let head = format!(
            r#"{{"t":"tenc","node":{},"home":{},"addrs":{},"cap":{cap}"#,
            jb(&node_bytes(&t.node)),
            jb(&home),
            jbs(&addrs)
        );
        let mut out = vec![0u8; cap];
        match t.encode(&mut out) {
            Ok(n) => self.lines.push(format!(r#"{head},"b":{}}}"#, jb(&out[..n]))),
            Err(e) => self.lines.push(format!(r#"{head},"err":"{}"}}"#, ttag(e))),
        }
        let mut text = vec![0u8; cap];
        match t.to_text(&mut text) {
            Ok(n) => self.lines.push(format!(
                r#"{{"t":"ttext","node":{},"home":{},"addrs":{},"cap":{cap},"b":{}}}"#,
                jb(&node_bytes(&t.node)),
                jb(&home),
                jbs(&addrs),
                jb(&text[..n])
            )),
            Err(e) => self.lines.push(format!(
                r#"{{"t":"ttext","node":{},"home":{},"addrs":{},"cap":{cap},"err":"{}"}}"#,
                jb(&node_bytes(&t.node)),
                jb(&home),
                jbs(&addrs),
                ttag(e)
            )),
        }
    }

    pub fn tfrom(&mut self, text: &[u8]) {
        match Ticket::from_text(text) {
            Ok(t) => {
                let mut bin = [0u8; 200];
                let n = t.encode(&mut bin).unwrap();
                self.lines
                    .push(format!(r#"{{"t":"tfrom","s":{},"b":{}}}"#, jb(text), jb(&bin[..n])));
            }
            Err(e) => self
                .lines
                .push(format!(r#"{{"t":"tfrom","s":{},"err":"{}"}}"#, jb(text), ttag(e))),
        }
    }

    pub fn cdec(&mut self, b: &[u8]) {
        let mut out = [SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0); record::MAX_ADDRS];
        match punch::decode(b, &mut out) {
            Some(n) => {
                let a: Vec<Vec<u8>> = out[..n].iter().map(addr_bytes).collect();
                self.lines
                    .push(format!(r#"{{"t":"cdec","b":{},"addrs":{}}}"#, jb(b), jbs(&a)));
            }
            None => self.lines.push(format!(r#"{{"t":"cdec","b":{},"err":"none"}}"#, jb(b))),
        }
    }

    pub fn cenc(&mut self, cs: &[SocketAddr], cap: usize) {
        let a: Vec<Vec<u8>> = cs.iter().map(addr_bytes).collect();
        let mut out = vec![0u8; cap];
        match punch::encode(cs, &mut out) {
            Some(n) => self.lines.push(format!(
                r#"{{"t":"cenc","addrs":{},"cap":{cap},"b":{}}}"#,
                jbs(&a),
                jb(&out[..n])
            )),
            None => self.lines.push(format!(
                r#"{{"t":"cenc","addrs":{},"cap":{cap},"err":"none"}}"#,
                jbs(&a)
            )),
        }
    }
}
