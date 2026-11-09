//! The recording simulation of `trace_handshake.rs`: three responder nodes (two honest, one the attacker's), one dialing
//! node, a client ticket store, a clock, and a line writer.
//!
//! Every step of either machine and of the client store is one `hs` line (see the header of `trace_handshake.rs`).
//! An id stands for one distinct byte string of one kind, so the checkers never see a hash function.
#![allow(clippy::too_many_arguments, clippy::cast_possible_wrap)]

use std::collections::{HashMap, VecDeque};
use std::fmt::Write as _;

use vinc_crypto::{Drbg, IdentityAlg, NodeId, Software};
use vinc_security::message::{Initial, MessageType, PrekeyField, Reject, Reply, ResumeHello, ResumeReply};
use vinc_security::tickets::MAX_EXPORT_ENTRY_LEN;
use vinc_security::{
    AlpnList, ClientTickets, ConnId, CreditRecord, Env, Established, Event, Failure, Initiator, InitiatorParams,
    KeyHandle, KeyRequest, KeyResponse, Output, PrekeyPolicy, Responder, ResponderConfig, ResponderStores, SoftKeys,
    SoftPrekeys,
};

use crate::sec_common::{ALPN, ALPN_B, Caps, PK, Party, T0, party};
use crate::tamper::{Class, Tamper};

/// The ticket store capacity of every responder node (`tk` of the begin line).
pub const TK: usize = 2;
/// The client store capacity (`ck` of the begin line).
pub const CK: usize = 2;
/// The byte lengths the model takes as constants (`LF`, `LS`, `LH` and `LR` of the model); asserted on every message.
pub const LF: usize = 1258;
pub const LS: usize = 106;
pub const LH: usize = 122;
pub const LR: usize = 101;
const NS: u64 = 1_000_000_000;

/// Dense ids for byte strings, one id per (kind, bytes).
#[derive(Default)]
pub struct Ids(HashMap<(u8, Vec<u8>), u32>);

impl Ids {
    pub fn id(&mut self, kind: u8, bytes: &[u8]) -> i64 {
        let next = u32::try_from(self.0.len()).unwrap() + 1;
        i64::from(*self.0.entry((kind, bytes.to_vec())).or_insert(next))
    }
}
const K_E: u8 = 1;
const K_PK: u8 = 2;
const K_TH: u8 = 3;
const K_KEY: u8 = 4;
const K_TID: u8 = 5;
const K_MSG: u8 = 6;
const K_HASH: u8 = 7;

pub fn type_name(ty: u8) -> &'static str {
    match ty {
        1 | 2 => "Init",
        3 => "PRej",
        4 => "Reply",
        5 => "Fin",
        6 => "Hello",
        7 => "RReply",
        8 => "RRej",
        _ => "None",
    }
}

/// How an input reached a machine.
#[derive(Clone)]
pub enum Inp {
    None,
    Exact(Vec<u8>),
    /// The original message and the delivered bytes, which differ in the model's field `fld`.
    Forged {
        base: Vec<u8>,
        bytes: Vec<u8>,
        fld: &'static str,
    },
    /// Bytes that do not parse.
    Malformed(Vec<u8>),
}

impl Inp {
    pub fn bytes(&self) -> &[u8] {
        match self {
            Self::Exact(b) | Self::Malformed(b) | Self::Forged { bytes: b, .. } => b,
            Self::None => &[],
        }
    }
}

pub fn ex(b: &[u8]) -> Inp {
    Inp::Exact(b.to_vec())
}

/// What a machine handed out after a step.
#[derive(Default)]
pub struct Drained {
    pub sends: Vec<Vec<u8>>,
    pub req: Option<(&'static str, Vec<u8>)>,
    pub early: Option<[u8; 32]>,
    pub est: Option<Established>,
    pub rejected: bool,
    pub failed: Option<Failure>,
}

macro_rules! drain {
    ($m:expr) => {{
        let mut d = Drained::default();
        while let Some(o) = $m.poll_output() {
            match o {
                Output::Send { data, .. } => d.sends.push(data.to_vec()),
                Output::Key(KeyRequest::Sign { message, .. }) => {
                    d.req = Some((
                        "sign",
                        message[vinc_security::labels::SIGNATURE_RESPONDER.len()..].to_vec(),
                    ));
                }
                Output::Key(KeyRequest::Decapsulate { .. }) => d.req = Some(("decap", vec![])),
                Output::Event(Event::EarlyKeys(e)) => d.early = Some(*e.secret.expose()),
                Output::Event(Event::ResumeRejected) => d.rejected = true,
                Output::Event(Event::Failed(f)) => d.failed = Some(f),
                Output::Event(Event::Established(e)) => d.est = Some(e),
            }
        }
        d
    }};
}

/// One node: an identity, a provider, a generator and (for a responder) its caches.
pub struct Node {
    pub party: Party,
    pub prov: Caps,
    pub drbg: Drbg,
    pub credit: CreditRecord,
    pub stores: ResponderStores<PK, TK>,
}

impl Node {
    fn new(tag: u8, seed: u8, hw: bool, credit: CreditRecord) -> Self {
        Self {
            party: party(IdentityAlg::Ed25519, tag),
            prov: Caps(Software, hw),
            drbg: Drbg::new(&[seed; 32]),
            credit,
            stores: ResponderStores::default(),
        }
    }
    pub fn node_id(&self) -> NodeId {
        self.party.id.node_id()
    }
}

/// A ticket whose expiry the test tracks, to say when it expires.
struct Exp {
    cli: bool,
    rn: u8,
    tid: [u8; 16],
    at: u64,
    done: bool,
}

pub struct Sim<'a> {
    ids: &'a mut Ids,
    pub buf: String,
    n: u32,
    wid: u32,
    pub now: u64,
    pub ini: Node,
    prekeys: SoftPrekeys<Caps>,
    /// The responder nodes 1 and 2 (honest) and 3 (the attacker's identity).
    pub nodes: Vec<Node>,
    pub client: ClientTickets<CK>,
    pub inits: Vec<Initiator>,
    pub resps: Vec<(u8, Responder)>,
    pub ests: HashMap<(char, usize), Established>,
    /// The tickets per session and the ticket lifetime in seconds of the responders made from now on.
    pub tps: u8,
    pub life: u32,
    exp: Vec<Exp>,
    pub snapshot: Vec<u8>,
}

fn json_ids(v: &[i64]) -> String {
    format!("[{}]", v.iter().map(ToString::to_string).collect::<Vec<_>>().join(","))
}

fn classify_err(r: &Result<(), Failure>) -> (&'static str, String) {
    match r {
        Ok(()) => ("ok", String::new()),
        Err(f) => {
            let name = format!("{f:?}").split('(').next().unwrap_or_default().to_owned();
            (if f.is_fatal() { "fatal" } else { "drop" }, name)
        }
    }
}

fn alpn_bytes(a: u8) -> &'static [u8] {
    if a == 1 { ALPN } else { ALPN_B }
}

/// The ticket ids of an exported state, and their expiries.
pub fn export_entries(bytes: &[u8]) -> Vec<([u8; 16], u64)> {
    let count = usize::from(bytes[1]);
    let mut pos = 2;
    let mut out = Vec::new();
    for _ in 0..count {
        pos += 1 + 32;
        let alpn_len = usize::from(bytes[pos]);
        pos += 1 + alpn_len;
        let tid: [u8; 16] = bytes[pos..pos + 16].try_into().unwrap();
        pos += 16 + 32 + 1;
        let expiry = u64::from_be_bytes(bytes[pos..pos + 8].try_into().unwrap());
        pos += 8 + 6;
        out.push((tid, expiry));
    }
    assert_eq!(pos, bytes.len());
    out
}

impl<'a> Sim<'a> {
    /// A new world: `ia` makes the dialing node the attacker's identity.
    pub fn new(ids: &'a mut Ids, wid: u32, ia: bool) -> Self {
        let now = T0;
        let mut ini = Node::new(
            if ia { 0x66 } else { 0x21 },
            0x11,
            false,
            CreditRecord::new(1 << 20, 100, 1200),
        );
        let prekeys = {
            let Node { prov, drbg, .. } = &mut ini;
            let mut env = Env {
                provider: &*prov,
                now,
                drbg,
            };
            SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap()
        };
        let mut s = Self {
            ids,
            buf: String::new(),
            n: 0,
            wid,
            now,
            ini,
            prekeys,
            nodes: vec![
                Node::new(0x22, 0x33, true, CreditRecord::new(2 << 20, 200, 1300)),
                Node::new(0x23, 0x34, true, CreditRecord::new(3 << 20, 300, 1400)),
                Node::new(0x66, 0x35, true, CreditRecord::new(4 << 20, 400, 1500)),
            ],
            client: ClientTickets::new(),
            inits: Vec::new(),
            resps: Vec::new(),
            ests: HashMap::new(),
            tps: 1,
            life: 60,
            exp: Vec::new(),
            snapshot: Vec::new(),
        };
        let _ = writeln!(
            s.buf,
            r#"{{"t":"hs","w":{wid},"n":0,"op":"begin","tk":{TK},"ck":{CK},"ia":{ia}}}"#
        );
        s
    }

    pub fn finish(self, trace: &mut String) {
        trace.push_str(&self.buf);
    }

    /// The node id of responder node `rn` (1, 2 or 3).
    pub fn node_id(&self, rn: u8) -> NodeId {
        self.nodes[usize::from(rn) - 1].node_id()
    }

    /// The JSON record of a message: its ids. Asserts the byte lengths the model takes as constants.
    fn mrec(&mut self, bytes: &[u8]) -> String {
        let mid = self.ids.id(K_MSG, bytes);
        let (mut e, mut pk, mut hpk, mut ct, mut tid, mut echo) = (-1, -1, -1, -1, -1, -1);
        let mut tids = Vec::new();
        let mut form = "none";
        let ty = MessageType::of(bytes).unwrap();
        match ty {
            MessageType::Initial | MessageType::ShortInitial => {
                let m = Initial::parse(bytes).unwrap();
                e = self.ids.id(K_E, &m.e);
                hpk = self.ids.id(K_HASH, &m.prekey_hash());
                form = if let PrekeyField::Full(k) = m.prekey {
                    pk = self.ids.id(K_PK, k);
                    assert_eq!(bytes.len(), LF);
                    "full"
                } else {
                    assert_eq!(bytes.len(), LS);
                    "short"
                };
            }
            MessageType::PrekeyReject | MessageType::ResumeReject => {
                echo = self.ids.id(K_TH, &Reject::parse(bytes, ty).unwrap().echo);
            }
            MessageType::Reply => {
                let m = Reply::parse(bytes).unwrap();
                e = self.ids.id(K_E, &m.e);
                ct = self.ids.id(K_PK, m.ct);
            }
            MessageType::ResumeHello => {
                let m = ResumeHello::parse(bytes).unwrap();
                e = self.ids.id(K_E, &m.e);
                tid = self.ids.id(K_TID, &m.tid);
                assert_eq!(bytes.len(), LH);
            }
            MessageType::ResumeReply => {
                let m = ResumeReply::parse(bytes).unwrap();
                e = self.ids.id(K_E, &m.e);
                tids = m.tickets.entries().iter().map(|t| self.ids.id(K_TID, &t.tid)).collect();
                assert_eq!(bytes.len(), LR, "a resume Reply of the traces carries one ticket");
            }
            MessageType::Finish => {}
        }
        format!(
            r#"{{"ty":"{}","mid":{mid},"e":{e},"pk":{pk},"hpk":{hpk},"ct":{ct},"tid":{tid},"echo":{echo},"form":"{form}","tids":{},"len":{}}}"#,
            type_name(bytes[0]),
            json_ids(&tids),
            bytes.len()
        )
    }

    /// Write one step line; `ov` replaces (or appends) keys of the generic line.
    fn step(
        &mut self,
        op: &str,
        who: char,
        rn: u8,
        s: usize,
        inp: &Inp,
        r: &Result<(), Failure>,
        d: &Drained,
        ov: &[(&str, String)],
    ) {
        self.n += 1;
        let (res, errname) = classify_err(r);
        let (ity, imid, ibase, ifld, imal) = match inp {
            Inp::None => ("None", -1, -1, "", false),
            Inp::Exact(b) => (type_name(b[0]), self.ids.id(K_MSG, b), -1, "", false),
            Inp::Forged { base, bytes, fld } => (
                type_name(bytes[0]),
                self.ids.id(K_MSG, bytes),
                self.ids.id(K_MSG, base),
                *fld,
                false,
            ),
            Inp::Malformed(b) => (
                type_name(b.first().copied().unwrap_or(0)),
                self.ids.id(K_MSG, b),
                -1,
                "",
                true,
            ),
        };
        let ilen = if matches!(inp, Inp::None) {
            -1
        } else {
            inp.bytes().len() as i64
        };
        // a malformed input is dropped whatever the state, with the Malformed or Unexpected reason
        let res = if imal {
            assert!(
                matches!(r, Err(f) if !f.is_fatal()),
                "malformed input must be dropped: {r:?}"
            );
            "drop"
        } else {
            res
        };
        let outs: Vec<String> = d.sends.iter().map(|b| self.mrec(b)).collect();
        let (req, rth) = match &d.req {
            None => ("none", -1),
            Some(("decap", _)) => ("decap", -1),
            Some((k, th)) => (*k, self.ids.id(K_TH, th)),
        };
        let mut evs = Vec::new();
        if d.early.is_some() {
            evs.push("\"early\"");
        }
        if d.est.is_some() {
            evs.push("\"est\"");
        }
        if d.rejected {
            evs.push("\"rejected\"");
        }
        if d.failed.is_some() {
            evs.push("\"failed\"");
        }
        let early = d.early.map_or(-1, |k| self.ids.id(K_KEY, &k));
        let (resumed, send, recv, rsm, cid, etids, alpn) = match &d.est {
            None => (false, -1, -1, -1, -1, Vec::new(), -1),
            Some(e) => (
                e.resumed,
                self.ids.id(K_KEY, e.traffic.send.expose()),
                self.ids.id(K_KEY, e.traffic.recv.expose()),
                self.ids.id(K_KEY, e.resume.expose()),
                self.ids.id(K_KEY, e.cid_secret.expose()),
                e.tickets
                    .entries()
                    .iter()
                    .map(|t| self.ids.id(K_TID, &t.tid))
                    .collect::<Vec<_>>(),
                if e.alpn.as_bytes() == ALPN { 1 } else { 2 },
            ),
        };
        let peer = if d.est.is_none() {
            "none"
        } else if who == 'I' {
            "R"
        } else {
            "I"
        };
        let mut kv: Vec<(&str, String)> = vec![
            ("t", "\"hs\"".into()),
            ("w", self.wid.to_string()),
            ("n", self.n.to_string()),
            ("op", format!("\"{op}\"")),
            ("who", format!("\"{who}\"")),
            ("rn", rn.to_string()),
            ("s", s.to_string()),
            ("ity", format!("\"{ity}\"")),
            ("imid", imid.to_string()),
            ("ibase", ibase.to_string()),
            ("ifld", format!("\"{ifld}\"")),
            ("imal", imal.to_string()),
            ("ilen", ilen.to_string()),
            ("res", format!("\"{res}\"")),
            ("err", format!("\"{errname}\"")),
            ("outs", format!("[{}]", outs.join(","))),
            ("req", format!("\"{req}\"")),
            ("rth", rth.to_string()),
            ("evs", format!("[{}]", evs.join(","))),
            ("early", early.to_string()),
            ("peer", format!("\"{peer}\"")),
            ("resumed", resumed.to_string()),
            ("send", send.to_string()),
            ("recv", recv.to_string()),
            ("rsm", rsm.to_string()),
            ("cid", cid.to_string()),
            ("etids", json_ids(&etids)),
            ("alpn", alpn.to_string()),
        ];
        for (k, v) in ov {
            match kv.iter_mut().find(|(key, _)| key == k) {
                Some(slot) => slot.1.clone_from(v),
                None => kv.push((k, v.clone())),
            }
        }
        kv.push(("z", "0".into()));
        let body = kv
            .iter()
            .map(|(k, v)| format!("\"{k}\":{v}"))
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(self.buf, "{{{body}}}");
    }

    /// An empty drain, for the steps that are not a machine's.
    fn quiet(&mut self, op: &str, who: char, rn: u8, s: usize, ov: &[(&str, String)]) {
        self.step(op, who, rn, s, &Inp::None, &Ok(()), &Drained::default(), ov);
    }

    fn note_est(&mut self, who: char, rn: u8, s: usize, d: &mut Drained) {
        if let Some(e) = d.est.take() {
            if who == 'R' {
                for t in e.tickets.entries() {
                    self.exp.push(Exp {
                        cli: false,
                        rn,
                        tid: t.tid,
                        at: self.now + u64::from(t.lifetime_s) * NS,
                        done: false,
                    });
                }
            }
            self.ests.insert((who, s), e.clone());
            d.est = Some(e);
        }
    }

    // ---- time ----

    /// Let `secs` seconds pass: every tracked ticket past its expiry is announced once (held or not).
    pub fn advance(&mut self, secs: u64) {
        self.now += secs * NS;
        let now = self.now;
        let due: Vec<usize> = (0..self.exp.len())
            .filter(|&i| !self.exp[i].done && self.exp[i].at < now)
            .collect();
        for i in due {
            self.exp[i].done = true;
            let (cli, rn, tid) = (self.exp[i].cli, self.exp[i].rn, self.exp[i].tid);
            let id = self.ids.id(K_TID, &tid);
            let (who, rn) = if cli { ('I', 0) } else { ('R', rn) };
            let scope = if cli { "cli" } else { "srv" };
            self.quiet(
                "expire",
                who,
                rn,
                0,
                &[("scope", format!("\"{scope}\"")), ("tid", id.to_string())],
            );
        }
    }

    // ---- the initiator ----

    /// Start an initiator dialing node `peer` (1, 2 or 3) for ALPN `alpn` (1 or 2). `short`: the peer is known to cache
    /// the prekey; `take`: ask the client store for a ticket first. Returns the session and the messages sent.
    pub fn start(&mut self, peer: u8, alpn: u8, short: bool, take: bool) -> (usize, Vec<Vec<u8>>) {
        let s = self.inits.len() + 1;
        let scid = ConnId::new(format!("I.{s:06}").as_bytes()).unwrap();
        self.start_with(peer, alpn, short, take, scid, None)
    }

    /// As [`Sim::start`], with the source connection id and (optionally) a generator seed of its own.
    pub fn start_with(
        &mut self,
        peer: u8,
        alpn: u8,
        short: bool,
        take: bool,
        scid: ConnId,
        seed: Option<u8>,
    ) -> (usize, Vec<Vec<u8>>) {
        let dial = self.node_id(peer);
        let now = self.now;
        let mut own = seed.map(|b| Drbg::new(&[b; 32]));
        let Node {
            party,
            prov,
            drbg,
            credit,
            ..
        } = &mut self.ini;
        let mut env = Env {
            provider: &*prov,
            now,
            drbg: own.as_mut().unwrap_or(drbg),
        };
        let prekey = self.prekeys.acquire(&mut env).unwrap();
        let ticket = if take {
            self.client.take(&dial, alpn_bytes(alpn), now)
        } else {
            None
        };
        let mut i = Initiator::new(
            &mut env,
            InitiatorParams {
                peer: dial,
                alpn: alpn_bytes(alpn),
                scid,
                identity: &party.id,
                prekey: &prekey,
                peer_has_prekey: short,
                ticket,
                credit: *credit,
            },
        )
        .unwrap();
        let mut d = drain!(i);
        let s = self.inits.len() + 1;
        self.inits.push(i);
        let mode = match d.sends.first().map(|m| m[0]) {
            Some(1) => "full",
            Some(2) => "short",
            Some(6) => "resume",
            other => panic!("unexpected first message {other:?}"),
        };
        assert_eq!(
            mode == "short",
            short && mode != "resume",
            "the initiator started in another mode"
        );
        let tid = if mode == "resume" {
            self.ids.id(K_TID, &ResumeHello::parse(&d.sends[0]).unwrap().tid)
        } else {
            -1
        };
        let who = match peer {
            1 => "R1",
            2 => "R2",
            _ => "A",
        };
        let ov = [
            ("mode", format!("\"{mode}\"")),
            ("tid", tid.to_string()),
            ("peer", format!("\"{who}\"")),
            ("alpn", alpn.to_string()),
            ("take", take.to_string()),
        ];
        self.step("start", 'I', 0, s, &Inp::None, &Ok(()), &d, &ov);
        (s, std::mem::take(&mut d.sends))
    }

    pub fn i_recv(&mut self, s: usize, inp: &Inp) -> (Result<(), Failure>, Drained) {
        let now = self.now;
        let Node { prov, drbg, .. } = &mut self.ini;
        let mut env = Env {
            provider: &*prov,
            now,
            drbg,
        };
        let r = self.inits[s - 1].handle(&mut env, inp.bytes());
        let mut d = drain!(self.inits[s - 1]);
        self.step("recv", 'I', 0, s, inp, &r, &d, &[]);
        self.note_est('I', 0, s, &mut d);
        (r, d)
    }

    /// Answer the outstanding key request (`ok`) or refuse it. `ok` needs a request to be outstanding.
    pub fn i_key(&mut self, s: usize, ok: bool) -> (Result<(), Failure>, Drained) {
        let now = self.now;
        let Node { party, prov, drbg, .. } = &mut self.ini;
        let mut env = Env {
            provider: &*prov,
            now,
            drbg,
        };
        let r = if ok {
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &party.kp)),
                prekeys: Some(&self.prekeys),
            };
            let had = self.inits[s - 1].answer_soft(&mut env, &soft);
            assert!(matches!(had, Ok(true) | Err(_)), "no key request was outstanding");
            had.map(|_| ())
        } else {
            self.inits[s - 1].on_key_response(&mut env, KeyResponse::Failed)
        };
        let mut d = drain!(self.inits[s - 1]);
        let ov = [("kind", format!("\"{}\"", if ok { "ok" } else { "fail" }))];
        self.step("key", 'I', 0, s, &Inp::None, &r, &d, &ov);
        self.note_est('I', 0, s, &mut d);
        (r, d)
    }

    pub fn i_retx(&mut self, s: usize) -> Drained {
        let now = self.now;
        let Node { prov, drbg, .. } = &mut self.ini;
        let mut env = Env {
            provider: &*prov,
            now,
            drbg,
        };
        let r = self.inits[s - 1].retransmit(&mut env);
        let d = drain!(self.inits[s - 1]);
        self.step("retx", 'I', 0, s, &Inp::None, &r, &d, &[]);
        d
    }

    pub fn i_shed(&mut self, s: usize) {
        self.inits[s - 1].shed();
        self.quiet("shed", 'I', 0, s, &[]);
    }

    // ---- the responders ----

    /// A responder session on node `rn`, with the world's tickets per session and lifetime.
    pub fn r_new(&mut self, rn: u8) -> usize {
        let s = self.resps.len() + 1;
        let node = &self.nodes[usize::from(rn) - 1];
        let mut cfg = ResponderConfig::new(
            node.party.id,
            ConnId::new(format!("R{rn}.{s:05}").as_bytes()).unwrap(),
            AlpnList::new(&[ALPN, ALPN_B]).unwrap(),
        );
        cfg.tickets_per_session = self.tps;
        cfg.ticket_lifetime_s = self.life;
        cfg.credit = node.credit;
        self.resps.push((rn, Responder::new(cfg)));
        s
    }

    pub fn r_recv(&mut self, s: usize, inp: &Inp) -> (Result<(), Failure>, Drained) {
        let rn = self.resps[s - 1].0;
        let now = self.now;
        let Node { prov, drbg, stores, .. } = &mut self.nodes[usize::from(rn) - 1];
        let mut env = Env {
            provider: &*prov,
            now,
            drbg,
        };
        let r = self.resps[s - 1].1.handle(&mut env, stores, inp.bytes());
        let mut d = drain!(self.resps[s - 1].1);
        self.step("recv", 'R', rn, s, inp, &r, &d, &[]);
        self.note_est('R', rn, s, &mut d);
        (r, d)
    }

    pub fn r_key(&mut self, s: usize, ok: bool) -> (Result<(), Failure>, Drained) {
        let rn = self.resps[s - 1].0;
        let now = self.now;
        let Node { party, prov, drbg, .. } = &mut self.nodes[usize::from(rn) - 1];
        let mut env = Env {
            provider: &*prov,
            now,
            drbg,
        };
        let r = if ok {
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &party.kp)),
                prekeys: None,
            };
            let had = self.resps[s - 1].1.answer_soft(&mut env, &soft);
            assert!(matches!(had, Ok(true) | Err(_)), "no key request was outstanding");
            had.map(|_| ())
        } else {
            self.resps[s - 1].1.on_key_response(&mut env, KeyResponse::Failed)
        };
        let mut d = drain!(self.resps[s - 1].1);
        let ov = [("kind", format!("\"{}\"", if ok { "ok" } else { "fail" }))];
        self.step("key", 'R', rn, s, &Inp::None, &r, &d, &ov);
        self.note_est('R', rn, s, &mut d);
        (r, d)
    }

    /// The loss timer of a responder: it answers only while waiting for the Finish, and says so by sending.
    pub fn r_retx(&mut self, s: usize) -> Drained {
        let rn = self.resps[s - 1].0;
        self.resps[s - 1].1.retransmit();
        let d = drain!(self.resps[s - 1].1);
        let r = if d.sends.is_empty() {
            Err(Failure::UnexpectedMessage)
        } else {
            Ok(())
        };
        self.step("retx", 'R', rn, s, &Inp::None, &r, &d, &[]);
        d
    }

    pub fn r_shed(&mut self, s: usize) {
        let rn = self.resps[s - 1].0;
        self.resps[s - 1].1.shed();
        self.quiet("shed", 'R', rn, s, &[]);
    }

    // ---- the client store ----

    /// The client takes the tickets that came with the established session `is`: the batch of the responder session
    /// `rs` of a full handshake, or the batch in the resume reply.
    pub fn accept(&mut self, is: usize, rs: usize) {
        let rn = self.resps[rs - 1].0;
        let ei = self.ests[&('I', is)].clone();
        let batch = if ei.resumed {
            ei.tickets
        } else {
            self.ests[&('R', rs)].tickets
        };
        self.client.accept_batch(&ei, &batch, self.now);
        let mut ids = Vec::new();
        for t in batch.entries() {
            ids.push(self.ids.id(K_TID, &t.tid));
            self.exp.push(Exp {
                cli: true,
                rn: 0,
                tid: t.tid,
                at: self.now + u64::from(t.lifetime_s) * NS,
                done: false,
            });
        }
        let ov = [("rs", rs.to_string()), ("tids", json_ids(&ids))];
        self.quiet("accept", 'I', rn, is, &ov);
    }

    /// Export the newest at most `max` tickets of the client store.
    pub fn export(&mut self, max: usize) -> Vec<u8> {
        let mut buf = vec![0u8; 2 + 4 * MAX_EXPORT_ENTRY_LEN];
        let n = self.client.export(self.now, max, &mut buf).unwrap();
        buf.truncate(n);
        let ids: Vec<i64> = export_entries(&buf)
            .iter()
            .map(|(t, _)| self.ids.id(K_TID, t))
            .collect();
        self.quiet(
            "export",
            'I',
            0,
            0,
            &[("max", max.to_string()), ("tids", json_ids(&ids))],
        );
        self.snapshot.clone_from(&buf);
        buf
    }

    /// Restore `bytes` (the last export, or a damaged copy of it) into the client store.
    pub fn restore(&mut self, bytes: &[u8]) -> Result<usize, ()> {
        let before = self.client.len();
        let r = self.client.restore(bytes, self.now);
        let (ok, stored, kept) = if let Ok(n) = &r {
            let kept: Vec<i64> = export_entries(bytes)
                .iter()
                .filter(|(_, at)| *at >= self.now)
                .map(|(t, _)| self.ids.id(K_TID, t))
                .collect();
            assert_eq!(*n, kept.len());
            (true, *n, kept)
        } else {
            assert_eq!(self.client.len(), before, "a malformed state stores nothing");
            (false, 0, Vec::new())
        };
        let ov = [
            ("ok", ok.to_string()),
            ("stored", stored.to_string()),
            ("kept", json_ids(&kept)),
        ];
        self.quiet("restore", 'I', 0, 0, &ov);
        r.map_err(|_| ())
    }

    /// The process restarts: the client store is empty again (the exported bytes stay with the host).
    pub fn restart(&mut self) {
        self.client = ClientTickets::new();
        self.quiet("restart", 'I', 0, 0, &[]);
    }

    // ---- driving ----

    /// Deliver `first` (sent by initiator `is`) and every message it causes, in order, answering key requests at once.
    /// The delivery with the index of `tamper` is replaced by its mutated bytes. An Initial goes to responder node
    /// `init_node`, a Hello to `hello_node`, one responder session per node.
    pub fn drive(
        &mut self,
        is: usize,
        first: Vec<Vec<u8>>,
        tamper: Option<&Tamper>,
        init_node: u8,
        hello_node: u8,
    ) -> Vec<Vec<u8>> {
        let mut pending: VecDeque<(bool, Vec<u8>)> = first.into_iter().map(|m| (true, m)).collect();
        let mut log = Vec::new();
        let mut cur_r: HashMap<u8, usize> = HashMap::new();
        for delivered in 0..16usize {
            let Some((to_resp, bytes)) = pending.pop_front() else {
                break;
            };
            let inp = match tamper {
                Some((k, mutated, class)) if *k == delivered => match class {
                    Class::Malformed => Inp::Malformed(mutated.clone()),
                    Class::Field(f) => Inp::Forged {
                        base: bytes.clone(),
                        bytes: mutated.clone(),
                        fld: f,
                    },
                    Class::Unmodelled => panic!("an unmodelled tamper is not run"),
                },
                _ => Inp::Exact(bytes.clone()),
            };
            log.push(bytes.clone());
            let mut d;
            if to_resp {
                let rn = if bytes[0] == 6 { hello_node } else { init_node };
                let rs = if let Some(&rs) = cur_r.get(&rn) {
                    rs
                } else {
                    let rs = self.r_new(rn);
                    cur_r.insert(rn, rs);
                    rs
                };
                d = self.r_recv(rs, &inp).1;
                loop {
                    pending.extend(d.sends.drain(..).map(|m| (false, m)));
                    if d.req.is_none() {
                        break;
                    }
                    d = self.r_key(rs, true).1;
                }
            } else {
                d = self.i_recv(is, &inp).1;
                loop {
                    pending.extend(d.sends.drain(..).map(|m| (true, m)));
                    if d.req.is_none() {
                        break;
                    }
                    d = self.i_key(is, true).1;
                }
            }
        }
        log
    }

    /// A full handshake with node 1 and the client taking the ticket: the setup of every resumption.
    pub fn setup_full(&mut self, alpn: u8) -> (usize, usize) {
        let (is, first) = self.start(1, alpn, false, false);
        let rs = self.resps.len() + 1;
        self.drive(is, first, None, 1, 1);
        assert!(self.ests.contains_key(&('I', is)) && self.ests.contains_key(&('R', rs)));
        self.accept(is, rs);
        (is, rs)
    }
}
