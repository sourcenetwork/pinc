//! Trace generation for the handshake: real runs of the `Initiator` and `Responder` through the public API, recorded
//! step by step as ndjson for the TLA+ trace check and the Lean replay; and the record-layer traces of `AmpBudget`.
//!
//! A world is one test scenario: one initiator node, up to two responder nodes (each with its own stores), and any
//! number of sessions. Every step of either machine (start, receive a message, answer a key request, hand tickets to
//! the client store) is one `hs` line: the input message (type, id, and for a tampered input the id of the original
//! and the field that changed), the outcome (`ok`, `drop`, `fatal`), the outputs (messages with the ids of their
//! public values, the key request and its transcript hash), the events, and key fingerprint ids at `Established` and
//! `EarlyKeys`. An id stands for one distinct byte string (equal bytes, equal id), so the checkers never see a hash
//! function: they check that the recorded ids relate exactly as the model's symbolic terms do.
//!
//! The fields the model folds into one parameter value (version, ALPN, AEAD offer, connection ids, credit record) are
//! tampered and asserted here, but only the version and the ALPN, which the machines refuse, are recorded; a changed
//! connection id, credit record or offer is accepted by the code and absorbed into the transcript, which the model cannot say
//! with one value, so those worlds are run and asserted but not written.
//!
//! Every scenario is asserted here, so the test is meaningful without the proof tools. The traces are written to the
//! directory in `VINC_TRACE_DIR` when it is set (`handshake.ndjson`, `security.ndjson`); otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    clippy::struct_excessive_bools,
    clippy::fn_params_excessive_bools,
    unreachable_pub
)]

use std::collections::{HashMap, VecDeque};
use std::fmt::Write as _;

use vinc_crypto::IdentityAlg;
use vinc_security::ids::aead_tag;
use vinc_security::message::{Finish, Initial, MessageType, PrekeyField, Reject, Reply, ResumeHello, ResumeReply};
use vinc_security::{
    AmpBudget, Env, Established, Event, Failure, Initiator, KeyHandle, KeyRequest, KeyResponse, Output, Responder,
    ResponderStores, SoftKeys,
};
use vinc_tests::SplitMix64;

mod sec_common;
use sec_common::{PK, TK, World, big_stack};

/// Dense ids for byte strings, one id per (kind, bytes).
#[derive(Default)]
struct Ids(HashMap<(u8, Vec<u8>), u32>);

impl Ids {
    fn id(&mut self, kind: u8, bytes: &[u8]) -> i64 {
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

fn type_name(ty: u8) -> &'static str {
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

/// The fields of a message a tamper can change, by name, or `None` if it does not parse.
fn fields(bytes: &[u8]) -> Option<Vec<(&'static str, Vec<u8>)>> {
    let ty = MessageType::of(bytes).ok()?;
    Some(match ty {
        MessageType::Initial | MessageType::ShortInitial => {
            let m = Initial::parse(bytes).ok()?;
            let pk = match m.prekey {
                PrekeyField::Full(k) => k.to_vec(),
                PrekeyField::Hash(h) => h.to_vec(),
            };
            vec![
                ("version", vec![m.version]),
                ("dcid", m.dcid.as_bytes().to_vec()),
                ("scid", m.scid.as_bytes().to_vec()),
                ("alpn", m.alpn.to_vec()),
                ("offer", vec![m.aead_offer.bits()]),
                ("e", m.e.to_vec()),
                ("pk", pk),
                ("credit", m.credit.encode().to_vec()),
            ]
        }
        MessageType::PrekeyReject | MessageType::ResumeReject => {
            vec![("echo", Reject::parse(bytes, ty).ok()?.echo.to_vec())]
        }
        MessageType::Reply => {
            let m = Reply::parse(bytes).ok()?;
            vec![
                ("scid", m.scid.as_bytes().to_vec()),
                ("aead", vec![aead_tag(m.aead)]),
                ("e", m.e.to_vec()),
                ("ct", m.ct.to_vec()),
                ("sealed", m.sealed.to_vec()),
            ]
        }
        MessageType::Finish => vec![("sealed", Finish::parse(bytes).ok()?.sealed.to_vec())],
        MessageType::ResumeHello => {
            let m = ResumeHello::parse(bytes).ok()?;
            vec![
                ("version", vec![m.version]),
                ("dcid", m.dcid.as_bytes().to_vec()),
                ("scid", m.scid.as_bytes().to_vec()),
                ("alpn", m.alpn.to_vec()),
                ("aead", vec![aead_tag(m.aead)]),
                ("tid", m.tid.to_vec()),
                ("e", m.e.to_vec()),
                ("binder", m.binder.to_vec()),
                ("credit", m.credit.encode().to_vec()),
            ]
        }
        MessageType::ResumeReply => {
            let m = ResumeReply::parse(bytes).ok()?;
            let mut t = [0u8; 81];
            let n = m.tickets.encode(&mut t).ok()?;
            vec![
                ("scid", m.scid.as_bytes().to_vec()),
                ("e", m.e.to_vec()),
                ("tickets", t[..n].to_vec()),
                ("credit", m.credit.encode().to_vec()),
                ("confirm", m.confirm.to_vec()),
            ]
        }
    })
}

/// What a tamper did to a message, as the model can state it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Class {
    /// Does not parse.
    Malformed,
    /// One modelled field changed: the model's field name.
    Field(&'static str),
    /// A field the model folds away changed (connection id, credit record, offer, Reply scid): run, assert, do not record.
    Unmodelled,
}

fn classify(orig: &[u8], mutated: &[u8]) -> Class {
    let (Some(a), Some(b)) = (fields(orig), fields(mutated)) else {
        return Class::Malformed;
    };
    let changed: Vec<&str> = a.iter().zip(&b).filter(|(x, y)| x.1 != y.1).map(|(x, _)| x.0).collect();
    let ty = orig[0];
    match changed.as_slice() {
        ["version" | "alpn"] => Class::Field("prm"),
        ["e"] => Class::Field("e"),
        ["pk"] => Class::Field("pk"),
        ["ct"] => Class::Field("ct"),
        ["sealed"] => Class::Field("sealed"),
        ["tid"] => Class::Field("tid"),
        ["binder"] => Class::Field("binder"),
        ["confirm"] => Class::Field("conf"),
        ["tickets"] => Class::Field("tids"),
        ["echo"] => Class::Field("echo"),
        ["scid"] if ty == 7 => Class::Field("rprm"),
        _ => Class::Unmodelled,
    }
}

struct Drained {
    sends: Vec<Vec<u8>>,
    req: Option<(&'static str, Vec<u8>)>,
    early: Option<[u8; 32]>,
    est: Option<Established>,
    rejected: bool,
    failed: Option<Failure>,
}

macro_rules! drain {
    ($m:expr) => {{
        let mut d = Drained {
            sends: vec![],
            req: None,
            early: None,
            est: None,
            rejected: false,
            failed: None,
        };
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

/// How an input reached a machine.
#[derive(Clone)]
enum Inp {
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
    fn bytes(&self) -> &[u8] {
        match self {
            Self::Exact(b) | Self::Malformed(b) | Self::Forged { bytes: b, .. } => b,
            Self::None => &[],
        }
    }
}

/// A tamper: the delivery index it applies to, the mutated bytes and what the mutation changed.
type Tamper = (usize, Vec<u8>, Class);

struct Sim<'a> {
    w: World,
    ids: &'a mut Ids,
    buf: String,
    n: u32,
    wid: u32,
    inits: Vec<Initiator>,
    resps: Vec<(u8, Responder)>,
    stores2: ResponderStores<PK, TK>,
    /// The Established value of each session: ('I' or 'R', session).
    ests: HashMap<(char, usize), Established>,
    keep: bool,
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

impl<'a> Sim<'a> {
    fn new(ids: &'a mut Ids, wid: u32) -> Self {
        let mut s = Self {
            w: World::new(IdentityAlg::Ed25519, IdentityAlg::Ed25519, false, false),
            ids,
            buf: String::new(),
            n: 0,
            wid,
            inits: Vec::new(),
            resps: Vec::new(),
            stores2: ResponderStores::default(),
            ests: HashMap::new(),
            keep: true,
        };
        let _ = writeln!(s.buf, r#"{{"t":"hs","w":{wid},"n":0,"op":"begin"}}"#);
        s
    }

    /// The JSON record of a message: its ids.
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
                    "full"
                } else {
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
            }
            MessageType::ResumeReply => {
                let m = ResumeReply::parse(bytes).unwrap();
                e = self.ids.id(K_E, &m.e);
                tids = m.tickets.entries().iter().map(|t| self.ids.id(K_TID, &t.tid)).collect();
            }
            MessageType::Finish => {}
        }
        format!(
            r#"{{"ty":"{}","mid":{mid},"e":{e},"pk":{pk},"hpk":{hpk},"ct":{ct},"tid":{tid},"echo":{echo},"form":"{form}","tids":{}}}"#,
            type_name(bytes[0]),
            json_ids(&tids)
        )
    }

    /// Write one step line.
    #[allow(clippy::too_many_arguments)]
    fn step(
        &mut self,
        op: &str,
        who: char,
        rn: u8,
        s: usize,
        inp: &Inp,
        r: &Result<(), Failure>,
        d: &Drained,
        extra: &str,
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
        let (resumed, send, recv, rsm, etids) = match &d.est {
            None => (false, -1, -1, -1, Vec::new()),
            Some(e) => (
                e.resumed,
                self.ids.id(K_KEY, e.traffic.send.expose()),
                self.ids.id(K_KEY, e.traffic.recv.expose()),
                self.ids.id(K_KEY, e.resume.expose()),
                e.tickets
                    .entries()
                    .iter()
                    .map(|t| self.ids.id(K_TID, &t.tid))
                    .collect::<Vec<_>>(),
            ),
        };
        let peer = if d.est.is_none() {
            "none"
        } else if who == 'I' {
            "R"
        } else {
            "I"
        };
        let _ = writeln!(
            self.buf,
            r#"{{"t":"hs","w":{},"n":{},"op":"{op}","who":"{who}","rn":{rn},"s":{s},"ity":"{ity}","imid":{imid},"ibase":{ibase},"ifld":"{ifld}","imal":{imal},"res":"{res}","err":"{errname}","outs":[{}],"req":"{req}","rth":{rth},"evs":[{}],"early":{early},"peer":"{peer}","resumed":{resumed},"send":{send},"recv":{recv},"rsm":{rsm},"etids":{},{extra}"z":0}}"#,
            self.wid,
            self.n,
            outs.join(","),
            evs.join(","),
            json_ids(&etids),
        );
    }

    /// Start an initiator: `mode` is "full", "short" or "resume".
    fn i_start(&mut self, mode: &str) -> (usize, Vec<Vec<u8>>) {
        let dial = self.w.dial();
        let mut i = self
            .w
            .initiator_with(dial, sec_common::ALPN, mode == "short", mode == "resume");
        let mut d = drain!(i);
        let s = self.inits.len() + 1;
        self.inits.push(i);
        let first = d.sends.first().map(|m| m[0]);
        let actual = match first {
            Some(1) => "full",
            Some(2) => "short",
            Some(6) => "resume",
            other => panic!("unexpected first message {other:?}"),
        };
        assert_eq!(actual, mode, "the initiator started in another mode");
        let tid = if actual == "resume" {
            self.ids.id(K_TID, &ResumeHello::parse(&d.sends[0]).unwrap().tid)
        } else {
            -1
        };
        let extra = format!(r#""mode":"{mode}","tid":{tid},"#);
        self.step("start", 'I', 0, s, &Inp::None, &Ok(()), &d, &extra);
        (s, std::mem::take(&mut d.sends))
    }

    fn i_recv(&mut self, s: usize, inp: &Inp) -> (Result<(), Failure>, Drained) {
        let World {
            i_prov, i_drbg, now, ..
        } = &mut self.w;
        let mut env = Env {
            provider: &*i_prov,
            now: *now,
            drbg: i_drbg,
        };
        let r = self.inits[s - 1].handle(&mut env, inp.bytes());
        let mut d = drain!(self.inits[s - 1]);
        self.step("recv", 'I', 0, s, inp, &r, &d, "");
        if let Some(e) = d.est.take() {
            self.ests.insert(('I', s), e.clone());
            d.est = Some(e);
        }
        (r, d)
    }

    fn i_key(&mut self, s: usize, ok: bool) -> (Result<(), Failure>, Drained) {
        let World {
            ip,
            i_prov,
            i_drbg,
            now,
            prekeys,
            ..
        } = &mut self.w;
        let mut env = Env {
            provider: &*i_prov,
            now: *now,
            drbg: i_drbg,
        };
        let r = if ok {
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &ip.kp)),
                prekeys: Some(&*prekeys),
            };
            self.inits[s - 1].answer_soft(&mut env, &soft).map(|_| ())
        } else {
            self.inits[s - 1].on_key_response(&mut env, KeyResponse::Failed)
        };
        let mut d = drain!(self.inits[s - 1]);
        let extra = format!(r#""kind":"{}","#, if ok { "ok" } else { "fail" });
        self.step("key", 'I', 0, s, &Inp::None, &r, &d, &extra);
        if let Some(e) = d.est.take() {
            self.ests.insert(('I', s), e.clone());
            d.est = Some(e);
        }
        (r, d)
    }

    fn r_new(&mut self, rn: u8) -> usize {
        let r = self.w.responder();
        self.resps.push((rn, r));
        self.resps.len()
    }

    fn r_recv(&mut self, s: usize, inp: &Inp) -> (Result<(), Failure>, Drained) {
        let rn = self.resps[s - 1].0;
        let World {
            r_prov,
            r_drbg,
            now,
            stores,
            ..
        } = &mut self.w;
        let mut env = Env {
            provider: &*r_prov,
            now: *now,
            drbg: r_drbg,
        };
        let st = if rn == 1 { stores } else { &mut self.stores2 };
        let r = self.resps[s - 1].1.handle(&mut env, st, inp.bytes());
        let mut d = drain!(self.resps[s - 1].1);
        self.step("recv", 'R', rn, s, inp, &r, &d, "");
        if let Some(e) = d.est.take() {
            self.ests.insert(('R', s), e.clone());
            d.est = Some(e);
        }
        (r, d)
    }

    fn r_key(&mut self, s: usize, ok: bool) -> (Result<(), Failure>, Drained) {
        let rn = self.resps[s - 1].0;
        let World {
            rp,
            r_prov,
            r_drbg,
            now,
            ..
        } = &mut self.w;
        let mut env = Env {
            provider: &*r_prov,
            now: *now,
            drbg: r_drbg,
        };
        let r = if ok {
            let soft = SoftKeys {
                signer: Some((KeyHandle(1), &rp.kp)),
                prekeys: None,
            };
            self.resps[s - 1].1.answer_soft(&mut env, &soft).map(|_| ())
        } else {
            self.resps[s - 1].1.on_key_response(&mut env, KeyResponse::Failed)
        };
        let mut d = drain!(self.resps[s - 1].1);
        let extra = format!(r#""kind":"{}","#, if ok { "ok" } else { "fail" });
        self.step("key", 'R', rn, s, &Inp::None, &r, &d, &extra);
        if let Some(e) = d.est.take() {
            self.ests.insert(('R', s), e.clone());
            d.est = Some(e);
        }
        (r, d)
    }

    /// The client takes the tickets that came with the established session `is`: the batch of the responder session
    /// `(rn, rs)` of a full handshake, or the batch in the resume reply.
    fn accept(&mut self, is: usize, rn: u8, rs: usize) {
        let ei = self.ests[&('I', is)].clone();
        let batch = if ei.resumed {
            ei.tickets
        } else {
            self.ests[&('R', rs)].tickets
        };
        let now = self.w.now;
        self.w.client.accept_batch(&ei, &batch, now);
        let tid = batch.entries().first().map_or(-1, |t| self.ids.id(K_TID, &t.tid));
        let extra = format!(r#""tid":{tid},"rs":{rs},"#);
        let d = Drained {
            sends: vec![],
            req: None,
            early: None,
            est: None,
            rejected: false,
            failed: None,
        };
        self.step("accept", 'I', rn, is, &Inp::None, &Ok(()), &d, &extra);
    }

    /// Deliver `first` (sent by initiator `is`) and every message it causes, in order, answering key requests at
    /// once. The delivery with the index of `tamper` is replaced by its mutated bytes. A Hello goes to responder
    /// node `hello_node`, everything else to node 1, one responder session per node.
    fn drive(&mut self, is: usize, first: Vec<Vec<u8>>, tamper: Option<&Tamper>, hello_node: u8) -> Vec<Vec<u8>> {
        let mut pending: VecDeque<(bool, Vec<u8>)> = first.into_iter().map(|m| (true, m)).collect();
        let mut log = Vec::new();
        let mut cur_r: HashMap<u8, usize> = HashMap::new();
        for delivered in 0..16usize {
            let Some((to_resp, bytes)) = pending.pop_front() else {
                break;
            };
            let inp = match tamper {
                Some((k, mutated, class)) if *k == delivered => {
                    if *class == Class::Malformed {
                        Inp::Malformed(mutated.clone())
                    } else {
                        Inp::Forged {
                            base: bytes.clone(),
                            bytes: mutated.clone(),
                            fld: if let Class::Field(f) = class { f } else { "unmodelled" },
                        }
                    }
                }
                _ => Inp::Exact(bytes.clone()),
            };
            log.push(bytes.clone());
            let mut d;
            if to_resp {
                let rn = if bytes[0] == 6 { hello_node } else { 1 };
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
    fn setup_full(&mut self) {
        let (is, first) = self.i_start("full");
        self.drive(is, first, None, 1);
        assert!(self.ests.contains_key(&('I', is)) && self.ests.contains_key(&('R', 1)));
        self.accept(is, 1, 1);
    }

    fn finish(self, trace: &mut String) {
        if self.keep {
            trace.push_str(&self.buf);
        }
    }
}

/// The messages of a flow in delivery order, from a dry run, and the setup it needs.
#[derive(Clone, Copy)]
enum Flow {
    Full,
    ShortMiss,
    Resume,
    ResumeReject,
}

impl Flow {
    fn run(self, sim: &mut Sim<'_>, tamper: Option<&Tamper>) -> Vec<Vec<u8>> {
        match self {
            Self::Full => {
                let (is, first) = sim.i_start("full");
                sim.drive(is, first, tamper, 1)
            }
            Self::ShortMiss => {
                let (is, first) = sim.i_start("short");
                sim.drive(is, first, tamper, 1)
            }
            Self::Resume | Self::ResumeReject => {
                sim.setup_full();
                let (is, first) = sim.i_start("resume");
                sim.drive(is, first, tamper, if matches!(self, Self::Resume) { 1 } else { 2 })
            }
        }
    }
}

/// Every message delivered by a flow, in order.
fn flow_messages(flow: Flow) -> Vec<Vec<u8>> {
    let mut ids = Ids::default();
    let mut sim = Sim::new(&mut ids, 0);
    flow.run(&mut sim, None)
}

/// The tampers of one message: the first and the last byte of each kind of change (a bit flipped), the message cut
/// by a byte and extended by one.
fn tamper_cases(msg: &[u8]) -> Vec<(Vec<u8>, Class)> {
    let mut seen: Vec<(Class, usize, usize)> = Vec::new();
    for idx in 1..msg.len() {
        let mut m = msg.to_vec();
        m[idx] ^= 1;
        let c = classify(msg, &m);
        match seen.iter_mut().find(|s| s.0 == c) {
            Some(s) => s.2 = idx,
            None => seen.push((c, idx, idx)),
        }
    }
    let mut out = Vec::new();
    for (c, first, last) in seen {
        // a changed byte of a full prekey may break the key's own range check, which the model does not say: only
        // its last byte (the seed of the matrix) is flipped
        let idxs: Vec<usize> = if c == Class::Field("pk") && msg[0] == 1 {
            vec![last]
        } else if first == last {
            vec![first]
        } else {
            vec![first, last]
        };
        for idx in idxs {
            let mut m = msg.to_vec();
            m[idx] ^= 1;
            out.push((m, c.clone()));
        }
    }
    out.push((msg[..msg.len() - 1].to_vec(), Class::Malformed));
    let mut ext = msg.to_vec();
    ext.push(0);
    out.push((ext, Class::Malformed));
    out
}

fn agree(i: &Established, r: &Established) {
    assert_eq!(i.traffic.send, r.traffic.recv);
    assert_eq!(i.traffic.recv, r.traffic.send);
    assert_eq!(i.resume, r.resume);
    assert_eq!(i.resumed, r.resumed);
}

fn ex(b: &[u8]) -> Inp {
    Inp::Exact(b.to_vec())
}

fn flip_field(msg: &[u8], name: &'static str) -> Inp {
    for (m, c) in tamper_cases(msg) {
        if c == Class::Field(name) {
            return Inp::Forged {
                base: msg.to_vec(),
                bytes: m,
                fld: name,
            };
        }
    }
    panic!("no tamper of field {name}");
}

fn scenarios(ids: &mut Ids, trace: &mut String, wid: &mut u32) {
    macro_rules! world {
        ($sim:ident, $body:block) => {{
            *wid += 1;
            #[allow(unused_mut)]
            let mut $sim = Sim::new(ids, *wid);
            $body
            $sim.finish(trace);
        }};
    }
    // full handshake
    world!(sim, {
        let (is, first) = sim.i_start("full");
        sim.drive(is, first, None, 1);
        let (ei, er) = (sim.ests[&('I', 1)].clone(), sim.ests[&('R', 1)].clone());
        agree(&ei, &er);
        assert!(!ei.resumed && er.tickets.entries().len() == 1);
    });
    // short Initial with a prekey hit: the cache was filled by an earlier handshake
    world!(sim, {
        sim.setup_full();
        let (is, first) = sim.i_start("short");
        assert_eq!(first[0][0], 2);
        let log = sim.drive(is, first, None, 1);
        assert_eq!(log.iter().map(|m| m[0]).collect::<Vec<_>>(), vec![2, 4, 5]);
    });
    // short Initial with a miss: reject, then the full Initial
    world!(sim, {
        let (is, first) = sim.i_start("short");
        let log = sim.drive(is, first, None, 1);
        assert_eq!(log.iter().map(|m| m[0]).collect::<Vec<_>>(), vec![2, 3, 1, 4, 5]);
        agree(&sim.ests[&('I', 1)], &sim.ests[&('R', 1)]);
    });
    // a reject made by another responder (with the right echo) falls the initiator back, a wrong echo is dropped
    world!(sim, {
        sim.setup_full();
        let (is, first) = sim.i_start("short");
        let rs2 = sim.r_new(2);
        let (_, d) = sim.r_recv(rs2, &ex(&first[0]));
        assert_eq!(d.sends[0][0], 3);
        let rej = d.sends[0].clone();
        let (r, _) = sim.i_recv(is, &flip_field(&rej, "echo"));
        assert!(r.is_err());
        let (r, d) = sim.i_recv(is, &ex(&rej));
        assert!(r.is_ok() && d.sends[0][0] == 1);
        // the same reject again: the initiator already moved to the full form
        let (r, _) = sim.i_recv(is, &ex(&rej));
        assert!(r.is_err());
        sim.drive(is, d.sends.clone(), None, 1);
        agree(&sim.ests[&('I', is)], &sim.ests[&('R', sim.resps.len())]);
    });
    // the same Initial twice, and a deferred key request: nothing changes while the host has not answered
    world!(sim, {
        let (is, first) = sim.i_start("full");
        let rs = sim.r_new(1);
        let (_, d) = sim.r_recv(rs, &ex(&first[0]));
        assert!(d.req.is_some() && d.sends.is_empty());
        let (r, d2) = sim.r_recv(rs, &ex(&first[0]));
        assert!(r.is_err() && d2.req.is_none() && d2.sends.is_empty());
        let (r, d) = sim.r_key(rs, true);
        assert!(r.is_ok());
        let reply = d.sends[0].clone();
        // a retransmitted Initial after the Reply gets the same Reply again
        let (_, d3) = sim.r_recv(rs, &ex(&first[0]));
        assert_eq!(d3.sends, vec![reply.clone()]);
        let (r, d) = sim.i_recv(is, &ex(&reply));
        assert!(r.is_ok() && d.req.is_some_and(|q| q.0 == "decap"));
        let (r, _) = sim.i_recv(is, &ex(&reply));
        assert!(r.is_err());
        let (r, d) = sim.i_key(is, true);
        assert!(r.is_ok() && d.req.is_some_and(|q| q.0 == "sign"));
        let (r, _) = sim.i_recv(is, &ex(&reply));
        assert!(r.is_err());
        let (r, d) = sim.i_key(is, true);
        assert!(r.is_ok() && d.est.is_some());
        let fin = d.sends[0].clone();
        let (r, d) = sim.r_recv(rs, &ex(&fin));
        assert!(r.is_ok() && d.est.is_some());
        // a second Finish and a second Initial reach a finished session
        assert!(sim.r_recv(rs, &ex(&fin)).0.is_err());
        assert!(sim.r_recv(rs, &ex(&first[0])).0.is_err());
        agree(&sim.ests[&('I', is)], &sim.ests[&('R', rs)]);
    });
    // key operations that fail: the responder's signature, the initiator's decapsulation and signature
    for stage in 0..3 {
        world!(sim, {
            let (is, first) = sim.i_start("full");
            let rs = sim.r_new(1);
            let _ = sim.r_recv(rs, &ex(&first[0]));
            if stage == 0 {
                let (r, d) = sim.r_key(rs, false);
                assert!(r.is_err() && d.failed.is_some());
                assert!(sim.r_recv(rs, &ex(&first[0])).0.is_err());
            } else {
                let reply = sim.r_key(rs, true).1.sends[0].clone();
                let _ = sim.i_recv(is, &ex(&reply));
                if stage == 1 {
                    let (r, d) = sim.i_key(is, false);
                    assert!(r.is_err() && d.failed.is_some());
                } else {
                    let _ = sim.i_key(is, true);
                    let (r, d) = sim.i_key(is, false);
                    assert!(r.is_err() && d.failed.is_some());
                }
                assert!(sim.i_recv(is, &ex(&reply)).0.is_err());
            }
        });
    }
    // resumption with 0-RTT keys, twice
    world!(sim, {
        sim.setup_full();
        let (is, first) = sim.i_start("resume");
        sim.drive(is, first, None, 1);
        let (ei, er) = (sim.ests[&('I', is)].clone(), sim.ests[&('R', 2)].clone());
        agree(&ei, &er);
        assert!(ei.resumed);
        sim.accept(is, 1, 2);
        let (is2, first2) = sim.i_start("resume");
        sim.drive(is2, first2, None, 1);
        assert!(sim.ests[&('I', is2)].resumed);
    });
    // a replayed Hello is rejected by a fresh responder, a Hello with a wrong binder does not burn the ticket
    world!(sim, {
        sim.setup_full();
        let (is, first) = sim.i_start("resume");
        let hello = first[0].clone();
        let bad = flip_field(&hello, "binder");
        let rs = sim.r_new(1);
        let (r, d) = sim.r_recv(rs, &bad);
        assert!(r.is_ok() && d.sends[0][0] == 8 && d.early.is_none());
        let rs2 = sim.r_new(1);
        let (r, d) = sim.r_recv(rs2, &ex(&hello));
        assert!(r.is_ok() && d.early.is_some() && d.est.is_some());
        let reply = d.sends[0].clone();
        let rs3 = sim.r_new(1);
        let (r, d) = sim.r_recv(rs3, &ex(&hello));
        assert!(r.is_ok() && d.sends[0][0] == 8 && d.early.is_none());
        let rej = d.sends[0].clone();
        // the reject reaches the initiator before the reply: it falls back, and the late reply is dropped
        let (r, d) = sim.i_recv(is, &ex(&rej));
        assert!(r.is_ok() && d.rejected && d.sends[0][0] == 1);
        assert!(sim.i_recv(is, &ex(&reply)).0.is_err());
        sim.drive(is, d.sends.clone(), None, 1);
    });
    // the same Hello twice to one responder session: the resumed responder sends its Reply again, with no second session
    world!(sim, {
        sim.setup_full();
        let (_, first) = sim.i_start("resume");
        let rs = sim.r_new(1);
        let (r, d) = sim.r_recv(rs, &ex(&first[0]));
        assert!(r.is_ok());
        let reply = d.sends[0].clone();
        let (r, d) = sim.r_recv(rs, &ex(&first[0]));
        assert!(r.is_ok() && d.sends == vec![reply] && d.est.is_none());
    });
    // resumption rejected (the responder has no such ticket): the full handshake follows
    world!(sim, {
        sim.setup_full();
        let (is, first) = sim.i_start("resume");
        let log = sim.drive(is, first, None, 2);
        assert_eq!(log.iter().map(|m| m[0]).collect::<Vec<_>>(), vec![6, 8, 1, 4, 5]);
        assert!(!sim.ests[&('I', is)].resumed);
    });
    // tampered and cut messages in each flow
    for flow in [Flow::Full, Flow::ShortMiss, Flow::Resume, Flow::ResumeReject] {
        let msgs = flow_messages(flow);
        for (k, msg) in msgs.iter().enumerate() {
            for tamper in tamper_cases(msg) {
                let tamper = (k, tamper.0, tamper.1);
                *wid += 1;
                let mut sim = Sim::new(ids, *wid);
                sim.keep = tamper.2 != Class::Unmodelled;
                flow.run(
                    &mut sim,
                    Some(&(tamper.0, tamper.1.clone(), tamper.2.clone())).map(|_| &tamper),
                );
                let (ty, last_i) = (msg[0], sim.inits.len());
                if let Class::Field(f) = tamper.2 {
                    let i_est = sim.ests.contains_key(&('I', last_i));
                    match (ty, f) {
                        (4 | 7, "sealed" | "conf" | "tids" | "rprm" | "e" | "ct") => assert!(!i_est, "{ty} {f}"),
                        (5, "sealed") => assert!(!sim.ests.contains_key(&('R', sim.resps.len()))),
                        (6, "binder" | "tid" | "e") => {
                            assert!(sim.ests.iter().filter(|(k, _)| k.0 == 'R').all(|(_, e)| !e.resumed));
                        }
                        _ => {}
                    }
                }
                sim.finish(trace);
            }
        }
    }
}

// ---- the record-layer traces ----

fn security_traces(out: &mut String) {
    let mut rng = SplitMix64::new(0x5EC0_0001);
    // the amplification budget
    for r in 0..40u32 {
        let mut b = AmpBudget::new();
        let big = r % 4 == 3;
        for seq in 0..120u32 {
            let n = if big && rng.next_u64().is_multiple_of(3) {
                u64::MAX - rng.next_u64() % 100
            } else {
                rng.next_u64() % 4000
            };
            let mut op = match rng.next_u64() % 8 {
                0 | 1 => "rx",
                2..=4 => "tx",
                6 if rng.next_u64().is_multiple_of(4) => "val",
                _ => "can",
            };
            // a send is recorded only when the sender kept the discipline (or the run exercises saturation)
            if op == "tx" && !(b.can_send(n) || big) {
                op = "can";
            }
            let mut can = false;
            match op {
                "rx" => b.on_receive(n),
                "tx" => b.on_send(n),
                "val" => b.validate(),
                _ => can = b.can_send(n),
            }
            // `tx` is recorded as what the model applies: the send happened iff the counter moved
            let _ = writeln!(
                out,
                r#"{{"t":"amp","run":{},"seq":{seq},"op":"{op}","n":{n},"can":{can},"rx":{},"tx":{},"valid":{}}}"#,
                r + 1,
                b.received(),
                b.sent(),
                b.is_validated()
            );
        }
    }
}

#[test]
fn handshake_traces() {
    big_stack(|| {
        let mut ids = Ids::default();
        let mut hs = String::new();
        let mut wid = 0u32;
        scenarios(&mut ids, &mut hs, &mut wid);
        let mut sec = String::new();
        security_traces(&mut sec);
        let lines = hs.lines().count();
        assert!(lines > 500, "{lines} handshake events");
        assert!(wid > 100, "{wid} worlds");
        for needle in [
            r#""op":"start""#,
            r#""op":"accept""#,
            r#""mode":"resume""#,
            r#""mode":"short""#,
            r#""evs":["early","est"]"#,
            r#""evs":["rejected"]"#,
            r#""res":"fatal""#,
            r#""imal":true"#,
            r#""ifld":"binder""#,
            r#""ifld":"sealed""#,
            r#""kind":"fail""#,
        ] {
            assert!(hs.contains(needle), "the runs never produce {needle}");
        }
        assert!(
            sec.contains(r#""t":"amp""#),
            "the runs never produce an amplification trace"
        );
        let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
            return;
        };
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("handshake.ndjson"), hs).unwrap();
        std::fs::write(dir.join("security.ndjson"), sec).unwrap();
    });
}
