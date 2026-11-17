//! The recorder of the node trace: turns every call into a machine of a [`World`] into one ndjson line of the
//! schema `TraceMembership.tla` and `Vinc.TraceMembership` read (see the header of `node.rs`).

use std::cell::RefCell;
use std::fmt::Write as _;
use std::rc::Rc;

use vinc_membership::codec::{Alive, Down, Entry, Frame, Path};
use vinc_membership::event::{QuietCause, Refusal, Removal};
use vinc_membership::{Carrier, CloseReason, Event, NodeId, Route, Trace};

use crate::common::{b, limbs, list, opt_limbs};
use crate::world::{Bc, Call, EnvSnap, Op, Recorder, StSnap};

/// The number of a node id in the traces: a node id is 32 equal bytes (the byte), a wide id (only `revoke` sees
/// them, which uses equality alone) is 30 zero bytes and a big-endian 16-bit number above 255 (256 plus the number).
pub fn nid(id: &NodeId) -> u32 {
    if id.iter().all(|x| *x == id[0]) {
        return u32::from(id[0]);
    }
    assert!(
        id[..30].iter().all(|x| *x == 0),
        "ids of the traces are 32 equal bytes or wide"
    );
    256 + u32::from(u16::from_be_bytes([id[30], id[31]]))
}

pub fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for x in bytes {
        write!(s, "{x:02x}").unwrap();
    }
    s
}

fn alive(a: Alive) -> u8 {
    a as u8
}

fn entry_json(e: &Entry<'_>) -> String {
    format!(
        "\"m\":{},\"inc\":{},\"ver\":{},\"th\":{}",
        nid(e.member),
        limbs(e.rec.inc),
        e.rec.ver,
        list(&e.rec.thash)
    )
}

fn down_json(d: &Down<'_>) -> String {
    let pr: Vec<String> = d
        .proof
        .probes()
        .iter()
        .map(|p| format!("[{},{}]", p.age_ms, p.path as u8))
        .collect();
    format!(
        "{{\"k\":\"down\",\"m\":{},\"inc\":{},\"sil\":{},\"pr\":[{}]}}",
        nid(d.member),
        limbs(d.inc),
        d.proof.silence_ms,
        pr.join(",")
    )
}

/// A frame in schema F.
pub fn frame_json(f: &Frame<'_>) -> String {
    match f {
        Frame::Hello(h) => format!(
            "{{\"k\":\"hello\",\"inc\":{},\"ver\":{},\"th\":{},\"snap\":{},\"homed\":{}}}",
            limbs(h.rec.inc),
            h.rec.ver,
            list(&h.rec.thash),
            b(h.snap),
            b(h.homed)
        ),
        Frame::Ack => "{\"k\":\"ack\"}".to_owned(),
        Frame::Probe => "{\"k\":\"probe\"}".to_owned(),
        Frame::Delta(e) => format!("{{\"k\":\"delta\",{},\"a\":{}}}", entry_json(e), alive(e.alive)),
        Frame::Snap(s) => {
            let es: Vec<String> = s
                .entries()
                .map(|e| {
                    assert_eq!(e.alive, Alive::Alive);
                    format!("{{{}}}", entry_json(&e))
                })
                .collect();
            format!(
                "{{\"k\":\"snap\",\"partial\":{},\"more\":{},\"es\":[{}]}}",
                b(s.partial),
                b(s.more),
                es.join(",")
            )
        }
        Frame::Down(d) => down_json(d),
        Frame::Other(o) => format!(
            "{{\"k\":\"other\",\"ty\":{},\"topic\":{},\"rest\":{}}}",
            o.ty,
            list(o.topic),
            list(o.rest)
        ),
    }
}

fn route_json(r: &Route) -> String {
    match r {
        Route::Session | Route::Reply => "\"r\":\"s\",\"via\":0".to_owned(),
        Route::Via(x) => format!("\"r\":\"v\",\"via\":{}", nid(x)),
    }
}

fn close_name(r: CloseReason) -> &'static str {
    match r {
        CloseReason::NoAck => "noack",
        CloseReason::Stale => "stale",
        CloseReason::Leave => "leave",
        CloseReason::Revoked => "revoked",
    }
}

fn opt_id(x: Option<&NodeId>) -> String {
    x.map_or_else(|| "[]".to_owned(), |x| format!("[{}]", nid(x)))
}

fn bc_json(c: &Bc) -> String {
    match c {
        Bc::Frame(from, ty, topic, rest) => {
            format!(
                "{{\"k\":\"frame\",\"from\":{},\"ty\":{ty},\"topic\":{},\"rest\":{}}}",
                nid(from),
                list(topic),
                list(rest)
            )
        }
        Bc::Hold(m) => format!("{{\"k\":\"hold\",\"m\":{}}}", nid(m)),
        Bc::Restore(m) => format!("{{\"k\":\"restore\",\"m\":{}}}", nid(m)),
        Bc::Release(m) => format!("{{\"k\":\"release\",\"m\":{}}}", nid(m)),
        Bc::Resub(h) => format!("{{\"k\":\"resub\",\"hub\":{}}}", nid(h)),
        Bc::Primary(old, new) => format!(
            "{{\"k\":\"primary\",\"old\":{},\"new\":{}}}",
            opt_id(old.as_ref()),
            nid(new)
        ),
    }
}

fn event_json(e: &Event) -> String {
    match e {
        Event::MemberJoined { member } => format!("{{\"k\":\"joined\",\"m\":{}}}", nid(member)),
        Event::MemberConfirmedDown { member } => format!("{{\"k\":\"down\",\"m\":{}}}", nid(member)),
        Event::MemberLeft { member } => format!("{{\"k\":\"left\",\"m\":{}}}", nid(member)),
        Event::MemberRevoked { member } => format!("{{\"k\":\"revoked\",\"m\":{}}}", nid(member)),
        Event::AddressChanged { member } => format!("{{\"k\":\"addr\",\"m\":{}}}", nid(member)),
        Event::StackChanged { member, version } => {
            format!("{{\"k\":\"stack\",\"m\":{},\"v\":{version}}}", nid(member))
        }
        Event::ViewChanged { epoch, members } => {
            format!("{{\"k\":\"view\",\"epoch\":{},\"n\":{members}}}", limbs(*epoch))
        }
        Event::Lost { count } => format!("{{\"k\":\"lost\",\"n\":{count}}}"),
    }
}

fn refusal(r: Refusal) -> u8 {
    match r {
        Refusal::NotApplicable => 0,
        Refusal::Unknown => 1,
        Refusal::LeaseFresh => 2,
        Refusal::CarrierOpen => 3,
        Refusal::NotIndependent => 4,
        Refusal::BadProof => 5,
    }
}

fn removal(r: Removal) -> u8 {
    match r {
        Removal::Reported => 0,
        Removal::Left => 1,
        Removal::LeaseExpired => 2,
        Removal::Revoked => 3,
    }
}

fn trace_json(t: &Trace) -> String {
    match t {
        Trace::Started { inc } => format!("{{\"k\":\"started\",\"inc\":{}}}", limbs(*inc)),
        Trace::Incarnation { inc } => format!("{{\"k\":\"incarnation\",\"inc\":{}}}", limbs(*inc)),
        Trace::FrameIn { peer, ty } => format!("{{\"k\":\"frame_in\",\"peer\":{},\"ty\":{ty}}}", nid(peer)),
        Trace::FrameOut { peer, ty } => format!("{{\"k\":\"frame_out\",\"peer\":{},\"ty\":{ty}}}", nid(peer)),
        Trace::BadFrame { peer } => format!("{{\"k\":\"bad_frame\",\"peer\":{}}}", nid(peer)),
        Trace::Attached { member } => format!("{{\"k\":\"attached\",\"member\":{}}}", nid(member)),
        Trace::Pulse { member } => format!("{{\"k\":\"pulse\",\"member\":{}}}", nid(member)),
        Trace::LeaseExpired { member } => format!("{{\"k\":\"lease_expired\",\"member\":{}}}", nid(member)),
        Trace::CarrierGone { member } => format!("{{\"k\":\"carrier_gone\",\"member\":{}}}", nid(member)),
        Trace::ProbeSent { member, path } => {
            let p = match path {
                Path::Session => 0,
                Path::Direct => 1,
                Path::Relay => 2,
            };
            format!("{{\"k\":\"probe_sent\",\"member\":{},\"path\":{p}}}", nid(member))
        }
        Trace::NoIndependentPath { member } => {
            format!("{{\"k\":\"no_independent_path\",\"member\":{}}}", nid(member))
        }
        Trace::Confirmed { member, .. } => format!("{{\"k\":\"confirmed\",\"member\":{}}}", nid(member)),
        Trace::LeaveSeen { member } => format!("{{\"k\":\"leave_seen\",\"member\":{}}}", nid(member)),
        Trace::DownSent { member } => format!("{{\"k\":\"down_sent\",\"member\":{}}}", nid(member)),
        Trace::DownAccepted { member } => format!("{{\"k\":\"down_accepted\",\"member\":{}}}", nid(member)),
        Trace::DownRefused { member, why } => {
            format!(
                "{{\"k\":\"down_refused\",\"member\":{},\"why\":{}}}",
                nid(member),
                refusal(*why)
            )
        }
        Trace::CarrierReturned { member, restored } => {
            format!(
                "{{\"k\":\"carrier_returned\",\"member\":{},\"restored\":{}}}",
                nid(member),
                b(*restored)
            )
        }
        Trace::SelfDelta { hub } => format!("{{\"k\":\"self_delta\",\"hub\":{}}}", nid(hub)),
        Trace::SnapApplied { hub, entries, more } => {
            format!(
                "{{\"k\":\"snap_applied\",\"hub\":{},\"entries\":{entries},\"more\":{}}}",
                nid(hub),
                b(*more)
            )
        }
        Trace::Absent { member } => format!("{{\"k\":\"absent\",\"member\":{}}}", nid(member)),
        Trace::Removed { member, why } => {
            format!(
                "{{\"k\":\"removed\",\"member\":{},\"why\":{}}}",
                nid(member),
                removal(*why)
            )
        }
        Trace::Deferred { member } => format!("{{\"k\":\"deferred\",\"member\":{}}}", nid(member)),
        Trace::Quiet { cause } => {
            let c = match cause {
                QuietCause::LateTimer => 0,
                QuietCause::Heal => 1,
            };
            format!("{{\"k\":\"quiet\",\"cause\":{c}}}")
        }
        Trace::HubStale { hub } => format!("{{\"k\":\"hub_stale\",\"hub\":{}}}", nid(hub)),
        Trace::Primary { hub } => format!("{{\"k\":\"primary\",\"hub\":{}}}", nid(hub)),
        Trace::HelloSuppressed { hub } => format!("{{\"k\":\"hello_suppressed\",\"hub\":{}}}", nid(hub)),
        Trace::SealFailed => "{\"k\":\"seal_failed\"}".to_owned(),
        Trace::Lost { count } => format!("{{\"k\":\"lost\",\"n\":{count}}}"),
    }
}

fn env_json(e: &EnvSnap) -> String {
    let ev: Vec<String> =
        e.ev.iter()
            .map(|(p, v)| {
                format!(
                    "[{},{{\"rx\":{},\"srtt\":{},\"pto\":{},\"inf\":{},\"direct\":{}}}]",
                    nid(p),
                    limbs(v.last_rx),
                    limbs(v.srtt),
                    v.pto,
                    v.inflight,
                    b(v.direct)
                )
            })
            .collect();
    let car: Vec<String> = e
        .car
        .iter()
        .map(|(m, c)| match c {
            Carrier::Open => format!("[{},{{\"k\":\"open\"}}]", nid(m)),
            Carrier::Gone { since, sleep } => format!(
                "[{},{{\"k\":\"gone\",\"since\":{},\"sleep\":{}}}]",
                nid(m),
                limbs(*since),
                opt_limbs(*sleep)
            ),
            Carrier::Unknown => unreachable!("unknown carriers are not listed"),
        })
        .collect();
    let acc: Vec<String> = e.acc.iter().map(|p| nid(p).to_string()).collect();
    let rv: Vec<String> = e.rv.iter().map(|p| nid(p).to_string()).collect();
    let gu: Vec<String> =
        e.gu.iter()
            .map(|(p, v)| format!("[{},{}]", nid(p), limbs(*v)))
            .collect();
    format!(
        "{{\"ev\":[{}],\"car\":[{}],\"acc\":[{}],\"rv\":[{}],\"gu\":[{}],\"ver\":{},\"tk\":{},\"refl\":{},\"pers\":{},\"sealed\":{},\"failseal\":{},\"failunseal\":{},\"floor\":9}}",
        ev.join(","),
        car.join(","),
        acc.join(","),
        rv.join(","),
        gu.join(","),
        e.ver,
        e.tk,
        b(e.refl),
        b(e.pers),
        opt_limbs(e.sealed),
        b(e.failseal),
        b(e.failunseal)
    )
}

fn st_json(s: &StSnap) -> String {
    let members: Vec<String> = s
        .members
        .iter()
        .map(|(m, r)| format!("[{},{},{},{}]", nid(m), limbs(r.inc), r.ver, list(&r.thash)))
        .collect();
    let roster: Vec<String> = s
        .roster
        .iter()
        .map(|(m, t)| format!("[{},{}]", nid(m), limbs(*t)))
        .collect();
    let hu: Vec<String> = s.hubs_up.iter().map(|x| nid(x).to_string()).collect();
    format!(
        "{{\"members\":[{}],\"epoch\":{},\"primary\":{},\"inc\":{},\"roster\":[{}],\"sealfailed\":{},\"maxframe\":{},\"hu\":[{}]}}",
        members.join(","),
        limbs(s.epoch),
        opt_id(s.primary.as_ref()),
        limbs(s.inc),
        roster.join(","),
        b(s.seal_failed),
        limbs(s.max_frame as u64),
        hu.join(",")
    )
}

/// The inputs of a call as the fields of the line.
fn op_json(c: &Call) -> String {
    let now = limbs(c.now);
    match &c.op {
        Op::Start {
            hub,
            hubs,
            wall,
            floor,
            ret,
        } => {
            let hs: Vec<String> = hubs.iter().map(|h| nid(h).to_string()).collect();
            format!(
                "\"op\":\"start\",\"me\":{},\"hub\":{},\"hubs\":[{}],\"now\":{now},\"wall\":{},\"floor\":{},\"ret\":\"{ret}\"",
                c.node + 1,
                b(*hub),
                hs.join(","),
                limbs(*wall),
                limbs(*floor)
            )
        }
        Op::Up { peer, incoming } => {
            format!(
                "\"op\":\"up\",\"peer\":{},\"inc\":{},\"now\":{now}",
                nid(peer),
                b(*incoming)
            )
        }
        Op::Down { peer, code } => format!(
            "\"op\":\"dn\",\"peer\":{},\"code\":{},\"now\":{now}",
            nid(peer),
            limbs(*code)
        ),
        Op::Bytes {
            peer,
            bytes,
            used,
            bad,
            mf,
        } => {
            let mut fs = Vec::new();
            let mut at = 0;
            while let Ok(Some((f, n))) = Frame::read_with(&bytes[at..], *mf) {
                fs.push(format!(
                    "{{\"f\":{},\"hex\":\"{}\"}}",
                    frame_json(&f),
                    hex(&bytes[at..at + n])
                ));
                at += n;
                if fs.len() == vinc_membership::MAX_FRAMES_PER_CALL {
                    break;
                }
            }
            if !*bad {
                assert_eq!(at, *used, "the frames recorded are the bytes the machine used");
            }
            format!(
                "\"op\":\"by\",\"peer\":{},\"now\":{now},\"mf\":{},\"fs\":[{}],\"bad\":{},\"rest\":\"{}\"",
                nid(peer),
                limbs(*mf as u64),
                fs.join(","),
                b(*bad),
                hex(&bytes[at..])
            )
        }
        Op::Timeout => format!("\"op\":\"to\",\"now\":{now}"),
        Op::CarrierGone { member } => format!("\"op\":\"cg\",\"member\":{},\"now\":{now}", nid(member)),
        Op::CarrierReturn { member } => format!("\"op\":\"cr\",\"member\":{},\"now\":{now}", nid(member)),
        Op::Leave => format!("\"op\":\"lv\",\"now\":{now}"),
        Op::Revoke { member, ok } => {
            format!(
                "\"op\":\"rv\",\"member\":{},\"now\":{now},\"ret\":\"{}\"",
                nid(member),
                if *ok { "ok" } else { "full" }
            )
        }
        Op::Moved => format!("\"op\":\"mv\",\"now\":{now}"),
        Op::SnapshotTo { peer } => format!("\"op\":\"sn\",\"peer\":{},\"now\":{now}", nid(peer)),
        Op::SetMaxFrame { max } => format!("\"op\":\"sm\",\"mf\":{},\"now\":{now}", limbs(*max as u64)),
    }
}

fn out_json(c: &Call) -> String {
    let sent: Vec<String> = c
        .sent
        .iter()
        .map(|(to, route, bytes, ok)| {
            let (f, n) = Frame::read(bytes)
                .expect("a sent frame parses")
                .expect("a sent frame is whole");
            assert_eq!(n, bytes.len());
            format!(
                "{{\"to\":{},{},\"f\":{},\"hex\":\"{}\",\"ok\":{}}}",
                nid(to),
                route_json(route),
                frame_json(&f),
                hex(bytes),
                b(*ok)
            )
        })
        .collect();
    let bc: Vec<String> = c.bc.iter().map(bc_json).collect();
    let cl: Vec<String> = c
        .closed
        .iter()
        .map(|(p, r)| format!("[{},\"{}\"]", nid(p), close_name(*r)))
        .collect();
    let ev: Vec<String> = c.events.iter().map(event_json).collect();
    let tr: Vec<String> = c.traces.iter().map(trace_json).collect();
    format!(
        "{{\"sent\":[{}],\"bc\":[{}],\"cl\":[{}],\"ev\":[{}],\"tr\":[{}],\"sealed\":{}}}",
        sent.join(","),
        bc.join(","),
        cl.join(","),
        ev.join(","),
        tr.join(","),
        opt_limbs(c.sealed_after)
    )
}

/// The lines of a recorded world, shared with the scenario that owns the world.
pub type Sink = Rc<RefCell<Vec<String>>>;

/// Records the calls of one world as the lines of run `run`.
pub struct JsonRec {
    pub run: usize,
    pub sink: Sink,
}

impl Recorder for JsonRec {
    fn record(&mut self, c: Call) {
        let line = format!(
            "{{\"t\":\"mem\",\"run\":{},\"n\":{},{},\"env\":{},\"out\":{},\"st\":{}}}",
            self.run,
            c.node,
            op_json(&c),
            env_json(&c.env),
            out_json(&c),
            st_json(&c.st)
        );
        self.sink.borrow_mut().push(line);
    }
}
