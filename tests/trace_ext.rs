//! Trace generation for the extension frame registry and its dispatch (`pinc-transport` `frame/ext.rs`, the endpoint's
//! `Co::Extension` arm in `pinc-core` `events.rs`), recorded as ndjson for the TLA+ trace check (`TraceExt.tla`) and the
//! Lean replay (`Pinc/TraceExt.lean`).
//!
//! The registry is read from the code (`ASSIGNED` and the constants) and recorded once. Then pairs of real endpoints
//! on a simulated link carry one extension frame at a time: every registered type, types between and beyond them (one,
//! two, four and eight bytes of varint), bodies of length 0, 1, 2, 100, the longest `REACH_OUT` body, one more, and
//! 1100, to a session the access check allowed and to one it has not. For each frame the receiving endpoint is
//! observed: the frames `read_extension` gives (the application ring), the `ReachOut` events and the body `Query`
//! gives for them. A real second protocol dialled over a session is the sub-session open: the child it accepts is
//! recorded.
//!
//! Two files are written: `ext.ndjson` holds the events whose numbers stay below 2^28 (the TLA+ checker has 32-bit
//! integers), `ext_wide.ndjson` every event.
//!
//! The test checks each observation against a naive reading of the dispatch, so it is meaningful without the proof
//! tools: a frame lands in the ring exactly when its type is neither the sub-session open nor `REACH_OUT`, its body is
//! not empty and the session is allowed, and what lands is the type and the body sent; a `REACH_OUT` event comes
//! exactly with a body of 1 to 153 bytes.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::too_many_arguments,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::many_single_char_names,
    unreachable_pub
)]

use pinc_core::{Answer, Command, EXT_BODY_MAX, Event, Query, REACH_BODY_MAX, Role, SessionId};
use pinc_tests::*;
use pinc_transport::frame::{EXTENSION_BASE, ext};

pinc_tests::install_counting_allocator!();

const NARROW: u64 = 1 << 28;

#[derive(Default)]
struct Out {
    narrow: String,
    wide: String,
    ring: usize,
    reach: usize,
    dropped_unallowed: usize,
    types: std::collections::BTreeSet<u64>,
}

impl Out {
    fn push(&mut self, narrow: bool, line: &str) {
        self.wide.push_str(line);
        self.wide.push('\n');
        if narrow {
            self.narrow.push_str(line);
            self.narrow.push('\n');
        }
    }
}

fn body_of(len: usize, seed: u8) -> Vec<u8> {
    (0..len).map(|i| seed.wrapping_add((i % 251) as u8)).collect()
}

/// Send one frame from `a` to `b` and say what `b` did with it.
fn frame(
    net: &mut CoreNet,
    a: usize,
    b: usize,
    sa: SessionId,
    sb: SessionId,
    ty: u64,
    len: usize,
    allowed: bool,
    out: &mut Out,
) {
    let body = body_of(len, ty as u8);
    let mark = net.nodes[b].events.len();
    let now = net.now;
    if net.nodes[a]
        .cmd(
            now,
            Command::SendExtension {
                session: sa,
                ty,
                body: &body,
            },
        )
        .is_err()
    {
        return;
    }
    net.run_for(300 * MS_NS);
    let reach_events = net.nodes[b].events[mark..]
        .iter()
        .filter(|(_, e)| matches!(e, Event::ReachOut { session } if *session == sb))
        .count();
    let rlen = match net.nodes[b].ep.query(Query::ReachOut(sb)) {
        Answer::ReachOut(held) if reach_events > 0 => {
            assert_eq!(held, &body[..], "the REACH_OUT body kept is the body sent");
            held.len() as i64
        }
        _ => -1,
    };
    let mut got = Vec::new();
    let mut buf = vec![0u8; EXT_BODY_MAX];
    while let Some((s, t, l)) = net.nodes[b].ep.read_extension(&mut buf).unwrap() {
        assert_eq!(s, sb);
        assert_eq!(&buf[..l], &body[..], "the frame the ring gives is the body sent");
        got.push((t, l));
    }
    // a naive reading of the dispatch
    let want_ring = ty != ext::SUB_SESSION_OPEN && ty != ext::REACH_OUT && len > 0 && allowed;
    let want_reach = ty == ext::REACH_OUT && len > 0 && len <= REACH_BODY_MAX;
    assert_eq!(
        got.len(),
        usize::from(want_ring),
        "ring: ty {ty:#x} len {len} allowed {allowed}: {got:?}"
    );
    if want_ring {
        assert_eq!(got[0], (ty, len));
    }
    assert_eq!(reach_events, usize::from(want_reach), "reach: ty {ty:#x} len {len}");
    out.ring += got.len();
    out.reach += reach_events;
    if !allowed && len > 0 && ty != ext::SUB_SESSION_OPEN && ty != ext::REACH_OUT {
        out.dropped_unallowed += 1;
    }
    out.types.insert(ty);
    let (rty, rl) = got.first().map_or((-1i64, -1i64), |&(t, l)| (t as i64, l as i64));
    let line = format!(
        r#"{{"t":"txex","op":"route","ty":{ty},"len":{len},"allowed":{allowed},"ring":{},"rty":{rty},"rlen":{rl},"reach":{reach_events},"reachlen":{rlen}}}"#,
        got.len()
    );
    out.push(ty < NARROW, &line);
}

const TYPES: [u64; 24] = [
    0x40,
    0x41,
    0x42,
    0x43,
    0x44,
    0x45,
    0x48,
    0x49,
    0x4a,
    0x4e,
    0x4f,
    0x50,
    0x7f,
    0x80,
    0x3fff,
    0x4000,
    0x4040,
    0x1_0000,
    0x0fff_ffff,
    0x1000_0000,
    0x3fff_ffff,
    0x4000_0000,
    0x1_0000_0000,
    0x3fff_ffff_ffff_ffff,
];
const LENS: [usize; 8] = [0, 1, 2, 100, REACH_BODY_MAX, REACH_BODY_MAX + 1, 1100, 3];

#[test]
fn extension_frames_reach_the_layer_that_registered_their_type() {
    big_stack(|| {
        let mut out = Out::default();
        // the registry as the code has it
        let assigned: Vec<String> = ext::ASSIGNED.iter().map(|(a, b)| format!("[{a},{b}]")).collect();
        let line = format!(
            r#"{{"t":"txex","op":"tbl","base":{EXTENSION_BASE},"sub":{},"reach":{},"reachmax":{REACH_BODY_MAX},"proofreq":{},"proof":{},"testfirst":{},"testlast":{},"assigned":[{}]}}"#,
            ext::SUB_SESSION_OPEN,
            ext::REACH_OUT,
            ext::PROOF_REQ,
            ext::PROOF,
            ext::TEST_FIRST,
            ext::TEST_LAST,
            assigned.join(",")
        );
        out.push(true, &line);

        // allowed sessions: every type with every length
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        for &ty in &TYPES {
            for &len in &LENS {
                frame(&mut net, a, b, sa, sb, ty, len, true, &mut out);
            }
        }
        // a second protocol over the session is a sub-session open: it makes a child, and nothing reaches the ring
        let before = net.nodes[b].count(|e| matches!(e, Event::Incoming { .. }));
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        net.nodes[a].connect(now, peer, ALPN_B, to, Role::Other).unwrap();
        net.run_for(2 * SEC_NS);
        let child = net.nodes[b].count(|e| matches!(e, Event::Incoming { .. })) - before;
        assert_eq!(child, 1, "the sub-session open made one child");
        let mut buf = vec![0u8; EXT_BODY_MAX];
        assert!(
            net.nodes[b].ep.read_extension(&mut buf).unwrap().is_none(),
            "the open is not for the ring"
        );
        out.push(
            true,
            &format!(r#"{{"t":"txex","op":"sub","child":{child},"ring":0,"reach":0}}"#),
        );

        // sessions the access check has not allowed: a frame to the ring is dropped, the endpoint's own frames are not
        for &ty in &TYPES {
            let mut net = CoreNet::new(10 * MS_NS);
            let (a, b) = (net.add(1), net.add(2));
            net.nodes[b].acp = Acp::Manual;
            let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
            let rep = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
            let sa = net.nodes[a].session(&rep);
            assert!(net.run(
                now + 5 * SEC_NS,
                |n| n.nodes[a].saw(|e| matches!(e, Event::Connected { .. })) && !n.nodes[b].checks.is_empty()
            ));
            let sb = net.nodes[b].ep.sessions().next().unwrap();
            for len in [0usize, 1, 100, REACH_BODY_MAX, 1100] {
                frame(&mut net, a, b, sa, sb, ty, len, false, &mut out);
            }
        }

        assert!(out.ring > 100, "ring {}", out.ring);
        assert!(out.reach >= 8, "reach {}", out.reach);
        assert!(out.dropped_unallowed > 50, "dropped {}", out.dropped_unallowed);
        assert!(out.types.len() >= 20);
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("ext.ndjson"), &out.narrow).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("ext_wide.ndjson"), &out.wide).unwrap();
        }
    });
}
