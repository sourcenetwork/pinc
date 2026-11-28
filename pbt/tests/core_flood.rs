//! `pinc-core`: two honest endpoints with an established session, and an unauthenticated third party that floods
//! either of them with what it can make: real datagrams of the session captured on the way and then cut, bit-flipped,
//! replayed, reflected, sent from another address; first flights of handshakes that never finish (whole and in
//! fragments); pure garbage. Some of those datagrams come from addresses that never answer (a spoofed source).
//!
//! Where the expected behaviour comes from:
//! - `pinc_core` (lib.rs): "never panics on input. Every table has a fixed bound." The bounds checked after every
//!   step are those of `core_harness::Host::check_stats` (sessions, half-open, event queue, held fragments, ledger,
//!   owed sessions, counters).
//! - `pinc_core::Ledger` (ledger.rs): "an address that wrote to us first is held to three times the bytes it sent
//!   until it answers something we sent it ... so a spoofed source gets at most three times what it sent". An address
//!   that never receives anything cannot answer, so every byte (with 28 bytes of headers a datagram) the endpoint
//!   sends to it is at most three times what came from it.
//! - api.rs: an event names a session "which is never reused"; commands.rs: a `Closed` is a session's last event.
//! - Universal: the third party holds no key of the session, so it cannot end it, change its bytes or add any: the
//!   bytes each side reads on the stream are exactly the bytes the other wrote, with the end, once the flood stops.

mod core_harness;

use std::net::SocketAddr;

use core_harness::{
    ALPN_A, Edit, HostCfg, MS, Net, SEC, Violation, apply_edit, big_stack, ghost_flights,
};
use ephyra::{check_generator, gens};
use pinc_core::{Command, Value};

/// The addresses the attacker forges; nobody lives at them and nothing sent to them is ever read.
fn spoof(i: u8) -> SocketAddr {
    ([192, 0, 2, 1 + (i % 8)], 7000 + u16::from(i % 3)).into()
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Attack {
    /// Milliseconds pass.
    Wait(
        #[ephyra(gen = gens::frequency(vec![
            (6, gens::int(0u16..=60).boxed()),
            (2, gens::int(0u16..=2_000).boxed()),
            (1, gens::int(0u16..=40_000).boxed()),
        ]))]
        u16,
    ),
    /// Noise to host 0 or 1, from a forged address, with a first byte that looks like a header now and then.
    Garbage(
        #[ephyra(gen = gens::int(0u8..=1))] u8,
        #[ephyra(gen = gens::int(0u8..=15))] u8,
        #[ephyra(gen = pinc_pbt::bytes(1400))] Vec<u8>,
        #[ephyra(gen = gens::int(0u8..=6))] u8,
    ),
    /// A captured datagram of the honest pair again (which one; where from: 0 its sender, 1 its receiver as the
    /// source of a reflection, 2.. a forged address; edits).
    Replay(
        u16,
        #[ephyra(gen = gens::int(0u8..=12))] u8,
        #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(0..=3))] Vec<Edit>,
    ),
    /// A first flight of a handshake that never finishes (a ghost dialer's datagram), from a forged address.
    Ghost(
        u16,
        #[ephyra(gen = gens::int(0u8..=15))] u8,
        #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(0..=2))] Vec<Edit>,
    ),
    /// One captured datagram many times from many forged addresses at once.
    Burst(u16, #[ephyra(gen = gens::int(1u8..=40))] u8),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Case {
    seed: u64,
    /// The first flights of the honest pair and of the ghosts are cut in minimum-size datagrams.
    split: bool,
    #[ephyra(gen = gens::int(0u64..=20))]
    jitter_ms: u64,
    #[ephyra(gen = gens::frequency(vec![(3, gens::int(0usize..=3_000).boxed()), (1, gens::int(0usize..=60_000).boxed())]))]
    len_a: usize,
    #[ephyra(gen = gens::int(0usize..=3_000))]
    len_b: usize,
    #[ephyra(gen = gens::vec(ephyra::any::<Attack>()).len(0..=40))]
    attacks: Vec<Attack>,
}

fn payload(len: usize, salt: u8) -> Vec<u8> {
    (0..len).map(|i| (i as u8).wrapping_mul(31).wrapping_add(salt) ^ (i >> 8) as u8).collect()
}

fn fail(v: Option<Violation>) {
    if let Some(v) = v {
        ephyra::signature(v.sig);
        panic!("{}: {}", v.sig, v.detail);
    }
}

fn run(c: &Case) {
    let mut net = Net::new(c.seed);
    net.faults.jitter = c.jitter_ms * MS;
    let cfg = HostCfg {
        split: c.split,
        ..HostCfg::default()
    };
    let (a, b) = (net.add(1, cfg), net.add(2, cfg));
    let Some((sa, sb)) = net.connect_pair(a, b, ALPN_A) else {
        fail(net.first_violation());
        panic!("the honest pair did not connect on a clean link");
    };
    net.run_for(300 * MS);
    let now = net.now;
    let Ok(core_harness::Reply2 { value: Value::Stream(st_a) }) =
        net.hosts[a].cmd(now, Command::OpenStream { session: sa, bidi: true })
    else {
        panic!("no stream on a fresh session")
    };
    let Ok(core_harness::Reply2 { value: Value::Stream(st_b) }) =
        net.hosts[b].cmd(now, Command::OpenStream { session: sb, bidi: true })
    else {
        panic!("no stream on a fresh session")
    };
    let (pa, pb) = (payload(c.len_a, 3), payload(c.len_b, 7));
    net.hosts[a].write(now, sa, st_a, pa.clone(), true);
    net.hosts[b].write(now, sb, st_b, pb.clone(), true);
    let targets = [(net.hosts[a].addr, net.hosts[a].id), (net.hosts[b].addr, net.hosts[b].id)];
    let ghosts = ghost_flights(net.now, &targets, c.split);

    for at in &c.attacks {
        match at {
            Attack::Wait(ms) => net.run_for(u64::from(*ms) * MS),
            Attack::Garbage(to, from, bytes, first) => {
                let mut d = bytes.clone();
                if let Some(f) = d.first_mut() {
                    *f = [*f, 0x40, 0x41, 0xC0, 0xC1, 0xE0, 0x00][usize::from(*first)];
                }
                let to = targets[usize::from(*to)].0;
                net.deliver(spoof(*from), to, d);
            },
            Attack::Replay(pick, src, edits) => {
                if net.captured.is_empty() {
                    continue;
                }
                let (from, to, mut d) = net.captured[usize::from(*pick) % net.captured.len()].clone();
                for e in edits {
                    apply_edit(&mut d, *e);
                }
                let from = match src {
                    0 => from,
                    1 => to,
                    s => spoof(*s),
                };
                net.deliver(from, to, d);
            },
            Attack::Ghost(pick, from, edits) => {
                if ghosts.is_empty() {
                    continue;
                }
                let (t, mut d) = ghosts[usize::from(*pick) % ghosts.len()].clone();
                for e in edits {
                    apply_edit(&mut d, *e);
                }
                net.deliver(spoof(*from), targets[t].0, d);
            },
            Attack::Burst(pick, n) => {
                if net.captured.is_empty() {
                    continue;
                }
                let (_, to, d) = net.captured[usize::from(*pick) % net.captured.len()].clone();
                for i in 0..*n {
                    net.deliver(spoof(i), to, d.clone());
                }
            },
        }
        net.pump_all();
        net.check();
        if net.first_violation().is_some() {
            break;
        }
    }
    fail(net.first_violation());

    // The flood is over: the transfer completes on its own.
    let deadline = net.now + 90 * SEC;
    net.run(deadline, |n| n.hosts[b].fin.contains(&(sb, st_a)) && n.hosts[a].fin.contains(&(sa, st_b)));
    fail(net.first_violation());
    let (ha, hb) = (&net.hosts[a], &net.hosts[b]);
    // keepalive.rs: "a plain session stops this 90 s after the application's last data and is left to lapse at the
    // idle timeout": a session that lapsed after the transfer ended (both ends arrived) closed on its own.
    let lapsed = |h: &core_harness::Host, s| {
        h.events.iter().any(|(_, e)| {
            matches!(e, pinc_core::Event::Closed { session, reason: pinc_core::EndReason::Transport(pinc_transport::conn::CloseReason::IdleTimeout) } if *session == s)
        })
    };
    let ended = hb.fin.contains(&(sb, st_a)) && ha.fin.contains(&(sa, st_b));
    let gone = |h: &core_harness::Host, s| h.closed.contains(&s) && !(ended && lapsed(h, s));
    assert!(!gone(ha, sa) && !gone(hb, sb), "a third party ended the honest session: {:?} / {:?}", ha.events.iter().rev().take(4).collect::<Vec<_>>(), hb.events.iter().rev().take(4).collect::<Vec<_>>());
    let got_a = hb.read.get(&(sb, st_a)).cloned().unwrap_or_default();
    assert!(got_a == pa, "the bytes read differ from the bytes written: read {} of {}", got_a.len(), pa.len());
    let got_b = ha.read.get(&(sa, st_b)).cloned().unwrap_or_default();
    assert!(got_b == pb, "the bytes read the other way differ: read {} of {}", got_b.len(), pb.len());
    assert!(hb.fin.contains(&(sb, st_a)) && ha.fin.contains(&(sa, st_b)), "a stream end never arrived");
    let extra = hb.read.keys().chain(ha.read.keys()).filter(|k| **k != (sb, st_a) && **k != (sa, st_b)).count();
    assert!(extra == 0, "bytes arrived on a stream nobody wrote");
    assert!(ha.count(|e| matches!(e, pinc_core::Event::Connected { session, .. } if *session == sa)) == 1);
    for ((h, to), sent) in &net.sent_to {
        if matches!(to.ip(), std::net::IpAddr::V4(v4) if v4.octets()[..3] == [192, 0, 2]) {
            let got = net.got_from.get(&(*h, *to)).copied().unwrap_or(0);
            assert!(*sent <= 3 * got, "host {h} sent {sent} bytes to the forged address {to}, which sent {got}");
        }
    }
}

fn in_support(c: &Case) -> bool {
    c.attacks.len() <= 40 && c.jitter_ms <= 20 && c.len_a <= 60_000
}

#[test]
fn a_flood_from_a_third_party_bounds_every_table_and_leaves_the_session_intact() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(60)
            .name("a_flood_from_a_third_party_bounds_every_table_and_leaves_the_session_intact");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run(&c)).assert_passed();
    });
}

#[test]
fn the_flood_case_generator_stays_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    check_generator(&cfg, ephyra::any::<Case>(), in_support).assert_passed();
}
