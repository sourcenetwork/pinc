//! A sender whose acknowledgements arrive late or in bursts, with nothing lost on the path, must finish its transfer
//! and not mistake delay for loss: no probe timeout climbs and no packet is declared lost.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::PathId;

const STREAMS: usize = 16;
const PER_STREAM: usize = 1024 * 1024;

/// What one run showed on the sender.
#[derive(Debug)]
struct Outcome {
    done: bool,
    took_ms: u64,
    max_pto: u32,
    lost: u64,
    ptos: u64,
}

/// Many streams from A over a clean link. Both directions are held `hold` ns in alternating `window` ns stretches
/// (0: never), and every handled or sent datagram costs `cost` ns of virtual CPU time.
fn run(hold: u64, window: u64, cost: u64, stale: bool) -> Outcome {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let base = Params::new(5_000);
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, base));
        assert!(net.connect(net.now + 10 * SEC));
        net.cost_ns = cost;
        net.stale_clock = stale;
        // One-way streams, opened as the peer's credit allows: each frees its place when it is read to its end.
        let mut ids: Vec<u64> = Vec::with_capacity(STREAMS);
        let data = pattern(PER_STREAM, 3);
        let mut off = [0usize; STREAMS];
        let mut fin = [false; STREAMS];
        let start = net.now;
        let mut held = false;
        let mut max_pto = 0;
        let done = net.run(start + 20 * SEC, |n| {
            let on = hold > 0 && ((n.now - start) / window).is_multiple_of(2);
            if on != held {
                let p = if on { Params::new(base.delay_ns + hold) } else { base };
                n.link.set(PathId(1), p, p);
                held = on;
            }
            // Write while anything moves, as an application woken by every writable event would.
            loop {
                let mut wrote = false;
                while ids.len() < STREAMS {
                    let Ok(id) = n.a.open_uni() else { break };
                    ids.push(id);
                    wrote = true;
                }
                for (i, id) in ids.iter().enumerate() {
                    while off[i] < data.len() {
                        let k = n.a.write(*id, &data[off[i]..]).unwrap();
                        if k == 0 {
                            break;
                        }
                        off[i] += k;
                        wrote = true;
                    }
                    if off[i] == data.len() && !fin[i] {
                        n.a.conn.finish(*id).unwrap();
                        fin[i] = true;
                        wrote = true;
                    }
                }
                max_pto = max_pto.max(n.a.conn.recovery().pto_count());
                if !n.flush() && !wrote {
                    break;
                }
            }
            ids.len() == STREAMS && ids.iter().all(|id| n.b.fin.contains(id))
        });
        let st = net.a.conn.stats();
        Outcome {
            done,
            took_ms: (net.now - start) / MS,
            max_pto,
            lost: st.packets_lost,
            ptos: st.ptos,
        }
    })
}

#[test]
fn held_datagrams_are_delay_not_loss() {
    for hold_ms in [5u64, 10, 25, 50] {
        for window_ms in [10u64, 30, 100] {
            let o = run(hold_ms * MS, window_ms * MS, 0, false);
            eprintln!("hold {hold_ms} ms window {window_ms} ms: {o:?}");
            assert!(o.done, "hold {hold_ms} ms window {window_ms} ms did not finish: {o:?}");
        }
    }
}

/// The single-thread shape: a window-sized burst occupies a stretch of time and the peer's acknowledgements come
/// back in bursts.
#[test]
fn cpu_bursts_do_not_stall_or_lose() {
    for cost_us in [2u64, 5, 10, 20, 50, 100, 200] {
        let o = run(0, MS, cost_us * 1000, false);
        eprintln!("cost {cost_us} us: {o:?}");
        assert!(o.done, "cost {cost_us} us did not finish: {o:?}");
        assert_eq!(
            o.lost, 0,
            "cost {cost_us} us: packets declared lost on a clean link: {o:?}"
        );
        assert_eq!(o.ptos, 0, "cost {cost_us} us: probe timeouts on a clean link: {o:?}");
        assert_eq!(
            o.max_pto, 0,
            "cost {cost_us} us: probe count climbed on a clean link: {o:?}"
        );
        // 16 MiB takes about 26 ms of virtual time per microsecond of cost per datagram when nothing stalls.
        assert!(o.took_ms < 60 * cost_us, "cost {cost_us} us: too slow, a stall: {o:?}");
    }
}

/// The same, with a clock read once per wake: a burst is stamped with the time it began.
#[test]
fn stale_clock_bursts_do_not_stall_or_lose() {
    for cost_us in [2u64, 5, 10, 20, 50, 100, 200] {
        let o = run(0, MS, cost_us * 1000, true);
        eprintln!("stale cost {cost_us} us: {o:?}");
        assert!(o.done, "cost {cost_us} us did not finish: {o:?}");
        assert_eq!(
            o.lost, 0,
            "cost {cost_us} us: packets declared lost on a clean link: {o:?}"
        );
        assert_eq!(o.ptos, 0, "cost {cost_us} us: probe timeouts on a clean link: {o:?}");
        assert_eq!(
            o.max_pto, 0,
            "cost {cost_us} us: probe count climbed on a clean link: {o:?}"
        );
        // 16 MiB takes about 26 ms of virtual time per microsecond of cost per datagram when nothing stalls.
        assert!(o.took_ms < 60 * cost_us, "cost {cost_us} us: too slow, a stall: {o:?}");
    }
}
