//! The random run of the timers trace: seeded random calls on a connected pair.

use vinc_tests::*;
use vinc_transport::conn::PathId;

use crate::duo::{How, app, close, inject, simple, with_pair};
use crate::rec::Log;

/// Random calls on a connected pair.
pub fn random_run(log: &mut Log, seed: u64, steps: usize) {
    with_pair(seed, seed.is_multiple_of(3), |d| {
        let mut rng = SplitMix64::new(seed ^ 0x7469_6d65);
        d.init(log);
        for _ in 0..steps {
            if d.nodes.iter().all(|x| x.conn.is_closed()) && rng.next_u64().is_multiple_of(8) {
                break;
            }
            let n = (rng.next_u64() % 2) as usize;
            match rng.next_u64() % 24 {
                0..=4 => {
                    // time moves on
                    let dt = [MS, 20 * MS, 300 * MS, SEC, 5 * SEC, 20 * SEC, 45 * SEC][(rng.next_u64() % 7) as usize];
                    match rng.next_u64() % 4 {
                        0 => {
                            d.advance_to_next(log);
                        }
                        1 => {
                            // just before the next deadline: nothing of the lifecycle may happen there
                            if let Some(t) = d.next_deadline() {
                                let t = t.div_ceil(1000) * 1000;
                                if t > d.now + 1000 {
                                    d.now = t - 1000;
                                    for m in 0..2 {
                                        d.poll(log, m);
                                        d.timeout(log, m);
                                    }
                                }
                            }
                        }
                        _ => {
                            d.now += dt;
                            d.fire(log);
                        }
                    }
                }
                5..=6 => {
                    d.poll(log, n);
                    d.timeout(log, n);
                }
                7..=9 => {
                    d.tx(log, n);
                }
                10..=13 => {
                    let waiting: Vec<usize> = (0..d.pool.len()).filter(|i| !d.pool[*i].2).collect();
                    if !waiting.is_empty() {
                        let i = waiting[(rng.next_u64() % waiting.len().min(3) as u64) as usize];
                        match rng.next_u64() % 10 {
                            0 => d.pool[i].2 = true,
                            1 => d.deliver(log, i, How::Altered),
                            _ => d.deliver(log, i, How::Fresh),
                        }
                    } else if !d.pool.is_empty() {
                        let i = (rng.next_u64() % d.pool.len() as u64) as usize;
                        d.deliver(log, i, How::Again);
                    }
                }
                14..=15 => {
                    let len = [10, 1000, 30_000][(rng.next_u64() % 3) as usize];
                    app(log, n, &mut d.nodes[n], d.now, len);
                }
                16 => {
                    let op = if d.nodes[n].conn.asleep() { "wake" } else { "sleep" };
                    simple(log, n, &mut d.nodes[n], d.now, op, 0);
                }
                17 => {
                    let down = u64::from(rng.next_u64().is_multiple_of(2));
                    simple(log, n, &mut d.nodes[n], d.now, "link", down);
                }
                18 => {
                    let ka = [0, 5 * SEC, 20 * SEC][(rng.next_u64() % 3) as usize];
                    simple(log, n, &mut d.nodes[n], d.now, "keepalive", ka);
                }
                19 => {
                    let sent = rng.next_u64() % 2;
                    simple(log, n, &mut d.nodes[n], d.now, "pulse", sent);
                }
                20 => {
                    if rng.next_u64().is_multiple_of(12) {
                        close(log, n, &mut d.nodes[n], d.now, rng.next_u64() % 0x50);
                    }
                }
                21 => {
                    if rng.next_u64().is_multiple_of(16) && !d.nodes[n].conn.is_closed() {
                        let path = PathId(if n == 0 { 1 } else { 2 });
                        inject(log, n, &mut d.nodes[n], d.now, path, rng.next_u64().is_multiple_of(2));
                    }
                }
                _ => {
                    d.exchange(log);
                }
            }
        }
    });
}
