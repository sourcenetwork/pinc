//! Every gate, a pass and a fail.

use std::rc::Rc;

use vinc_sim::suite::grade::fixture::blank_world;
use vinc_sim::suite::grade::{GATES, GateReport, GateStatus, RunFacts, evaluate_gates, gate_det};
use vinc_sim::suite::rec::{IntentMeta, MemberEvent, MustArg, Rec};
use vinc_sim::suite::world::model::{Change, ChangeKind, Cut, IntentKind, Param, World};

use crate::common::*;

// ----------------------------------------------------------------------------------------------- gates

/// Runs a clean three-node, 600 s recording through `edit` and grades it.
fn gates_of(world_edit: impl FnOnce(&mut World), edit: impl FnOnce(&mut Rec, &mut RunFacts)) -> GateReport {
    let mut w = blank_world("S2", 3, DUR);
    world_edit(&mut w);
    let world = Rc::new(w);
    let mut rec = Rec::new(world.clone());
    let mut facts = RunFacts::new(&world);
    for i in 0..3 {
        rec.node_started(i, 0);
        facts.nodes[i].view = Some((1, (0..3).filter(|&j| j != i).collect()));
    }
    edit(&mut rec, &mut facts);
    rec.finish(DUR, 0.0, rec.punched_paths);
    evaluate_gates(&world, &rec, &facts)
}

fn clean() -> GateReport {
    gates_of(|_| {}, |_, _| {})
}

fn failed(r: &GateReport) -> Vec<&'static str> {
    r.failed()
}

fn fail_msgs(r: &GateReport, g: &str) -> Vec<String> {
    match r.status(g) {
        Some(GateStatus::Fail(m)) => m.clone(),
        other => panic!("{g} is {other:?}"),
    }
}

fn meta_to(to: usize) -> IntentMeta {
    IntentMeta {
        to: Some(to),
        ..IntentMeta::default()
    }
}

#[test]
fn a_clean_run_passes_every_gate_it_applies_to() {
    let r = clean();
    assert_eq!(r.gates.len(), GATES.len());
    for (g, s) in &r.gates {
        let expect = match *g {
            "G-DET" => GateStatus::Pending,
            "G-SIZE" | "G-NOPUNCH" => GateStatus::NotApplicable,
            _ => GateStatus::Pass,
        };
        assert_eq!(*s, expect, "{g}");
    }
    assert!(r.all_clear());
}

#[test]
fn g_det_compares_two_trace_hashes() {
    assert_eq!(gate_det("ab", "ab"), GateStatus::Pass);
    assert!(matches!(gate_det("ab", "ac"), GateStatus::Fail(_)));
}

#[test]
fn g_int_fails_on_recorded_integrity_and_on_an_undelivered_must_fetch() {
    let r = gates_of(|_| {}, |rec, _| rec.integrity_violation(5, 1, "corrupted bytes"));
    assert_eq!(failed(&r), vec!["G-INT"]);
    assert_eq!(fail_msgs(&r, "G-INT"), vec!["corrupted bytes".to_owned()]);
    let r = gates_of(
        |_| {},
        |rec, _| {
            rec.intent(
                IntentKind::Fetch,
                1,
                sec(5),
                sec(500),
                &[1],
                100,
                MustArg::Flag(true),
                IntentMeta::default(),
            );
        },
    );
    assert_eq!(failed(&r), vec!["G-INT", "G-LIVE"]);
    let r = gates_of(
        |_| {},
        |rec, _| {
            let i = rec.intent(
                IntentKind::Fetch,
                1,
                sec(5),
                sec(500),
                &[1],
                100,
                MustArg::Flag(true),
                IntentMeta::default(),
            );
            rec.delivered(i, 1, sec(9), 0);
        },
    );
    assert!(failed(&r).is_empty());
}

#[test]
fn g_live_counts_a_late_delivery_as_undelivered() {
    let run = |at: u64| {
        gates_of(
            |_| {},
            |rec, _| {
                let i = rec.intent(
                    IntentKind::Publish,
                    0,
                    sec(10),
                    sec(20),
                    &[1, 2],
                    5,
                    MustArg::Flag(true),
                    IntentMeta::default(),
                );
                rec.delivered(i, 1, sec(11), 5);
                rec.delivered(i, 2, at, 5);
            },
        )
    };
    assert!(failed(&run(sec(20))).is_empty(), "exactly at the deadline is on time");
    let r = run(sec(20) + 1);
    assert_eq!(failed(&r), vec!["G-LIVE"]);
    assert!(fail_msgs(&r, "G-LIVE")[0].starts_with("publish intents undelivered"));
    // a never delivered docsync names its own kind
    let r = gates_of(
        |_| {},
        |rec, _| {
            rec.intent(
                IntentKind::Docsync,
                0,
                sec(10),
                sec(20),
                &[1],
                5,
                MustArg::Flag(true),
                meta_to(1),
            );
        },
    );
    assert!(fail_msgs(&r, "G-LIVE")[0].starts_with("docsync intents undelivered"));
}

#[test]
fn g_order_needs_consecutive_sequences_and_every_must_push() {
    let seqs = |s: &'static [u64]| {
        gates_of(
            |_| {},
            move |rec, _| {
                for &x in s {
                    rec.pushlog_delivered(0, 1, x);
                }
            },
        )
    };
    assert!(failed(&seqs(&[1, 2, 3])).is_empty());
    assert_eq!(failed(&seqs(&[1, 3])), vec!["G-ORDER"]);
    assert_eq!(failed(&seqs(&[1, 1])), vec!["G-ORDER"]);
    let r = gates_of(
        |_| {},
        |rec, _| {
            rec.intent(
                IntentKind::Push,
                0,
                sec(5),
                sec(50),
                &[1],
                5,
                MustArg::Flag(true),
                IntentMeta::default(),
            );
        },
    );
    assert_eq!(failed(&r), vec!["G-ORDER", "G-LIVE"]);
}

#[test]
fn g_connect_allows_the_longer_of_thirty_seconds_and_the_deadline() {
    let run = |deadline: u64, connect_after: Option<u64>| {
        gates_of(
            |_| {},
            move |rec, _| {
                let i = rec.intent(
                    IntentKind::Echo,
                    0,
                    sec(10),
                    sec(10) + deadline,
                    &[],
                    32,
                    MustArg::Flag(true),
                    meta_to(1),
                );
                if let Some(c) = connect_after {
                    rec.echo_connected(i, sec(10) + c);
                }
            },
        )
    };
    assert!(failed(&run(sec(30), Some(sec(30)))).is_empty());
    assert_eq!(failed(&run(sec(30), Some(sec(30) + 1))), vec!["G-CONNECT"]);
    assert!(
        failed(&run(sec(120), Some(sec(100)))).is_empty(),
        "the intent deadline stretches the allowance"
    );
    assert_eq!(failed(&run(sec(30), None)), vec!["G-CONNECT"]);
}

#[test]
fn g_size_applies_to_s11_only() {
    let s11 = |edit: fn(&mut Rec, &mut RunFacts)| {
        gates_of(
            |w| w.id = "S11".to_owned(),
            move |rec, f| {
                let i = rec.intent(
                    IntentKind::Fetch,
                    1,
                    sec(5),
                    sec(500),
                    &[1],
                    100,
                    MustArg::Flag(true),
                    IntentMeta::default(),
                );
                rec.delivered(i, 1, sec(9), 0);
                edit(rec, f);
            },
        )
    };
    assert_eq!(s11(|_, _| {}).status("G-SIZE"), Some(&GateStatus::Pass));
    let r = s11(|rec, _| rec.state_sample(sec(5), 1, 64 * 1024 * 1024 + 1));
    assert!(failed(&r).contains(&"G-SIZE"));
    let r = s11(|_, f| f.nodes[1].state_peak = 65 * 1024 * 1024);
    assert!(failed(&r).contains(&"G-SIZE"), "a host-observed peak counts as well");
    let r = gates_of(
        |w| w.id = "S11".to_owned(),
        |rec, _| {
            rec.intent(
                IntentKind::Fetch,
                1,
                sec(5),
                sec(500),
                &[1],
                100,
                MustArg::Flag(true),
                IntentMeta::default(),
            );
        },
    );
    assert_eq!(
        fail_msgs(&r, "G-SIZE"),
        vec!["a value size class did not complete".to_owned()]
    );
    assert_eq!(clean().status("G-SIZE"), Some(&GateStatus::NotApplicable));
}

#[test]
fn g_sec_failure_modes() {
    let one = |edit: fn(&mut Rec, &mut RunFacts), msg: &str| {
        let r = gates_of(|_| {}, edit);
        assert_eq!(failed(&r), vec!["G-SEC"], "{msg}");
        assert!(fail_msgs(&r, "G-SEC")[0].contains(msg), "{msg}");
    };
    one(|_, f| f.sec.hndl_known_payload_keys = 1, "harvest-now-decrypt-later");
    one(|_, f| f.sec.forward_secrecy_broken = 1, "forward secrecy");
    one(|rec, _| rec.wire(0, 5, 100, false, true, false, 0, None), "plaintext");
    one(|_, f| f.sec.plaintext_payload.push((1, 5)), "plaintext");
    one(|_, f| f.sec.nonce_reuse = 1, "nonce reused");
    one(
        |rec, _| rec.violation(5, "G-SEC", 0, "origin mismatch"),
        "origin mismatch",
    );
    // amplification: more than 3x the bytes received from a spoofed address
    let amp = |rx: u64, tx: u64| {
        gates_of(
            |_| {},
            move |rec, _| {
                rec.amp_probe(0, addr(9));
                rec.udp_received(0, 5, addr(9), rx, 0);
                rec.wire(0, 6, tx, false, false, false, 0, Some(addr(9)));
            },
        )
    };
    assert!(failed(&amp(10, 30)).is_empty());
    assert_eq!(failed(&amp(10, 31)), vec!["G-SEC"]);
    assert!(failed(&amp(0, 3)).is_empty(), "received counts as at least 1");
    assert_eq!(failed(&amp(0, 4)), vec!["G-SEC"]);
}

#[test]
fn g_sec_is_not_evaluated_when_key_provenance_is_unknown() {
    let r = gates_of(|_| {}, |_, f| f.sec.unknown_provenance = 2);
    assert!(matches!(r.status("G-SEC"), Some(GateStatus::NotEvaluated(_))));
    assert!(!r.all_clear());
    assert_eq!(r.not_evaluated().len(), 1);
    // a definite failure still wins
    let r = gates_of(
        |_| {},
        |_, f| {
            f.sec.unknown_provenance = 2;
            f.sec.nonce_reuse = 1;
        },
    );
    assert_eq!(failed(&r), vec!["G-SEC"]);
}

#[test]
fn g_acp_fails_on_delivery_without_an_allow_answer() {
    let r = gates_of(|_| {}, |rec, _| assert!(!rec.check_acp_delivery(sec(5), 0, 1)));
    assert_eq!(failed(&r), vec!["G-ACP"]);
    let r = gates_of(
        |_| {},
        |rec, _| {
            rec.acp_decide(sec(4), 0, Some(1));
            assert!(rec.check_acp_delivery(sec(5), 0, 1));
        },
    );
    assert!(failed(&r).is_empty());
    let r = gates_of(
        |w| w.denied = vec![1],
        |rec, _| assert!(!rec.check_acp_delivery(sec(5), 0, 1)),
    );
    assert_eq!(failed(&r), vec!["G-ACP"]);
}

#[test]
fn g_nopunch_follows_the_reference_evaluation_order() {
    let np = |w: &mut World| {
        w.params.insert("no_punch".to_owned(), Param::Bool(true));
    };
    let r = gates_of(np, |_, _| {});
    assert_eq!(r.status("G-NOPUNCH"), Some(&GateStatus::Pass));
    let r = gates_of(np, |rec, _| rec.punched_paths = 1);
    assert_eq!(failed(&r), vec!["G-NOPUNCH"]);
    // a gate decided earlier in the evaluation order (here G-INT) also fails G-NOPUNCH
    let r = gates_of(np, |rec, _| rec.integrity_violation(5, 0, "x"));
    assert_eq!(failed(&r), vec!["G-INT", "G-NOPUNCH"]);
    // the reference decides G-NOPUNCH before G-BOUND, so a later failure does not reach it
    let r = gates_of(np, |rec, _| rec.state_sample(5, 0, 65 * 1024 * 1024));
    assert_eq!(failed(&r), vec!["G-BOUND"]);
    assert_eq!(clean().status("G-NOPUNCH"), Some(&GateStatus::NotApplicable));
}

#[test]
fn g_medium_spec_and_prov_are_the_recorded_ones_plus_the_lint() {
    let r = gates_of(
        |_| {},
        |rec, _| rec.violation(5, "G-MEDIUM", 0, "datagram above the path MTU"),
    );
    assert_eq!(failed(&r), vec!["G-MEDIUM"]);
    let r = gates_of(|_| {}, |rec, _| rec.crash(5, 1, "poll_event", "Panic"));
    assert_eq!(failed(&r), vec!["G-SPEC"]);
    assert!(fail_msgs(&r, "G-SPEC")[0].contains("never raise on peer input"));
    let r = gates_of(
        |_| {},
        |rec, _| rec.violation(5, "G-PROV", 0, "export_state returned a non-bytes part"),
    );
    assert_eq!(failed(&r), vec!["G-PROV"]);
    let r = gates_of(|_| {}, |_, f| f.prov_clean = false);
    assert_eq!(failed(&r), vec!["G-PROV"]);
}

#[test]
fn g_bound_caps_by_device_class() {
    let peak = |device: &'static str, bytes: u64| {
        gates_of(
            |_| {},
            move |rec, f| {
                f.nodes[1].device = device.to_owned();
                rec.state_sample(sec(5), 1, bytes);
            },
        )
    };
    let mib = 1024 * 1024;
    assert!(failed(&peak("desktop", 64 * mib)).is_empty());
    assert_eq!(failed(&peak("desktop", 64 * mib + 1)), vec!["G-BOUND"]);
    assert!(failed(&peak("phone", 16 * mib)).is_empty());
    assert_eq!(failed(&peak("phone", 17 * mib)), vec!["G-BOUND"]);
    assert_eq!(failed(&peak("browser", 17 * mib)), vec!["G-BOUND"]);
    assert_eq!(failed(&peak("mcu", 32 * 1024 + 1)), vec!["G-BOUND"]);
    // cloud: 1 MiB + 16 KiB * 3 nodes + 256 KiB * max(1, fetches) = 1 MiB + 48 KiB + 256 KiB
    let cap = mib + 48 * 1024 + 256 * 1024;
    assert!(failed(&peak("cloud", cap)).is_empty());
    assert_eq!(failed(&peak("cloud", cap + 1)), vec!["G-BOUND"]);
    assert!(fail_msgs(&peak("cloud", cap + 1), "G-BOUND")[0].contains("(cloud)"));
    // soak: the last third may not exceed twice the middle third plus 64 KiB
    let soak = |last: u64| {
        gates_of(
            |w| w.soak = true,
            move |rec, _| {
                rec.state_sample(sec(300), 0, 1000);
                rec.state_sample(sec(500), 0, last);
            },
        )
    };
    assert!(failed(&soak(2000 + 64 * 1024)).is_empty());
    assert_eq!(failed(&soak(2001 + 64 * 1024)), vec!["G-BOUND"]);
}

#[test]
fn g_surface_probe_and_stream_round_trips() {
    // base round trip: 2 * (10 ms up + 40 ms region + 10 ms down) = 120 ms, half of it 60 ms
    let probe = |after: u64| {
        gates_of(
            |_| {},
            move |rec, _| {
                let i = rec.intent(
                    IntentKind::Echo,
                    0,
                    sec(10),
                    sec(40),
                    &[],
                    32,
                    MustArg::Flag(true),
                    IntentMeta {
                        probe: true,
                        ..meta_to(1)
                    },
                );
                rec.echo_connected(i, sec(10) + after);
            },
        )
    };
    assert!(failed(&probe(ms(60))).is_empty());
    assert_eq!(failed(&probe(ms(60) + 1)), vec!["G-SURFACE"]);
    // five echoes with written, served and a delivery: fwd / back must have a median at most 1.8
    let stream = |fwd: u64, back: u64| {
        gates_of(
            |_| {},
            move |rec, _| {
                for k in 0..5 {
                    let t = sec(10 + k);
                    let i = rec.intent(
                        IntentKind::Echo,
                        0,
                        t,
                        t + sec(30),
                        &[],
                        32,
                        MustArg::Flag(false),
                        meta_to(1),
                    );
                    rec.echo_written(i, t);
                    rec.echo_served(i, t + fwd);
                    rec.delivered(i, 0, t + fwd + back, 32);
                }
            },
        )
    };
    assert!(failed(&stream(ms(180), ms(100))).is_empty(), "1.8 passes");
    assert_eq!(failed(&stream(ms(181), ms(100))), vec!["G-SURFACE"]);
    // four ratios are not enough to decide
    let four = gates_of(
        |_| {},
        |rec, _| {
            for k in 0..4 {
                let t = sec(10 + k);
                let i = rec.intent(
                    IntentKind::Echo,
                    0,
                    t,
                    t + sec(30),
                    &[],
                    32,
                    MustArg::Flag(false),
                    meta_to(1),
                );
                rec.echo_written(i, t);
                rec.echo_served(i, t + ms(500));
                rec.delivered(i, 0, t + ms(501), 32);
            }
        },
    );
    assert!(failed(&four).is_empty());
}

fn join_world(w: &mut World) {
    w.changes.push(Change {
        t: sec(100),
        kind: ChangeKind::Crash,
        node: 2,
        version: None,
    });
}

fn crash_of_two(rec: &mut Rec, f: &mut RunFacts) {
    rec.node_stopped(2, sec(100), false);
    f.nodes[2].alive_at_end = false;
    f.nodes[0].view = Some((1, vec![1]));
    f.nodes[1].view = Some((1, vec![0]));
}

#[test]
fn g_aware_completeness_of_a_crash() {
    let with = |events: &'static [(usize, u64, bool)]| {
        gates_of(join_world, move |rec, f| {
            crash_of_two(rec, f);
            for &(node, at, confirmed) in events {
                let ev = if confirmed {
                    MemberEvent::ConfirmedDown(Some(2))
                } else {
                    MemberEvent::Suspected(Some(2))
                };
                rec.core_event(sec(at), node, 0, &ev);
            }
        })
    };
    assert!(failed(&with(&[(0, 110, true), (1, 120, true)])).is_empty());
    let r = with(&[]);
    assert_eq!(failed(&r), vec!["G-AWARE"]);
    assert!(fail_msgs(&r, "G-AWARE")[0].starts_with("a crash was not reported"));
    assert_eq!(
        failed(&with(&[(0, 110, true), (1, 110, false)])),
        vec!["G-AWARE"],
        "a suspicion is not a confirmation"
    );
    assert_eq!(
        failed(&with(&[(0, 110, true), (1, 161, true)])),
        vec!["G-AWARE"],
        "after the bound"
    );
    assert!(
        failed(&with(&[(0, 110, true), (1, 160, true)])).is_empty(),
        "at the bound"
    );
}

#[test]
fn g_aware_skips_changes_it_cannot_expect_to_be_seen() {
    // the change is too close to the end of the run for the bound to elapse
    let late = gates_of(
        |w| {
            w.changes.push(Change {
                t: sec(580),
                kind: ChangeKind::Crash,
                node: 2,
                version: None,
            })
        },
        |rec, f| {
            rec.node_stopped(2, sec(580), false);
            f.nodes[2].alive_at_end = false;
            f.nodes[0].view = Some((1, vec![1]));
            f.nodes[1].view = Some((1, vec![0]));
        },
    );
    assert!(failed(&late).is_empty());
    // the node came back before the bound elapsed
    let back = gates_of(join_world, |rec, _| {
        rec.node_stopped(2, sec(100), false);
        rec.node_started(2, sec(130));
    });
    assert!(failed(&back).is_empty());
    // node 0 and node 2 were cut apart, node 1 reported
    let cut = gates_of(
        |w| {
            join_world(w);
            w.partitions.push(Cut {
                from: sec(50),
                to: sec(300),
                x: vec![0],
                y: vec![2],
                both: true,
            });
        },
        |rec, f| {
            crash_of_two(rec, f);
            rec.core_event(sec(110), 1, 0, &MemberEvent::ConfirmedDown(Some(2)));
        },
    );
    assert!(failed(&cut).is_empty());
    // a denied node is not tracked
    let denied = gates_of(
        |w| {
            join_world(w);
            w.denied = vec![2];
        },
        crash_of_two,
    );
    assert!(failed(&denied).is_empty());
}

#[test]
fn g_aware_join_stack_and_revoke_events_must_match_their_kind() {
    let join = |report: bool| {
        gates_of(
            |w| {
                w.changes.push(Change {
                    t: sec(100),
                    kind: ChangeKind::Join,
                    node: 2,
                    version: None,
                })
            },
            move |rec, _| {
                rec.alive_iv.insert(2, vec![(sec(100), None)]);
                if report {
                    rec.core_event(sec(101), 0, 0, &MemberEvent::Joined(Some(2)));
                    rec.core_event(sec(101), 1, 0, &MemberEvent::Joined(Some(2)));
                }
            },
        )
    };
    assert!(failed(&join(true)).is_empty());
    assert!(fail_msgs(&join(false), "G-AWARE")[0].starts_with("a join was not reported"));
    let stack = |version: u64| {
        gates_of(
            |w| {
                w.changes.push(Change {
                    t: sec(100),
                    kind: ChangeKind::Stack,
                    node: 2,
                    version: Some(2),
                })
            },
            move |rec, _| {
                for j in 0..2 {
                    rec.core_event(
                        sec(105),
                        j,
                        0,
                        &MemberEvent::StackChanged {
                            member: Some(2),
                            version,
                        },
                    );
                }
            },
        )
    };
    assert!(failed(&stack(2)).is_empty());
    assert_eq!(failed(&stack(3)), vec!["G-AWARE"]);
    let revoke = gates_of(
        |w| {
            w.changes.push(Change {
                t: sec(100),
                kind: ChangeKind::Revoke,
                node: 2,
                version: None,
            })
        },
        |rec, f| {
            rec.revoke(2, sec(100));
            f.nodes[0].view = Some((1, vec![1]));
            f.nodes[1].view = Some((1, vec![0]));
            f.nodes[2].alive_at_end = true;
            for j in 0..2 {
                rec.core_event(sec(101), j, 0, &MemberEvent::Revoked(Some(2)));
            }
        },
    );
    assert!(failed(&revoke).is_empty());
}

#[test]
fn g_aware_accuracy_epochs_and_convergence() {
    let suspect = |n: u64| {
        gates_of(
            |_| {},
            move |rec, _| {
                for k in 0..n {
                    rec.core_event(sec(100 + 100 * k), 0, 0, &MemberEvent::Suspected(Some(1)));
                }
            },
        )
    };
    assert!(failed(&suspect(2)).is_empty(), "two false suspicions are tolerated");
    let r = suspect(3);
    assert_eq!(failed(&r), vec!["G-AWARE"]);
    assert!(fail_msgs(&r, "G-AWARE")[0].starts_with("false suspicions"));
    // a suspicion of a node that is suspended is not false
    let r = gates_of(
        |_| {},
        |rec, _| {
            rec.suspended(1, sec(90), sec(400));
            for k in 0..3 {
                rec.core_event(sec(100 + 100 * k), 0, 0, &MemberEvent::Suspected(Some(1)));
            }
        },
    );
    assert!(failed(&r).is_empty());
    // epochs
    let r = gates_of(
        |_| {},
        |rec, _| {
            rec.core_event(5, 0, 1, &MemberEvent::ViewChanged { epoch: 3 });
            rec.core_event(6, 0, 1, &MemberEvent::ViewChanged { epoch: 3 });
        },
    );
    assert_eq!(
        fail_msgs(&r, "G-AWARE"),
        vec!["view epoch not strictly increasing".to_owned()]
    );
    // convergence
    let r = gates_of(|_| {}, |_, f| f.nodes[0].view = Some((1, vec![1])));
    assert!(fail_msgs(&r, "G-AWARE")[0].contains("did not converge"));
    let r = gates_of(|_| {}, |_, f| f.nodes[0].view = None);
    assert!(fail_msgs(&r, "G-AWARE")[0].contains("view() did not return"));
    let r = gates_of(|_| {}, |_, f| f.nodes[2].alive_at_end = false);
    assert!(fail_msgs(&r, "G-AWARE")[0].contains("still lists departed"));
    // a suspended node need not be listed and may be listed
    let r = gates_of(
        |_| {},
        |_, f| {
            f.nodes[2].suspended_at_end = true;
            f.nodes[0].view = Some((1, vec![1]));
            f.nodes[1].view = Some((1, vec![0, 2]));
        },
    );
    assert!(failed(&r).is_empty());
}

#[test]
fn g_aware_is_not_evaluated_without_a_membership_layer() {
    let r = gates_of(|_| {}, |_, f| f.has_membership = false);
    assert!(matches!(r.status("G-AWARE"), Some(GateStatus::NotEvaluated(m)) if m.contains("membership")));
    assert!(!r.all_clear());
    // a recorded epoch violation is a definite failure and stays one
    let r = gates_of(
        |_| {},
        |rec, f| {
            f.has_membership = false;
            rec.violation(5, "G-AWARE", 0, "view epoch not strictly increasing");
        },
    );
    assert_eq!(failed(&r), vec!["G-AWARE"]);
}

#[test]
fn the_endpoint_constants_tighten_but_never_loosen_the_world_caps() {
    // a crash at 300 s; both other nodes confirm it `after` seconds later; the bound is the smaller of the endpoint's
    // and the world's 150 s
    let run = |bound: u64, after: u64| {
        gates_of(
            |w| {
                w.changes.push(Change {
                    t: sec(300),
                    kind: ChangeKind::Crash,
                    node: 2,
                    version: None,
                })
            },
            move |rec, f| {
                f.awareness_bound_ns = sec(bound);
                crash_of_two(rec, f);
                rec.node_stopped(2, sec(300), false);
                rec.alive_iv.insert(2, vec![(0, Some(sec(300)))]);
                for j in 0..2 {
                    rec.core_event(sec(300 + after), j, 0, &MemberEvent::ConfirmedDown(Some(2)));
                }
            },
        )
    };
    assert!(failed(&run(400, 150)).is_empty());
    assert_eq!(
        failed(&run(400, 151)),
        vec!["G-AWARE"],
        "an endpoint bound of 400 s is cut to the world's 150 s"
    );
    assert!(failed(&run(30, 30)).is_empty());
    assert_eq!(
        failed(&run(30, 31)),
        vec!["G-AWARE"],
        "a tighter endpoint bound applies"
    );
}
