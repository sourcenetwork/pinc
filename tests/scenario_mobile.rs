//! Scenario target covering S3. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(["S3"]);

/// S3 run 2 seed 55022: node 8 moves and its address at hub 2 changes; node 11 dials node 8 through hub 2 from 60 s
/// on. The hub's session with the quiet node 8 idles out and comes back only by the packet that validates an address
/// again (an answer to a challenge, or the packet the session follows), after which node 8 sends nothing for a while.
/// The hub counts that packet as hearing node 8, as the reference model stamps a path with every packet that comes in
/// on it, so it keeps tunnelling node 11's resends down node 8's UDP session and the document sync from node 11 to
/// node 8 arrives within its bound. Counting only the packets that came from an address validated before they were
/// read, the hub judged node 8's session stale and the delivery was lost.
#[test]
fn a_member_heard_on_the_address_its_hub_just_validated_is_reached_by_the_hub_tunnel() {
    let v = pinc_sim::suite::world::variants()
        .into_iter()
        .find(|v| v.id == "S3" && v.seed == 55022)
        .unwrap();
    let r = scenario_support::run_child(&v, pinc_sim::Driver::Pinc, "0").result;
    assert!(r.ran);
    assert!(
        r.gates.failed().is_empty(),
        "S3 seed 55022 missed {:?}; late or missing: {:?}",
        r.gates.failed(),
        r.late
    );
}
