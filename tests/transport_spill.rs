//! A connection whose streams hold spill slots gives every one back to the endpoint's arena when it hands its memory
//! back, whether its streams ended or not: the endpoint does that when a session ends in any way.
#![allow(clippy::unwrap_used)]

use pinc_tests::*;
use pinc_transport::conn::Lent;
use pinc_transport::stream::spill::SpillArena;

#[test]
fn handing_the_memory_back_mid_transfer_returns_every_spill_slot() {
    big_stack(|| {
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut w = World::new(pinc_crypto::IdentityAlg::Ed25519);
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, Params::new(10 * MS)));
        net.a.spill = SpillArena::new_boxed(8);
        net.b.spill = SpillArena::new_boxed(8);
        assert!(net.connect(net.now + 30 * SEC));
        let id = net.a.conn.open_bi().unwrap();
        let data = pattern(8 << 20, 1);
        let mut off = 0;
        let spilled = net.run(net.now + 60 * SEC, |n| {
            // Half the datagrams A sends from its 3,000th to its 3,600th are lost: one burst in a wide flight.
            let ab = &mut n.link.routes.first_mut().unwrap().ab;
            ab.p.loss_ppm = if (3000..3600).contains(&ab.sent) { 500_000 } else { 0 };
            while off < data.len() {
                let chunk = data.get(off..(off + 65_536).min(data.len())).unwrap();
                let k = n.a.conn.write(id, chunk).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            n.a.spill.held() + n.b.spill.held() > 0
        });
        assert!(spilled, "nothing spilled");
        let (a, b) = (net.a.conn.stats(), net.b.conn.stats());
        assert!(a.range_spills + b.range_spills > 0, "the connections count the spill");
        assert_eq!(a.spill_lost + b.spill_lost, 0, "every slot went back to a lent arena");
        let Net { mut a, mut b, .. } = net;
        drop(a.conn.into_resources(&mut Lent { spill: &mut a.spill }));
        drop(b.conn.into_resources(&mut Lent { spill: &mut b.spill }));
        assert_eq!(
            a.spill.held() + b.spill.held(),
            0,
            "a slot stayed held after its connection was gone"
        );
    });
}
