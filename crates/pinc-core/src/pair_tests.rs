//! The reference count of the table of address pairs: an id that names no pair is counted, never silently skipped.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "test assertions")]

use core::net::SocketAddr;

use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{KeyHandle, LocalIdentity};
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::{BufferPool, RawChunk};
use pinc_transport::stream::{self, NoSource, Streams};

use crate::endpoint::{Endpoint, EndpointConfig};
use crate::slot::Slot;

type Ep<'s> = Endpoint<'s, 's, Software, NoSource, 1, 2, 16, 1, 1, 10, 1, 1, 1>;

fn addr(i: u8) -> SocketAddr {
    SocketAddr::from(([10, 0, 0, i], 9))
}

/// A held pair is released once and leaves; an id whose pair is gone, held or let go of again, counts one each.
#[test]
fn an_id_that_names_no_pair_is_counted_when_retained_or_released() {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let mut slab: [RawChunk; 0] = [];
    let pool = BufferPool::from_slab(&mut slab);
    let mut streams = Streams::<NoSource, 1, 2>::new(&stream::Config::new(false), &pool);
    let loss = LossEstimate::new();
    let mut slots = [Slot::<Software, NoSource, 1, 2, 16, 1>::new(Resources {
        pool,
        streams: (&mut streams).into(),
        loss: (&loss).into(),
        tables: Tables::new(),
    })];
    let mut ep: Ep<'_> = Endpoint::new(0, Software, Drbg::new(&[3; 32]), id, EndpointConfig::new(5), &mut slots);
    let (pid, minted) = ep.path_id_minted(addr(1), addr(2));
    assert!(minted);
    ep.retain_pair(pid);
    ep.release_pair(pid);
    assert_eq!(ep.node_stats().pair_refs_unbalanced, 0, "a balanced hold counted");
    assert!(ep.path_addrs(pid).is_none(), "the last release kept the pair");
    ep.release_pair(pid);
    assert_eq!(
        ep.node_stats().pair_refs_unbalanced,
        1,
        "a release of an id with no pair passed unseen"
    );
    ep.retain_pair(pid);
    assert_eq!(
        ep.node_stats().pair_refs_unbalanced,
        2,
        "a hold of an id with no pair passed unseen"
    );
}

/// The memory a session costs: `Meta` is held once per slot (`slot.rs` states the size).
#[cfg(target_pointer_width = "64")]
#[test]
fn the_slot_meta_has_the_documented_size() {
    assert_eq!(core::mem::size_of::<crate::slot::Meta<4>>(), 2832, "Meta at NP = 4");
}
