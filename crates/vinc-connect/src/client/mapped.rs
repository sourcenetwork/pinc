//! The port mappings the host holds, as the connectivity layer treats them: a mapped address is held until a relay
//! reported the node's IP at it, is then offered first and makes the class port-mapped, and is withdrawn, with the
//! class falling back, when nothing vouches for it any more. One rule ([`netcheck::mapped_seen`]) decides.
//!
//! Invariants: a withdrawn mapping never leaves the node without a class (it takes the class it replaced), and the
//! record that withdraws it is asked for at once.

use core::net::SocketAddr;

use super::conn::{Connectivity, Notice};
use super::netcheck;
use crate::record::{MAX_ADDRS, Reach};
use vinc_crypto::Provider;

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// Set the external addresses of the port mappings the host holds (at most two) at `now`. A mapped address leads
    /// the candidates and the record, and decides the port-mapped class, only while a relay reported its IP
    /// ([`netcheck::mapped_seen`]): until then it is held and not published, and a change in what passes is published
    /// at once.
    pub fn set_mapped(&mut self, now: u64, addrs: &[SocketAddr]) {
        let mut mapped = [None; 2];
        for (d, a) in mapped.iter_mut().zip(addrs) {
            *d = Some(*a);
        }
        if mapped == self.mapped {
            return;
        }
        self.mapped = mapped;
        self.update_class(now);
    }

    /// The mapped addresses a relay vouches for, given the reflexive addresses `refl`.
    fn live_of(&self, refl: &[SocketAddr]) -> [Option<SocketAddr>; 2] {
        self.mapped.map(|m| m.filter(|m| netcheck::mapped_seen(refl, m)))
    }

    /// Ask for the record again when the mapped addresses a relay vouches for changed.
    pub(super) fn refresh_mapped(&mut self, now: u64) {
        let mut refl = [self.me_addr(); MAX_ADDRS];
        let nr = self.net.reflexive_into(&mut refl);
        let live = self.live_of(refl.get(..nr).unwrap_or_default());
        if live != self.live {
            let had = self.live.iter().any(Option::is_some);
            self.live = live;
            self.sign.want_record();
            // A mapping that made the node port-mapped is no longer vouched for: the class falls back to the one the
            // node would have without it, noted while it was port-mapped (`classify` of the same observations without
            // a mapping, never `None` because a reflexive address was in them). The class is never withdrawn to nothing:
            // a node with no class publishes no record, and the one that lists the mapping would stay at the relay.
            if had && self.class == Some(Reach::PortMapped) && !live.iter().any(Option::is_some) {
                self.class = self.unmapped;
                if let Some(c) = self.class {
                    self.notice(Notice::Class(c));
                }
                self.next_publish = now;
            }
        }
    }

    /// The candidates this node offers a peer: the external addresses of its port mappings a relay vouches for first
    /// ([`netcheck::mapped_seen`]), then its reflexive addresses, then its local ones, at most 8. A node with no
    /// mapping offers its reflexive addresses, then its local ones.
    pub fn candidates(&self, out: &mut [SocketAddr; MAX_ADDRS]) -> usize {
        let mut refl = [self.me_addr(); MAX_ADDRS];
        let nr = self.net.reflexive_into(&mut refl);
        let mut n = 0;
        let live = self.live_of(refl.get(..nr).unwrap_or_default());
        for a in live
            .iter()
            .flatten()
            .chain(refl.iter().take(nr))
            .chain(self.local.iter().flatten())
        {
            if n < MAX_ADDRS
                && !out.get(..n).unwrap_or_default().contains(a)
                && let Some(d) = out.get_mut(n)
            {
                *d = *a;
                n += 1;
            }
        }
        n
    }
}
