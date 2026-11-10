//! The roots a node serves. A value is answered only if the host registered its root here and the store holds it
//! whole; the set is bounded, so a host that registers more than [`PROVIDED_MAX`] roots must drop some first.

use alloc::collections::BTreeSet;

use crate::apps::Apps;
use crate::config::Store;
use crate::ep::Ep;
use crate::node::Node;

/// The most roots a node serves at once.
pub const PROVIDED_MAX: usize = 4096;

/// The registered roots.
#[derive(Debug, Default)]
pub(crate) struct Provided(BTreeSet<[u8; 32]>);

impl Provided {
    pub(crate) fn contains(&self, root: &[u8; 32]) -> bool {
        self.0.contains(root)
    }
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
{
    /// Serve the value under `root` to peers that ask for it, once the store holds it whole. True if the root is
    /// registered afterwards; false if the values layer is off or [`PROVIDED_MAX`] other roots are registered.
    pub fn values_provide(&mut self, root: &[u8; 32]) -> bool {
        let Some(v) = self.vals.as_deref_mut() else {
            return false;
        };
        let set = &mut v.net.provided.0;
        set.contains(root) || (set.len() < PROVIDED_MAX && set.insert(*root))
    }

    /// Stop serving the value under `root`. True if it was registered.
    pub fn values_unprovide(&mut self, root: &[u8; 32]) -> bool {
        self.vals.as_deref_mut().is_some_and(|v| v.net.provided.0.remove(root))
    }
}
