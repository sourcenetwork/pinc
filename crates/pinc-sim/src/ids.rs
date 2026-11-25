//! Handles the simulator hands out when a topology is built. They are only valid for the simulator that issued them.

macro_rules! id {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub(crate) u32);

        impl $name {
            /// The index in creation order, from 0.
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(
    /** A node. */
    NodeId
);
id!(
    /** A NAT device. */
    NatId
);
id!(
    /** A LAN: a site with its own uplink and downlink. */
    LanId
);
id!(
    /** An adversary host: a place that can inject spoofed datagrams. */
    HostId
);
id!(
    /** A point datagrams travel between: a node interface, a NAT, or a host. Links connect sites. */
    SiteId
);
id!(
    /** An on-path observer attached to one link direction. */
    ObsId
);

/// One network interface of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IfaceId {
    /// The node owning the interface.
    pub node: NodeId,
    /// The interface's index within the node, from 0.
    pub idx: u32,
}
