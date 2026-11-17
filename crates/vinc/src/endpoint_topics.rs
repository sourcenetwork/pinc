//! Topics on the endpoint: join, leave, publish, neighbours and events.
//!
//! A topic is a name; every endpoint that joined it and every endpoint that publishes to it reaches the others through
//! the hubs (the relays the builder names), or straight when a hub is unreachable and the publisher knows the
//! subscribers (join hints). Messages are signed by their publisher over the topic, the message id and the bytes, so a
//! hub or a relay that alters one is caught, and a peer the access hook refuses (with [`Direction::Gossip`](crate::Direction))
//! neither delivers nor receives anything.
//!
//! # Keeping a message as proof
//!
//! Build the endpoint with [`Builder::envelopes`](crate::Builder::envelopes)`(true)` and each topic message arrives as
//! an [`Event::Envelope`] in place of the [`Event::Message`]. Store its
//! [`into_bytes`](crate::envelope::Envelope::into_bytes), and later anyone checks them with [`envelope::verify`](crate::envelope::verify), with no endpoint, no session and no
//! network. A verified envelope proves that the key behind the origin's id signed this topic, this message id, this
//! exact payload and this timestamp. It does not prove the key was unrevoked then, the message's position among
//! others, or that anyone received it. A kind 1 statement carries no label of its own (it begins with the topic's
//! bytes), so such a proof also holds for a raw signature by the same key over bytes of that shape: an application
//! that signs bytes a peer chose with [`Endpoint::sign`] can be made to produce one (vinc#572; the guard of `sign`
//! refuses reserved label prefixes, which an unlabelled topic statement does not carry). Everything sent on a stream
//! or as a datagram is deniable by construction (both ends hold the keys), and is never part of an envelope.

use alloc::vec::Vec;
use core::time::Duration;

use vinc_broadcast::ReachStats;
use vinc_crypto::NodeId;

use crate::addr::NodeAddr;
use crate::endpoint::{Discovery, Endpoint};
use crate::engine::Try;
use crate::error::Result;
use crate::event::{Event, MessageId};
use crate::host::Hosted;

impl<H: Hosted, D: Discovery> Endpoint<H, D> {
    /// Join `topic`: from now on its messages arrive as [`Event::Message`]. The peers of `hints` are dialed and taken as
    /// members of the topic, so a publish reaches them with no hub. Returns whether the topic was new.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] for a topic name over 255 bytes, [`crate::ErrorKind::Busy`] when the endpoint tracks
    /// as many topics as [`Limits::topics`](crate::Limits::topics) allows, [`crate::ErrorKind::Shutdown`] once the
    /// endpoint stopped.
    pub async fn join(&self, topic: &[u8], hints: &[NodeAddr]) -> Result<bool> {
        self.0
            .shared
            .run(|core, now| Try::Done(core.join(now, topic, hints)))
            .await
    }

    /// Leave `topic`; whether it was joined.
    pub async fn leave(&self, topic: &[u8]) -> bool {
        self.0.shared.run(|core, now| Try::Done(core.leave(now, topic))).await
    }

    /// Publish `payload` to `topic`; the topic need not be joined. With `wait`, first waits up to that long for a member of
    /// the topic this endpoint has a session with (see [`neighbors`](Self::neighbors)). A burst is held back, not
    /// dropped: while 1,024 publishes still wait for a hub to acknowledge them, the call waits until one of them is
    /// acknowledged or given up (after 90 seconds). On an endpoint that is a hub the call waits while the topic's log is
    /// full of messages its subscribers are still owed; a subscriber that takes nothing for two seconds is let go.
    ///
    /// # Errors
    /// [`crate::ErrorKind::TooLarge`] when `payload` is over [`max_message`](Self::max_message),
    /// [`crate::ErrorKind::TimedOut`] when `wait` passed with no neighbour, and the errors of [`join`](Self::join).
    pub async fn publish(&self, topic: &[u8], payload: &[u8], wait: Option<Duration>) -> Result<MessageId> {
        let sh = &self.0.shared;
        if let Some(wait) = wait {
            let mut deadline = None;
            sh.run(|core, now| {
                let at = *deadline
                    .get_or_insert_with(|| now.saturating_add(u64::try_from(wait.as_nanos()).unwrap_or(u64::MAX)));
                core.neighbor_wait(topic, at, now)
            })
            .await?;
        }
        sh.run(|core, now| core.publish(now, topic, payload)).await
    }

    /// The members of `topic` this endpoint has a session with now, sorted by id.
    pub fn neighbors(&self, topic: &[u8]) -> Vec<NodeId> {
        self.0
            .shared
            .lock()
            .map(|core| core.neighbors(topic))
            .unwrap_or_default()
    }

    /// The adjacency table of [`Builder::connected_topics`](crate::Builder::connected_topics). On a hub: the records it
    /// holds, the records it refused, and whether its table is closed ([`Event::ReachClosed`]) and why it stays so. On
    /// a member: how many records it signed. `None` once the endpoint stopped.
    pub fn reach_stats(&self) -> Option<ReachStats> {
        self.0.shared.lock().map(|core| core.node.reach_stats())
    }

    /// The next event about a topic; `None` once the endpoint stopped and the events are read. Events queue while no one
    /// reads, up to a bound; what does not fit is counted and reported as [`Event::Lost`].
    pub async fn event(&self) -> Option<Event> {
        self.0.shared.run(|core, _| core.poll_event()).await
    }

    /// The largest payload [`publish`](Self::publish) takes, in bytes ([`Limits::topic_message`](crate::Limits::topic_message)).
    pub fn max_message(&self) -> usize {
        self.0.max_message
    }
}
