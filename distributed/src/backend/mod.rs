//! Where nodes run. Backend (a), [`containers`]: containers and network namespaces on this machine, wired and shaped
//! by the plan. Every backend starts the same binary in node mode in every node and measures it from the kernel.

pub mod containers;
pub mod fleet;
pub mod proc;
pub mod ssh;

use std::net::Ipv4Addr;

pub use proc::Proc;

use crate::error::Result;
use crate::metrics::{Qdisc, Reading};
use crate::plan::{Plan, ShapePoint};
use crate::scenario::Shape;

use self::containers::Containers;
use self::ssh::Ssh;

/// Where the nodes of a run are: the one interface every workload and fault uses. Each call forwards to the backend's own
/// method of the same name.
#[derive(Debug)]
pub enum Cluster {
    /// Containers on this machine.
    Containers(Containers),
    /// Real machines over SSH.
    Ssh(Box<Ssh>),
}

macro_rules! each {
    ($self:ident, $b:ident => $e:expr) => {
        match $self {
            Self::Containers($b) => $e,
            Self::Ssh($b) => $e,
        }
    };
}

impl Cluster {
    /// Start node `i`'s program with `args` and `env`.
    ///
    /// # Errors
    /// The node does not exist or the backend failed.
    pub fn spawn(&self, i: usize, args: &[String], env: &[(String, String)]) -> Result<Proc> {
        each!(self, b => b.spawn(i, args, env))
    }

    /// Kill every program of node `i`.
    ///
    /// # Errors
    /// The backend failed.
    pub async fn stop(&self, i: usize) -> Result<()> {
        each!(self, b => b.stop(i).await)
    }

    /// Freeze or thaw node `i`.
    ///
    /// # Errors
    /// The backend failed.
    pub async fn pause(&self, i: usize, pause: bool) -> Result<()> {
        each!(self, b => b.pause(i, pause).await)
    }

    /// Node `i`'s CPU time and interface counters.
    ///
    /// # Errors
    /// The backend failed.
    pub async fn reading(&self, i: usize) -> Result<Reading> {
        each!(self, b => b.reading(i).await)
    }

    /// Start measuring node `i`'s peak memory afresh (where the backend can).
    ///
    /// # Errors
    /// The backend failed.
    pub async fn peak_reset(&self, i: usize) -> Result<()> {
        match self {
            Self::Containers(b) => b.peak_reset(i).await,
            Self::Ssh(_) => Ok(()),
        }
    }

    /// Node `i`'s peak memory in bytes.
    ///
    /// # Errors
    /// The backend failed.
    pub async fn peak_read(&self, i: usize) -> Result<Option<u64>> {
        each!(self, b => b.peak_read(i).await)
    }

    /// The counters of every shaper of site `s`.
    ///
    /// # Errors
    /// The backend failed.
    pub async fn shapers(&self, s: usize) -> Result<Vec<Qdisc>> {
        each!(self, b => b.shapers(s).await)
    }

    /// Give one direction of a link a new shape, now.
    ///
    /// # Errors
    /// The backend failed or cannot change this link.
    pub async fn reshape(&self, at: &ShapePoint, shape: &Shape) -> Result<()> {
        each!(self, b => b.reshape(at, shape).await)
    }

    /// The names of the containers or scopes of the run, for the quiet-host check.
    pub fn scopes(&self) -> Vec<String> {
        each!(self, b => b.scopes())
    }

    /// The image or binary the nodes run, for the results.
    pub fn image_id(&self) -> String {
        match self {
            Self::Containers(b) => b.image_id().to_owned(),
            Self::Ssh(_) => "the harness binary copied to each machine".into(),
        }
    }

    /// The address node `i` binds and others reach it at, its slot among the nodes of its machine, and the address other
    /// sites see (a translated site's router).
    pub fn address(&self, plan: &Plan, i: usize) -> (Ipv4Addr, Ipv4Addr, u16) {
        match self {
            Self::Containers(_) => (
                plan.nodes.get(i).map_or(Ipv4Addr::UNSPECIFIED, |n| n.ip),
                plan.public_ip(i),
                0,
            ),
            Self::Ssh(b) => {
                let (ip, slot) = b.address(i);
                (ip, ip, slot)
            }
        }
    }

    /// Remove what the run made and check that nothing is left; returns what is.
    ///
    /// # Errors
    /// The backend failed.
    pub async fn down(&mut self) -> Result<Vec<String>> {
        each!(self, b => b.down().await)
    }
}
