//! The fleet of backend (b): real machines the harness reaches over SSH. The file is the one `terraform apply` writes
//! in `distributed/infra` (`hosts.toml`), or one written by hand for machines that exist already, a single machine
//! included.
//!
//! This module only knows the file, where scenario nodes go, and the exact command lines the SSH backend sends. It
//! starts nothing, so all of it is tested without a machine.
//!
//! Invariants: every node of a scenario has exactly one host and a slot among the nodes of that host, and the slots of
//! one host are distinct (they decide the node's ports); a machine's address as peers use it is an IPv4 literal; a name
//! that reaches a shell is checked to hold no character the shell reads.

use std::net::Ipv4Addr;

use serde::{Deserialize, Serialize};

use crate::scenario::{NodeSpec, Problem, Site};

/// The most nodes one machine runs: ports are spaced by [`PORT_STEP`] above the stacks' base ports.
pub const MAX_PER_HOST: usize = 64;
/// The distance between the ports of two nodes of one machine.
pub const PORT_STEP: u16 = 16;

fn ssh_port() -> u16 {
    22
}

fn user() -> String {
    "ec2-user".into()
}

fn bin() -> String {
    "/tmp/vinc-distributed/vinc-distributed".into()
}

const fn yes() -> bool {
    true
}

/// One machine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Host {
    /// Its name: letters, digits and dashes.
    pub name: String,
    /// What SSH connects to: an address or a name the SSH configuration knows.
    pub address: String,
    /// The machine's IPv4 address as the other machines reach it, when that is not `address`.
    #[serde(default)]
    pub private: Option<String>,
    /// The login.
    #[serde(default = "user")]
    pub user: String,
    /// The scenario site this machine stands for (a region, say); scenario nodes of that site run here.
    #[serde(default)]
    pub site: Option<String>,
    /// Whether it is in the cluster placement group.
    #[serde(default)]
    pub cluster: bool,
    /// The SSH port.
    #[serde(default = "ssh_port")]
    pub port: u16,
    /// A private key file for this machine.
    #[serde(default)]
    pub key: Option<String>,
    /// Where the harness puts its binary on the machine.
    #[serde(default = "bin")]
    pub bin: String,
    /// Whether the login needs `sudo -n` for what a run does as root (control groups, `tc`).
    #[serde(default = "yes")]
    pub sudo: bool,
    /// The network interface the machine's address is on; found by asking the machine when absent.
    #[serde(default)]
    pub interface: Option<String>,
}

/// The file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fleet {
    /// The machines.
    pub hosts: Vec<Host>,
}

/// Where one node runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Placement {
    /// Index into [`Fleet::hosts`].
    pub host: usize,
    /// Among the nodes of that host, from 0.
    pub slot: usize,
}

/// Whether `s` is safe to put in a command line as one word.
pub fn plain(s: &str) -> bool {
    !s.is_empty()
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.' | b'/' | b':' | b'@'))
}

impl Host {
    /// The address peers use, when it is an IPv4 literal.
    pub fn ip(&self) -> Option<Ipv4Addr> {
        self.private.as_deref().unwrap_or(&self.address).parse().ok()
    }

    /// The argument list of `ssh` that runs `remote` on this machine (no terminal, no questions, keys only).
    pub fn ssh(&self, remote: &str) -> Vec<String> {
        let mut a: Vec<String> = [
            "-o",
            "BatchMode=yes",
            "-o",
            "LogLevel=ERROR",
            "-o",
            "ServerAliveInterval=15",
            "-o",
            "ServerAliveCountMax=8",
            "-o",
            "StrictHostKeyChecking=accept-new",
            "-p",
        ]
        .iter()
        .map(|s| (*s).to_owned())
        .collect();
        a.push(self.port.to_string());
        if let Some(k) = &self.key {
            a.extend(["-i".into(), k.clone()]);
        }
        a.push(format!("{}@{}", self.user, self.address));
        a.push(remote.to_owned());
        a
    }

    /// `cmd` as root when the login is not.
    pub fn root(&self, cmd: &str) -> String {
        if self.sudo {
            format!("sudo -n {cmd}")
        } else {
            cmd.to_owned()
        }
    }
}

impl Fleet {
    /// Read the file.
    ///
    /// # Errors
    /// The text is not a fleet file; the message names the line.
    pub fn parse(text: &str) -> Result<Self, String> {
        toml::from_str(text).map_err(|e| e.to_string())
    }

    /// Every problem of the fleet; empty when it can be used.
    pub fn validate(&self) -> Vec<Problem> {
        let mut out = Vec::new();
        if self.hosts.is_empty() {
            out.push(Problem::new("hosts", "name at least one machine"));
        }
        for (i, h) in self.hosts.iter().enumerate() {
            let p = |f: &str| format!("hosts[{i}].{f}");
            if !h.name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') || h.name.is_empty() {
                out.push(Problem::new(p("name"), "use letters, digits and dashes"));
            }
            if self.hosts.iter().take(i).any(|o| o.name == h.name) {
                out.push(Problem::new(p("name"), "another machine has this name"));
            }
            for (f, v) in [
                ("address", Some(&h.address)),
                ("user", Some(&h.user)),
                ("bin", Some(&h.bin)),
            ] {
                if v.is_some_and(|v| !plain(v)) {
                    out.push(Problem::new(p(f), "use letters, digits and - _ . / : @ only"));
                }
            }
            if h.ip().is_none() {
                out.push(Problem::new(
                    p("private"),
                    "give the machine's IPv4 address here (or as the address): the other machines reach it there",
                ));
            }
            if h.interface.as_deref().is_some_and(|v| !plain(v)) {
                out.push(Problem::new(p("interface"), "use letters, digits and - _ . only"));
            }
        }
        out
    }

    /// Where each node goes: the hosts whose `site` is the node's site, else every host, in turn.
    ///
    /// # Errors
    /// A machine would run more than [`MAX_PER_HOST`] nodes.
    pub fn place(&self, nodes: &[NodeSpec], sites: &[Site]) -> Result<Vec<Placement>, String> {
        let mut used = vec![0usize; self.hosts.len()];
        let mut turn = 0usize;
        let mut out = Vec::with_capacity(nodes.len());
        for n in nodes {
            let site = sites.get(n.site).map(|s| s.name.as_str());
            let mut cands: Vec<usize> = (0..self.hosts.len())
                .filter(|i| self.hosts.get(*i).is_some_and(|h| h.site.as_deref() == site))
                .collect();
            if cands.is_empty() {
                cands = (0..self.hosts.len()).collect();
            }
            // The candidate with the fewest nodes so far; ties go to the one that comes first after the last pick.
            let pick = cands
                .iter()
                .copied()
                .min_by_key(|i| {
                    (
                        used.get(*i).copied().unwrap_or(0),
                        (*i + self.hosts.len() - turn % self.hosts.len().max(1)) % self.hosts.len().max(1),
                    )
                })
                .ok_or("the fleet has no machine")?;
            let slot = used.get(pick).copied().unwrap_or(0);
            if slot >= MAX_PER_HOST {
                return Err(format!(
                    "machine {} would run more than {MAX_PER_HOST} nodes; add machines to the fleet",
                    self.hosts.get(pick).map_or("?", |h| h.name.as_str())
                ));
            }
            if let Some(u) = used.get_mut(pick) {
                *u += 1;
            }
            turn = pick + 1;
            out.push(Placement { host: pick, slot });
        }
        Ok(out)
    }
}

/// A port of a stack for the node in `slot` of its machine.
pub fn port(base: u16, slot: u16) -> u16 {
    base.saturating_add(slot.saturating_mul(PORT_STEP))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use super::*;
    use crate::scenario::{Nat, Role, Shape};

    const FILE: &str = r#"
[[hosts]]
name = "east-1"
address = "203.0.113.10"
private = "10.0.1.10"
site = "east"
cluster = true

[[hosts]]
name = "east-2"
address = "203.0.113.11"
site = "east"

[[hosts]]
name = "west-1"
address = "203.0.113.20"
user = "admin"
port = 2222
site = "west"
"#;

    fn node(name: &str, site: usize) -> NodeSpec {
        NodeSpec {
            name: name.into(),
            site,
            role: Role::Peer,
            link: Shape::lan(),
        }
    }

    fn sites() -> Vec<Site> {
        ["east", "west"]
            .iter()
            .map(|n| Site {
                name: (*n).into(),
                nat: Nat::None,
                lan: Shape::lan(),
                pos: None,
            })
            .collect()
    }

    #[test]
    fn the_file_terraform_writes_parses_and_validates() {
        let f = Fleet::parse(FILE).unwrap();
        assert_eq!(f.hosts.len(), 3);
        assert!(f.validate().is_empty(), "{:?}", f.validate());
        assert_eq!(f.hosts[0].ip(), Some("10.0.1.10".parse().unwrap()));
        assert_eq!(f.hosts[1].ip(), Some("203.0.113.11".parse().unwrap()));
        assert_eq!(f.hosts[2].port, 2222);
        assert!(Fleet::parse("[[hosts]]\nname = \"a\"\naddress = \"x\"\nbogus = 1").is_err());
    }

    #[test]
    fn problems_name_the_machine_and_the_field() {
        let f = Fleet::parse(
            "[[hosts]]\nname = \"a b\"\naddress = \"h; rm -rf /\"\n[[hosts]]\nname = \"a b\"\naddress = \"vertex\"",
        )
        .unwrap();
        let paths: Vec<String> = f.validate().into_iter().map(|p| p.path).collect();
        assert!(paths.contains(&"hosts[0].name".to_owned()));
        assert!(paths.contains(&"hosts[0].address".to_owned()));
        assert!(
            paths.contains(&"hosts[1].name".to_owned()),
            "a duplicate name: {paths:?}"
        );
        // A name the SSH configuration knows is no address peers can use.
        assert!(paths.contains(&"hosts[1].private".to_owned()));
    }

    #[test]
    fn nodes_go_to_the_machines_of_their_site_in_turn_with_distinct_slots() {
        let f = Fleet::parse(FILE).unwrap();
        let nodes: Vec<NodeSpec> = (0..4)
            .map(|i| node(&format!("e{i}"), 0))
            .chain((0..2).map(|i| node(&format!("w{i}"), 1)))
            .collect();
        let p = f.place(&nodes, &sites()).unwrap();
        // East nodes alternate over the two east machines; west nodes share the one west machine.
        let east: Vec<(usize, usize)> = p[..4].iter().map(|x| (x.host, x.slot)).collect();
        assert_eq!(east, vec![(0, 0), (1, 0), (0, 1), (1, 1)]);
        assert_eq!(p[4], Placement { host: 2, slot: 0 });
        assert_eq!(p[5], Placement { host: 2, slot: 1 });
    }

    #[test]
    fn a_site_no_machine_stands_for_uses_every_machine() {
        let f = Fleet::parse(FILE).unwrap();
        let p = f
            .place(&[node("a", 0), node("b", 0), node("c", 0)], &sites()[..1])
            .unwrap();
        assert_eq!(p.len(), 3);
        let mut by_host = [0; 3];
        for x in &p {
            by_host[x.host] += 1;
        }
        assert_eq!(by_host.iter().sum::<i32>(), 3);
    }

    #[test]
    fn a_machine_that_would_hold_too_many_nodes_is_refused() {
        let f = Fleet::parse("[[hosts]]\nname = \"one\"\naddress = \"10.0.0.1\"").unwrap();
        let nodes: Vec<NodeSpec> = (0..=MAX_PER_HOST).map(|i| node(&format!("n{i}"), 0)).collect();
        assert!(f.place(&nodes, &sites()).unwrap_err().contains("more than"));
    }

    #[test]
    fn the_ssh_command_line_is_exact() {
        let f = Fleet::parse(FILE).unwrap();
        let a = f.hosts[2].ssh("true");
        assert!(a.windows(2).any(|w| w == ["-p", "2222"]));
        assert_eq!(a[a.len() - 2], "admin@203.0.113.20");
        assert_eq!(a[a.len() - 1], "true");
        assert!(a.contains(&"BatchMode=yes".to_owned()));
        assert_eq!(f.hosts[0].root("tc qdisc show"), "sudo -n tc qdisc show");
    }

    #[test]
    fn ports_are_spaced_by_slot() {
        assert_eq!(port(4433, 0), 4433);
        assert_eq!(port(4433, 3), 4433 + 48);
        assert_eq!(port(65_530, 9), u16::MAX);
    }
}
