//! The harness's one error type: what failed, in words an operator can act on.

use std::fmt;

use crate::scenario::Problem;

/// Why an operation of the harness failed.
#[derive(Debug)]
pub enum Error {
    /// The scenario has problems; nothing was started.
    Scenario(Vec<Problem>),
    /// A previous run left containers or links behind; nothing was started.
    Leftovers(Vec<String>),
    /// A tool the backend needs is missing or refused (Docker, sudo, ip, tc).
    Host(String),
    /// A command failed.
    Command {
        /// The command line.
        cmd: String,
        /// What it printed on its error output.
        stderr: String,
    },
    /// A node program failed or stopped answering.
    Node(String),
    /// Something took longer than allowed.
    Timeout(String),
    /// The run was interrupted by a signal; everything was torn down.
    Interrupted,
    /// A file could not be read or written.
    Io(std::io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Scenario(p) => {
                write!(f, "the scenario has {} problem(s):", p.len())?;
                for x in p {
                    write!(f, "\n  {x}")?;
                }
                Ok(())
            }
            Self::Leftovers(l) => write!(
                f,
                "a previous run left {} object(s) behind ({}); run `vinc-distributed clean` first",
                l.len(),
                l.join(", ")
            ),
            Self::Host(m) | Self::Node(m) | Self::Timeout(m) => f.write_str(m),
            Self::Command { cmd, stderr } => write!(f, "`{cmd}` failed: {}", stderr.trim()),
            Self::Interrupted => f.write_str("the run was interrupted; everything it created was removed"),
            Self::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// The harness's result.
pub type Result<T, E = Error> = std::result::Result<T, E>;
