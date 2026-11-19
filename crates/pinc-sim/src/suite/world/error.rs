//! The error of world generation.

use std::fmt;

/// Why a world could not be generated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorldError {
    /// The scenario id is not one of the generated scenarios.
    UnknownScenario(String),
    /// A parameter the scenario reads is missing.
    MissingParam(String),
    /// A parameter has a different type than the scenario reads.
    BadParam {
        /// The parameter name.
        key: String,
        /// What was expected.
        want: &'static str,
    },
    /// The scenario had to draw from, or index into, an empty or too short population (the reference raises there).
    Empty(&'static str),
}

impl fmt::Display for WorldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownScenario(id) => write!(f, "unknown scenario {id}"),
            Self::MissingParam(k) => write!(f, "missing parameter {k}"),
            Self::BadParam { key, want } => write!(f, "parameter {key} must be {want}"),
            Self::Empty(what) => write!(f, "nothing to draw from: {what}"),
        }
    }
}

impl std::error::Error for WorldError {}
