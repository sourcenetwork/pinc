//! The sizes an application's build may set.
//!
//! The tables of an endpoint that do not grow with its session table are constants, sized for a node with hundreds of
//! peers. The build of an application may set each one in the environment of the compiler, most simply in the `[env]`
//! table of its `.cargo/config.toml`:
//!
//! | Variable | Sets | Default | Least |
//! |---|---|---|---|
//! | `PINC_EVENT_BASE` | [`EVENT_BASE`](crate::EVENT_BASE) | 1024 | 128 |
//! | `PINC_LEDGER_ENTRIES` | [`LEDGER_ENTRIES`](crate::LEDGER_ENTRIES) | 1024 | 1 |
//! | `PINC_SUBS_SEEN` | [`SUBS_SEEN`](crate::SUBS_SEEN) | 1024 | 1 |
//! | `PINC_PEER_RTTS` | [`PEER_RTTS`](crate::PEER_RTTS) | 256 | 1 |
//! | `PINC_PREKEY_PEERS` | [`PREKEY_PEERS`](crate::PREKEY_PEERS) | 256 | 1 |
//! | `PINC_REJOIN_ADDRS` | the addresses whose last re-join challenge is remembered | 200 | 1 |
//! | `PINC_MAX_DATAGRAM` | [`MAX_DATAGRAM`](crate::MAX_DATAGRAM) | 9216 | 1200 |
//!
//! A variable that is not set leaves its default. One that is not a whole number, or is below the least the endpoint
//! works with, stops the build. A size is one choice for the whole binary: every endpoint in it has the same tables.
//!
//! The sizes change no rule, only how much a node remembers at once and the largest datagram it takes in.

/// The size the build set in `set`, or `default`; `not_a_number` and `too_small` are what stops the build.
pub(crate) const fn parse(
    set: Option<&str>,
    default: usize,
    least: usize,
    not_a_number: &str,
    too_small: &str,
) -> usize {
    let Some(text) = set else { return default };
    let mut digits = text.as_bytes();
    // Nine digits are below `u32::MAX`, which every table needs of its size.
    assert!(!digits.is_empty() && digits.len() <= 9, "{}", not_a_number);
    let mut n = 0;
    while let [digit, rest @ ..] = digits {
        assert!(digit.is_ascii_digit(), "{}", not_a_number);
        n = n * 10 + (*digit - b'0') as usize;
        digits = rest;
    }
    assert!(n >= least, "{}", too_small);
    n
}

/// The size named by a variable of the compiler's environment, with its default and the least it may be.
macro_rules! size {
    ($var:literal, $default:expr, $least:expr) => {
        $crate::sizes::parse(
            option_env!($var),
            $default,
            $least,
            concat!($var, " is not a whole number of at most nine digits"),
            concat!($var, " is below the least the endpoint works with"),
        )
    };
}
pub(crate) use size;

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn a_size_that_is_not_set_is_its_default() {
        assert_eq!(parse(None, 1024, 128, "", ""), 1024);
    }

    #[test]
    fn a_size_that_is_set_is_taken() {
        assert_eq!(parse(Some("128"), 1024, 128, "", ""), 128);
        assert_eq!(parse(Some("65536"), 1024, 128, "", ""), 65536);
    }

    #[test]
    #[should_panic(expected = "below")]
    fn a_size_below_the_least_stops_the_build() {
        parse(Some("127"), 1024, 128, "not a number", "below");
    }

    #[test]
    #[should_panic(expected = "not a number")]
    fn a_size_that_is_not_a_number_stops_the_build() {
        parse(Some("1k"), 1024, 128, "not a number", "below");
    }

    #[test]
    #[should_panic(expected = "not a number")]
    fn an_empty_size_stops_the_build() {
        parse(Some(""), 1024, 128, "not a number", "below");
    }
}
