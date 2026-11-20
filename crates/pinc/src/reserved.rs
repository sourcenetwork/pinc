//! The bytes an application may not sign with the identity key.
//!
//! The identity key also signs the protocol's own statements, so [`check`] refuses data that begins with the start of
//! one: the start of every label (any version), the node record's magic, the beacon's magic and the sleep notice's
//! label. Invariant: every entry of [`PREFIXES`] is built from the constant the module that signs the statement
//! defines, never copied; the tests check each is the start of what that module really signs.
//! Statements signed over a 32-byte hash cannot be told from an application's own hash by a prefix.

use crate::error::{Error, Result};

/// The starts of the statements the protocol signs as plain bytes.
const PREFIXES: [&[u8]; 4] = [
    pinc_crypto::labels::RESERVED.as_bytes(),
    pinc_connect::record::MAGIC_PREFIX,
    pinc_connect::local::MAGIC_PREFIX,
    pinc_connect::relay::sleep::LABEL,
];

/// Refuse `data` that begins with a reserved prefix.
///
/// # Errors
/// [`crate::ErrorKind::Config`] when it does.
pub(crate) fn check(data: &[u8]) -> Result<()> {
    if PREFIXES.iter().any(|p| data.starts_with(p)) {
        return Err(Error::config(
            "these bytes are reserved for the protocol's own signatures",
        ));
    }
    Ok(())
}

#[cfg(all(test, feature = "std"))]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use pinc_connect::record::{Reach, RecordFields};
    use pinc_crypto::{IdentityAlg, Keypair};
    use std::net::SocketAddr;

    fn node() -> pinc_crypto::NodeId {
        Keypair::from_seed(IdentityAlg::Ed25519, &[3; 32]).unwrap().node_id()
    }

    /// What each module really signs, from the module's own functions.
    fn signed_statements() -> [Vec<u8>; 4] {
        let me = node();
        let mut pk = [0u8; pinc_crypto::identity::MAX_PUBLIC_KEY_LEN];
        let pk_len = Keypair::from_seed(IdentityAlg::Ed25519, &[3; 32])
            .unwrap()
            .public_key(&mut pk)
            .unwrap();
        let addrs: [SocketAddr; 1] = ["127.0.0.1:9".parse().unwrap()];
        let fields = RecordFields {
            home: me,
            seq: 1,
            reach: Reach::Public,
            addrs: &addrs,
            hints: &[],
        };
        let mut out = vec![0u8; pinc_connect::record::MAX_RECORD_LEN];
        let n = pinc_connect::record::prepare(&me, &pk[..pk_len], &fields, &mut out).unwrap();
        let record = out[..n].to_vec();
        let mut out = vec![0u8; 512];
        let n = pinc_connect::local::prepare(&me, &pk[..pk_len], 1, &addrs, &[], &mut out).unwrap();
        let beacon = out[..n].to_vec();
        let sleep = pinc_connect::relay::sleep::message(&me, &me, 1).unwrap().to_vec();
        let mut handshake = pinc_crypto::labels::PREFIX.as_bytes().to_vec();
        handshake.extend_from_slice(&[7; 32]);
        [handshake, record, beacon, sleep]
    }

    #[test]
    fn every_prefix_starts_what_its_module_signs() {
        let signed = signed_statements();
        for (prefix, statement) in PREFIXES.iter().zip(&signed) {
            assert!(statement.starts_with(prefix), "{prefix:?}");
            assert!(check(statement).is_err());
            assert!(check(prefix).is_err());
        }
    }

    #[test]
    fn data_that_differs_from_a_prefix_is_signed() {
        for p in PREFIXES {
            let mut last = p.to_vec();
            *last.last_mut().unwrap() ^= 1;
            check(&last).unwrap();
            check(&p[..p.len() - 1]).unwrap();
        }
    }
}
