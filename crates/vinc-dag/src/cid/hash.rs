//! Block hashing for the supported multihash codes.

use sha2::{Digest, Sha256};

use super::{BLAKE3, CidError, DIGEST_LEN, SHA2_256};

/// The 32-byte digest of `block` under the multihash `code`.
pub(super) fn digest(code: u64, block: &[u8]) -> Result<[u8; DIGEST_LEN], CidError> {
    match code {
        SHA2_256 => Ok(Sha256::digest(block).into()),
        BLAKE3 => Ok(*blake3::hash(block).as_bytes()),
        other => Err(CidError::UnsupportedHash(other)),
    }
}
