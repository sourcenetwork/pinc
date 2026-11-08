//! Stateless reset: build one and recognise one.

use vinc_crypto::ct_eq;

use super::PacketError;

/// The length of a stateless-reset token.
pub const RESET_TOKEN_LEN: usize = 16;
/// The shortest stateless reset: a short-header-sized prefix and the token.
pub const MIN_RESET_LEN: usize = 25;

/// Build a stateless reset of `len` bytes into `out` and return `len`.
///
/// The first `len - 16` bytes are taken from `random` (the caller supplies unpredictable bytes), with the first byte
/// forced to the short-header form `0b01xx_xxxx`; the token is last. The caller picks `len` smaller than the packet
/// it answers so that two endpoints without state cannot loop.
///
/// # Errors
/// [`PacketError::ResetTooShort`] for `len` under [`MIN_RESET_LEN`], [`PacketError::ResetEntropy`] if `random` has
/// fewer than `len - 16` bytes, a [`PacketError::Wire`] if `out` is shorter than `len`.
pub fn build_stateless_reset(
    out: &mut [u8],
    len: usize,
    random: &[u8],
    token: &[u8; RESET_TOKEN_LEN],
) -> Result<usize, PacketError> {
    if len < MIN_RESET_LEN {
        return Err(PacketError::ResetTooShort);
    }
    let prefix_len = len - RESET_TOKEN_LEN;
    let prefix = random.get(..prefix_len).ok_or(PacketError::ResetEntropy)?;
    let short = len.saturating_sub(out.len());
    let dst = out
        .get_mut(..len)
        .ok_or(vinc_wire::WireError::BufferTooSmall { needed: short })?;
    let (head, tail) = dst.split_at_mut(prefix_len);
    head.copy_from_slice(prefix);
    if let Some(first) = head.first_mut() {
        *first = (*first & 0b0001_1111) | 0b0100_0000;
    }
    tail.copy_from_slice(token);
    Ok(len)
}

/// Whether `datagram` is a stateless reset for any of `tokens`: at least [`MIN_RESET_LEN`] bytes, the short-header
/// first-byte form and a final 16 bytes equal to a token. Every token is compared, in constant time, whatever the
/// outcome.
pub fn is_stateless_reset<'t>(datagram: &[u8], tokens: impl IntoIterator<Item = &'t [u8; RESET_TOKEN_LEN]>) -> bool {
    let Some(tail) = datagram
        .len()
        .checked_sub(RESET_TOKEN_LEN)
        .filter(|_| datagram.len() >= MIN_RESET_LEN)
        .and_then(|at| datagram.get(at..))
    else {
        return false;
    };
    datagram.first().is_some_and(|b| b & 0b1100_0000 == 0b0100_0000)
        & tokens.into_iter().fold(false, |hit, t| hit | ct_eq(t, tail))
}
