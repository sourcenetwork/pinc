//! Every domain-separation label of the security layer.
//!
//! Invariants: each label is a `pub const` that starts with [`PREFIX`], and all labels are distinct from each other
//! and from the labels of `vinc-crypto`, so no two derivations or signatures in the protocol share a domain. A label
//! is used for exactly one purpose (a transcript, a key derivation or a signature prefix).

/// The prefix of every label.
pub const PREFIX: &str = "VINC 2026 v1 ";
/// Domain of the full handshake transcript, and its first absorbed field.
pub const HANDSHAKE: &str = "VINC 2026 v1 handshake";
/// Domain of the resumption handshake transcript, and its first absorbed field.
pub const RESUME_HANDSHAKE: &str = "VINC 2026 v1 resume handshake";
/// Domain of the initial chaining key.
pub const CHAIN: &str = "VINC 2026 v1 chain";
/// Domain of the hash of an initiator prekey.
pub const KEM_KEY_HASH: &str = "VINC 2026 v1 prekey hash";
/// Prefix of the message the responder signs. Its length equals that of [`SIGNATURE_INITIATOR`].
pub const SIGNATURE_RESPONDER: &str = "VINC 2026 v1 responder";
/// Prefix of the message the initiator signs. Its length equals that of [`SIGNATURE_RESPONDER`].
pub const SIGNATURE_INITIATOR: &str = "VINC 2026 v1 initiator";
/// Derives the handshake secret of the initiator-to-responder direction.
pub const HANDSHAKE_INITIATOR: &str = "VINC 2026 v1 handshake secret initiator";
/// Derives the handshake secret of the responder-to-initiator direction.
pub const HANDSHAKE_RESPONDER: &str = "VINC 2026 v1 handshake secret responder";
/// Derives the application secret of the initiator-to-responder direction.
pub const APPLICATION_INITIATOR: &str = "VINC 2026 v1 application secret initiator";
/// Derives the application secret of the responder-to-initiator direction.
pub const APPLICATION_RESPONDER: &str = "VINC 2026 v1 application secret responder";
/// Derives the resumption secret of a session.
pub const RESUMPTION: &str = "VINC 2026 v1 resumption secret";
/// Derives the pre-shared key of a ticket from the resumption secret and the ticket id.
pub const TICKET: &str = "VINC 2026 v1 ticket";
/// Derives the binder key from a pre-shared key.
pub const BINDER: &str = "VINC 2026 v1 binder";
/// Derives the early-data secret from a pre-shared key and the resume Hello transcript.
pub const EARLY_DATA: &str = "VINC 2026 v1 early data";
/// Derives the key of the confirmation tag of a resumption.
pub const RESUME_CONFIRM: &str = "VINC 2026 v1 resume confirm";
/// Derives the secret of a sub-session from a parent application secret.
pub const SUB_SESSION: &str = "VINC 2026 v1 sub session";
/// Domain of the hash that binds the ALPN and connection ids of a sub-session into its secret.
pub const SUB_SESSION_CONTEXT: &str = "VINC 2026 v1 sub session context";
/// Derives a packet-protection key from a traffic secret.
pub const PACKET_KEY: &str = "VINC 2026 v1 packet key";
/// Derives a packet-protection IV from a traffic secret.
pub const PACKET_IV: &str = "VINC 2026 v1 packet iv";
/// Derives a header-protection key from a traffic secret.
pub const HEADER_KEY: &str = "VINC 2026 v1 header key";
/// Derives the next generation of a traffic secret.
pub const KEY_UPDATE: &str = "VINC 2026 v1 key update";
/// Associated data of an address-validation token.
pub const TOKEN: &str = "VINC 2026 v1 token";

/// Every label above except [`PREFIX`], for tests that check uniqueness and the prefix.
pub const ALL: [&str; 22] = [
    HANDSHAKE,
    RESUME_HANDSHAKE,
    CHAIN,
    KEM_KEY_HASH,
    SIGNATURE_RESPONDER,
    SIGNATURE_INITIATOR,
    HANDSHAKE_INITIATOR,
    HANDSHAKE_RESPONDER,
    APPLICATION_INITIATOR,
    APPLICATION_RESPONDER,
    RESUMPTION,
    TICKET,
    BINDER,
    EARLY_DATA,
    RESUME_CONFIRM,
    SUB_SESSION,
    SUB_SESSION_CONTEXT,
    PACKET_KEY,
    PACKET_IV,
    HEADER_KEY,
    KEY_UPDATE,
    TOKEN,
];
