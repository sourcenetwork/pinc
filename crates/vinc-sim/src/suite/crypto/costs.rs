//! The CPU cost model: counts of primitive work per node and the reference harness's per-device constants.
//!
//! Invariants: counting is exact and integer; [`Registry::take_work`] converts and resets one node's counters and
//! carries the sub-nanosecond remainder to the next call, so the nanoseconds charged over a run equal the float sum
//! the reference accumulates, up to one nanosecond.

use super::registry::Registry;

/// What one node has done since its counters were last taken.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Work {
    /// AEAD seal and open calls.
    pub aead: u64,
    /// Bytes sealed or opened (an open counts the tag too, as the reference does).
    pub aead_bytes: u64,
    /// Bytes hashed (hashes, MAC inputs, signed and verified messages).
    pub hash_bytes: u64,
    /// X25519 scalar multiplications (public key and shared secret).
    pub x25519: u64,
    /// ML-KEM-768 key generations.
    pub kem_keygen: u64,
    /// ML-KEM-768 encapsulations.
    pub kem_encaps: u64,
    /// ML-KEM-768 decapsulations.
    pub kem_decaps: u64,
    /// Key expansions.
    pub hkdf: u64,
    /// Keyed hashes (key extractions).
    pub mac: u64,
    /// Signatures made.
    pub sign: u64,
    /// Signatures verified.
    pub verify: u64,
}

#[derive(Default)]
pub(super) struct WorkSlot {
    pub(super) work: Work,
    carry: f64,
}

/// The cost of each primitive on one device class, in nanoseconds per call or per byte.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DeviceCosts {
    /// Hashing, per byte.
    pub hash_b: f64,
    /// AEAD, per byte.
    pub aead_b: f64,
    /// AEAD, per call.
    pub aead: f64,
    /// One X25519 multiplication.
    pub x25519: f64,
    /// ML-KEM-768 key generation.
    pub mlkem_keygen: f64,
    /// ML-KEM-768 encapsulation.
    pub mlkem_encaps: f64,
    /// ML-KEM-768 decapsulation.
    pub mlkem_decaps: f64,
    /// One signature.
    pub sign: f64,
    /// One verification.
    pub verify: f64,
    /// One key expansion.
    pub hkdf: f64,
    /// One keyed hash.
    pub mac: f64,
    /// Verifying a slice, per byte (the store charges it).
    pub verify_slice_b: f64,
    /// One interpreted tick of the reference (not used by the real endpoint).
    pub tick: f64,
    /// One transmit call.
    pub io_call: f64,
    /// One transmitted segment.
    pub io_seg: f64,
}

impl DeviceCosts {
    /// A cloud server.
    pub const CLOUD: Self = Self {
        hash_b: 0.139,
        aead_b: 0.5,
        aead: 150.0,
        x25519: 40_000.0,
        mlkem_keygen: 25_000.0,
        mlkem_encaps: 30_000.0,
        mlkem_decaps: 32_000.0,
        sign: 20_000.0,
        verify: 50_000.0,
        hkdf: 600.0,
        mac: 200.0,
        verify_slice_b: 0.139,
        tick: 25.0,
        io_call: 1500.0,
        io_seg: 300.0,
    };
    /// A desktop.
    pub const DESKTOP: Self = Self {
        hash_b: 0.2,
        aead_b: 0.7,
        aead: 200.0,
        x25519: 50_000.0,
        mlkem_keygen: 30_000.0,
        mlkem_encaps: 36_000.0,
        mlkem_decaps: 38_000.0,
        sign: 25_000.0,
        verify: 60_000.0,
        hkdf: 800.0,
        mac: 250.0,
        verify_slice_b: 0.2,
        tick: 30.0,
        io_call: 2000.0,
        io_seg: 400.0,
    };
    /// A phone.
    pub const PHONE: Self = Self {
        hash_b: 2.39,
        aead_b: 3.0,
        aead: 600.0,
        x25519: 150_000.0,
        mlkem_keygen: 90_000.0,
        mlkem_encaps: 110_000.0,
        mlkem_decaps: 115_000.0,
        sign: 70_000.0,
        verify: 180_000.0,
        hkdf: 2_400.0,
        mac: 700.0,
        verify_slice_b: 2.39,
        tick: 90.0,
        io_call: 6000.0,
        io_seg: 1200.0,
    };
    /// A browser (WebAssembly): twice the desktop costs, an assumption of the reference.
    pub const BROWSER: Self = Self::DESKTOP.scaled(2.0);

    /// Every cost multiplied by `factor` (a slow CPU, the reference's `cpu_factor`).
    #[must_use]
    pub const fn scaled(self, f: f64) -> Self {
        Self {
            hash_b: self.hash_b * f,
            aead_b: self.aead_b * f,
            aead: self.aead * f,
            x25519: self.x25519 * f,
            mlkem_keygen: self.mlkem_keygen * f,
            mlkem_encaps: self.mlkem_encaps * f,
            mlkem_decaps: self.mlkem_decaps * f,
            sign: self.sign * f,
            verify: self.verify * f,
            hkdf: self.hkdf * f,
            mac: self.mac * f,
            verify_slice_b: self.verify_slice_b * f,
            tick: self.tick * f,
            io_call: self.io_call * f,
            io_seg: self.io_seg * f,
        }
    }

    /// The costs of a device class by its reference name (`cloud`, `desktop`, `phone`, `browser`).
    pub fn named(device: &str) -> Option<Self> {
        match device {
            "cloud" => Some(Self::CLOUD),
            "desktop" => Some(Self::DESKTOP),
            "phone" => Some(Self::PHONE),
            "browser" => Some(Self::BROWSER),
            _ => None,
        }
    }

    /// The nanoseconds of `w` on this device.
    pub fn cost_of(&self, w: &Work) -> f64 {
        w.aead as f64 * self.aead
            + w.aead_bytes as f64 * self.aead_b
            + w.hash_bytes as f64 * self.hash_b
            + w.x25519 as f64 * self.x25519
            + w.kem_keygen as f64 * self.mlkem_keygen
            + w.kem_encaps as f64 * self.mlkem_encaps
            + w.kem_decaps as f64 * self.mlkem_decaps
            + w.hkdf as f64 * self.hkdf
            + w.mac as f64 * self.mac
            + w.sign as f64 * self.sign
            + w.verify as f64 * self.verify
    }
}

impl Registry {
    /// The work `node` did since the last call, in whole nanoseconds on `costs`; resets the counters.
    pub fn take_work(&self, node: usize, costs: &DeviceCosts) -> u64 {
        let mut st = self.st.borrow_mut();
        st.work_mut(node);
        let slot = &mut st.work[node];
        let total = costs.cost_of(&slot.work) + slot.carry;
        slot.work = Work::default();
        let whole = total.floor();
        slot.carry = total - whole;
        whole as u64
    }

    /// The counters of `node` without resetting them.
    pub fn peek_work(&self, node: usize) -> Work {
        self.st.borrow().work.get(node).map(|s| s.work).unwrap_or_default()
    }
}
