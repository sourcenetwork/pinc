//! The header codecs of the trace: long and short headers, datagrams, and sealed and opened packets.

use std::cell::RefCell;
use std::fmt::Write as _;

use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{Aead, Capabilities, CryptoError, Provider, Secret, Software};
use vinc_security::{HeaderKey, PacketKey};
use vinc_tests::SplitMix64;
use vinc_transport::packet::{
    ConnId, Header, LongHeader, LongType, PacketError, PnLayout, ShortHeader, Unprotected, open, packets, sample_at,
    seal, short_dcid, short_header_len, unprotect_header,
};
use vinc_wire::{WireError, Writer};

/// [`Software`] that keeps the associated data of every seal and open.
pub struct Rec {
    inner: Software,
    aad: RefCell<Option<Vec<u8>>>,
}

impl Provider for Rec {
    type AeadKey = <Software as Provider>::AeadKey;
    type HpKey = <Software as Provider>::HpKey;
    type X25519Secret = <Software as Provider>::X25519Secret;
    type KemEncapsKey = <Software as Provider>::KemEncapsKey;
    type KemDecapsKey = <Software as Provider>::KemDecapsKey;
    type KemCiphertext = <Software as Provider>::KemCiphertext;

    fn capabilities(&self) -> Capabilities {
        self.inner.capabilities()
    }
    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<Self::AeadKey, CryptoError> {
        self.inner.aead_key(alg, key)
    }
    fn seal(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError> {
        *self.aad.borrow_mut() = Some(aad.to_vec());
        self.inner.seal(key, nonce, aad, buf)
    }
    fn open(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError> {
        *self.aad.borrow_mut() = Some(aad.to_vec());
        self.inner.open(key, nonce, aad, buf, tag)
    }
    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<Self::HpKey, CryptoError> {
        self.inner.hp_key(alg, key)
    }
    fn hp_mask(&self, key: &Self::HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN] {
        self.inner.hp_mask(key, sample)
    }
    fn sha256(&self, data: &[u8]) -> [u8; 32] {
        self.inner.sha256(data)
    }
    fn x25519_secret(&self, seed: &[u8; 32]) -> Self::X25519Secret {
        self.inner.x25519_secret(seed)
    }
    fn x25519_public(&self, secret: &Self::X25519Secret) -> [u8; 32] {
        self.inner.x25519_public(secret)
    }
    fn x25519_dh(&self, secret: &Self::X25519Secret, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError> {
        self.inner.x25519_dh(secret, peer)
    }
    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (Self::KemDecapsKey, Self::KemEncapsKey) {
        self.inner.kem_keygen(d, z)
    }
    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<Self::KemEncapsKey, CryptoError> {
        self.inner.kem_encaps_key(bytes)
    }
    fn kem_encaps_key_bytes(&self, ek: &Self::KemEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN] {
        self.inner.kem_encaps_key_bytes(ek)
    }
    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<Self::KemCiphertext, CryptoError> {
        self.inner.kem_ciphertext(bytes)
    }
    fn kem_ciphertext_bytes(&self, ct: &Self::KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN] {
        self.inner.kem_ciphertext_bytes(ct)
    }
    fn kem_encapsulate(
        &self,
        ek: &Self::KemEncapsKey,
        m: &[u8; 32],
    ) -> Result<(Self::KemCiphertext, Secret<32>), CryptoError> {
        self.inner.kem_encapsulate(ek, m)
    }
    fn kem_decapsulate(&self, dk: &Self::KemDecapsKey, ct: &Self::KemCiphertext) -> Result<Secret<32>, CryptoError> {
        self.inner.kem_decapsulate(dk, ct)
    }
}

/// The name of an error and the number it carries (the bytes missing, or the version found).
pub fn err_name(e: &PacketError) -> (&'static str, u64) {
    match e {
        PacketError::Wire(WireError::Truncated { needed }) => ("Truncated", *needed as u64),
        PacketError::Wire(WireError::BufferTooSmall { needed }) => ("BufferTooSmall", *needed as u64),
        PacketError::Wire(WireError::VarintTooLong) => ("VarintTooLong", 0),
        PacketError::Wire(WireError::VarintOverflow) => ("VarintOverflow", 0),
        PacketError::Wire(WireError::VarintNonMinimal) => ("VarintNonMinimal", 0),
        PacketError::Form => ("Form", 0),
        PacketError::LongType => ("LongType", 0),
        PacketError::Version(v) => ("Version", u64::from(*v)),
        PacketError::ConnIdLength => ("ConnIdLength", 0),
        PacketError::Reserved => ("Reserved", 0),
        PacketError::PnLength => ("PnLength", 0),
        PacketError::TooShort => ("TooShort", 0),
        PacketError::Length => ("Length", 0),
        PacketError::Record(_) => ("Record", 0),
        _ => ("other", 0),
    }
}

pub fn arr(b: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in b.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "{x}");
    }
    s.push(']');
    s
}

pub fn pick(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

pub fn bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

pub fn cid(rng: &mut SplitMix64) -> ConnId {
    let len = [0, 1, 4, 8, 19, 20, pick(rng, 21)][pick(rng, 7) as usize] as usize;
    ConnId::new(&bytes(rng, len)).unwrap()
}

pub fn ty_bits(ty: LongType) -> u8 {
    match ty {
        LongType::Handshake => 0,
        LongType::ZeroRtt => 1,
    }
}

/// One `LongHeader::write` into a buffer of `cap` bytes: the event, and the bytes written if it succeeded.
pub fn long_write(out: &mut String, h: &LongHeader, pn_len: usize, cap: usize) -> Option<Vec<u8>> {
    let mut buf = vec![0xeeu8; cap];
    let mut w = Writer::new(&mut buf);
    let r = h.write(&mut w, pn_len);
    let written = w.written().to_vec();
    let (e, n) = r.as_ref().err().map_or(("ok", 0), err_name);
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"lw","ty":{},"dcid":{},"scid":{},"bl":{},"pn":{pn_len},"cap":{cap},"err":"{e}","n":{n},"b":{}}}"#,
        ty_bits(h.ty),
        arr(h.dcid.as_bytes()),
        arr(h.scid.as_bytes()),
        h.body_len,
        arr(&written)
    );
    if r.is_err() {
        assert!(written.is_empty(), "a refused write wrote {} bytes", written.len());
        return None;
    }
    assert_eq!(written.len(), h.header_len());
    Some(written)
}

/// One `LongHeader::parse`.
pub fn long_parse(out: &mut String, input: &[u8]) -> Result<(LongHeader, usize), PacketError> {
    let r = LongHeader::parse(input);
    match &r {
        Ok((h, hl)) => {
            let _ = writeln!(
                out,
                r#"{{"t":"txhd","op":"lp","in":{},"err":"ok","n":0,"ty":{},"dcid":{},"scid":{},"bl":{},"hl":{hl}}}"#,
                arr(input),
                ty_bits(h.ty),
                arr(h.dcid.as_bytes()),
                arr(h.scid.as_bytes()),
                h.body_len
            );
        }
        Err(e) => {
            let (e, n) = err_name(e);
            let _ = writeln!(
                out,
                r#"{{"t":"txhd","op":"lp","in":{},"err":"{e}","n":{n},"ty":0,"dcid":[],"scid":[],"bl":0,"hl":0}}"#,
                arr(input)
            );
        }
    }
    r
}

pub fn short_write(out: &mut String, h: &ShortHeader, pn: &[u8], cap: usize) -> Option<Vec<u8>> {
    let mut buf = vec![0xeeu8; cap];
    let mut w = Writer::new(&mut buf);
    let r = h.write(&mut w, pn);
    let written = w.written().to_vec();
    let (e, n) = r.as_ref().err().map_or(("ok", 0), err_name);
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"sw","kp":{},"dcid":{},"pn":{},"cap":{cap},"err":"{e}","n":{n},"b":{}}}"#,
        h.key_phase,
        arr(h.dcid.as_bytes()),
        arr(pn),
        arr(&written)
    );
    if r.is_err() {
        assert!(written.is_empty(), "a refused write wrote {} bytes", written.len());
        return None;
    }
    assert_eq!(written.len(), short_header_len(h.dcid.as_bytes().len(), pn.len()));
    Some(written)
}

pub fn short_read(out: &mut String, input: &[u8], dl: usize) -> Result<ConnId, PacketError> {
    let r = short_dcid(input, dl);
    let (e, id) = match &r {
        Ok(id) => ("ok", id.as_bytes().to_vec()),
        Err(e) => (err_name(e).0, Vec::new()),
    };
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"sd","in":{},"dl":{dl},"err":"{e}","id":{}}}"#,
        arr(input),
        arr(&id)
    );
    r
}

/// One datagram through the iterator: every item with the offset of the bytes it lends.
pub fn datagram(out: &mut String, d: &[u8], dl: usize) {
    let mut buf = d.to_vec();
    let base = buf.as_ptr() as usize;
    let total = buf.len();
    let mut items = String::from("[");
    let (mut next, mut ended, mut count) = (0usize, false, 0);
    for it in packets(&mut buf, dl) {
        assert!(!ended, "an item follows a short packet or an error");
        if count > 0 {
            items.push(',');
        }
        count += 1;
        match it {
            Ok(pkt) => {
                let s = pkt.bytes.as_ptr() as usize - base;
                let len = pkt.bytes.len();
                assert_eq!(s, next, "the packets are not back to back");
                assert!(len > 0 && s + len <= total);
                next = s + len;
                let po = pkt.pn_off();
                match pkt.header {
                    Header::Long { header, header_len } => {
                        assert_eq!(len, header_len + header.body_len);
                        let _ = write!(
                            items,
                            r#"{{"k":"long","ty":{},"dcid":{},"scid":{},"bl":{},"hl":{header_len},"s":{s},"len":{len},"po":{po}}}"#,
                            ty_bits(header.ty),
                            arr(header.dcid.as_bytes()),
                            arr(header.scid.as_bytes()),
                            header.body_len
                        );
                    }
                    Header::Short { dcid } => {
                        assert_eq!(next, total, "a short packet does not run to the end");
                        ended = true;
                        let _ = write!(
                            items,
                            r#"{{"k":"short","dcid":{},"s":{s},"len":{len},"po":{po}}}"#,
                            arr(dcid.as_bytes())
                        );
                    }
                }
            }
            Err(e) => {
                ended = true;
                let (e, n) = err_name(&e);
                let _ = write!(items, r#"{{"k":"err","err":"{e}","n":{n},"s":{next}}}"#);
            }
        }
    }
    if !ended {
        assert!(
            d[next..].iter().all(|b| *b == 0),
            "bytes that are not padding were skipped"
        );
    }
    items.push(']');
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"dg","in":{},"dl":{dl},"items":{items}}}"#,
        arr(d)
    );
}

pub struct Keys {
    p: Rec,
    tx: PacketKey<Rec>,
    rx: PacketKey<Rec>,
    hk: HeaderKey<Rec>,
    pn: u64,
}

pub fn keys(aead: Aead, tag: u8) -> Keys {
    let p = Rec {
        inner: Software,
        aad: RefCell::new(None),
    };
    let s = Secret::new([tag; 32]);
    Keys {
        tx: PacketKey::from_secret(&p, aead, &s).unwrap(),
        rx: PacketKey::from_secret(&p, aead, &s).unwrap(),
        hk: HeaderKey::from_secret(&p, aead, &s).unwrap(),
        p,
        pn: 0,
    }
}

/// One `seal` of `buf`, which holds the header and the payload: the event has the buffer before the call and the
/// associated data the AEAD was given.
pub fn seal_ev(out: &mut String, k: &mut Keys, buf: &mut [u8], layout: PnLayout, payload_len: usize) -> Option<usize> {
    let before = buf.to_vec();
    *k.p.aad.borrow_mut() = None;
    k.pn += 1;
    let r = seal(&mut k.tx, &k.hk, &k.p, buf, layout, payload_len, k.pn);
    let aad = k.p.aad.borrow_mut().take();
    let (e, n) = r.as_ref().err().map_or(("ok", 0), err_name);
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"seal","pk":{},"po":{},"pl":{},"pay":{payload_len},"err":"{e}","n":{n},"aad":{},"total":{}}}"#,
        arr(&before),
        layout.pn_off,
        layout.pn_len,
        arr(aad.as_deref().unwrap_or_default()),
        r.as_ref().map_or(0, |t| *t)
    );
    if r.is_ok() {
        let aad = aad.unwrap();
        assert_eq!(
            aad,
            before[..layout.pn_off + layout.pn_len],
            "the associated data is not the header as written"
        );
    } else {
        assert!(aad.is_none(), "a refused seal reached the AEAD");
    }
    r.ok()
}

/// One `open` of `packet` (header protection already removed): the event has the packet before the call and the
/// associated data the AEAD was given, if the call reached it.
pub fn open_ev(out: &mut String, k: &mut Keys, packet: &mut [u8], pn_off: usize, un: &Unprotected) -> bool {
    let before = packet.to_vec();
    *k.p.aad.borrow_mut() = None;
    let r = open(&mut k.rx, &k.p, packet, pn_off, un, None);
    let aad = k.p.aad.borrow_mut().take();
    let (e, _) = r.as_ref().err().map_or(("ok", 0), err_name);
    let (ps, pe) = r.as_ref().map_or((0, 0), |o| (o.payload_start, o.payload_end));
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"open","pk":{},"po":{pn_off},"pl":{},"err":"{e}","reached":{},"aad":{},"ps":{ps},"pe":{pe}}}"#,
        arr(&before),
        un.pn_len,
        aad.is_some(),
        arr(aad.as_deref().unwrap_or_default())
    );
    if let Some(aad) = &aad {
        assert_eq!(
            aad[..],
            before[..pn_off + un.pn_len],
            "the associated data is not the header received"
        );
    }
    r.is_ok()
}

/// Seal a packet whose header is `hdr` (packet number included), read it back through `unprotect_header` and
/// `open`, and call `open` on cut and damaged copies.
pub fn sealed(out: &mut String, rng: &mut SplitMix64, k: &mut Keys, hdr: &[u8], layout: PnLayout) {
    let pay = [0, 1, 2, 3, 20, pick(rng, 40)][pick(rng, 6) as usize] as usize;
    let room = hdr.len() + pay + 16;
    let room = match pick(rng, 8) {
        0 => room - 1 - pick(rng, 16) as usize,
        1 => room + 1 + pick(rng, 4) as usize,
        _ => room,
    };
    let mut buf = vec![0u8; room.max(hdr.len())];
    buf[..hdr.len()].copy_from_slice(hdr);
    let filled = (hdr.len() + pay).min(buf.len());
    rng.fill(&mut buf[hdr.len()..filled]);
    let mut first = buf[0];
    if pick(rng, 5) == 0 {
        // a reserved bit, or another packet-number length, under the mask
        first ^= [0x04, 0x08, 0x0c, 0x01, 0x02, 0x03][pick(rng, 6) as usize];
        buf[0] = first;
    }
    let plain = buf.clone();
    let Some(total) = seal_ev(out, k, &mut buf, layout, pay) else {
        return;
    };
    assert_eq!(total, hdr.len() + pay + 16);
    let packet = &mut buf[..total];
    let prot = packet.to_vec();
    let un = unprotect_header(&k.hk, &k.p, packet, layout.pn_off, layout.long);
    // the sample taken from the protected packet is the one the mask was made from: unmasking leaves it as it was
    let s_prot = sample_at(&prot, layout.pn_off);
    let s_plain = sample_at(packet, layout.pn_off);
    assert_eq!(s_prot, s_plain, "unmasking changed the sample");
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"smpp","p":{},"u":{},"po":{},"s":{}}}"#,
        arr(&prot),
        arr(packet),
        layout.pn_off,
        arr(s_prot.as_ref().map_or(&[][..], |s| &s[..]))
    );
    let pl = un.as_ref().map_or(0, |u| u.pn_len);
    let (e, _) = un.as_ref().err().map_or(("ok", 0), err_name);
    let _ = writeln!(
        out,
        r#"{{"t":"txhd","op":"un","first":{},"pn":{},"err":"{e}","pl":{pl},"kp":{},"tr":{}}}"#,
        packet[0],
        arr(&packet[layout.pn_off..layout.pn_off + pl]),
        un.as_ref().is_ok_and(Unprotected::key_phase),
        un.as_ref().map_or(0, |u| u.truncated)
    );
    assert_eq!(packet[0], first, "the first byte did not come back");
    let Ok(un) = un else { return };
    assert_eq!(
        packet[..layout.pn_off + pl.min(layout.pn_len)],
        plain[..layout.pn_off + pl.min(layout.pn_len)]
    );
    let mut copy = packet.to_vec();
    let ok = open_ev(out, k, packet, layout.pn_off, &un);
    assert_eq!(
        ok,
        pl == layout.pn_len,
        "a packet opens exactly with its own packet-number length"
    );
    if ok {
        assert_eq!(
            packet[..total - 16],
            plain[..total - 16],
            "the header and the payload did not come back"
        );
    }
    // cut below the tag, cut inside the header, and a damaged header byte
    let cut = (layout.pn_off + pl + pick(rng, 16) as usize).min(total);
    let _ = open_ev(out, k, &mut copy.clone()[..cut], layout.pn_off, &un);
    let cut = pick(rng, (layout.pn_off + pl) as u64) as usize;
    let _ = open_ev(out, k, &mut copy.clone()[..cut], layout.pn_off, &un);
    let at = pick(rng, (layout.pn_off + pl) as u64) as usize;
    copy[at] ^= 1 << pick(rng, 8);
    assert!(
        !open_ev(out, k, &mut copy, layout.pn_off, &un),
        "a changed header byte still opens"
    );
}

pub fn body_len(rng: &mut SplitMix64, wide: bool) -> usize {
    if wide {
        let edges: [u64; 12] = [
            (1 << 31) - 1,
            1 << 31,
            (1 << 56) - 1,
            1 << 56,
            (1 << 62) + 5,
            (1 << 63) - 2,
            (1 << 63) - 1,
            1 << 63,
            (1 << 63) + 1,
            u64::MAX - 1,
            u64::MAX,
            rng.next_u64(),
        ];
        return usize::try_from(edges[pick(rng, 12) as usize]).unwrap_or(usize::MAX);
    }
    let edges = [
        0,
        1,
        2,
        126,
        127,
        128,
        129,
        16383,
        16384,
        2_097_151,
        2_097_152,
        (1 << 28) - 1,
        1 << 28,
        (1 << 31) - 1,
    ];
    match pick(rng, 4) {
        0 => edges[pick(rng, edges.len() as u64) as usize],
        1 => pick(rng, 1 << 20) as usize,
        _ => pick(rng, 60) as usize,
    }
}

pub fn long_run(rng: &mut SplitMix64, out: &mut String, wide: bool, n: u32) {
    for i in 0..n {
        let ty = if pick(rng, 2) == 0 {
            LongType::Handshake
        } else {
            LongType::ZeroRtt
        };
        let h = LongHeader {
            ty,
            dcid: cid(rng),
            scid: cid(rng),
            body_len: body_len(rng, wide),
        };
        let hl = h.header_len();
        let good = usize::from(ty == LongType::ZeroRtt) * 2;
        // every packet-number length into a buffer around the header's size
        for pn_len in 0..4 {
            let cap = [0, hl - 1, hl, hl + 1, pick(rng, hl as u64 + 4) as usize][pick(rng, 5) as usize];
            let _ = long_write(out, &h, pn_len, cap);
        }
        let _ = long_write(out, &h, good, hl - 1 - pick(rng, hl as u64 - 1) as usize);
        let Some(enc) = long_write(out, &h, good, hl + pick(rng, 3) as usize) else {
            assert!(h.body_len as u64 >= 1 << 63, "a header that fits was refused");
            continue;
        };
        if wide {
            continue;
        }
        // read back with the body and something after it
        if h.body_len <= 200 {
            let mut whole = enc.clone();
            whole.extend(bytes(rng, h.body_len));
            let trail = pick(rng, 4) as usize;
            whole.extend(bytes(rng, trail));
            let (back, n) = long_parse(out, &whole).unwrap();
            assert_eq!((back, n), (h, hl), "the header did not come back");
            if h.body_len > 0 {
                let short = hl + pick(rng, h.body_len as u64) as usize;
                assert_eq!(long_parse(out, &whole[..short]).err(), Some(PacketError::Length));
            }
            // the low four bits of a 0-RTT first byte are under the mask: any value parses to the same header
            if ty == LongType::ZeroRtt {
                whole[0] = (whole[0] & 0xf0) | pick(rng, 16) as u8;
                assert_eq!(long_parse(out, &whole).unwrap(), (h, hl));
            }
            // an id length one past the longest id
            for at in [2, 3 + h.dcid.as_bytes().len()] {
                let mut bad = whole.clone();
                bad[at] = 21;
                bad.extend(bytes(rng, 24));
                assert_eq!(long_parse(out, &bad).err(), Some(PacketError::ConnIdLength));
            }
            // one byte of the header changed
            let at = [0, 1, 2, 3 + h.dcid.as_bytes().len(), pick(rng, hl as u64) as usize][pick(rng, 5) as usize];
            let mut bad = whole.clone();
            bad[at] = rng.next_u64() as u8;
            if let Ok((back, n)) = long_parse(out, &bad) {
                // accepted: it is the encoding of what it yields
                let mut again = vec![0u8; n];
                back.write(
                    &mut Writer::new(&mut again),
                    usize::from(back.ty == LongType::ZeroRtt) * 2,
                )
                .unwrap();
                assert_eq!(
                    again[1..],
                    bad[1..n],
                    "an accepted header is not the encoding of its fields"
                );
                assert_eq!(again[0] & 0xf0, bad[0] & 0xf0);
            }
        } else {
            let mut whole = enc.clone();
            whole.extend(bytes(rng, 3));
            assert_eq!(long_parse(out, &whole).err(), Some(PacketError::Length));
        }
        // a length that is no varint: too long, not minimal, cut
        if i % 8 == 1 {
            let fixed = 4 + h.dcid.as_bytes().len() + h.scid.as_bytes().len();
            for tail in [
                &[0x80u8; 9][..],
                &[0xff; 12],
                &[0x80, 0x00],
                &[0xff, 0x80, 0x00, 0x01],
                &[0x80; 3],
                &[0xff; 8],
            ] {
                let mut bad = enc[..fixed].to_vec();
                bad.extend_from_slice(tail);
                assert!(long_parse(out, &bad).is_err());
            }
        }
        // cut at every length
        if i % 4 == 0 {
            for m in 0..hl {
                let r = long_parse(out, &enc[..m]);
                assert!(
                    matches!(r, Err(PacketError::Wire(WireError::Truncated { .. }))),
                    "a header cut at {m} of {hl} gave {r:?}"
                );
            }
        }
    }
}

pub fn short_run(rng: &mut SplitMix64, out: &mut String, n: u32) {
    for _ in 0..n {
        let h = ShortHeader {
            key_phase: pick(rng, 2) == 0,
            dcid: cid(rng),
        };
        let dl = h.dcid.as_bytes().len();
        for pl in 0..6 {
            let pn = bytes(rng, pl);
            let hl = short_header_len(dl, pl);
            let cap = [0, hl - 1, hl, hl + 1, pick(rng, hl as u64 + 4) as usize][pick(rng, 5) as usize];
            let Some(enc) = short_write(out, &h, &pn, cap) else {
                continue;
            };
            let mut whole = enc.clone();
            let trail = pick(rng, 5) as usize;
            whole.extend(bytes(rng, trail));
            assert_eq!(short_read(out, &whole, dl).unwrap(), h.dcid, "the id did not come back");
            for other in [0, dl + 1, 20, 21, pick(rng, 30) as usize] {
                let _ = short_read(out, &whole, other);
            }
            let cut = pick(rng, 1 + dl as u64) as usize;
            assert_eq!(short_read(out, &whole[..cut], dl).err(), Some(PacketError::TooShort));
            whole[0] = rng.next_u64() as u8;
            let _ = short_read(out, &whole, dl);
        }
    }
}

/// A long packet with a body of random bytes.
pub fn long_packet(rng: &mut SplitMix64) -> Vec<u8> {
    let ty = if pick(rng, 2) == 0 {
        LongType::Handshake
    } else {
        LongType::ZeroRtt
    };
    let h = LongHeader {
        ty,
        dcid: cid(rng),
        scid: cid(rng),
        body_len: pick(rng, 40) as usize,
    };
    let mut buf = vec![0u8; h.header_len() + h.body_len];
    let mut w = Writer::new(&mut buf);
    h.write(&mut w, usize::from(ty == LongType::ZeroRtt) * 2).unwrap();
    let hl = h.header_len();
    rng.fill(&mut buf[hl..]);
    buf
}

pub fn datagram_run(rng: &mut SplitMix64, out: &mut String, n: u32) {
    for _ in 0..n {
        let dl = [0, 4, 8, 20, 21, pick(rng, 24)][pick(rng, 6) as usize] as usize;
        let mut d = Vec::new();
        for _ in 0..pick(rng, 4) {
            d.extend(long_packet(rng));
        }
        match pick(rng, 6) {
            0 | 1 => {
                // a short packet with an id of the configured length, or one byte too short for it
                d.push(0x40 | (pick(rng, 32) as u8));
                let rest = if pick(rng, 4) == 0 {
                    dl.saturating_sub(1)
                } else {
                    dl + pick(rng, 30) as usize
                };
                d.extend(bytes(rng, rest));
            }
            2 => d.extend(vec![0u8; pick(rng, 12) as usize]),
            3 => {
                d.extend(vec![0u8; 1 + pick(rng, 4) as usize]);
                d.push(1 + pick(rng, 255) as u8);
            }
            4 => {
                let len = 1 + pick(rng, 6) as usize;
                d.extend(bytes(rng, len));
            }
            _ => {}
        }
        match pick(rng, 6) {
            0 if !d.is_empty() => d.truncate(pick(rng, d.len() as u64) as usize),
            1 if !d.is_empty() => {
                let at = pick(rng, d.len() as u64) as usize;
                d[at] = rng.next_u64() as u8;
            }
            _ => {}
        }
        datagram(out, &d, dl);
    }
    // bytes with no structure
    for _ in 0..n / 4 {
        let len = pick(rng, 24) as usize;
        let mut d = bytes(rng, len);
        if let Some(b) = d.first_mut() {
            *b = [0, 0x40, 0x7f, 0xc0, 0xd1, 0xe0, *b][pick(rng, 7) as usize];
        }
        datagram(out, &d, pick(rng, 4) as usize);
    }
}

/// The low `len` bytes of `pn`, big-endian: the packet number the next seal uses.
pub fn pn_bytes(pn: u64, len: usize) -> Vec<u8> {
    pn.to_be_bytes()[8 - len..].to_vec()
}

pub fn sealed_run(rng: &mut SplitMix64, out: &mut String, n: u32) {
    for aead in [Aead::ChaCha20Poly1305, Aead::Aes128Gcm] {
        let mut k = keys(aead, 7);
        for _ in 0..n {
            if pick(rng, 3) == 0 {
                // a 0-RTT packet: the long header, then the two bytes of the packet number
                let (dcid, scid) = (cid(rng), cid(rng));
                let pay = pick(rng, 40) as usize;
                let h = LongHeader {
                    ty: LongType::ZeroRtt,
                    dcid,
                    scid,
                    body_len: 2 + pay + 16,
                };
                let mut hdr = vec![0u8; h.header_len() + 2];
                let mut w = Writer::new(&mut hdr);
                h.write(&mut w, 2).unwrap();
                w.put_slice(&pn_bytes(k.pn + 1, 2)).unwrap();
                let layout = PnLayout {
                    pn_off: h.header_len(),
                    pn_len: 2,
                    long: true,
                };
                sealed(out, rng, &mut k, &hdr, layout);
            } else {
                let h = ShortHeader {
                    key_phase: pick(rng, 2) == 0,
                    dcid: cid(rng),
                };
                let pl = 2 + pick(rng, 2) as usize;
                let dl = h.dcid.as_bytes().len();
                let mut hdr = vec![0u8; short_header_len(dl, pl)];
                h.write(&mut Writer::new(&mut hdr), &pn_bytes(k.pn + 1, pl)).unwrap();
                sealed(
                    out,
                    rng,
                    &mut k,
                    &hdr,
                    PnLayout {
                        pn_off: 1 + dl,
                        pn_len: pl,
                        long: false,
                    },
                );
            }
        }
    }
}
