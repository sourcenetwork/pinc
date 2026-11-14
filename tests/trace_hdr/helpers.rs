//! The `pad_to` and `sample_at` helpers of the trace.

use std::fmt::Write as _;

use vinc_tests::SplitMix64;
use vinc_transport::packet::{pad_to, sample_at};
use vinc_wire::Writer;

use super::headers::{arr, bytes, err_name, pick};

/// `pad_to` on a writer that holds some bytes: the padding is zeros, the writer ends at `max(written, min_len)`, and a
/// refusal writes nothing.
pub fn pad_run(rng: &mut SplitMix64, out: &mut String, n: u32) {
    for _ in 0..n {
        let cap = match pick(rng, 4) {
            0 => pick(rng, 8) as usize,
            _ => pick(rng, 400) as usize,
        };
        let pre = if cap == 0 {
            0
        } else {
            pick(rng, cap.min(150) as u64 + 1) as usize
        };
        let min_len = match pick(rng, 8) {
            0 => cap,
            1 => cap + 1 + pick(rng, 3) as usize,
            2 => pre + [0usize, 1, 62, 63, 64, 65, 127, 128, 129][pick(rng, 9) as usize],
            3 => pre,
            4 => pre.saturating_sub(1),
            _ => pick(rng, 450) as usize,
        };
        let head: Vec<u8> = bytes(rng, pre).into_iter().map(|b| b | 1).collect();
        let mut buf = vec![0xeeu8; cap];
        let mut w = Writer::new(&mut buf);
        w.put_slice(&head).unwrap();
        let r = pad_to(&mut w, min_len);
        let written = w.written().to_vec();
        let (e, k) = r.as_ref().err().map_or(("ok", 0), err_name);
        let _ = writeln!(
            out,
            r#"{{"t":"txhd","op":"pad","cap":{cap},"pre":{},"min":{min_len},"err":"{e}","n":{k},"out":{}}}"#,
            arr(&head),
            arr(&written)
        );
        assert_eq!(
            buf[written.len()..],
            vec![0xeeu8; cap - written.len()],
            "padding went past the writer"
        );
        assert_eq!(written[..pre], head[..], "padding changed what was written");
        if r.is_ok() {
            assert_eq!(written.len(), pre.max(min_len));
            assert!(written[pre..].iter().all(|b| *b == 0));
        } else {
            assert!(min_len > cap);
            assert_eq!(written.len(), pre, "a refused padding wrote");
            assert_eq!(k as usize, min_len - cap);
        }
    }
}

/// `sample_at` on random packets at offsets around the shortest packet it accepts, and (wide) at offsets no slice
/// holds, where the sum with `SAMPLE_SKIP` overflows.
pub fn sample_run(rng: &mut SplitMix64, out: &mut String, wide: bool, n: u32) {
    for _ in 0..n {
        let len = pick(rng, 70) as usize;
        let pk = bytes(rng, len);
        let po = if wide {
            [
                usize::MAX,
                usize::MAX - 3,
                usize::MAX - 4,
                usize::MAX - 19,
                usize::MAX - 20,
                1 << 62,
            ][pick(rng, 6) as usize]
        } else {
            match pick(rng, 7) {
                0 => len.saturating_sub(20),
                1 => len.saturating_sub(19),
                2 => (len + 1).saturating_sub(21),
                3 => len,
                4 => len + 1,
                5 => 0,
                _ => pick(rng, 60) as usize,
            }
        };
        let r = sample_at(&pk, po);
        let (e, _) = r.as_ref().err().map_or(("ok", 0), err_name);
        let _ = writeln!(
            out,
            r#"{{"t":"txhd","op":"smp","pk":{},"po":{po},"err":"{e}","s":{}}}"#,
            arr(&pk),
            arr(r.as_ref().map_or(&[][..], |s| &s[..]))
        );
        match r {
            Ok(s) => assert_eq!(&s[..], &pk[po + 4..po + 20]),
            Err(_) => assert!(po.checked_add(20).is_none_or(|e| e > len)),
        }
    }
}
