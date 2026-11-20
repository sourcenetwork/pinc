//! `Core::service` rotates the prekeys exactly when they are due and the identity is not borrowed, offering the
//! identity's store fresh entropy first; the run is recorded for the trace check of the prekey model.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cell::Cell;
use core::fmt::Write as _;
use core::ops::RangeInclusive;

use pinc_security::KeyHandle as WireHandle;

use super::adjacent_tests::{C, core};
use crate::keys::{PREKEY_LIFE, PREKEY_USES, trace_out};

fn st(c: &C) -> String {
    let (held, next, at, used) = c.prekeys.view();
    let held: Vec<String> = held.iter().map(ToString::to_string).collect();
    format!(
        r#"{{"held":[{}],"next":{next},"at":{},"used":{used}}}"#,
        held.join(","),
        trace_out::limbs(at)
    )
}

/// One `service` call at `now`; `borrowed` says the identity is held by the caller of this function.
fn svc(c: &mut C, out: &mut String, now: u64, borrowed: bool, fresh_says: bool) {
    let (held, next, at, used) = c.prekeys.view();
    let due = now >= at || used >= PREKEY_USES;
    let rotates = due && !borrowed;
    let asked = Cell::new(0u32);
    c.service(now, &mut |bytes| {
        asked.set(asked.get() + 1);
        *bytes = [0x77; 32];
        fresh_says
    });
    assert_eq!(
        asked.get(),
        u32::from(rotates),
        "the store is offered fresh bytes exactly once per rotation"
    );
    let (held_after, next_after, at_after, used_after) = c.prekeys.view();
    if rotates {
        assert_eq!(next_after, next + 1);
        assert_eq!(held_after.last(), Some(&next));
        assert_eq!(held_after.len(), (held.len() + 1).min(2));
        assert_eq!(at_after, now.saturating_add(PREKEY_LIFE));
        assert_eq!(used_after, 0);
    } else {
        assert_eq!((held_after, next_after, at_after, used_after), (held, next, at, used));
    }
    writeln!(
        out,
        r#"{{"t":"pk","op":"svc","now":{},"b":{borrowed},"asked":{},"st":{}}}"#,
        trace_out::limbs(now),
        asked.get(),
        st(c)
    )
    .unwrap();
}

/// `n` requests for the newest prekey with a ciphertext it refuses: each is a use.
fn uses(c: &mut C, out: &mut String, n: RangeInclusive<u32>) {
    for _ in n {
        let newest = c.prekeys.view().1 - 1;
        assert!(c.prekeys.decapsulate(WireHandle(newest), &[]).is_none());
        writeln!(
            out,
            r#"{{"t":"pk","op":"dec","h":{newest},"valid":false,"ans":false,"st":{}}}"#,
            st(c)
        )
        .unwrap();
    }
}

#[test]
fn trace_prekey_service() {
    let mut c = core();
    let mut out = String::new();
    assert_eq!(c.prekeys.view(), (alloc::vec![1], 2, 1 + PREKEY_LIFE, 0));
    writeln!(out, r#"{{"t":"pk","op":"load","st":{}}}"#, st(&c)).unwrap();
    svc(&mut c, &mut out, 2, false, true);
    svc(&mut c, &mut out, 1 + PREKEY_LIFE, false, false);
    svc(&mut c, &mut out, 1 + 2 * PREKEY_LIFE, false, true);
    assert_eq!(c.prekeys.view().0, alloc::vec![2, 3], "the first generation is dropped");
    let at = 1 + 3 * PREKEY_LIFE;
    let id = alloc::rc::Rc::clone(&c.identity);
    let g = id.borrow_mut();
    svc(&mut c, &mut out, at, true, true);
    drop(g);
    svc(&mut c, &mut out, at, false, true);
    uses(&mut c, &mut out, 1..=PREKEY_USES);
    svc(&mut c, &mut out, at, false, true);
    svc(&mut c, &mut out, u64::MAX, false, true);
    svc(&mut c, &mut out, u64::MAX, false, true);
    svc(&mut c, &mut out, 5, false, true);
    trace_out::append(&out);
}
