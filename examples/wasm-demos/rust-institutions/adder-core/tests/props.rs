//! Native tests of the adder: the same Rust source that is compiled to Wasm, with the `spec`
//! imports replaced by `spec::Observer`, which records every import call.

use adder_core::spec::{Event, Observer};
use adder_core::{add, add_comm, checked_add};
use proptest::prelude::*;

fn trace(f: impl FnOnce(&mut Observer<&mut dyn FnMut(Event)>)) -> Vec<Event> {
    let mut log = Vec::new();
    let mut push = |e| log.push(e);
    f(&mut Observer(&mut push));
    log
}

#[test]
fn add_unit() {
    assert_eq!(add(2, 3), 5);
    assert_eq!(add(i32::MAX, 1), i32::MIN);
}

proptest! {
    #[test]
    fn add_commutative(a: i32, b: i32) {
        prop_assert_eq!(add(a, b), add(b, a));
    }

    #[test]
    fn add_associative(a: i32, b: i32, c: i32) {
        prop_assert_eq!(add(add(a, b), c), add(a, add(b, c)));
    }

    /// The import trace of `add_comm` is exactly one `assert(1)`.
    #[test]
    fn add_comm_asserts_true(a: i32, b: i32) {
        prop_assert_eq!(trace(|s| add_comm(s, a, b)), vec![Event::assert(1)]);
    }

    /// `checked_add` raises the alarm exactly when the mathematical sum overflows `i32`.
    #[test]
    fn checked_add_alarm_iff_overflow(a: i32, b: i32) {
        let overflow = (a as i64 + b as i64) != (a.wrapping_add(b) as i64);
        let mut r = 0;
        let t = trace(|s| r = checked_add(s, a, b));
        prop_assert_eq!(t == vec![Event::alarm()], overflow);
        prop_assert_eq!(t.is_empty(), !overflow);
        if !overflow { prop_assert_eq!(r, a + b); }
    }
}
