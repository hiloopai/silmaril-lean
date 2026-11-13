//! The smallest demo: an adder over the `spec` institution (the logic; `adder` exports it).
//!
//! Exports `add`, `checked_add` and `add_comm`; imports `spec.alarm : [] -> []` and
//! `spec.assert : [i32] -> []`. Questions (answered on the compiled `.wasm`, see the README):
//!
//! * `spec.alarm` is never called while `add` is active (`never-call-from`): proved;
//! * `spec.assert` never receives `0` (`assert-never-false`): proved — rustc/LLVM folded
//!   `a + b == b + a` to `1`, and the checker confirms it on the binary.
#![cfg_attr(target_family = "wasm", no_std)]

institution::institution! {
    /// The specification institution.
    pub mod spec = "spec" {
        /// Raise an alarm: a call means "something bad happened".
        fn alarm();
        /// An assertion: a call with `0` is a violation.
        fn assert(cond: i32);
    }
}

use spec::Api;

/// Wrapping addition; never raises the alarm.
pub fn add(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}

/// Addition that raises the alarm on overflow (and returns `0`).
pub fn checked_add<S: Api>(s: &mut S, a: i32, b: i32) -> i32 {
    match a.checked_add(b) {
        Some(c) => c,
        None => {
            s.alarm();
            0
        }
    }
}

/// Assert that `add` is commutative at `(a, b)`.
pub fn add_comm<S: Api>(s: &mut S, a: i32, b: i32) {
    s.assert((add(a, b) == add(b, a)) as i32);
}
