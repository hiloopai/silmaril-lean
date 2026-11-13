//! Property tests.
//!
//! * `source_*`: properties of the Rust source (run natively). The compiler is trusted here: these
//!   say nothing about the .wasm on their own.
//! * `wasm_*`: properties of the committed `adder.wasm`, run in `wasmi`, including a differential
//!   test against the source.

use adder_harness::{check_case, Compiled};
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn source_add_commutative(a: i32, b: i32) {
        prop_assert_eq!(adder::add(a, b), adder::add(b, a));
    }

    #[test]
    fn source_add_associative(a: i32, b: i32, c: i32) {
        prop_assert_eq!(adder::add(adder::add(a, b), c), adder::add(a, adder::add(b, c)));
    }

    #[test]
    fn source_mul_commutative(a: i32, b: i32) {
        prop_assert_eq!(adder::mul(a, b), adder::mul(b, a));
    }

    #[test]
    fn source_max_is_upper_bound(a: i32, b: i32) {
        let m = adder::max(a, b);
        prop_assert!(m >= a && m >= b && (m == a || m == b));
    }

    #[test]
    fn source_odd_is_odd(a: i32) {
        prop_assert_eq!(adder::odd(a) & 1, 1);
    }

    #[test]
    fn wasm_agrees_with_source(a: i32, b: i32, k: i32) {
        let mut c = Compiled::new();
        prop_assert_eq!(check_case(&mut c, a, b, k), Ok(()));
    }
}

#[test]
fn wasm_boundary_cases() {
    let mut c = Compiled::new();
    let edges = [0, 1, -1, 2, -2, i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1];
    for &a in &edges {
        for &b in &edges {
            for &k in &edges {
                check_case(&mut c, a, b, k).unwrap();
            }
        }
    }
    assert_eq!(c.add(i32::MAX, 1), i32::MIN);
}
