//! Property tests, all run on the committed AssemblyScript `adder.wasm` in `wasmi`.
//!
//! Unlike the Rust demo, there is no native run of the source: the `wasm_*` properties are
//! checked on the compiled module directly, and `wasm_agrees_with_source` is a differential
//! test against the hand transcription `as_adder_harness::src`.

use as_adder_harness::{check_case, src, Compiled};
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn wasm_add_commutative(a: i32, b: i32) {
        let mut c = Compiled::new();
        prop_assert_eq!(c.add(a, b), c.add(b, a));
    }

    #[test]
    fn wasm_add_associative(a: i32, b: i32, k: i32) {
        let mut c = Compiled::new();
        let (ab, bk) = (c.add(a, b), c.add(b, k));
        prop_assert_eq!(c.add(ab, k), c.add(a, bk));
    }

    #[test]
    fn wasm_mul_commutative(a: i32, b: i32) {
        let mut c = Compiled::new();
        prop_assert_eq!(c.mul(a, b), c.mul(b, a));
    }

    #[test]
    fn wasm_max_is_upper_bound(a: i32, b: i32) {
        let mut c = Compiled::new();
        let m = c.max(a, b);
        prop_assert!(m >= a && m >= b && (m == a || m == b));
    }

    #[test]
    fn wasm_odd_is_odd(a: i32) {
        let mut c = Compiled::new();
        prop_assert_eq!(c.odd(a) & 1, 1);
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
    assert_eq!(src::odd(i32::MAX), -1);
}
