//! Property tests.
//!
//! * `source_*`: properties of the C source, compiled natively for the host by `build.rs`. The
//!   compiler is trusted here: on their own these say nothing about the `.wasm`.
//! * `wasm_*`: properties of the committed `adder.wasm`, run in `wasmi`, including a
//!   differential test against the native build of the same C source.

use c_adder_harness::{check_case, gcd_ref, native, Compiled};
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn source_add_commutative(a: i32, b: i32) {
        prop_assert_eq!(native::add(a, b), native::add(b, a));
    }

    #[test]
    fn source_add_associative(a: i32, b: i32, c: i32) {
        prop_assert_eq!(native::add(native::add(a, b), c), native::add(a, native::add(b, c)));
    }

    #[test]
    fn source_mul_commutative(a: i32, b: i32) {
        prop_assert_eq!(native::mul(a, b), native::mul(b, a));
    }

    #[test]
    fn source_max_is_upper_bound(a: i32, b: i32) {
        let m = native::max(a, b);
        prop_assert!(m >= a && m >= b && (m == a || m == b));
    }

    #[test]
    fn source_odd_is_odd(a: i32) {
        prop_assert_eq!(native::odd(a) & 1, 1);
    }

    #[test]
    fn source_popcount_counts_ones(x: u32) {
        prop_assert_eq!(native::popcount(x), x.count_ones() as i32);
    }

    #[test]
    fn source_gcd_divides_and_is_greatest(a: u32, b: u32) {
        let g = native::gcd(a, b);
        prop_assert_eq!(g, gcd_ref(a, b));
        if g != 0 {
            prop_assert_eq!(a % g, 0);
            prop_assert_eq!(b % g, 0);
        } else {
            prop_assert_eq!((a, b), (0, 0));
        }
    }

    #[test]
    fn wasm_agrees_with_source(a: i32, b: i32, k: i32) {
        let mut c = Compiled::new();
        prop_assert_eq!(check_case(&mut c, a, b, k), Ok(()));
    }

    /// Small arguments make `gcd` interesting (many common factors).
    #[test]
    fn wasm_gcd_small(a in 0u32..2000, b in 0u32..2000) {
        let mut c = Compiled::new();
        prop_assert_eq!(c.gcd(a, b), gcd_ref(a, b));
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
    assert_eq!(c.gcd(0, 0), 0);
    assert_eq!(c.gcd(12, 18), 6);
    assert_eq!(c.popcount(u32::MAX), 32);
}

/// Consecutive Fibonacci numbers are the worst case for Euclid's algorithm (most iterations).
#[test]
fn wasm_gcd_fibonacci() {
    let mut c = Compiled::new();
    let (mut f0, mut f1) = (0u32, 1u32);
    while let Some(f2) = f0.checked_add(f1) {
        assert_eq!(c.gcd(f2, f1), 1);
        (f0, f1) = (f1, f2);
    }
}
