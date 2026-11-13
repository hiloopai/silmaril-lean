//! A tiny `no_std` crate compiled to `wasm32-unknown-unknown`.
//!
//! Every export is a total function on `i32` (wrapping arithmetic, no panics), so the compiled
//! module has no imports, no memory traffic and no traps on these paths.
#![cfg_attr(target_arch = "wasm32", no_std)]

/// Wrapping 32-bit addition.
#[no_mangle]
pub extern "C" fn add(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}

/// Wrapping 32-bit multiplication.
#[no_mangle]
pub extern "C" fn mul(a: i32, b: i32) -> i32 {
    a.wrapping_mul(b)
}

/// Signed maximum.
#[no_mangle]
pub extern "C" fn max(a: i32, b: i32) -> i32 {
    if a < b { b } else { a }
}

/// `2a + 1`, wrapping: always odd.
#[no_mangle]
pub extern "C" fn odd(a: i32) -> i32 {
    a.wrapping_mul(2).wrapping_add(1)
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
