//! The adder as a Wasm module: exports `add`, `checked_add`, `add_comm`.
#![cfg_attr(target_family = "wasm", no_std)]
// Only a Wasm module: empty on other targets.
#![cfg(target_family = "wasm")]

use adder_core::spec;

#[unsafe(no_mangle)]
pub extern "C" fn add(a: i32, b: i32) -> i32 {
    adder_core::add(a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn checked_add(a: i32, b: i32) -> i32 {
    adder_core::checked_add(&mut spec::Wasm, a, b)
}

#[unsafe(no_mangle)]
pub extern "C" fn add_comm(a: i32, b: i32) {
    adder_core::add_comm(&mut spec::Wasm, a, b)
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
