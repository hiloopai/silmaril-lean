//! The proposition "`checked_add(a, i32::MAX)` overflows for some `a`", as a module whose only
//! import is `env.attest : [] -> []`: export `probe(a)` calls `attest` when the adder raises its
//! alarm.
#![cfg_attr(target_family = "wasm", no_std)]
// Only a Wasm module: empty on other targets.
#![cfg(target_family = "wasm")]

institution::institution! {
    /// The Attest encoding's single import.
    pub mod att = "env" {
        fn attest();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn probe(a: i32) -> i32 {
    adder_core::checked_add(
        &mut adder_core::spec::Observer(|_| att::attest()),
        a,
        i32::MAX,
    )
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
