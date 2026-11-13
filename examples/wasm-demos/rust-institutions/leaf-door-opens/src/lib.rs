//! The proposition "the buggy door lock opens for some PIN", as a module whose only import is
//! `env.attest : [] -> []`: export `try_pin(pin)` runs the buggy lock's `enter(pin)` and calls
//! `attest` when the lock's own `spec.attest` fires; the lock's other imports are ignored.
#![cfg_attr(target_family = "wasm", no_std)]
// Only a Wasm module: empty on other targets.
#![cfg(target_family = "wasm")]

institution::institution! {
    /// The Attest encoding's single import.
    pub mod att = "env" {
        fn attest();
    }
}

use door_lock::{door, spec};

static LOCK: door_lock::Global = door_lock::Global::new();

#[unsafe(no_mangle)]
pub extern "C" fn try_pin(pin: i32) {
    let mut s = spec::Observer(|e| {
        if e == spec::Event::attest() {
            att::attest()
        }
    });
    LOCK.with(|l| l.enter::<true, _, _>(&mut s, &mut door::Observer(|_| {}), pin))
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}
