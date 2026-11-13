//! The door lock with the PIN comparison inverted, as a Wasm module.
#![cfg_attr(target_family = "wasm", no_std)]
// Only a Wasm module: empty on other targets.
#![cfg(target_family = "wasm")]
door_lock::door_exports!(true);
