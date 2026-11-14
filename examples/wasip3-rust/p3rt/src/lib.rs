//! The two items a `no_std` component needs: a global allocator (`dlmalloc`, the allocator
//! Rust's `std` uses on wasm) and a panic handler that traps.  With no `std`, no wasi-libc
//! symbols are linked, so the components import WASI 0.3 interfaces only.  Without wasi-libc
//! nothing provides `cabi_realloc` either (wit-bindgen links its own only on `wasm32-wasip1`
//! and `wasm32-unknown-unknown`), so it is defined here, as in `wit_bindgen::rt`.
#![no_std]

extern crate alloc;

#[global_allocator]
static ALLOC: dlmalloc::GlobalDlmalloc = dlmalloc::GlobalDlmalloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    core::arch::wasm32::unreachable()
}

/// The canonical ABI's allocation function (`wit_bindgen::rt::cabi_realloc`'s definition).
///
/// # Safety
/// Called by the host with the canonical ABI's arguments only.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn cabi_realloc(
    old_ptr: *mut u8,
    old_len: usize,
    align: usize,
    new_len: usize,
) -> *mut u8 {
    use alloc::alloc::{alloc, realloc, Layout};
    let ptr = unsafe {
        if old_len == 0 {
            if new_len == 0 {
                return align as *mut u8;
            }
            alloc(Layout::from_size_align_unchecked(new_len, align))
        } else {
            realloc(old_ptr, Layout::from_size_align_unchecked(old_len, align), new_len)
        }
    };
    if ptr.is_null() {
        core::arch::wasm32::unreachable();
    }
    ptr
}
