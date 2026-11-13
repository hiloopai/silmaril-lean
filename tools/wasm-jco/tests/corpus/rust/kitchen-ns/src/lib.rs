#![no_std]
extern crate alloc;
use alloc::{format, string::{String, ToString}, vec::Vec};

#[global_allocator]
static A: dlmalloc::GlobalDlmalloc = dlmalloc::GlobalDlmalloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }

#[unsafe(no_mangle)]
pub unsafe extern "C" fn cabi_realloc(old: *mut u8, old_len: usize, align: usize, new_len: usize) -> *mut u8 {
    use alloc::alloc::{alloc, realloc, Layout};
    if new_len == 0 { return align as *mut u8; }
    unsafe {
        if old_len == 0 { alloc(Layout::from_size_align_unchecked(new_len, align)) }
        else { realloc(old, Layout::from_size_align_unchecked(old_len, align), new_len) }
    }
}

#[path = "../../kitchen/src/kitchen.rs"]
mod kitchen;
include!("../../kitchen/src/impl.rs");
