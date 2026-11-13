// kind: reactor
// A WASI preview 1 reactor (cdylib) whose exports are the world's functions (reactor.wit): it
// writes to stdout through the adapter and keeps state across calls within an instance.
use std::sync::atomic::{AtomicU32, Ordering};
static CALLS: AtomicU32 = AtomicU32::new(0);

#[no_mangle]
pub extern "C" fn add(a: u32, b: u32) -> u32 {
    let n = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
    println!("add({a}, {b}) call {n}");
    a.wrapping_add(b)
}

#[no_mangle]
pub extern "C" fn scale(x: f64, k: i32) -> f64 {
    eprintln!("scale by {k}");
    x * k as f64
}
