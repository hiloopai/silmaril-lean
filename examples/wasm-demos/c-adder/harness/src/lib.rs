//! Runs the committed `adder.wasm` (compiled from `../src/adder.c` by clang) with the `wasmi`
//! interpreter, next to the same C source compiled natively for the host.
//!
//! The bytes are embedded with `include_bytes!`, so the tests and the fuzzer exercise exactly
//! the file that Lean ingests.

use wasmi::{Engine, Linker, Module, Store, TypedFunc};

/// The committed compiled module.
pub const ADDER_WASM: &[u8] = include_bytes!("../../wasm/adder.wasm");

/// The C source, compiled natively by `build.rs` (host `cc`, `-O2`).
pub mod native {
    mod ffi {
        extern "C" {
            pub fn add(a: i32, b: i32) -> i32;
            pub fn mul(a: i32, b: i32) -> i32;
            pub fn max(a: i32, b: i32) -> i32;
            pub fn odd(a: i32) -> i32;
            pub fn popcount(x: u32) -> i32;
            pub fn gcd(a: u32, b: u32) -> u32;
        }
    }
    // SAFETY (all six): the C functions are pure, total functions on their integer arguments
    // (no memory access, no undefined behaviour: arithmetic is on `uint32_t`, `%` only with a
    // non-zero divisor).
    pub fn add(a: i32, b: i32) -> i32 {
        unsafe { ffi::add(a, b) }
    }
    pub fn mul(a: i32, b: i32) -> i32 {
        unsafe { ffi::mul(a, b) }
    }
    pub fn max(a: i32, b: i32) -> i32 {
        unsafe { ffi::max(a, b) }
    }
    pub fn odd(a: i32) -> i32 {
        unsafe { ffi::odd(a) }
    }
    pub fn popcount(x: u32) -> i32 {
        unsafe { ffi::popcount(x) }
    }
    pub fn gcd(a: u32, b: u32) -> u32 {
        unsafe { ffi::gcd(a, b) }
    }
}

/// A reference GCD, written independently of the C source (binary GCD, Stein's algorithm).
pub fn gcd_ref(mut a: u32, mut b: u32) -> u32 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

/// An instance of the committed module with its six function exports.
pub struct Compiled {
    store: Store<()>,
    add: TypedFunc<(i32, i32), i32>,
    mul: TypedFunc<(i32, i32), i32>,
    max: TypedFunc<(i32, i32), i32>,
    odd: TypedFunc<i32, i32>,
    popcount: TypedFunc<i32, i32>,
    gcd: TypedFunc<(i32, i32), i32>,
}

impl Compiled {
    /// Instantiates the committed module (it has no imports).
    pub fn new() -> Self {
        let engine = Engine::default();
        let module = Module::new(&engine, ADDER_WASM).expect("adder.wasm decodes and validates");
        let mut store = Store::new(&engine, ());
        let linker = Linker::<()>::new(&engine);
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("instantiates")
            .start(&mut store)
            .expect("no start trap");
        Compiled {
            add: instance.get_typed_func(&store, "add").expect("export add"),
            mul: instance.get_typed_func(&store, "mul").expect("export mul"),
            max: instance.get_typed_func(&store, "max").expect("export max"),
            odd: instance.get_typed_func(&store, "odd").expect("export odd"),
            popcount: instance.get_typed_func(&store, "popcount").expect("export popcount"),
            gcd: instance.get_typed_func(&store, "gcd").expect("export gcd"),
            store,
        }
    }

    pub fn add(&mut self, a: i32, b: i32) -> i32 {
        self.add.call(&mut self.store, (a, b)).expect("add does not trap")
    }
    pub fn mul(&mut self, a: i32, b: i32) -> i32 {
        self.mul.call(&mut self.store, (a, b)).expect("mul does not trap")
    }
    pub fn max(&mut self, a: i32, b: i32) -> i32 {
        self.max.call(&mut self.store, (a, b)).expect("max does not trap")
    }
    pub fn odd(&mut self, a: i32) -> i32 {
        self.odd.call(&mut self.store, a).expect("odd does not trap")
    }
    /// Wasm `i32` is sign-agnostic; the C parameter is `uint32_t`.
    pub fn popcount(&mut self, x: u32) -> i32 {
        self.popcount.call(&mut self.store, x as i32).expect("popcount does not trap")
    }
    pub fn gcd(&mut self, a: u32, b: u32) -> u32 {
        self.gcd.call(&mut self.store, (a as i32, b as i32)).expect("gcd does not trap") as u32
    }
}

impl Default for Compiled {
    fn default() -> Self {
        Self::new()
    }
}

/// Checks the compiled exports against the natively compiled C source on one input triple;
/// returns a description of the first disagreement.
pub fn check_case(c: &mut Compiled, a: i32, b: i32, k: i32) -> Result<(), String> {
    let (ua, ub) = (a as u32, b as u32);
    let pairs = [
        ("add", c.add(a, b), native::add(a, b)),
        ("mul", c.mul(a, b), native::mul(a, b)),
        ("max", c.max(a, b), native::max(a, b)),
        ("odd", c.odd(a), native::odd(a)),
        ("popcount", c.popcount(ua), native::popcount(ua)),
        ("gcd", c.gcd(ua, ub) as i32, native::gcd(ua, ub) as i32),
    ];
    for (name, wasm, src) in pairs {
        if wasm != src {
            return Err(format!("{name}({a}, {b}): wasm {wasm} != native C {src}"));
        }
    }
    // Properties, on the compiled module itself.
    let (ab, ba) = (c.add(a, b), c.add(b, a));
    if ab != ba {
        return Err(format!("wasm add not commutative at ({a}, {b})"));
    }
    let bk = c.add(b, k);
    let (l, r) = (c.add(ab, k), c.add(a, bk));
    if l != r {
        return Err(format!("wasm add not associative at ({a}, {b}, {k})"));
    }
    if c.odd(a) & 1 != 1 {
        return Err(format!("wasm odd({a}) is even"));
    }
    if c.popcount(ua) != ua.count_ones() as i32 {
        return Err(format!("wasm popcount({ua}) != count_ones"));
    }
    let g = c.gcd(ua, ub);
    if g != gcd_ref(ua, ub) {
        return Err(format!("wasm gcd({ua}, {ub}) = {g} != reference {}", gcd_ref(ua, ub)));
    }
    if g != c.gcd(ub, ua) {
        return Err(format!("wasm gcd not symmetric at ({ua}, {ub})"));
    }
    Ok(())
}
