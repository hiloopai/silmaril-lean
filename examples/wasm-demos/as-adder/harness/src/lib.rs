//! Runs the committed AssemblyScript `adder.wasm` with the `wasmi` interpreter.
//!
//! The committed module is `../wasm/adder.wasm`, built from `../assembly/index.ts` by
//! `asc` 0.28.20 (see the README). The bytes are embedded, so the tests and the fuzzer
//! exercise exactly the file that Lean ingests.
//!
//! AssemblyScript cannot be run natively, so the reference model [`src`] is a hand
//! transcription of `assembly/index.ts` into Rust (AssemblyScript `i32` arithmetic wraps
//! modulo 2^32, like Rust's `wrapping_*`). It is not derived from the `.ts` file.

use wasmi::{Engine, Linker, Module, Store, TypedFunc};

/// The committed compiled module.
pub const ADDER_WASM: &[u8] = include_bytes!("../../wasm/adder.wasm");

/// The AssemblyScript source, transcribed by hand.
pub mod src {
    /// `a + b` on `i32`.
    pub fn add(a: i32, b: i32) -> i32 {
        a.wrapping_add(b)
    }
    /// `a * b` on `i32`.
    pub fn mul(a: i32, b: i32) -> i32 {
        a.wrapping_mul(b)
    }
    /// `a < b ? b : a` (signed).
    pub fn max(a: i32, b: i32) -> i32 {
        if a < b {
            b
        } else {
            a
        }
    }
    /// `a * 2 + 1` on `i32`.
    pub fn odd(a: i32) -> i32 {
        a.wrapping_mul(2).wrapping_add(1)
    }
}

/// An instance of the committed module with its four exports.
pub struct Compiled {
    store: Store<()>,
    add: TypedFunc<(i32, i32), i32>,
    mul: TypedFunc<(i32, i32), i32>,
    max: TypedFunc<(i32, i32), i32>,
    odd: TypedFunc<i32, i32>,
}

impl Compiled {
    /// Instantiates the committed module. It has no imports (`--runtime stub` with no
    /// allocation and no `abort` call site), so the linker is empty: a closed host.
    pub fn new() -> Self {
        let engine = Engine::default();
        let module = Module::new(&engine, ADDER_WASM).expect("adder.wasm decodes and validates");
        assert_eq!(module.imports().len(), 0, "the AssemblyScript module has no imports");
        let mut store = Store::new(&engine, ());
        let linker = Linker::<()>::new(&engine);
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("instantiates")
            .start(&mut store)
            .expect("no start trap");
        let add = instance.get_typed_func(&store, "add").expect("export add");
        let mul = instance.get_typed_func(&store, "mul").expect("export mul");
        let max = instance.get_typed_func(&store, "max").expect("export max");
        let odd = instance.get_typed_func(&store, "odd").expect("export odd");
        Compiled { store, add, mul, max, odd }
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
}

impl Default for Compiled {
    fn default() -> Self {
        Self::new()
    }
}

/// Checks the compiled exports on one input triple: against the transcribed source, and the
/// algebraic properties directly on the compiled module. Returns the first failure.
pub fn check_case(c: &mut Compiled, a: i32, b: i32, k: i32) -> Result<(), String> {
    let pairs = [
        ("add", c.add(a, b), src::add(a, b)),
        ("mul", c.mul(a, b), src::mul(a, b)),
        ("max", c.max(a, b), src::max(a, b)),
        ("odd", c.odd(a), src::odd(a)),
    ];
    for (name, wasm, model) in pairs {
        if wasm != model {
            return Err(format!("{name}({a}, {b}): wasm {wasm} != source {model}"));
        }
    }
    let (ab, ba) = (c.add(a, b), c.add(b, a));
    if ab != ba {
        return Err(format!("wasm add not commutative at ({a}, {b})"));
    }
    let bk = c.add(b, k);
    let (l, r) = (c.add(ab, k), c.add(a, bk));
    if l != r {
        return Err(format!("wasm add not associative at ({a}, {b}, {k})"));
    }
    if c.mul(a, b) != c.mul(b, a) {
        return Err(format!("wasm mul not commutative at ({a}, {b})"));
    }
    let m = c.max(a, b);
    if !(m >= a && m >= b && (m == a || m == b)) {
        return Err(format!("wasm max({a}, {b}) = {m} is not the larger argument"));
    }
    if c.odd(a) & 1 != 1 {
        return Err(format!("wasm odd({a}) is even"));
    }
    Ok(())
}
