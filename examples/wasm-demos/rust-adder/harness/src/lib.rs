//! Runs the committed `adder.wasm` with the `wasmi` interpreter, next to the Rust source.
//!
//! The committed module is `../wasm/adder.wasm` (see the README for its build command). The
//! bytes are embedded here, so the tests and the fuzzer exercise exactly the file that Lean
//! ingests.

use wasmi::{Engine, Linker, Module, Store, TypedFunc};

/// The committed compiled module.
pub const ADDER_WASM: &[u8] = include_bytes!("../../wasm/adder.wasm");

/// An instance of the committed module with its four exports.
pub struct Compiled {
    store: Store<()>,
    add: TypedFunc<(i32, i32), i32>,
    mul: TypedFunc<(i32, i32), i32>,
    max: TypedFunc<(i32, i32), i32>,
    odd: TypedFunc<i32, i32>,
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

/// Checks the compiled exports against the Rust source on one input triple; returns a
/// description of the first disagreement.
pub fn check_case(c: &mut Compiled, a: i32, b: i32, k: i32) -> Result<(), String> {
    let pairs = [
        ("add", c.add(a, b), adder::add(a, b)),
        ("mul", c.mul(a, b), adder::mul(a, b)),
        ("max", c.max(a, b), adder::max(a, b)),
        ("odd", c.odd(a), adder::odd(a)),
    ];
    for (name, wasm, src) in pairs {
        if wasm != src {
            return Err(format!("{name}({a}, {b}): wasm {wasm} != source {src}"));
        }
    }
    // Algebraic properties, on the compiled module itself.
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
    Ok(())
}
