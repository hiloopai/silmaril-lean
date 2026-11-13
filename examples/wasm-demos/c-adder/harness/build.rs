//! Compiles `../src/adder.c` for the host, so the tests can run the C source natively next to
//! the committed `.wasm` (the native build is the "source + compiler" stand-in).
fn main() {
    println!("cargo:rerun-if-changed=../src/adder.c");
    cc::Build::new()
        .file("../src/adder.c")
        .opt_level(2)
        .warnings(true)
        .compile("adder_native");
}
