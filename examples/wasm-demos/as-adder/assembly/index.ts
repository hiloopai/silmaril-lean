// The AssemblyScript source of wasm/adder.wasm (see ../README.md).
// i32 arithmetic in AssemblyScript wraps modulo 2^32, like Rust's wrapping_* operations.

export function add(a: i32, b: i32): i32 {
  return a + b;
}

export function mul(a: i32, b: i32): i32 {
  return a * b;
}

export function max(a: i32, b: i32): i32 {
  return a < b ? b : a;
}

export function odd(a: i32): i32 {
  return a * 2 + 1;
}
