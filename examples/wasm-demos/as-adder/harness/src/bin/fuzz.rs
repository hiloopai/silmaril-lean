//! A stable-toolchain fuzz loop: random and boundary-biased inputs, compiled module vs source.
//!
//! Usage (in `harness/`): `cargo run --release --bin fuzz -- [ITERATIONS] [SEED]`
//! (defaults: 1_000_000 iterations, seed 0x5eed). Exits non-zero on the first disagreement.

use as_adder_harness::{check_case, Compiled};

/// SplitMix64.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    /// Uniform `i32` half the time, a boundary value (+-small offset) otherwise.
    fn i32(&mut self) -> i32 {
        const EDGES: [i32; 6] = [0, 1, -1, i32::MAX, i32::MIN, 1 << 16];
        let r = self.next();
        if r & 1 == 0 {
            (r >> 32) as i32
        } else {
            let e = EDGES[((r >> 8) % EDGES.len() as u64) as usize];
            e.wrapping_add(((r >> 16) % 5) as i32 - 2)
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let iters: u64 = args.next().map(|s| s.parse().expect("ITERATIONS")).unwrap_or(1_000_000);
    let seed: u64 = args
        .next()
        .map(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).expect("SEED (hex)"))
        .unwrap_or(0x5eed);
    let mut rng = Rng(seed);
    let mut c = Compiled::new();
    for i in 0..iters {
        let (a, b, k) = (rng.i32(), rng.i32(), rng.i32());
        if let Err(e) = check_case(&mut c, a, b, k) {
            eprintln!("iteration {i}: {e}");
            std::process::exit(1);
        }
    }
    println!("fuzz: {iters} cases, seed {seed:#x}: compiled adder.wasm agrees with the transcribed AssemblyScript source");
}
