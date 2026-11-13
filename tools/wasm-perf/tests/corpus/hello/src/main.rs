// A std-only WASI 0.2 command (hash maps, B-trees, formatting, a file read): a real component
// from the pinned Rust toolchain for tools/wasm-perf/tests/bench.sh (no dependencies, built
// offline). Release: about 140 KB; debug (DWARF sections): about 3.7 MB.
use std::collections::{BTreeMap, HashMap};
fn main() {
    let mut m: HashMap<String, u64> = HashMap::new();
    let mut b: BTreeMap<u64, String> = BTreeMap::new();
    for (i, a) in std::env::args().enumerate() { m.insert(a.clone(), i as u64); b.insert(i as u64, a); }
    println!("{:?} {:?}", m, b);
    let s = std::fs::read_to_string("/x").unwrap_or_default();
    println!("{}", s.len());
}
