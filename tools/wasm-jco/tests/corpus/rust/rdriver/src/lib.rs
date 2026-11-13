#![allow(clippy::all)]
mod rdriver;
use rdriver::corpus::res::store::{consume, snap, Counter};

struct C;

impl rdriver::Guest for C {
    fn run(n: u32) -> u32 {
        let a = Counter::new(n);
        a.incr(3);
        let b = Counter::new(10);
        let m = Counter::merge(&a, &b);
        m.incr(1);
        consume(m) + a.get()
    }
    fn label(n: u32) -> String {
        let a = Counter::new(n);
        let s = snap(&a, "c");
        format!("{}={}", s.name, s.value)
    }
}

rdriver::export!(C with_types_in rdriver);
