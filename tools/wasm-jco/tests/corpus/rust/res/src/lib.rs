#![allow(clippy::all)]
mod res;
use res::exports::corpus::res::store::{Counter, CounterBorrow, Guest, GuestCounter, Snapshot};
use std::cell::Cell;

struct C;
struct MyCounter(Cell<u32>);

impl GuestCounter for MyCounter {
    fn new(start: u32) -> Self {
        MyCounter(Cell::new(start))
    }
    fn incr(&self, by: u32) -> u32 {
        self.0.set(self.0.get().wrapping_add(by));
        self.0.get()
    }
    fn get(&self) -> u32 {
        self.0.get()
    }
    fn merge(a: CounterBorrow<'_>, b: CounterBorrow<'_>) -> Counter {
        let a = a.get::<MyCounter>().0.get();
        let b = b.get::<MyCounter>().0.get();
        Counter::new(MyCounter(Cell::new(a.wrapping_add(b))))
    }
}

impl Guest for C {
    type Counter = MyCounter;
    fn snap(c: CounterBorrow<'_>, name: String) -> Snapshot {
        Snapshot { name, value: c.get::<MyCounter>().0.get() }
    }
    fn consume(c: Counter) -> u32 {
        c.get::<MyCounter>().0.get()
    }
}

res::export!(C with_types_in res);
