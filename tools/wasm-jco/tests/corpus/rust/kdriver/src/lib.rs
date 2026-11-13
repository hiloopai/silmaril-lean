#![allow(clippy::all)]
mod kdriver;
use kdriver::corpus::kitchen::geo;
use kdriver::corpus::kitchen::types::{Color, Perms, Point, Shape};

struct C;

impl kdriver::Guest for C {
    fn go(n: u32) -> String {
        let a = geo::area(Shape::Rect(Point { x: n as i32, y: 3 }));
        let p = geo::shift(Point { x: 1, y: 2 }, n as i32);
        let names = geo::names(&[Color::Blue, Color::Red]);
        let f = geo::check(Perms::READ | Perms::EXEC);
        let r = geo::parse(&format!("{n}"));
        let e = geo::parse("x");
        let first = geo::first(&[n, 1]);
        let (len, up) = geo::pair("abc", &[1, 2, 3]);
        format!("{a} {},{} {} {:?} {:?} {} {:?} {len} {up}", p.x, p.y, names.join("+"), f.bits(), r, e.is_err(), first)
    }
}

kdriver::export!(C with_types_in kdriver);
