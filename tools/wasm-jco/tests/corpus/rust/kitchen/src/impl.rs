use kitchen::exports::corpus::kitchen::geo::Guest as Geo;
use kitchen::exports::corpus::kitchen::geo::{Color, Perms, Point, Shape};

struct C;

impl kitchen::Guest for C {
    fn greet(name: String) -> String {
        format!("hello, {name}!")
    }
    fn sum(xs: Vec<f64>) -> f64 {
        xs.iter().sum()
    }
}

impl Geo for C {
    fn area(s: Shape) -> u64 {
        match s {
            Shape::Circle(r) => 3 * (r as u64) * (r as u64),
            Shape::Rect(p) => (p.x as i64 * p.y as i64).unsigned_abs(),
            Shape::None => 0,
        }
    }
    fn shift(p: Point, dx: i32) -> Point {
        Point { x: p.x.wrapping_add(dx), y: p.y }
    }
    fn names(c: Vec<Color>) -> Vec<String> {
        c.into_iter()
            .map(|c| match c {
                Color::Red => "red".to_string(),
                Color::Green => "green".to_string(),
                Color::Blue => "blue".to_string(),
            })
            .collect()
    }
    fn check(p: Perms) -> Perms {
        p ^ Perms::EXEC
    }
    fn parse(s: String) -> Result<u32, String> {
        s.trim().parse::<u32>().map_err(|e| format!("{e}"))
    }
    fn first(xs: Vec<u32>) -> Option<u32> {
        xs.first().copied()
    }
    fn pair(a: String, b: Vec<u8>) -> (u32, String) {
        (b.len() as u32, a.to_uppercase())
    }
}

kitchen::export!(C with_types_in kitchen);
