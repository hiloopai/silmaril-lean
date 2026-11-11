//! Terms of straight-line integer Wasm, mirroring `Silmaril.Wasm.Auto.EGraph.Term`.
//!
//! The text form is WAT's folded syntax: `(i32.add (local.get 0) (i32.const 1))`.
//! Constants are kept canonical (`0 <= n < 2^width`), as the Lean checker compares
//! constants as natural numbers.

use crate::sexp::Sexp;
use std::fmt::Write as _;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ty {
    I32,
    I64,
}

impl Ty {
    pub fn width(self) -> u32 {
        match self {
            Ty::I32 => 32,
            Ty::I64 => 64,
        }
    }
    pub fn mask(self) -> u64 {
        match self {
            Ty::I32 => 0xffff_ffff,
            Ty::I64 => u64::MAX,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Ty::I32 => "i32",
            Ty::I64 => "i64",
        }
    }
    pub fn lean(self) -> &'static str {
        match self {
            Ty::I32 => ".i32",
            Ty::I64 => ".i64",
        }
    }
    pub fn parse(s: &str) -> Option<Ty> {
        match s {
            "i32" => Some(Ty::I32),
            "i64" => Some(Ty::I64),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UnOp {
    Clz,
    Ctz,
    Popcnt,
    Extend8,
    Extend16,
    Extend32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Rotl,
    Rotr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RelOp {
    Eq,
    Ne,
    LtS,
    LtU,
    GtS,
    GtU,
    LeS,
    LeU,
    GeS,
    GeU,
}

const UNOPS: &[(&str, UnOp, &str)] = &[
    ("clz", UnOp::Clz, ".clz"),
    ("ctz", UnOp::Ctz, ".ctz"),
    ("popcnt", UnOp::Popcnt, ".popcnt"),
    ("extend8_s", UnOp::Extend8, "(.extend .i8)"),
    ("extend16_s", UnOp::Extend16, "(.extend .i16)"),
    ("extend32_s", UnOp::Extend32, "(.extend .i32)"),
];

const BINOPS: &[(&str, BinOp, &str)] = &[
    ("add", BinOp::Add, ".add"),
    ("sub", BinOp::Sub, ".sub"),
    ("mul", BinOp::Mul, ".mul"),
    ("div_s", BinOp::DivS, "(.div .signed)"),
    ("div_u", BinOp::DivU, "(.div .unsigned)"),
    ("rem_s", BinOp::RemS, "(.rem .signed)"),
    ("rem_u", BinOp::RemU, "(.rem .unsigned)"),
    ("and", BinOp::And, ".and"),
    ("or", BinOp::Or, ".or"),
    ("xor", BinOp::Xor, ".xor"),
    ("shl", BinOp::Shl, ".shl"),
    ("shr_s", BinOp::ShrS, "(.shr .signed)"),
    ("shr_u", BinOp::ShrU, "(.shr .unsigned)"),
    ("rotl", BinOp::Rotl, ".rotl"),
    ("rotr", BinOp::Rotr, ".rotr"),
];

const RELOPS: &[(&str, RelOp, &str)] = &[
    ("eq", RelOp::Eq, ".eq"),
    ("ne", RelOp::Ne, ".ne"),
    ("lt_s", RelOp::LtS, "(.lt .signed)"),
    ("lt_u", RelOp::LtU, "(.lt .unsigned)"),
    ("gt_s", RelOp::GtS, "(.gt .signed)"),
    ("gt_u", RelOp::GtU, "(.gt .unsigned)"),
    ("le_s", RelOp::LeS, "(.le .signed)"),
    ("le_u", RelOp::LeU, "(.le .unsigned)"),
    ("ge_s", RelOp::GeS, "(.ge .signed)"),
    ("ge_u", RelOp::GeU, "(.ge .unsigned)"),
];

fn find<T: Copy + PartialEq>(
    table: &[(&'static str, T, &'static str)],
    x: T,
) -> (&'static str, &'static str) {
    let e = table
        .iter()
        .find(|e| e.1 == x)
        .expect("operator table is complete");
    (e.0, e.2)
}

/// The operator of a node, without its children.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Op {
    Const(Ty, u64),
    Lget(u32),
    Un(Ty, UnOp),
    Test(Ty),
    Bin(Ty, BinOp),
    Rel(Ty, RelOp),
}

impl Op {
    pub fn arity(&self) -> usize {
        match self {
            Op::Const(..) | Op::Lget(_) => 0,
            Op::Un(..) | Op::Test(_) => 1,
            Op::Bin(..) | Op::Rel(..) => 2,
        }
    }

    /// The result type, given the operand types (Lean's `Term.typeOf`).
    pub fn type_of(&self, locals: &[Ty], ch: &[Option<Ty>]) -> Option<Ty> {
        match self {
            Op::Const(t, _) => Some(*t),
            Op::Lget(i) => locals.get(*i as usize).copied(),
            Op::Un(t, _) => (ch[0] == Some(*t)).then_some(*t),
            Op::Test(t) => (ch[0] == Some(*t)).then_some(Ty::I32),
            Op::Bin(t, _) => (ch[0] == Some(*t) && ch[1] == Some(*t)).then_some(*t),
            Op::Rel(t, _) => (ch[0] == Some(*t) && ch[1] == Some(*t)).then_some(Ty::I32),
        }
    }

    /// The WAT instruction name.
    pub fn wat(&self) -> String {
        match self {
            Op::Const(t, _) => format!("{}.const", t.name()),
            Op::Lget(_) => "local.get".into(),
            Op::Un(t, op) => format!("{}.{}", t.name(), find(UNOPS, *op).0),
            Op::Test(t) => format!("{}.eqz", t.name()),
            Op::Bin(t, op) => format!("{}.{}", t.name(), find(BINOPS, *op).0),
            Op::Rel(t, op) => format!("{}.{}", t.name(), find(RELOPS, *op).0),
        }
    }

    /// Parse an operator name such as `i32.add`; `None` for an unknown name.
    pub fn parse_name(name: &str) -> Option<OpName> {
        if name == "local.get" {
            return Some(OpName::Lget);
        }
        let (t, rest) = name.split_once('.')?;
        let t = Ty::parse(t)?;
        if rest == "const" {
            return Some(OpName::Const(t));
        }
        if rest == "eqz" {
            return Some(OpName::Op(Op::Test(t)));
        }
        if let Some(e) = UNOPS.iter().find(|e| e.0 == rest) {
            if e.1 == UnOp::Extend32 && t == Ty::I32 {
                return None;
            }
            return Some(OpName::Op(Op::Un(t, e.1)));
        }
        if let Some(e) = BINOPS.iter().find(|e| e.0 == rest) {
            return Some(OpName::Op(Op::Bin(t, e.1)));
        }
        if let Some(e) = RELOPS.iter().find(|e| e.0 == rest) {
            return Some(OpName::Op(Op::Rel(t, e.1)));
        }
        None
    }

    /// The Lean constructor application without children (children are appended).
    pub fn lean_head(&self) -> String {
        match self {
            Op::Const(t, n) => format!(".const {} {}", t.lean(), n),
            Op::Lget(i) => format!(".lget {i}"),
            Op::Un(t, op) => format!(".un {} {}", t.lean(), find(UNOPS, *op).1),
            Op::Test(t) => format!(".test {}", t.lean()),
            Op::Bin(t, op) => format!(".bin {} {}", t.lean(), find(BINOPS, *op).1),
            Op::Rel(t, op) => format!(".rel {} {}", t.lean(), find(RELOPS, *op).1),
        }
    }
}

pub enum OpName {
    Lget,
    Const(Ty),
    Op(Op),
}

/// Parse an integer literal of type `t` (decimal or `0x` hex, possibly negative) into
/// its canonical unsigned value.
pub fn parse_const(t: Ty, s: &str) -> Result<u64, String> {
    let (neg, body) = match s.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, s),
    };
    let body = body.replace('_', "");
    let v: u128 = if let Some(h) = body.strip_prefix("0x") {
        u128::from_str_radix(h, 16).map_err(|e| format!("bad constant {s}: {e}"))?
    } else {
        body.parse::<u128>()
            .map_err(|e| format!("bad constant {s}: {e}"))?
    };
    let m = t.mask() as u128;
    if v > m {
        return Err(format!("constant {s} does not fit {}", t.name()));
    }
    let v = if neg { (m + 1 - v) & m } else { v };
    Ok(v as u64)
}

/// A term tree.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Term {
    pub op: Op,
    pub ch: Vec<Term>,
}

impl Term {
    pub fn leaf(op: Op) -> Term {
        Term { op, ch: vec![] }
    }

    pub fn type_of(&self, locals: &[Ty]) -> Option<Ty> {
        let ch: Vec<Option<Ty>> = self.ch.iter().map(|c| c.type_of(locals)).collect();
        self.op.type_of(locals, &ch)
    }

    pub fn parse(s: &Sexp) -> Result<Term, String> {
        let items = s
            .list()
            .ok_or_else(|| format!("expected a term, got {s}"))?;
        let head = items
            .first()
            .and_then(Sexp::atom)
            .ok_or_else(|| format!("bad term {s}"))?;
        let name = Op::parse_name(head).ok_or_else(|| format!("unknown instruction {head}"))?;
        match name {
            OpName::Lget => {
                let i = items
                    .get(1)
                    .and_then(Sexp::atom)
                    .ok_or("local.get needs an index")?;
                let i: u32 = i.parse().map_err(|_| format!("bad local index {i}"))?;
                Ok(Term::leaf(Op::Lget(i)))
            }
            OpName::Const(t) => {
                let n = items
                    .get(1)
                    .and_then(Sexp::atom)
                    .ok_or("const needs a value")?;
                Ok(Term::leaf(Op::Const(t, parse_const(t, n)?)))
            }
            OpName::Op(op) => {
                let ch: Vec<Term> = items[1..]
                    .iter()
                    .map(Term::parse)
                    .collect::<Result<_, _>>()?;
                if ch.len() != op.arity() {
                    return Err(format!("{head} takes {} operands", op.arity()));
                }
                Ok(Term { op, ch })
            }
        }
    }

    pub fn wat(&self) -> String {
        let mut s = String::new();
        self.write_wat(&mut s);
        s
    }

    fn write_wat(&self, s: &mut String) {
        match &self.op {
            Op::Const(t, n) => {
                let _ = write!(s, "({}.const {})", t.name(), n);
            }
            Op::Lget(i) => {
                let _ = write!(s, "(local.get {i})");
            }
            op => {
                let _ = write!(s, "({}", op.wat());
                for c in &self.ch {
                    s.push(' ');
                    c.write_wat(s);
                }
                s.push(')');
            }
        }
    }

    pub fn lean(&self) -> String {
        if self.ch.is_empty() {
            format!("({})", self.op.lean_head())
        } else {
            let ch: Vec<String> = self.ch.iter().map(Term::lean).collect();
            format!("({} {})", self.op.lean_head(), ch.join(" "))
        }
    }

    /// The flat instruction sequence (Lean's `Term.compile`).
    pub fn flat(&self, out: &mut Vec<String>) {
        for c in &self.ch {
            c.flat(out);
        }
        match &self.op {
            Op::Const(t, n) => out.push(format!("{}.const {}", t.name(), n)),
            Op::Lget(i) => out.push(format!("local.get {i}")),
            op => out.push(op.wat()),
        }
    }

    pub fn get(&self, path: &[usize]) -> Option<&Term> {
        match path.split_first() {
            None => Some(self),
            Some((i, rest)) => self.ch.get(*i)?.get(rest),
        }
    }

    pub fn set(&self, path: &[usize], r: Term) -> Option<Term> {
        match path.split_first() {
            None => Some(r),
            Some((i, rest)) => {
                let mut t = self.clone();
                let c = t.ch.get(*i)?.set(rest, r)?;
                t.ch[*i] = c;
                Some(t)
            }
        }
    }
}

/// Lift a flat instruction sequence (one instruction per line or `;`-separated, WAT
/// names) into the terms it leaves on the stack. Untrusted: the Lean side compiles the
/// terms back and compares.
pub fn lift_flat(src: &str) -> Result<Vec<Term>, String> {
    let mut stack: Vec<Term> = vec![];
    for raw in src.split(['\n', ';']) {
        let line = raw.split("#").next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let mut words = line.split_whitespace();
        let name = words.next().unwrap_or("");
        let arg = words.next();
        let op = Op::parse_name(name).ok_or_else(|| format!("unsupported instruction `{line}`"))?;
        match op {
            OpName::Lget => {
                let i: u32 = arg
                    .ok_or("local.get needs an index")?
                    .parse()
                    .map_err(|_| format!("bad index in `{line}`"))?;
                stack.push(Term::leaf(Op::Lget(i)));
            }
            OpName::Const(t) => {
                let n = parse_const(t, arg.ok_or("const needs a value")?)?;
                stack.push(Term::leaf(Op::Const(t, n)));
            }
            OpName::Op(op) => {
                let k = op.arity();
                if stack.len() < k {
                    return Err(format!("stack underflow at `{line}`"));
                }
                let ch = stack.split_off(stack.len() - k);
                stack.push(Term { op, ch });
            }
        }
    }
    Ok(stack)
}

/// Evaluate an operator on constant operands (Silmaril's `intUnOp`, `intBinOp`,
/// `intTestOp`, `intRelOp`); `None` for a trap.
pub fn fold(op: &Op, args: &[u64]) -> Option<(Ty, u64)> {
    let b = |x: bool| (Ty::I32, x as u64);
    match op {
        Op::Un(t, u) => {
            let w = t.width();
            let x = args[0] & t.mask();
            let r = match u {
                UnOp::Clz => {
                    if w == 32 {
                        (x as u32).leading_zeros() as u64
                    } else {
                        x.leading_zeros() as u64
                    }
                }
                UnOp::Ctz => {
                    if w == 32 {
                        (x as u32).trailing_zeros() as u64
                    } else {
                        x.trailing_zeros() as u64
                    }
                }
                UnOp::Popcnt => x.count_ones() as u64,
                UnOp::Extend8 => (sext(x, 8) as u64) & t.mask(),
                UnOp::Extend16 => (sext(x, 16) as u64) & t.mask(),
                UnOp::Extend32 => (sext(x, 32) as u64) & t.mask(),
            };
            Some((*t, r))
        }
        Op::Test(_) => Some(b(args[0] == 0)),
        Op::Bin(t, o) => {
            let w = t.width();
            let m = t.mask();
            let (x, y) = (args[0] & m, args[1] & m);
            let sx = sext(x, w);
            let sy = sext(y, w);
            let sh = (y % w as u64) as u32;
            let r = match o {
                BinOp::Add => x.wrapping_add(y),
                BinOp::Sub => x.wrapping_sub(y),
                BinOp::Mul => x.wrapping_mul(y),
                BinOp::DivU => {
                    if y == 0 {
                        return None;
                    }
                    x / y
                }
                BinOp::DivS => {
                    if y == 0 {
                        return None;
                    }
                    let min = 1u64 << (w - 1);
                    if x == min && y == m {
                        return None;
                    }
                    (sx.wrapping_div(sy)) as u64
                }
                BinOp::RemU => {
                    if y == 0 {
                        return None;
                    }
                    x % y
                }
                BinOp::RemS => {
                    if y == 0 {
                        return None;
                    }
                    if sy == -1 { 0 } else { (sx % sy) as u64 }
                }
                BinOp::And => x & y,
                BinOp::Or => x | y,
                BinOp::Xor => x ^ y,
                BinOp::Shl => {
                    if sh == 0 {
                        x
                    } else {
                        x << sh
                    }
                }
                BinOp::ShrU => {
                    if sh == 0 {
                        x
                    } else {
                        x >> sh
                    }
                }
                BinOp::ShrS => (sx >> sh) as u64,
                BinOp::Rotl => {
                    let r = (y % w as u64) as u32;
                    if r == 0 { x } else { (x << r) | (x >> (w - r)) }
                }
                BinOp::Rotr => {
                    let r = (y % w as u64) as u32;
                    if r == 0 { x } else { (x >> r) | (x << (w - r)) }
                }
            };
            Some((*t, r & m))
        }
        Op::Rel(t, o) => {
            let w = t.width();
            let m = t.mask();
            let (x, y) = (args[0] & m, args[1] & m);
            let (sx, sy) = (sext(x, w), sext(y, w));
            Some(b(match o {
                RelOp::Eq => x == y,
                RelOp::Ne => x != y,
                RelOp::LtU => x < y,
                RelOp::GtU => x > y,
                RelOp::LeU => x <= y,
                RelOp::GeU => x >= y,
                RelOp::LtS => sx < sy,
                RelOp::GtS => sx > sy,
                RelOp::LeS => sx <= sy,
                RelOp::GeS => sx >= sy,
            }))
        }
        Op::Const(..) | Op::Lget(_) => None,
    }
}

/// Sign-extend the low `bits` bits of `x` to an `i64`.
fn sext(x: u64, bits: u32) -> i64 {
    if bits >= 64 {
        x as i64
    } else {
        let s = 64 - bits;
        ((x << s) as i64) >> s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constants_are_canonical() {
        assert_eq!(parse_const(Ty::I32, "-1").unwrap(), 0xffff_ffff);
        assert_eq!(parse_const(Ty::I64, "-1").unwrap(), u64::MAX);
        assert_eq!(parse_const(Ty::I32, "0x10").unwrap(), 16);
        assert!(parse_const(Ty::I32, "4294967296").is_err());
    }

    #[test]
    fn folding_matches_wasm() {
        let i = |t, o| Op::Bin(t, o);
        assert_eq!(
            fold(&i(Ty::I32, BinOp::DivS), &[0x8000_0000, 0xffff_ffff]),
            None
        );
        assert_eq!(
            fold(&i(Ty::I32, BinOp::RemS), &[0x8000_0000, 0xffff_ffff]),
            Some((Ty::I32, 0))
        );
        assert_eq!(fold(&i(Ty::I32, BinOp::Shl), &[1, 33]), Some((Ty::I32, 2)));
        assert_eq!(
            fold(&i(Ty::I32, BinOp::ShrS), &[0x8000_0000, 31]),
            Some((Ty::I32, 0xffff_ffff))
        );
        assert_eq!(
            fold(&i(Ty::I32, BinOp::Rotl), &[0x8000_0001, 1]),
            Some((Ty::I32, 3))
        );
        assert_eq!(fold(&Op::Un(Ty::I32, UnOp::Clz), &[1]), Some((Ty::I32, 31)));
        assert_eq!(
            fold(&Op::Un(Ty::I64, UnOp::Extend8), &[0x80]),
            Some((Ty::I64, 0xffff_ffff_ffff_ff80))
        );
    }
}
