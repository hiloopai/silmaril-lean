//! Parser for the subset of herdtools7 `.litmus` files used by the corpus.
//!
//! Supported: the `X86` dialect (herd's Intel-like syntax, `MOV [x],$1`) and the `X86_64`
//! dialect (AT&T syntax, `movl $1,(x)`); an initial-state block with typed location
//! declarations, location values and thread registers (an integer or a location address); a
//! program table (`P0 | P1 ;` rows); an optional `locations [...]` clause, which is skipped;
//! and a final condition `exists`, `~exists` or `forall` over `/\`, `\/`, `~`, `true`.
//! OCaml comments `(* ... *)` are removed first. Anything else is an error, never ignored.

use std::fmt;

/// The herd architecture dialect of a test.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arch {
    /// Intel-like syntax (`MOV EAX,[x]`).
    X86,
    /// AT&T syntax (`movl (x),%eax`).
    X86_64,
}

/// A location declaration from the initial-state block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub name: String,
    /// Element size in bytes.
    pub elem: u64,
    /// Number of elements (1 for a scalar).
    pub count: u64,
    /// Initial value (scalars only; arrays start at zero).
    pub init: i128,
}

/// The initial value of a thread register.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegInit {
    Int(i128),
    /// The address of a location.
    Addr(String),
}

/// The quantifier of the final condition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quant {
    Exists,
    NotExists,
    Forall,
}

/// One comparison in the final condition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// `T:REG = v`.
    Reg {
        thread: usize,
        reg: String,
        value: i128,
    },
    /// `[x] = v` or `x = v`.
    Loc { name: String, value: i128 },
}

/// A final-condition formula.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    True,
    Atom(Atom),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}

/// A parsed litmus test.
#[derive(Clone, Debug)]
pub struct Test {
    pub arch: Arch,
    pub name: String,
    /// The first quoted line after the name, if any.
    pub doc: Option<String>,
    pub decls: Vec<Decl>,
    pub regs: Vec<(usize, String, RegInit)>,
    /// Instruction text per thread, in program order (empty cells dropped).
    pub threads: Vec<Vec<String>>,
    pub quant: Quant,
    pub cond: Expr,
}

/// A parse error.
#[derive(Debug, PartialEq, Eq)]
pub struct Error(pub String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

fn err<T>(msg: impl Into<String>) -> Result<T, Error> {
    Err(Error(msg.into()))
}

/// Remove OCaml comments `(* ... *)` (nesting allowed).
fn strip_comments(s: &str) -> Result<String, Error> {
    let b = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let (mut i, mut depth) = (0usize, 0usize);
    while i < b.len() {
        if b[i] == b'(' && b.get(i + 1) == Some(&b'*') {
            depth += 1;
            i += 2;
        } else if depth > 0 && b[i] == b'*' && b.get(i + 1) == Some(&b')') {
            depth -= 1;
            i += 2;
        } else {
            if depth == 0 {
                out.push(b[i] as char);
            }
            i += 1;
        }
    }
    if depth != 0 {
        return err("unterminated comment");
    }
    Ok(out)
}

/// Parse an integer: decimal or `0x` hexadecimal, optionally negative.
pub fn parse_int(s: &str) -> Result<i128, Error> {
    let s = s.trim();
    let (neg, body) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s),
    };
    let v = if let Some(h) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
        i128::from_str_radix(h, 16)
    } else {
        body.parse::<i128>()
    }
    .map_err(|_| Error(format!("bad integer `{s}`")))?;
    Ok(if neg { -v } else { v })
}

fn is_ident(s: &str) -> bool {
    !s.is_empty()
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !s.starts_with(|c: char| c.is_ascii_digit())
}

fn type_size(ty: &str) -> Option<u64> {
    Some(match ty {
        "int8_t" | "uint8_t" | "char" => 1,
        "int16_t" | "uint16_t" | "short" => 2,
        "int" | "int32_t" | "uint32_t" => 4,
        "int64_t" | "uint64_t" | "long" => 8,
        _ => return None,
    })
}

/// Parse one item of the initial-state block.
fn parse_init_item(item: &str, test: &mut Test) -> Result<(), Error> {
    let item = item.trim();
    if item.is_empty() {
        return Ok(());
    }
    let (lhs, rhs) = match item.split_once('=') {
        Some((l, r)) => (l.trim(), Some(r.trim())),
        None => (item, None),
    };
    let words: Vec<&str> = lhs.split_whitespace().collect();
    let (ty, target) = match words.as_slice() {
        [t] => (None, *t),
        [ty, t] => (Some(*ty), *t),
        _ => return err(format!("bad init item `{item}`")),
    };
    if let Some((th, reg)) = target.split_once(':') {
        let thread = th
            .parse::<usize>()
            .map_err(|_| Error(format!("bad thread in `{item}`")))?;
        let reg = reg.trim().to_string();
        let init = match rhs {
            None => RegInit::Int(0),
            Some(v) if is_ident(v) => RegInit::Addr(v.to_string()),
            Some(v) => RegInit::Int(parse_int(v)?),
        };
        test.regs.push((thread, reg, init));
        return Ok(());
    }
    let target = match target.strip_prefix('[') {
        Some(t) => t
            .strip_suffix(']')
            .ok_or_else(|| Error(format!("bad location `{item}`")))?,
        None => target,
    };
    let (name, count) = match target.split_once('[') {
        Some((n, c)) => {
            let c = c
                .strip_suffix(']')
                .ok_or_else(|| Error(format!("bad array `{item}`")))?;
            (n, parse_int(c)? as u64)
        }
        None => (target, 1),
    };
    if !is_ident(name) {
        return err(format!("bad location name in `{item}`"));
    }
    let elem = match ty {
        Some(t) => type_size(t).ok_or_else(|| Error(format!("unsupported type `{t}`")))?,
        None => 4,
    };
    let init = match rhs {
        None => 0,
        Some(v) if count == 1 => parse_int(v)?,
        Some(_) => return err(format!("array initialisers are not supported: `{item}`")),
    };
    if let Some(d) = test.decls.iter_mut().find(|d| d.name == name) {
        if ty.is_some() {
            d.elem = elem;
            d.count = count;
        }
        d.init = init;
    } else {
        test.decls.push(Decl {
            name: name.to_string(),
            elem,
            count,
            init,
        });
    }
    Ok(())
}

/// Parse a `.litmus` file.
pub fn parse(src: &str) -> Result<Test, Error> {
    let src = strip_comments(src)?;
    let mut lines = src.lines();
    let head = loop {
        match lines.next() {
            Some(l) if l.trim().is_empty() => continue,
            Some(l) => break l.trim().to_string(),
            None => return err("empty file"),
        }
    };
    let (arch, name) = match head.split_once(char::is_whitespace) {
        Some(("X86", n)) => (Arch::X86, n.trim()),
        Some(("X86_64", n)) => (Arch::X86_64, n.trim()),
        _ => return err(format!("unsupported header `{head}`")),
    };
    let rest: Vec<&str> = lines.collect();
    let rest = rest.join("\n");
    let open = rest.find('{').ok_or_else(|| Error("missing `{`".into()))?;
    let close = open
        + rest[open..]
            .find('}')
            .ok_or_else(|| Error("missing `}`".into()))?;
    let preamble = &rest[..open];
    let doc = preamble.lines().find_map(|l| {
        let l = l.trim();
        (l.len() >= 2 && l.starts_with('"') && l.ends_with('"'))
            .then(|| l[1..l.len() - 1].to_string())
    });
    let mut test = Test {
        arch,
        name: name.to_string(),
        doc,
        decls: Vec::new(),
        regs: Vec::new(),
        threads: Vec::new(),
        quant: Quant::Exists,
        cond: Expr::True,
    };
    for item in rest[open + 1..close].split(';') {
        parse_init_item(item, &mut test)?;
    }
    // Program table and condition.
    let body = &rest[close + 1..];
    let kw = ["~exists", "exists", "forall", "locations", "filter"];
    let cut = body
        .lines()
        .scan(0usize, |off, l| {
            let start = *off;
            *off += l.len() + 1;
            Some((start, l))
        })
        .find(|(_, l)| {
            let t = l.trim_start();
            kw.iter().any(|k| t.starts_with(k))
        })
        .map(|(o, _)| o)
        .ok_or_else(|| Error("missing final condition".into()))?;
    let table = &body[..cut];
    let mut rows = table.split(';').map(str::trim).filter(|r| !r.is_empty());
    let header = rows
        .next()
        .ok_or_else(|| Error("missing program table".into()))?;
    let procs: Vec<&str> = header.split('|').map(str::trim).collect();
    for (i, p) in procs.iter().enumerate() {
        if *p != format!("P{i}") {
            return err(format!("bad thread header `{header}`"));
        }
    }
    test.threads = vec![Vec::new(); procs.len()];
    for row in rows {
        let cells: Vec<&str> = row.split('|').map(str::trim).collect();
        if cells.len() != procs.len() {
            return err(format!(
                "row `{row}` has {} cells, expected {}",
                cells.len(),
                procs.len()
            ));
        }
        for (t, c) in cells.iter().enumerate() {
            if !c.is_empty() {
                test.threads[t].push(c.to_string());
            }
        }
    }
    let mut cond = body[cut..].trim();
    if let Some(r) = cond.strip_prefix("locations") {
        let end = r
            .find(']')
            .ok_or_else(|| Error("bad locations clause".into()))?;
        cond = r[end + 1..].trim();
    }
    let (quant, formula) = if let Some(r) = cond.strip_prefix("~exists") {
        (Quant::NotExists, r)
    } else if let Some(r) = cond.strip_prefix("exists") {
        (Quant::Exists, r)
    } else if let Some(r) = cond.strip_prefix("forall") {
        (Quant::Forall, r)
    } else {
        return err(format!("unsupported condition `{cond}`"));
    };
    test.quant = quant;
    let toks = tokenize(formula)?;
    let mut p = ExprParser {
        toks: &toks,
        pos: 0,
    };
    test.cond = p.or()?;
    if p.pos != toks.len() {
        return err(format!("trailing tokens in condition `{formula}`"));
    }
    Ok(test)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    LParen,
    RParen,
    And,
    Or,
    Not,
    Eq,
    Word(String),
}

fn tokenize(s: &str) -> Result<Vec<Tok>, Error> {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        let c = b[i] as char;
        if c.is_whitespace() {
            i += 1;
        } else if c == '(' {
            out.push(Tok::LParen);
            i += 1;
        } else if c == ')' {
            out.push(Tok::RParen);
            i += 1;
        } else if s[i..].starts_with("/\\") {
            out.push(Tok::And);
            i += 2;
        } else if s[i..].starts_with("\\/") {
            out.push(Tok::Or);
            i += 2;
        } else if c == '~' {
            out.push(Tok::Not);
            i += 1;
        } else if c == '=' {
            out.push(Tok::Eq);
            i += 1;
        } else {
            let start = i;
            while i < b.len() {
                let d = b[i] as char;
                if d.is_ascii_alphanumeric() || "_:[]-+.".contains(d) {
                    i += 1;
                } else {
                    break;
                }
            }
            if i == start {
                return err(format!("unexpected `{c}` in condition"));
            }
            out.push(Tok::Word(s[start..i].to_string()));
        }
    }
    Ok(out)
}

struct ExprParser<'a> {
    toks: &'a [Tok],
    pos: usize,
}

impl ExprParser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn or(&mut self) -> Result<Expr, Error> {
        let mut e = self.and()?;
        while self.peek() == Some(&Tok::Or) {
            self.pos += 1;
            e = Expr::Or(Box::new(e), Box::new(self.and()?));
        }
        Ok(e)
    }
    fn and(&mut self) -> Result<Expr, Error> {
        let mut e = self.unary()?;
        while self.peek() == Some(&Tok::And) {
            self.pos += 1;
            e = Expr::And(Box::new(e), Box::new(self.unary()?));
        }
        Ok(e)
    }
    fn unary(&mut self) -> Result<Expr, Error> {
        match self.peek().cloned() {
            Some(Tok::Not) => {
                self.pos += 1;
                Ok(Expr::Not(Box::new(self.unary()?)))
            }
            Some(Tok::LParen) => {
                self.pos += 1;
                let e = self.or()?;
                if self.peek() != Some(&Tok::RParen) {
                    return err("missing `)`");
                }
                self.pos += 1;
                Ok(e)
            }
            Some(Tok::Word(w)) if w == "true" => {
                self.pos += 1;
                Ok(Expr::True)
            }
            Some(Tok::Word(lhs)) => {
                self.pos += 1;
                if self.peek() != Some(&Tok::Eq) {
                    return err(format!("expected `=` after `{lhs}`"));
                }
                self.pos += 1;
                let Some(Tok::Word(v)) = self.peek().cloned() else {
                    return err("expected a value");
                };
                self.pos += 1;
                let value = parse_int(&v)?;
                if let Some((t, r)) = lhs.split_once(':') {
                    let thread = t
                        .parse::<usize>()
                        .map_err(|_| Error(format!("bad thread `{lhs}`")))?;
                    Ok(Expr::Atom(Atom::Reg {
                        thread,
                        reg: r.to_string(),
                        value,
                    }))
                } else {
                    let name = lhs.trim_start_matches('[').trim_end_matches(']');
                    if !is_ident(name) {
                        return err(format!("bad location `{lhs}`"));
                    }
                    Ok(Expr::Atom(Atom::Loc {
                        name: name.to_string(),
                        value,
                    }))
                }
            }
            t => err(format!("unexpected token {t:?}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_intel_sb() {
        let t = parse(
            "X86 SB\n\"PodWR Fre PodWR Fre\"\nCycle=x\n{\n}\n P0          | P1          ;\n MOV [x],$1  | MOV [y],$1  ;\n MOV EAX,[y] | MOV EAX,[x] ;\nexists\n(0:EAX=0 /\\ 1:EAX=0)\n",
        )
        .unwrap();
        assert_eq!(t.arch, Arch::X86);
        assert_eq!(t.name, "SB");
        assert_eq!(t.doc.as_deref(), Some("PodWR Fre PodWR Fre"));
        assert_eq!(
            t.threads,
            vec![
                vec!["MOV [x],$1", "MOV EAX,[y]"],
                vec!["MOV [y],$1", "MOV EAX,[x]"]
            ]
        );
        assert_eq!(t.quant, Quant::Exists);
        assert!(matches!(t.cond, Expr::And(_, _)));
    }

    #[test]
    fn parses_att_with_types_comments_and_not_exists() {
        let t = parse(
            "X86_64 A011\n{\n  int y; (* comment *)\n  int64_t x=-1; 0:rax=y; 1:rbx=0x10;\n}\n  P0         |  P1            ;\n movl $1,(y) | movl $2,%eax   ;\n             | xchgl (y),%eax ;\n~exists 1:rax=1 /\\ [y]=1\n",
        )
        .unwrap();
        assert_eq!(t.arch, Arch::X86_64);
        assert_eq!(t.decls.len(), 2);
        assert_eq!(
            t.decls[1],
            Decl {
                name: "x".into(),
                elem: 8,
                count: 1,
                init: -1
            }
        );
        assert_eq!(t.regs[0], (0, "rax".into(), RegInit::Addr("y".into())));
        assert_eq!(t.regs[1], (1, "rbx".into(), RegInit::Int(16)));
        assert_eq!(t.threads[0], vec!["movl $1,(y)"]);
        assert_eq!(t.threads[1].len(), 2);
        assert_eq!(t.quant, Quant::NotExists);
    }

    #[test]
    fn parses_locations_clause_and_forall() {
        let t = parse("X86_64 A010\n{ uint64_t x; }\n P0 ;\n movq %rbx,(x) ;\nlocations [x;]\nforall [x] = 0x2\n").unwrap();
        assert_eq!(t.quant, Quant::Forall);
        assert_eq!(
            t.cond,
            Expr::Atom(Atom::Loc {
                name: "x".into(),
                value: 2
            })
        );
    }

    #[test]
    fn rejects_bad_rows_and_conditions() {
        assert!(parse("X86 T\n{}\n P0 | P1 ;\n MOV [x],$1 ;\nexists (x=1)\n").is_err());
        assert!(parse("X86 T\n{}\n P0 ;\n MFENCE ;\nexists (x=1 /\\)\n").is_err());
        assert!(parse("ARM T\n{}\n P0 ;\n NOP ;\nexists (x=1)\n").is_err());
        assert!(parse("X86 T\n{ int a[2]={1,2}; }\n P0 ;\n MFENCE ;\nexists (x=1)\n").is_err());
    }

    #[test]
    fn precedence_and_binds_tighter_than_or() {
        let t = parse("X86 T\n{}\n P0 ;\n MFENCE ;\nexists (x=1 \\/ y=2 /\\ ~z=3)\n").unwrap();
        let Expr::Or(_, r) = t.cond else { panic!() };
        assert!(matches!(*r, Expr::And(_, _)));
    }
}
