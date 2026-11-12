//! The `--ast` S-expression stream: a reader mirroring `SExp/Parse.lean` and a printer
//! transcribing `SExp/Printer.lean` (`spectec/src/util/sexpr.ml`).  Atoms keep their quotes,
//! exactly as `SExp.atom` does.

/// An S-expression: a bare or quoted atom, or a tagged node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExp {
    Atom(String),
    Node(String, Vec<SExp>),
}

fn is_layout(c: u8) -> bool {
    c == b' ' || c == b'\n'
}

fn is_bare(c: u8) -> bool {
    !is_layout(c) && c != b'(' && c != b')' && c != b'"'
}

struct Cursor<'a> {
    s: &'a [u8],
    pos: usize,
}

impl Cursor<'_> {
    fn peek(&self) -> Option<u8> {
        self.s.get(self.pos).copied()
    }
    fn skip_layout(&mut self) {
        while self.peek().is_some_and(is_layout) {
            self.pos += 1;
        }
    }
    fn skip_bare(&mut self) {
        while self.peek().is_some_and(is_bare) {
            self.pos += 1;
        }
    }
    fn slice(&self, start: usize) -> Result<String, String> {
        String::from_utf8(self.s[start..self.pos].to_vec()).map_err(|e| e.to_string())
    }
    fn one(&mut self) -> Result<SExp, String> {
        self.skip_layout();
        match self.peek() {
            None => Err("unexpected end of input".into()),
            Some(b')') => Err(format!("unexpected `)` at byte {}", self.pos)),
            Some(b'(') => {
                self.pos += 1;
                let start = self.pos;
                self.skip_bare();
                if self.pos == start {
                    return Err(format!("a node needs a bare tag at byte {start}"));
                }
                let tag = self.slice(start)?;
                let mut kids = Vec::new();
                loop {
                    self.skip_layout();
                    match self.peek() {
                        None => return Err("unterminated node".into()),
                        Some(b')') => {
                            self.pos += 1;
                            return Ok(SExp::Node(tag, kids));
                        }
                        Some(_) => kids.push(self.one()?),
                    }
                }
            }
            Some(b'"') => {
                let start = self.pos;
                self.pos += 1;
                loop {
                    match self.peek() {
                        None => return Err("unterminated string".into()),
                        Some(b'"') => {
                            self.pos += 1;
                            break;
                        }
                        Some(b'\\') => {
                            if self.s.get(self.pos + 1).is_none() {
                                return Err("unterminated escape".into());
                            }
                            self.pos += 2;
                        }
                        Some(_) => self.pos += 1,
                    }
                }
                Ok(SExp::Atom(self.slice(start)?))
            }
            Some(c) if is_bare(c) => {
                let start = self.pos;
                self.skip_bare();
                Ok(SExp::Atom(self.slice(start)?))
            }
            Some(c) => Err(format!("unexpected character {:?}", c as char)),
        }
    }
}

/// Read a whole stream of top-level S-expressions.
pub fn parse_stream(text: &str) -> Result<Vec<SExp>, String> {
    let mut c = Cursor {
        s: text.as_bytes(),
        pos: 0,
    };
    let mut out = Vec::new();
    loop {
        c.skip_layout();
        if c.peek().is_none() {
            return Ok(out);
        }
        out.push(c.one()?);
    }
}

/// Read exactly one S-expression.
pub fn parse_one(text: &str) -> Result<SExp, String> {
    let mut v = parse_stream(text)?;
    if v.len() == 1 {
        Ok(v.remove(0))
    } else {
        Err(format!("expected one S-expression, found {}", v.len()))
    }
}

/// `pp` (`sexpr.ml:15-23`): the flat byte width, and the layout appended to `out`.
fn pp(off: usize, width: usize, e: &SExp) -> (usize, String) {
    match e {
        SExp::Atom(s) => (s.len(), s.clone()),
        SExp::Node(tag, kids) => {
            let lrs: Vec<(usize, String)> = kids.iter().map(|k| pp(off + 2, width, k)).collect();
            let len = tag.len() + lrs.len() + (2 + lrs.iter().map(|l| l.0).sum::<usize>());
            let (sep, fin) = if off + len <= width {
                (" ".to_string(), String::new())
            } else {
                (
                    format!("\n  {}", " ".repeat(off)),
                    format!("\n{}", " ".repeat(off)),
                )
            };
            let mut s = String::with_capacity(len);
            s.push('(');
            s.push_str(tag);
            for (_, r) in &lrs {
                s.push_str(&sep);
                s.push_str(r);
            }
            s.push_str(&fin);
            s.push(')');
            (len, s)
        }
    }
}

/// `SExp.render`: the layout of one S-expression against a target width.
pub fn render(width: usize, e: &SExp) -> String {
    pp(0, width, e).1
}

/// `SExp.astFile`: the exact contents of a `spectec --ast -o FILE` file.
pub fn ast_file(width: usize, es: &[SExp]) -> String {
    let mut s = String::new();
    for e in es {
        s.push_str(&render(width, e));
        s.push('\n');
    }
    s.push('\n');
    s
}

/// `Errata.wideWidth`: wide enough that nothing breaks.
pub const WIDE_WIDTH: usize = 1_000_000_000;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_round_trip() {
        let t = "(typ \"N\" (inst (alias nat)))";
        let e = parse_one(t).unwrap();
        assert_eq!(render(80, &e), t);
    }
}
