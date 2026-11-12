//! A minimal S-expression reader (`;` comments, atoms, lists, `"strings"`).

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    Str(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            _ => None,
        }
    }
    pub fn list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(l) => Some(l),
            _ => None,
        }
    }
    pub fn string(&self) -> Option<&str> {
        match self {
            Sexp::Str(s) | Sexp::Atom(s) => Some(s),
            _ => None,
        }
    }
    /// The tail of a list whose head is the atom `key`.
    pub fn field(items: &[Sexp], key: &str) -> Option<Vec<Sexp>> {
        items.iter().find_map(|s| {
            let l = s.list()?;
            (l.first()?.atom()? == key).then(|| l[1..].to_vec())
        })
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(a) => write!(f, "{a}"),
            Sexp::Str(s) => write!(f, "{s:?}"),
            Sexp::List(l) => {
                write!(f, "(")?;
                for (i, x) in l.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Parse every S-expression of a text.
pub fn parse_all(src: &str) -> Result<Vec<Sexp>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut pos = 0;
    let mut out = vec![];
    loop {
        skip(&chars, &mut pos);
        if pos >= chars.len() {
            return Ok(out);
        }
        out.push(parse_one(&chars, &mut pos)?);
    }
}

fn skip(c: &[char], pos: &mut usize) {
    while *pos < c.len() {
        if c[*pos].is_whitespace() {
            *pos += 1;
        } else if c[*pos] == ';' {
            while *pos < c.len() && c[*pos] != '\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

fn parse_one(c: &[char], pos: &mut usize) -> Result<Sexp, String> {
    skip(c, pos);
    match c.get(*pos) {
        None => Err("unexpected end of input".into()),
        Some('(') => {
            *pos += 1;
            let mut items = vec![];
            loop {
                skip(c, pos);
                match c.get(*pos) {
                    None => return Err("unclosed parenthesis".into()),
                    Some(')') => {
                        *pos += 1;
                        return Ok(Sexp::List(items));
                    }
                    _ => items.push(parse_one(c, pos)?),
                }
            }
        }
        Some(')') => Err("unexpected `)`".into()),
        Some('"') => {
            *pos += 1;
            let mut s = String::new();
            while let Some(&ch) = c.get(*pos) {
                *pos += 1;
                if ch == '"' {
                    return Ok(Sexp::Str(s));
                }
                s.push(ch);
            }
            Err("unclosed string".into())
        }
        Some(_) => {
            let start = *pos;
            while *pos < c.len() && !c[*pos].is_whitespace() && c[*pos] != '(' && c[*pos] != ')' {
                *pos += 1;
            }
            Ok(Sexp::Atom(c[start..*pos].iter().collect()))
        }
    }
}
