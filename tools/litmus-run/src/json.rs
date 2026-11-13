//! A minimal JSON reader (std only) for `tools/litmus-x86/export/corpus.json`.
//!
//! Numbers are kept as their source text; the export writes every value that may exceed 2^53
//! as a hex string, so callers convert numbers with [`Value::uint`].

/// A JSON value.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Num(String),
    Str(String),
    Arr(Vec<Value>),
    Obj(Vec<(String, Value)>),
}

/// A parse or shape error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

struct P<'a> {
    s: &'a [u8],
    i: usize,
}

impl P<'_> {
    fn err<T>(&self, m: &str) -> Result<T, Error> {
        Err(Error(format!("json: {m} at byte {}", self.i)))
    }
    fn ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }
    fn eat(&mut self, c: u8) -> Result<(), Error> {
        self.ws();
        if self.s.get(self.i) == Some(&c) {
            self.i += 1;
            Ok(())
        } else {
            self.err(&format!("expected `{}`", c as char))
        }
    }
    fn lit(&mut self, w: &str, v: Value) -> Result<Value, Error> {
        if self.s[self.i..].starts_with(w.as_bytes()) {
            self.i += w.len();
            Ok(v)
        } else {
            self.err("bad literal")
        }
    }
    fn string(&mut self) -> Result<String, Error> {
        self.eat(b'"')?;
        let mut out = String::new();
        loop {
            let Some(&c) = self.s.get(self.i) else {
                return self.err("unterminated string");
            };
            self.i += 1;
            match c {
                b'"' => return Ok(out),
                b'\\' => {
                    let Some(&e) = self.s.get(self.i) else {
                        return self.err("bad escape");
                    };
                    self.i += 1;
                    match e {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'n' => out.push('\n'),
                        b't' => out.push('\t'),
                        b'r' => out.push('\r'),
                        b'u' => {
                            let h = self
                                .s
                                .get(self.i..self.i + 4)
                                .and_then(|h| std::str::from_utf8(h).ok())
                                .and_then(|h| u32::from_str_radix(h, 16).ok())
                                .and_then(char::from_u32);
                            let Some(ch) = h else {
                                return self.err("bad \\u escape");
                            };
                            self.i += 4;
                            out.push(ch);
                        }
                        _ => return self.err("bad escape"),
                    }
                }
                _ => {
                    // Copy one UTF-8 sequence.
                    let start = self.i - 1;
                    let len = match c {
                        0x00..=0x7f => 1,
                        0xc0..=0xdf => 2,
                        0xe0..=0xef => 3,
                        _ => 4,
                    };
                    let Some(chunk) = self.s.get(start..start + len) else {
                        return self.err("truncated utf-8");
                    };
                    match std::str::from_utf8(chunk) {
                        Ok(t) => out.push_str(t),
                        Err(_) => return self.err("bad utf-8"),
                    }
                    self.i = start + len;
                }
            }
        }
    }
    fn value(&mut self) -> Result<Value, Error> {
        self.ws();
        match self.s.get(self.i) {
            None => self.err("unexpected end"),
            Some(b'n') => self.lit("null", Value::Null),
            Some(b't') => self.lit("true", Value::Bool(true)),
            Some(b'f') => self.lit("false", Value::Bool(false)),
            Some(b'"') => Ok(Value::Str(self.string()?)),
            Some(b'[') => {
                self.i += 1;
                let mut v = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&b']') {
                    self.i += 1;
                    return Ok(Value::Arr(v));
                }
                loop {
                    v.push(self.value()?);
                    self.ws();
                    match self.s.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b']') => {
                            self.i += 1;
                            return Ok(Value::Arr(v));
                        }
                        _ => return self.err("expected `,` or `]`"),
                    }
                }
            }
            Some(b'{') => {
                self.i += 1;
                let mut v = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&b'}') {
                    self.i += 1;
                    return Ok(Value::Obj(v));
                }
                loop {
                    self.ws();
                    let k = self.string()?;
                    self.eat(b':')?;
                    v.push((k, self.value()?));
                    self.ws();
                    match self.s.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {
                            self.i += 1;
                            return Ok(Value::Obj(v));
                        }
                        _ => return self.err("expected `,` or `}`"),
                    }
                }
            }
            Some(c) if c.is_ascii_digit() || *c == b'-' => {
                let start = self.i;
                self.i += 1;
                while self.i < self.s.len()
                    && matches!(
                        self.s[self.i],
                        b'0'..=b'9' | b'.' | b'e' | b'E' | b'+' | b'-'
                    )
                {
                    self.i += 1;
                }
                Ok(Value::Num(
                    String::from_utf8_lossy(&self.s[start..self.i]).into_owned(),
                ))
            }
            Some(_) => self.err("unexpected character"),
        }
    }
}

/// Parse a JSON document.
pub fn parse(src: &str) -> Result<Value, Error> {
    let mut p = P {
        s: src.as_bytes(),
        i: 0,
    };
    let v = p.value()?;
    p.ws();
    if p.i != p.s.len() {
        return p.err("trailing data");
    }
    Ok(v)
}

impl Value {
    /// A field of an object.
    pub fn get(&self, k: &str) -> Result<&Value, Error> {
        match self {
            Value::Obj(v) => v
                .iter()
                .find(|(n, _)| n == k)
                .map(|(_, v)| v)
                .ok_or_else(|| Error(format!("missing field `{k}`"))),
            _ => Err(Error(format!("field `{k}` of a non-object"))),
        }
    }
    /// The elements of an array.
    pub fn arr(&self) -> Result<&[Value], Error> {
        match self {
            Value::Arr(v) => Ok(v),
            _ => Err(Error("expected an array".into())),
        }
    }
    /// A string.
    pub fn str(&self) -> Result<&str, Error> {
        match self {
            Value::Str(s) => Ok(s),
            _ => Err(Error("expected a string".into())),
        }
    }
    /// An unsigned integer: a decimal number, or a `0x` hex string.
    pub fn uint(&self) -> Result<u128, Error> {
        let bad = || Error(format!("expected an unsigned integer, got {self:?}"));
        match self {
            Value::Num(n) => n.parse().map_err(|_| bad()),
            Value::Str(s) => s
                .strip_prefix("0x")
                .and_then(|h| u128::from_str_radix(h, 16).ok())
                .ok_or_else(bad),
            _ => Err(bad()),
        }
    }
    /// `null`.
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }
}

/// Decode a string of hex byte pairs.
pub fn hex_bytes(s: &str) -> Result<Vec<u8>, Error> {
    if !s.len().is_multiple_of(2) {
        return Err(Error(format!("odd-length hex `{s}`")));
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| Error(format!("bad hex `{s}`"))))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values() {
        let v = parse(r#" {"a": [1, "0x1f", null, true, {"b": "x\"éé"}], "c": {}} "#).unwrap();
        let a = v.get("a").unwrap().arr().unwrap();
        assert_eq!(a[0].uint().unwrap(), 1);
        assert_eq!(a[1].uint().unwrap(), 31);
        assert!(a[2].is_null());
        assert_eq!(a[3], Value::Bool(true));
        assert_eq!(a[4].get("b").unwrap().str().unwrap(), "x\"éé");
        assert_eq!(v.get("c").unwrap(), &Value::Obj(vec![]));
        assert!(parse("[1,]").is_err());
        assert!(parse("{} x").is_err());
        assert_eq!(hex_bytes("0faef0").unwrap(), vec![0x0f, 0xae, 0xf0]);
        assert!(hex_bytes("0fa").is_err());
    }
}
