//! A minimal JSON reader, enough for `specs/spectec/manifest.json`.

use std::collections::BTreeMap;

/// A JSON value.
#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    /// Numbers are kept as their source text.
    Num(String),
    Str(String),
    Arr(Vec<Json>),
    Obj(BTreeMap<String, Json>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(m) => m.get(key),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_arr(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(v) => Some(v),
            _ => None,
        }
    }
    pub fn as_usize(&self) -> Option<usize> {
        match self {
            Json::Num(s) => s.parse().ok(),
            _ => None,
        }
    }
}

/// Parse a complete JSON document.
pub fn parse(text: &str) -> Result<Json, String> {
    let mut p = Parser {
        s: text.as_bytes(),
        i: 0,
    };
    let v = p.value()?;
    p.ws();
    if p.i != p.s.len() {
        return Err(format!("trailing data at byte {}", p.i));
    }
    Ok(v)
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl Parser<'_> {
    fn ws(&mut self) {
        while self.i < self.s.len() && matches!(self.s[self.i], b' ' | b'\n' | b'\r' | b'\t') {
            self.i += 1;
        }
    }
    fn eat(&mut self, c: u8) -> Result<(), String> {
        self.ws();
        if self.s.get(self.i) == Some(&c) {
            self.i += 1;
            Ok(())
        } else {
            Err(format!("expected `{}` at byte {}", c as char, self.i))
        }
    }
    fn lit(&mut self, word: &str, v: Json) -> Result<Json, String> {
        if self.s[self.i..].starts_with(word.as_bytes()) {
            self.i += word.len();
            Ok(v)
        } else {
            Err(format!("bad literal at byte {}", self.i))
        }
    }
    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        match self.s.get(self.i) {
            None => Err("unexpected end of JSON".into()),
            Some(b'{') => {
                self.i += 1;
                let mut m = BTreeMap::new();
                self.ws();
                if self.s.get(self.i) == Some(&b'}') {
                    self.i += 1;
                    return Ok(Json::Obj(m));
                }
                loop {
                    self.ws();
                    let k = self.string()?;
                    self.eat(b':')?;
                    let v = self.value()?;
                    m.insert(k, v);
                    self.ws();
                    match self.s.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b'}') => {
                            self.i += 1;
                            return Ok(Json::Obj(m));
                        }
                        _ => return Err(format!("expected `,` or `}}` at byte {}", self.i)),
                    }
                }
            }
            Some(b'[') => {
                self.i += 1;
                let mut v = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&b']') {
                    self.i += 1;
                    return Ok(Json::Arr(v));
                }
                loop {
                    v.push(self.value()?);
                    self.ws();
                    match self.s.get(self.i) {
                        Some(b',') => self.i += 1,
                        Some(b']') => {
                            self.i += 1;
                            return Ok(Json::Arr(v));
                        }
                        _ => return Err(format!("expected `,` or `]` at byte {}", self.i)),
                    }
                }
            }
            Some(b'"') => Ok(Json::Str(self.string()?)),
            Some(b't') => self.lit("true", Json::Bool(true)),
            Some(b'f') => self.lit("false", Json::Bool(false)),
            Some(b'n') => self.lit("null", Json::Null),
            Some(_) => {
                let start = self.i;
                while self.i < self.s.len()
                    && matches!(
                        self.s[self.i],
                        b'-' | b'+' | b'.' | b'e' | b'E' | b'0'..=b'9'
                    )
                {
                    self.i += 1;
                }
                if start == self.i {
                    return Err(format!("unexpected byte at {}", self.i));
                }
                Ok(Json::Num(
                    String::from_utf8_lossy(&self.s[start..self.i]).into_owned(),
                ))
            }
        }
    }
    fn string(&mut self) -> Result<String, String> {
        if self.s.get(self.i) != Some(&b'"') {
            return Err(format!("expected string at byte {}", self.i));
        }
        self.i += 1;
        let mut out = Vec::new();
        loop {
            match self.s.get(self.i) {
                None => return Err("unterminated string".into()),
                Some(b'"') => {
                    self.i += 1;
                    return String::from_utf8(out).map_err(|e| e.to_string());
                }
                Some(b'\\') => {
                    let e = *self.s.get(self.i + 1).ok_or("bad escape")?;
                    self.i += 2;
                    let c = match e {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'/' => '/',
                        b'n' => '\n',
                        b't' => '\t',
                        b'r' => '\r',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'u' => {
                            let h = std::str::from_utf8(
                                self.s.get(self.i..self.i + 4).ok_or("bad \\u")?,
                            )
                            .map_err(|e| e.to_string())?;
                            self.i += 4;
                            char::from_u32(u32::from_str_radix(h, 16).map_err(|e| e.to_string())?)
                                .ok_or("surrogate escapes are not supported")?
                        }
                        _ => return Err("bad escape".into()),
                    };
                    let mut buf = [0; 4];
                    out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
                }
                Some(&b) => {
                    out.push(b);
                    self.i += 1;
                }
            }
        }
    }
}

/// Print a JSON value as Python's `json.dumps(v, indent=2, sort_keys=True)` does (the layout of
/// the vendored manifests), without a trailing newline.  Non-ASCII is escaped as `\uXXXX`.
pub fn pretty(v: &Json) -> String {
    let mut out = String::new();
    pretty_at(v, 0, &mut out);
    out
}

fn pretty_at(v: &Json, depth: usize, out: &mut String) {
    let pad = |d: usize| "  ".repeat(d);
    match v {
        Json::Null => out.push_str("null"),
        Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Json::Num(n) => out.push_str(n),
        Json::Str(s) => quote(s, out),
        Json::Arr(xs) if xs.is_empty() => out.push_str("[]"),
        Json::Obj(m) if m.is_empty() => out.push_str("{}"),
        Json::Arr(xs) => {
            out.push('[');
            for (i, x) in xs.iter().enumerate() {
                out.push_str(if i == 0 { "\n" } else { ",\n" });
                out.push_str(&pad(depth + 1));
                pretty_at(x, depth + 1, out);
            }
            out.push('\n');
            out.push_str(&pad(depth));
            out.push(']');
        }
        Json::Obj(m) => {
            out.push('{');
            for (i, (k, x)) in m.iter().enumerate() {
                out.push_str(if i == 0 { "\n" } else { ",\n" });
                out.push_str(&pad(depth + 1));
                quote(k, out);
                out.push_str(": ");
                pretty_at(x, depth + 1, out);
            }
            out.push('\n');
            out.push_str(&pad(depth));
            out.push('}');
        }
    }
}

fn quote(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                let mut buf = [0u16; 2];
                for u in c.encode_utf16(&mut buf) {
                    out.push_str(&format!("\\u{u:04x}"));
                }
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_nested() {
        let v = parse(r#"{"a": [1, "x\"y", true, null], "b": {}}"#).unwrap();
        assert_eq!(v.get("a").unwrap().as_arr().unwrap()[0].as_usize(), Some(1));
        assert_eq!(
            v.get("a").unwrap().as_arr().unwrap()[1].as_str(),
            Some("x\"y")
        );
    }

    #[test]
    fn pretty_reprints_the_main_manifest() {
        std::env::set_current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../..")).unwrap();
        let text = std::fs::read_to_string("specs/spectec/e7a9df7c/manifest.json").unwrap();
        assert_eq!(pretty(&parse(&text).unwrap()) + "\n", text);
        assert_eq!(
            pretty(&parse(r#"{"a":"\u00e9\n","b":[]}"#).unwrap()),
            "{\n  \"a\": \"\\u00e9\\n\",\n  \"b\": []\n}"
        );
    }
}
