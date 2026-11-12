//! The `spectec_erratum` commands of `Silmaril/Raw/Wasm/SpecTec/SpecTec/Errata/*.lean`, read as
//! text and applied to S-expressions exactly as the Lean elaborator `elabSpectecErratum`
//! (`Errata.lean`) applies them.  The Lean files stay the single source of truth.

use crate::sexp::{self, SExp};

/// One `spectec_erratum` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Erratum {
    pub issue: u32,
    /// The script constant, e.g. `Specs.wasm30`.
    pub script: String,
    pub target: String,
    pub replacing: String,
    pub with: String,
    pub name: Option<String>,
}

/// Decode the body of a Lean string literal (without the quotes).
fn lean_unescape(body: &str) -> Result<String, String> {
    let mut out = String::new();
    let mut it = body.chars().peekable();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match it.next() {
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('\'') => out.push('\''),
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('x') => {
                let h: String = it.by_ref().take(2).collect();
                let n = u32::from_str_radix(&h, 16).map_err(|e| e.to_string())?;
                out.push(char::from_u32(n).ok_or("bad \\x escape")?);
            }
            Some('\n') => {
                while it.peek().is_some_and(|c| c.is_whitespace()) {
                    it.next();
                }
            }
            other => return Err(format!("unsupported Lean escape \\{other:?}")),
        }
    }
    Ok(out)
}

#[derive(Debug, PartialEq)]
enum Tok {
    Word(String),
    Str(String),
}

/// Tokenize from `src`, stopping at the first character that is neither layout, a word
/// character, nor a string literal.
fn tokens(src: &str) -> Result<Vec<Tok>, String> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    loop {
        while i < b.len() && b[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= b.len() {
            return Ok(out);
        }
        if b[i] == b'"' {
            let start = i + 1;
            i += 1;
            while i < b.len() && b[i] != b'"' {
                if b[i] == b'\\' {
                    i += 1;
                }
                i += 1;
            }
            out.push(Tok::Str(lean_unescape(&src[start..i])?));
            i += 1;
        } else if b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'.' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'.') {
                i += 1;
            }
            out.push(Tok::Word(src[start..i].to_string()));
        } else {
            return Ok(out);
        }
    }
}

/// Every `spectec_erratum` command in a Lean source file, in file order.
pub fn extract(src: &str) -> Result<Vec<Erratum>, String> {
    let mut out = Vec::new();
    let mut offset = 0;
    for line in src.split_inclusive('\n') {
        if line.starts_with("spectec_erratum ") {
            out.push(command(&src[offset..])?);
        }
        offset += line.len();
    }
    Ok(out)
}

fn command(src: &str) -> Result<Erratum, String> {
    let toks = tokens(src)?;
    let mut it = toks.into_iter().peekable();
    let word = |w: &str, it: &mut std::iter::Peekable<std::vec::IntoIter<Tok>>| match it.next() {
        Some(Tok::Word(x)) if w.is_empty() || x == w => Ok(x),
        other => Err(format!(
            "expected `{w}` in spectec_erratum, found {other:?}"
        )),
    };
    word("spectec_erratum", &mut it)?;
    let issue = word("", &mut it)?
        .parse::<u32>()
        .map_err(|e| e.to_string())?;
    word("in", &mut it)?;
    let script = word("", &mut it)?;
    word("on", &mut it)?;
    let Some(Tok::Str(target)) = it.next() else {
        return Err("spectec_erratum: missing target".into());
    };
    let strs = |it: &mut std::iter::Peekable<std::vec::IntoIter<Tok>>| {
        let mut s = String::new();
        while let Some(Tok::Str(x)) = it.peek() {
            s.push_str(x);
            it.next();
        }
        s
    };
    word("because", &mut it)?;
    strs(&mut it);
    word("replacing", &mut it)?;
    let replacing = strs(&mut it);
    word("with", &mut it)?;
    let with = strs(&mut it);
    let name = match it.peek() {
        Some(Tok::Word(w)) if w == "as" => {
            it.next();
            Some(word("", &mut it)?)
        }
        _ => None,
    };
    Ok(Erratum {
        issue,
        script,
        target,
        replacing,
        with,
        name,
    })
}

fn flatten(defs: &[SExp]) -> Vec<&SExp> {
    let mut out = Vec::new();
    for d in defs {
        match d {
            SExp::Node(t, ks) if t == "rec" => out.extend(flatten(ks)),
            d => out.push(d),
        }
    }
    out
}

/// Apply one erratum to `script`, returning the corrected definition (as `elabSpectecErratum`
/// computes it: unique definition named `target`, rendered flat, fragment replaced exactly
/// once, re-read; the result must differ and declare the same thing).
pub fn corrected(e: &Erratum, script: &[SExp]) -> Result<SExp, String> {
    let hits: Vec<&SExp> = flatten(script)
        .into_iter()
        .filter(|d| crate::emit::decl_kind(d).is_some_and(|(_, n)| n == e.target))
        .collect();
    let [orig] = hits.as_slice() else {
        return Err(format!(
            "erratum {}: {} definitions named {}",
            e.issue,
            hits.len(),
            e.target
        ));
    };
    let printed = sexp::render(sexp::WIDE_WIDTH, orig);
    let n = printed.matches(&e.replacing).count();
    if e.replacing.is_empty() || n != 1 {
        return Err(format!(
            "erratum {} on {}: fragment occurs {n} times",
            e.issue, e.target
        ));
    }
    let edited = printed.replacen(&e.replacing, &e.with, 1);
    let form = sexp::parse_one(&edited)?;
    crate::emit::def(&form)?;
    if &form == *orig {
        return Err(format!("erratum {} leaves {} unchanged", e.issue, e.target));
    }
    if crate::emit::decl_kind(&form) != crate::emit::decl_kind(orig) {
        return Err(format!(
            "erratum {} changes what {} declares",
            e.issue, e.target
        ));
    }
    Ok(form)
}

/// `IL.replaceDef`: replace every definition declaring the same thing as `new`, at any depth.
fn replace_def(new: &SExp, d: &SExp) -> SExp {
    match d {
        SExp::Node(t, ks) if t == "rec" => {
            SExp::Node(t.clone(), ks.iter().map(|k| replace_def(new, k)).collect())
        }
        d if crate::emit::decl_kind(d).is_some()
            && crate::emit::decl_kind(d) == crate::emit::decl_kind(new) =>
        {
            new.clone()
        }
        d => d.clone(),
    }
}

/// `IL.applyErrata`: each erratum computed against the *base* script (as the Lean commands
/// are), then spliced in list order with `replaceDefs`.  Fails, like `Erratum.applies`, when
/// the target is not declared exactly once in the script it is spliced into, or the splice
/// would change nothing.
pub fn apply_all(errata: &[Erratum], base: &[SExp]) -> Result<Vec<SExp>, String> {
    let mut cur = base.to_vec();
    for e in errata {
        let new = corrected(e, base)?;
        let count = flatten(&cur)
            .iter()
            .filter(|d| crate::emit::decl_kind(d).is_some_and(|(_, n)| n == e.target))
            .count();
        if count != 1 {
            return Err(format!(
                "erratum {}: {count} targets in the spliced script",
                e.issue
            ));
        }
        let old = flatten(&cur)
            .into_iter()
            .find(|d| crate::emit::decl_kind(d) == crate::emit::decl_kind(&new))
            .cloned();
        if old.as_ref() == Some(&new) || old.is_none() {
            return Err(format!("erratum {} does not apply", e.issue));
        }
        cur = cur.iter().map(|d| replace_def(&new, d)).collect();
    }
    Ok(cur)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_a_command() {
        let src = "x\nspectec_erratum 654 in Specs.wasm30 on \"Bi32\"\n  because \"a\" \"b\"\n  replacing \"(var \\\"uN\\\"\" \" x\"\n  with \"y\"\n  as erratum654Bi32\n\nnext";
        let e = extract(src).unwrap();
        assert_eq!(e.len(), 1);
        assert_eq!(e[0].issue, 654);
        assert_eq!(e[0].script, "Specs.wasm30");
        assert_eq!(e[0].replacing, "(var \"uN\" x");
        assert_eq!(e[0].with, "y");
        assert_eq!(e[0].name.as_deref(), Some("erratum654Bi32"));
    }
}
