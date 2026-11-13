//! A reader for the canonical Core documents the Lean probe prints, and the queries the tool
//! needs: a procedure's parameters, its statements by source line (as `CompilesTo.stmtsAt`
//! finds them), its local objects and its return label (`CompilesTo.returnSaves`).
//!
//! The Lean header recomputes every one of these facts (`StmtAt`, `RetAt`, `ElaboratesFn`);
//! a disagreement makes a generated proof fail, not a goal unsound.

use anyhow::{Result, anyhow, bail};

/// An S-expression: an atom (including `$str` payloads, kept with their quotes stripped) or a
/// list.
#[derive(Clone, Debug, PartialEq)]
pub enum Sx {
    Atom(String),
    Str(String),
    List(Vec<Sx>),
}

impl Sx {
    pub fn head(&self) -> Option<&str> {
        match self {
            Sx::List(xs) => match xs.first() {
                Some(Sx::Atom(a)) => Some(a),
                _ => None,
            },
            _ => None,
        }
    }
    pub fn args(&self) -> &[Sx] {
        match self {
            Sx::List(xs) if !xs.is_empty() => &xs[1..],
            _ => &[],
        }
    }
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sx::Atom(a) => Some(a),
            _ => None,
        }
    }
    /// `($str "…")` → the string.
    pub fn str_payload(&self) -> Option<&str> {
        if self.head() == Some("$str") {
            match self.args().first() {
                Some(Sx::Str(s)) => Some(s),
                _ => None,
            }
        } else {
            None
        }
    }
    /// `($list …)` → the items.
    pub fn list_items(&self) -> Option<&[Sx]> {
        (self.head() == Some("$list")).then(|| self.args())
    }
}

pub fn parse(text: &str) -> Result<Sx> {
    let bytes = text.as_bytes();
    let mut pos = 0;
    let sx = parse_at(bytes, &mut pos)?;
    Ok(sx)
}

fn skip_ws(b: &[u8], pos: &mut usize) {
    while *pos < b.len() && (b[*pos] as char).is_whitespace() {
        *pos += 1;
    }
}

fn parse_at(b: &[u8], pos: &mut usize) -> Result<Sx> {
    skip_ws(b, pos);
    if *pos >= b.len() {
        bail!("unexpected end of document");
    }
    match b[*pos] {
        b'(' => {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                skip_ws(b, pos);
                if *pos >= b.len() {
                    bail!("unterminated list");
                }
                if b[*pos] == b')' {
                    *pos += 1;
                    return Ok(Sx::List(items));
                }
                items.push(parse_at(b, pos)?);
            }
        }
        b'"' => {
            *pos += 1;
            let mut s = Vec::new();
            while *pos < b.len() && b[*pos] != b'"' {
                if b[*pos] == b'\\' && *pos + 1 < b.len() {
                    *pos += 1;
                }
                s.push(b[*pos]);
                *pos += 1;
            }
            *pos += 1;
            Ok(Sx::Str(String::from_utf8_lossy(&s).into_owned()))
        }
        _ => {
            let start = *pos;
            while *pos < b.len()
                && !(b[*pos] as char).is_whitespace()
                && b[*pos] != b'('
                && b[*pos] != b')'
            {
                *pos += 1;
            }
            Ok(Sx::Atom(
                String::from_utf8_lossy(&b[start..*pos]).into_owned(),
            ))
        }
    }
}

/// A Core symbol: digest (hex), number, description.
#[derive(Clone, Debug, PartialEq)]
pub struct Sym {
    pub digest: String,
    pub number: u64,
    /// `(kind, name)`, e.g. `("SD_ObjectAddress", "s")`; `("SD_None", "")`.
    pub desc: (String, String),
}

pub fn sym(sx: &Sx) -> Option<Sym> {
    if sx.head() != Some("Symbol") {
        return None;
    }
    let a = sx.args();
    let digest = a.first()?.str_payload()?.to_string();
    let number = a.get(1)?.atom()?.parse().ok()?;
    let d = a.get(2)?;
    let kind = d.head()?.to_string();
    let name = d
        .args()
        .first()
        .and_then(|x| x.str_payload())
        .unwrap_or("")
        .to_string();
    Some(Sym {
        digest,
        number,
        desc: (kind, name),
    })
}

impl Sym {
    /// The Lean term of the symbol.
    pub fn lean(&self) -> String {
        let bytes: Vec<String> = (0..self.digest.len() / 2)
            .map(|i| format!("0x{}", &self.digest[2 * i..2 * i + 2]))
            .collect();
        let desc = match self.desc.0.as_str() {
            "SD_None" => ".none".to_string(),
            "SD_Id" => format!(".id {:?}", self.desc.1),
            "SD_ObjectAddress" => format!(".objectAddress {:?}", self.desc.1),
            "SD_Return" => ".return_".to_string(),
            "SD_FunArgValue" => format!(".funArgValue {:?}", self.desc.1),
            other => format!(
                "(.id {:?}) /- unsupported description {other} -/",
                self.desc.1
            ),
        };
        format!("⟨⟨[{}]⟩, {}, {}⟩", bytes.join(", "), self.number, desc)
    }
}

/// A located Core statement.
#[derive(Clone, Debug)]
pub struct Stmt {
    pub first_line: i64,
    #[allow(dead_code)]
    pub last_line: i64,
    pub node: String,
}

/// What the tool needs to know about one elaborated procedure.
#[derive(Clone, Debug)]
pub struct Proc {
    #[allow(dead_code)]
    pub sym: Sym,
    pub params: Vec<Sym>,
    pub stmts: Vec<Stmt>,
    /// Objects bound by patterns (`SD_ObjectAddress`) anywhere in the body.
    pub locals: Vec<Sym>,
    /// The return labels: (label, params).
    pub returns: Vec<(Sym, Vec<Sym>)>,
    /// Constructs whose presence the tool reports (calls, runs other than return).
    pub nodes: Vec<String>,
}

/// The Core document's procedure named `name`.
pub fn procedure(doc: &Sx, name: &str) -> Result<Proc> {
    // ($document 1 commit impl (generic_file main cc tagDefs stdlib impl globs funs …))
    let file = doc
        .args()
        .get(3)
        .ok_or_else(|| anyhow!("document without a file"))?;
    let funs = file
        .args()
        .get(6)
        .ok_or_else(|| anyhow!("file without procedures"))?;
    for entry in funs.args() {
        let [s, decl] = entry.args() else { continue };
        let Some(s) = sym(s) else { continue };
        if s.desc != ("SD_Id".to_string(), name.to_string()) {
            continue;
        }
        if decl.head() != Some("Proc") {
            bail!("{name} is not a procedure with a body");
        }
        let a = decl.args();
        let params = a
            .get(3)
            .and_then(|l| l.list_items())
            .ok_or_else(|| anyhow!("{name}: no parameter list"))?
            .iter()
            .filter_map(|t| t.args().first().and_then(sym))
            .collect();
        let body = a.get(4).ok_or_else(|| anyhow!("{name}: no body"))?;
        let mut p = Proc {
            sym: s,
            params,
            stmts: vec![],
            locals: vec![],
            returns: vec![],
            nodes: vec![],
        };
        walk_expr(body, &mut p);
        return Ok(p);
    }
    bail!("the Core document has no procedure {name}")
}

fn loc_lines(annots: &[Sx]) -> Option<(i64, i64)> {
    // the first Aloc, as `exprLoc` reads it
    for a in annots {
        if a.head() == Some("Aloc") {
            let l = a.args().first()?;
            return match l.head() {
                Some("$loc_region") => {
                    let x = l.args();
                    Some((
                        x.get(1)?.atom()?.parse().ok()?,
                        x.get(4)?.atom()?.parse().ok()?,
                    ))
                }
                Some("$loc_point") => {
                    let x = l.args();
                    let line = x.get(1)?.atom()?.parse().ok()?;
                    Some((line, line))
                }
                _ => None,
            };
        }
    }
    None
}

fn pattern_syms(p: &Sx, out: &mut Vec<Sym>) {
    if let Some(s) = sym(p) {
        if s.desc.0 == "SD_ObjectAddress" {
            out.push(s);
        }
        return;
    }
    if let Sx::List(xs) = p {
        for x in xs {
            pattern_syms(x, out);
        }
    }
}

/// Mirrors `CompilesTo.subexprs`: pre-order through Esseq, Ewseq, Eif, Elet, Ebound, Esave,
/// Eannot, Ecase, Eunseq, End, Epar.
fn walk_expr(e: &Sx, p: &mut Proc) {
    if e.head() != Some("Expr") {
        return;
    }
    let [annots, node] = e.args() else { return };
    let annots = annots.list_items().unwrap_or(&[]);
    let tag = node.head().unwrap_or("").to_string();
    let is_stmt = annots.iter().any(|a| a.head() == Some("Astmt"));
    if is_stmt && let Some((first, last)) = loc_lines(annots) {
        p.stmts.push(Stmt {
            first_line: first,
            last_line: last,
            node: tag.clone(),
        });
    }
    p.nodes.push(tag.clone());
    let n = node.args();
    match tag.as_str() {
        "Esseq" | "Ewseq" => {
            if let Some(pat) = n.first() {
                pattern_syms(pat, &mut p.locals);
            }
            walk_expr(&n[1], p);
            walk_expr(&n[2], p);
        }
        "Eif" => {
            walk_expr(&n[1], p);
            walk_expr(&n[2], p);
        }
        "Elet" => {
            pattern_syms(&n[0], &mut p.locals);
            walk_expr(&n[2], p);
        }
        "Ebound" => walk_expr(&n[0], p),
        "Eannot" => walk_expr(&n[1], p),
        "Esave" => {
            let is_ret = annots.iter().any(|a| {
                a.head() == Some("Alabel")
                    && a.args().first().and_then(|x| x.head()) == Some("LAreturn")
            });
            if is_ret {
                let label = n[0].args().first().and_then(sym);
                let ps = n[1]
                    .list_items()
                    .unwrap_or(&[])
                    .iter()
                    .filter_map(|t| t.args().first().and_then(sym))
                    .collect();
                if let Some(l) = label {
                    p.returns.push((l, ps));
                }
            }
            walk_expr(&n[2], p);
        }
        "Ecase" => {
            for arm in n[1].list_items().unwrap_or(&[]) {
                if let [pat, body] = arm.args() {
                    pattern_syms(pat, &mut p.locals);
                    walk_expr(body, p);
                }
            }
        }
        "Eunseq" | "End" | "Epar" => {
            for x in n[0].list_items().unwrap_or(&[]) {
                walk_expr(x, p);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A probe output for `int add3(int a, int b, int c) { int s = a + b; int t = s + c;
    /// return t; }` (lines 2 to 7), its Core document cut down to what [`procedure`] reads: the
    /// parameters, the located statements (the block from line 3, then lines 4, 5 and 6), the
    /// objects the patterns bind and the return label.
    const ADD3: &str = r#"BEGIN-CORE-DOCUMENT
($document 1 ($str "test") ($str "test")
 (generic_file ($none) (Normal_callconv) ($map) ($map) ($map) ($list) ($map ($tuple (Symbol ($str "00") 4 (SD_Id ($str "add3")))
  (Proc ($loc_region ($str "") 2 1 ($str "") 7 2) ($some 5) (BTy_loaded (OTy_integer))
   ($list
    ($tuple (Symbol ($str "00") 1 (SD_ObjectAddress ($str "a"))) (BTy_object (OTy_pointer)))
    ($tuple (Symbol ($str "00") 2 (SD_ObjectAddress ($str "b"))) (BTy_object (OTy_pointer)))
    ($tuple (Symbol ($str "00") 3 (SD_ObjectAddress ($str "c"))) (BTy_object (OTy_pointer))))
   (Expr ($list) (Esseq
    (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit))))
    (Expr ($list (Aloc ($loc_region ($str "") 3 1 ($str "") 7 2)) (Astmt)) (Esseq
     (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str "00") 6 (SD_ObjectAddress ($str "s")))) (BTy_object (OTy_pointer)))))
     (Expr ($list) (Eaction))
     (Expr ($list) (Esseq
      (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str "00") 7 (SD_ObjectAddress ($str "t")))) (BTy_object (OTy_pointer)))))
      (Expr ($list) (Eaction))
      (Expr ($list) (Esseq
       (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit))))
       (Expr ($list (Aloc ($loc_region ($str "") 4 3 ($str "") 4 17)) (Astmt)) (Epure))
       (Expr ($list) (Esseq
        (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit))))
        (Expr ($list (Aloc ($loc_region ($str "") 5 3 ($str "") 5 17)) (Astmt)) (Epure))
        (Expr ($list (Aloc ($loc_region ($str "") 6 3 ($str "") 6 12)) (Astmt)) (Erun))))))))))
    (Expr ($list (Alabel (LAreturn)) (Aloc ($loc_region ($str "") 2 1 ($str "") 7 2))) (Esave
     ($tuple (Symbol ($str "00") 8 (SD_Id ($str "ret_8"))) (BTy_loaded (OTy_integer)))
     ($list
      ($tuple (Symbol ($str "00") 9 (SD_None)) (BTy_loaded (OTy_integer))))
     (Expr ($list) (Epure))))))))) ($map) ($map) ($map) ($map)))
END-CORE-DOCUMENT"#;

    #[test]
    fn straight_add3_statements() {
        let raw = ADD3;
        let i = raw.find("BEGIN-CORE-DOCUMENT\n").unwrap() + "BEGIN-CORE-DOCUMENT\n".len();
        let j = raw.find("END-CORE-DOCUMENT").unwrap();
        let doc = parse(&raw[i..j]).unwrap();
        let p = procedure(&doc, "add3").unwrap();
        let lines: Vec<i64> = p.stmts.iter().map(|s| s.first_line).collect();
        assert_eq!(lines, vec![3, 4, 5, 6]); // the block (from `{`) and its three statements
        assert_eq!(p.params.len(), 3);
        assert_eq!(p.returns.len(), 1);
        assert_eq!(p.returns[0].1.len(), 1);
        assert_eq!(p.sym.lean(), "⟨⟨[0x00]⟩, 4, .id \"add3\"⟩");
        assert!(
            p.locals.iter().any(|s| s.desc.1 == "s") && p.locals.iter().any(|s| s.desc.1 == "t")
        );
    }
}
