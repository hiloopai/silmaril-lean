//! S-expressions to Lean source for `Silmaril.SpecTec.IL` terms.
//!
//! This is a transcription of `IL.decodeDef?` (`Silmaril/Raw/Wasm/SpecTec/SpecTec/IL/Decode.lean`)
//! whose output is Lean source instead of a value, written so that the elaborated term is the
//! one `qDef` (`Import.lean`) reflects: the same constructors in the same argument order, raw
//! `Nat` numerals at type `Nat`, `Int` numerals at type `Int`, and string literals.  Generated
//! files `open Silmaril.SpecTec.IL`, so constructors are written `Exp.caseE …`: namespace-qualified,
//! never dot notation.

use crate::sexp::SExp;

type R = Result<String, String>;

fn err<T>(what: &str, e: &SExp) -> Result<T, String> {
    let mut s = crate::sexp::render(crate::sexp::WIDE_WIDTH, e);
    if s.len() > 200 {
        s.truncate(200);
        s.push('…');
    }
    Err(format!("not a printed {what}: {s}"))
}

fn app(ctor: &str, args: &[String]) -> String {
    let mut s = String::from("(");
    s.push_str(ctor);
    for a in args {
        s.push(' ');
        s.push_str(a);
    }
    s.push(')');
    s
}

/// A list term.  Lean's `[…]` notation elaborates long literals through `have` bindings, which
/// `qDef` does not produce, so long lists are written with `::` instead.
pub fn list(items: Vec<String>) -> String {
    if items.len() < LONG_LIST {
        format!("[{}]", items.join(", "))
    } else {
        format!("({} :: [])", items.join(" :: "))
    }
}

/// Lists at least this long are written with `::`.
pub const LONG_LIST: usize = 16;

/// A Lean string literal denoting `s`.
pub fn lean_str(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            '\r' => o.push_str("\\r"),
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                o.push_str(&format!("\\x{:02x}", c as u32))
            }
            c if (c as u32) > 0x7e => o.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// `Escape.unquote?`: an OCaml-`String.escaped` quoted atom to its text.
pub fn unquote(atom: &str) -> Option<String> {
    let body = atom.strip_prefix('"')?.strip_suffix('"')?;
    let b = body.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'\\' {
            let e = *b.get(i + 1)?;
            let byte = match e {
                b'"' => 34,
                b'\\' => 92,
                b'n' => 10,
                b't' => 9,
                b'r' => 13,
                b'b' => 8,
                _ => {
                    let d = b.get(i + 1..i + 4)?;
                    if !d.iter().all(u8::is_ascii_digit) {
                        return None;
                    }
                    let n = (d[0] - b'0') as u32 * 100
                        + (d[1] - b'0') as u32 * 10
                        + (d[2] - b'0') as u32;
                    let named = matches!(n, 34 | 92 | 10 | 9 | 13 | 8);
                    if n >= 256 || named || (32..=126).contains(&n) {
                        return None;
                    }
                    i += 4;
                    out.push(n as u8);
                    continue;
                }
            };
            out.push(byte);
            i += 2;
        } else if (32..=126).contains(&c) && c != b'"' && c != b'\\' {
            out.push(c);
            i += 1;
        } else {
            return None;
        }
    }
    String::from_utf8(out).ok()
}

fn text(e: &SExp) -> R {
    match e {
        SExp::Atom(a) => unquote(a)
            .map(|s| lean_str(&s))
            .ok_or_else(|| format!("bad text atom {a}")),
        _ => err("text", e),
    }
}

fn atom_is(e: &SExp) -> Option<&str> {
    match e {
        SExp::Atom(a) => Some(a),
        _ => None,
    }
}

fn node(e: &SExp) -> Option<(&str, &[SExp])> {
    match e {
        SExp::Node(t, k) => Some((t, k)),
        _ => None,
    }
}

/// `Digits.parseDec?`: canonical decimal, returned as its digits.
fn dec(s: &str) -> Option<&str> {
    let ok =
        !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) && (s == "0" || !s.starts_with('0'));
    ok.then_some(s)
}

fn num(e: &SExp) -> R {
    let Some((tag, [SExp::Atom(s)])) = node(e) else {
        return err("num", e);
    };
    match tag {
        "nat" => dec(s)
            .map(|d| app("Num.natN", &[d.to_string()]))
            .ok_or_else(|| format!("bad nat {s}")),
        "int" => {
            let (sign, digits) = s.split_at(1.min(s.len()));
            let d = dec(digits).ok_or_else(|| format!("bad int {s}"))?;
            match sign {
                "+" => Ok(app("Num.intN", &[format!("({d} : Int)")])),
                "-" if d != "0" => Ok(app("Num.intN", &[format!("(-{d} : Int)")])),
                _ => Err(format!("bad int {s}")),
            }
        }
        "real" => Ok(app("Num.realN", &[lean_str(s)])),
        _ => Err(format!(
            "unsupported num {tag} {s} (rationals are not emitted)"
        )),
    }
}

fn enum_atom(e: &SExp, table: &[(&str, &str)], what: &str) -> R {
    if let Some(a) = atom_is(e) {
        for (k, v) in table {
            if *k == a {
                return Ok((*v).to_string());
            }
        }
    }
    err(what, e)
}

const NUMTYP: &[(&str, &str)] = &[
    ("nat", "NumTyp.natT"),
    ("int", "NumTyp.intT"),
    ("rat", "NumTyp.ratT"),
    ("real", "NumTyp.realT"),
];

fn num_typ(e: &SExp) -> R {
    enum_atom(e, NUMTYP, "numtyp")
}

fn op_typ(e: &SExp) -> R {
    if atom_is(e) == Some("bool") {
        return Ok("OpTyp.boolT".into());
    }
    Ok(app("OpTyp.numT", &[num_typ(e)?]))
}

fn many(es: &[SExp], f: fn(&SExp) -> R) -> R {
    Ok(list(es.iter().map(f).collect::<Result<_, _>>()?))
}

fn iter(e: &SExp) -> R {
    match e {
        SExp::Atom(a) if a == "opt" => Ok("Iter.opt".into()),
        SExp::Atom(a) if a == "list" => Ok("Iter.list".into()),
        SExp::Atom(a) if a == "list1" => Ok("Iter.list1".into()),
        SExp::Node(t, k) if t == "listn" => match k.as_slice() {
            // `qIter` reflects the optional name at type `String`, not `Id`.
            [e] => Ok(app(
                "Iter.listN",
                &[exp(e)?, "(@Option.none String)".into()],
            )),
            [e, x] => Ok(app(
                "Iter.listN",
                &[exp(e)?, format!("(@Option.some String {})", text(x)?)],
            )),
            _ => err("iter", e),
        },
        _ => err("iter", e),
    }
}

fn iter_exp(ks: &[SExp]) -> R {
    let [it, ds @ ..] = ks else {
        return Err("empty iterexp".into());
    };
    Ok(app("IterExp.mk", &[iter(it)?, many(ds, dom)?]))
}

fn dom(e: &SExp) -> R {
    match node(e) {
        Some(("dom", [x, e])) => Ok(app("Dom.mk", &[text(x)?, exp(e)?])),
        _ => err("dom", e),
    }
}

fn typ(e: &SExp) -> R {
    match e {
        SExp::Atom(a) => match a.as_str() {
            "bool" => Ok("Typ.boolT".into()),
            "text" => Ok("Typ.textT".into()),
            "nat" | "int" | "rat" | "real" => Ok(app("Typ.numT", &[num_typ(e)?])),
            _ => err("typ", e),
        },
        SExp::Node(t, k) => match (t.as_str(), k.as_slice()) {
            ("var", [x, args @ ..]) => Ok(app("Typ.varT", &[text(x)?, many(args, arg)?])),
            ("tup", bs) => Ok(app("Typ.tupT", &[many(bs, typ_bind)?])),
            ("iter", [t, it]) => Ok(app("Typ.iterT", &[typ(t)?, iter(it)?])),
            _ => err("typ", e),
        },
    }
}

fn typ_bind(e: &SExp) -> R {
    match node(e) {
        Some(("bind", [x, t])) => Ok(app("TypBind.mk", &[text(x)?, typ(t)?])),
        _ => err("bind", e),
    }
}

fn def_typ(e: &SExp) -> R {
    match node(e) {
        Some(("alias", [t])) => Ok(app("DefTyp.aliasT", &[typ(t)?])),
        Some(("struct", fs)) => Ok(app("DefTyp.structT", &[many(fs, typ_field)?])),
        Some(("variant", cs)) => Ok(app("DefTyp.variantT", &[many(cs, typ_case)?])),
        _ => err("deftyp", e),
    }
}

fn field_or_case(e: &SExp, tag: &str, ctor: &str) -> R {
    match node(e) {
        Some((t, [a, ty, rest @ ..])) if t == tag => {
            let (ps, args, tail) = params_rest(rest)?;
            if !args.is_empty() {
                return err(tag, e);
            }
            Ok(app(
                ctor,
                &[text(a)?, typ(ty)?, list(ps), many(tail, prem)?],
            ))
        }
        _ => err(tag, e),
    }
}

fn typ_field(e: &SExp) -> R {
    field_or_case(e, "field", "TypField.mk")
}

fn typ_case(e: &SExp) -> R {
    field_or_case(e, "case", "TypCase.mk")
}

fn exp(e: &SExp) -> R {
    let Some((t, k)) = node(e) else {
        return err("exp", e);
    };
    let a = |c: &str, xs: Vec<String>| Ok(app(c, &xs));
    match (t, k) {
        ("var", [x]) => a("Exp.varE", vec![text(x)?]),
        ("bool", [b]) => match atom_is(b) {
            Some("true") => a("Exp.boolE", vec!["true".into()]),
            Some("false") => a("Exp.boolE", vec!["false".into()]),
            _ => err("bool", b),
        },
        ("num", [n]) => a("Exp.numE", vec![num(n)?]),
        ("text", [x]) => a("Exp.textE", vec![text(x)?]),
        ("un", [op, ty, e1]) => a(
            "Exp.unE",
            vec![
                enum_atom(
                    op,
                    &[
                        ("not", "UnOp.notOp"),
                        ("plus", "UnOp.plusOp"),
                        ("minus", "UnOp.minusOp"),
                    ],
                    "unop",
                )?,
                op_typ(ty)?,
                exp(e1)?,
            ],
        ),
        ("bin", [op, ty, e1, e2]) => a(
            "Exp.binE",
            vec![bin_op(op)?, op_typ(ty)?, exp(e1)?, exp(e2)?],
        ),
        ("cmp", [op, ty, e1, e2]) => a(
            "Exp.cmpE",
            vec![cmp_op(op)?, op_typ(ty)?, exp(e1)?, exp(e2)?],
        ),
        ("idx", [e1, e2]) => a("Exp.idxE", vec![exp(e1)?, exp(e2)?]),
        ("slice", [e1, e2, e3]) => a("Exp.sliceE", vec![exp(e1)?, exp(e2)?, exp(e3)?]),
        ("upd", [e1, p, e2]) => a("Exp.updE", vec![exp(e1)?, path(p)?, exp(e2)?]),
        ("ext", [e1, p, e2]) => a("Exp.extE", vec![exp(e1)?, path(p)?, exp(e2)?]),
        ("struct", fs) => a("Exp.strE", vec![many(fs, exp_field)?]),
        ("dot", [e1, x]) => a("Exp.dotE", vec![exp(e1)?, text(x)?]),
        ("comp", [e1, e2]) => a("Exp.compE", vec![exp(e1)?, exp(e2)?]),
        ("mem", [e1, e2]) => a("Exp.memE", vec![exp(e1)?, exp(e2)?]),
        ("len", [e1]) => a("Exp.lenE", vec![exp(e1)?]),
        ("tup", es) => a("Exp.tupE", vec![many(es, exp)?]),
        ("call", [x, args @ ..]) => a("Exp.callE", vec![text(x)?, many(args, arg)?]),
        ("iter", [e1, rest @ ..]) => a("Exp.iterE", vec![exp(e1)?, iter_exp(rest)?]),
        ("proj", [e1, SExp::Atom(i)]) => {
            let int = if let Some(d) = i.strip_prefix('-') {
                dec(d)
                    .filter(|d| *d != "0")
                    .map(|d| format!("(-{d} : Int)"))
            } else {
                dec(i).map(|d| format!("({d} : Int)"))
            };
            a(
                "Exp.projE",
                vec![exp(e1)?, int.ok_or_else(|| format!("bad proj index {i}"))?],
            )
        }
        ("case", [op, e1]) => a("Exp.caseE", vec![text(op)?, exp(e1)?]),
        ("uncase", [e1, op]) => a("Exp.uncaseE", vec![exp(e1)?, text(op)?]),
        ("opt", []) => a("Exp.optE", vec!["none".into()]),
        ("opt", [e1]) => a("Exp.optE", vec![format!("(some {})", exp(e1)?)]),
        ("unopt", [e1]) => a("Exp.theE", vec![exp(e1)?]),
        ("list", es) => a("Exp.listE", vec![many(es, exp)?]),
        ("lift", [e1]) => a("Exp.liftE", vec![exp(e1)?]),
        ("cat", [e1, e2]) => a("Exp.catE", vec![exp(e1)?, exp(e2)?]),
        ("cvt", [t1, t2, e1]) => a("Exp.cvtE", vec![exp(e1)?, num_typ(t1)?, num_typ(t2)?]),
        ("sub", [t1, t2, e1]) => a("Exp.subE", vec![exp(e1)?, typ(t1)?, typ(t2)?]),
        _ => err("exp", e),
    }
}

fn bin_op(e: &SExp) -> R {
    enum_atom(
        e,
        &[
            ("and", "BinOp.andOp"),
            ("or", "BinOp.orOp"),
            ("impl", "BinOp.implOp"),
            ("equiv", "BinOp.equivOp"),
            ("add", "BinOp.addOp"),
            ("sub", "BinOp.subOp"),
            ("mul", "BinOp.mulOp"),
            ("div", "BinOp.divOp"),
            ("mod", "BinOp.modOp"),
            ("pow", "BinOp.powOp"),
        ],
        "binop",
    )
}

fn cmp_op(e: &SExp) -> R {
    enum_atom(
        e,
        &[
            ("eq", "CmpOp.eqOp"),
            ("ne", "CmpOp.neOp"),
            ("lt", "CmpOp.ltOp"),
            ("gt", "CmpOp.gtOp"),
            ("le", "CmpOp.leOp"),
            ("ge", "CmpOp.geOp"),
        ],
        "cmpop",
    )
}

fn exp_field(e: &SExp) -> R {
    match node(e) {
        Some(("field", [x, e1])) => Ok(app("ExpField.mk", &[text(x)?, exp(e1)?])),
        _ => err("expfield", e),
    }
}

fn path(e: &SExp) -> R {
    match e {
        SExp::Atom(a) if a == "root" => Ok("Path.rootP".into()),
        SExp::Node(t, k) => match (t.as_str(), k.as_slice()) {
            ("idx", [p, e1]) => Ok(app("Path.idxP", &[path(p)?, exp(e1)?])),
            ("slice", [p, e1, e2]) => Ok(app("Path.sliceP", &[path(p)?, exp(e1)?, exp(e2)?])),
            ("dot", [p, x]) => Ok(app("Path.dotP", &[path(p)?, text(x)?])),
            _ => err("path", e),
        },
        _ => err("path", e),
    }
}

/// `Digits.parseHexByteString?`: exactly `Printf.sprintf "0x%02X"`.
fn hex_byte(s: &str) -> Option<String> {
    let h = s.strip_prefix("0x")?;
    if h.is_empty()
        || h.len() > 16
        || !h
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'A'..=b'F').contains(&b))
    {
        return None;
    }
    let n = u64::from_str_radix(h, 16).ok()?;
    (format!("0x{n:02X}") == s).then(|| n.to_string())
}

fn sym(e: &SExp) -> R {
    match e {
        SExp::Atom(a) if a == "eps" => Ok("Sym.epsG".into()),
        SExp::Node(t, k) => match (t.as_str(), k.as_slice()) {
            ("var", [x, args @ ..]) => Ok(app("Sym.varG", &[text(x)?, many(args, arg)?])),
            ("num", [SExp::Atom(n)]) => Ok(app(
                "Sym.numG",
                &[hex_byte(n).ok_or_else(|| format!("bad grammar numeral {n}"))?],
            )),
            ("text", [x]) => Ok(app("Sym.textG", &[text(x)?])),
            ("seq", gs) => Ok(app("Sym.seqG", &[many(gs, sym)?])),
            ("alt", gs) => Ok(app("Sym.altG", &[many(gs, sym)?])),
            ("range", [g1, g2]) => Ok(app("Sym.rangeG", &[sym(g1)?, sym(g2)?])),
            ("iter", [g, rest @ ..]) => Ok(app("Sym.iterG", &[sym(g)?, iter_exp(rest)?])),
            ("attr", [e1, g]) => Ok(app("Sym.attrG", &[exp(e1)?, sym(g)?])),
            _ => err("sym", e),
        },
        _ => err("sym", e),
    }
}

fn prem(e: &SExp) -> R {
    match e {
        SExp::Atom(a) if a == "else" => Ok("Prem.elsePr".into()),
        SExp::Node(t, k) => match (t.as_str(), k.as_slice()) {
            ("rule", [x, rest @ ..]) => {
                let (args, tail) = args_rest(rest)?;
                match tail {
                    [op, e1] => Ok(app(
                        "Prem.rulePr",
                        &[text(x)?, list(args), text(op)?, exp(e1)?],
                    )),
                    _ => err("rule premise", e),
                }
            }
            ("if", [e1]) => Ok(app("Prem.ifPr", &[exp(e1)?])),
            ("let", [e1, e2]) => Ok(app("Prem.letPr", &[exp(e1)?, exp(e2)?])),
            ("iter", [p, rest @ ..]) => Ok(app("Prem.iterPr", &[prem(p)?, iter_exp(rest)?])),
            _ => err("prem", e),
        },
        _ => err("prem", e),
    }
}

fn arg(e: &SExp) -> R {
    match node(e) {
        Some(("exp", [x])) => Ok(app("Arg.expA", &[exp(x)?])),
        Some(("typ", [x])) => Ok(app("Arg.typA", &[typ(x)?])),
        Some(("def", [x])) => Ok(app("Arg.defA", &[text(x)?])),
        Some(("gram", [x])) => Ok(app("Arg.gramA", &[sym(x)?])),
        _ => err("arg", e),
    }
}

fn is_pa_tag(e: &SExp) -> bool {
    matches!(node(e), Some(("exp" | "typ" | "def" | "gram", _)))
}

fn is_param_shaped(e: &SExp) -> bool {
    match node(e) {
        Some(("exp", ks)) => ks.len() == 2,
        Some(("typ", [k])) => matches!(k, SExp::Atom(a) if unquote(a).is_some()),
        Some(("def" | "gram", ks)) => ks.len() >= 2,
        _ => false,
    }
}

fn args_rest(ks: &[SExp]) -> Result<(Vec<String>, &[SExp]), String> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < ks.len() && is_pa_tag(&ks[i]) {
        out.push(arg(&ks[i])?);
        i += 1;
    }
    Ok((out, &ks[i..]))
}

type ParamsRest<'a> = (Vec<String>, Vec<String>, &'a [SExp]);

fn params_rest(ks: &[SExp]) -> Result<ParamsRest<'_>, String> {
    let mut ps = Vec::new();
    let mut i = 0;
    while i < ks.len() && is_param_shaped(&ks[i]) {
        ps.push(param(&ks[i])?);
        i += 1;
    }
    let (args, rest) = args_rest(&ks[i..])?;
    Ok((ps, args, rest))
}

fn param(e: &SExp) -> R {
    match node(e) {
        Some(("exp", [x, t])) => Ok(app("Param.expP", &[text(x)?, typ(t)?])),
        Some(("typ", [x])) => Ok(app("Param.typP", &[text(x)?])),
        Some((tag @ ("def" | "gram"), [x, rest @ ..])) => {
            let (ps, args, tail) = params_rest(rest)?;
            match (args.is_empty(), tail) {
                (true, [t]) => {
                    let c = if tag == "def" {
                        "Param.defP"
                    } else {
                        "Param.gramP"
                    };
                    Ok(app(c, &[text(x)?, list(ps), typ(t)?]))
                }
                _ => err("param", e),
            }
        }
        _ => err("param", e),
    }
}

fn inst(e: &SExp) -> R {
    match node(e) {
        Some(("inst", ks)) => {
            let (ps, args, tail) = params_rest(ks)?;
            match tail {
                [dt] => Ok(app("Inst.instD", &[list(ps), list(args), def_typ(dt)?])),
                _ => err("inst", e),
            }
        }
        _ => err("inst", e),
    }
}

fn rule(e: &SExp) -> R {
    match node(e) {
        Some(("rule", [x, ks @ ..])) => {
            let (ps, args, tail) = params_rest(ks)?;
            match (args.is_empty(), tail) {
                (true, [op, e1, prems @ ..]) => Ok(app(
                    "Rule.ruleD",
                    &[text(x)?, list(ps), text(op)?, exp(e1)?, many(prems, prem)?],
                )),
                _ => err("rule", e),
            }
        }
        _ => err("rule", e),
    }
}

fn clause(e: &SExp) -> R {
    match node(e) {
        Some(("clause", ks)) => {
            let (ps, args, tail) = params_rest(ks)?;
            match tail {
                [e1, prems @ ..] => Ok(app(
                    "Clause.defD",
                    &[list(ps), list(args), exp(e1)?, many(prems, prem)?],
                )),
                _ => err("clause", e),
            }
        }
        _ => err("clause", e),
    }
}

fn prod(e: &SExp) -> R {
    match node(e) {
        Some(("prod", ks)) => {
            let (ps, args, tail) = params_rest(ks)?;
            match (args.is_empty(), tail) {
                (true, [g, e1, prems @ ..]) => Ok(app(
                    "Prod.prodD",
                    &[list(ps), sym(g)?, exp(e1)?, many(prems, prem)?],
                )),
                _ => err("prod", e),
            }
        }
        _ => err("prod", e),
    }
}

/// `IL.decodeDef?`, emitting the Lean term `qDef` would build.
pub fn def(e: &SExp) -> R {
    let Some((t, k)) = node(e) else {
        return err("def", e);
    };
    if t == "rec" {
        return Ok(app("Def.recD", &[many(k, def)?]));
    }
    let [x, ks @ ..] = k else {
        return err("def", e);
    };
    let (ps, args, tail) = params_rest(ks)?;
    if !args.is_empty() {
        return err("def", e);
    }
    match (t, tail) {
        ("typ", insts) => Ok(app("Def.typD", &[text(x)?, list(ps), many(insts, inst)?])),
        ("rel", [op, ty, rules @ ..]) => Ok(app(
            "Def.relD",
            &[text(x)?, list(ps), text(op)?, typ(ty)?, many(rules, rule)?],
        )),
        ("def", [ty, clauses @ ..]) => Ok(app(
            "Def.decD",
            &[text(x)?, list(ps), typ(ty)?, many(clauses, clause)?],
        )),
        ("gram", [ty, prods @ ..]) => Ok(app(
            "Def.gramD",
            &[text(x)?, list(ps), typ(ty)?, many(prods, prod)?],
        )),
        _ => err("def", e),
    }
}

/// The `(kind, name)` a definition declares, as `IL.declKind?`; `None` for `rec`.
pub fn decl_kind(e: &SExp) -> Option<(&str, String)> {
    match node(e)? {
        (t @ ("typ" | "rel" | "def" | "gram"), [x, ..]) => Some((t, unquote(atom_is(x)?)?)),
        _ => None,
    }
}

/// Break a long single-line term into lines of about `width` columns, only at the space before
/// an opening parenthesis or bracket and never inside a string literal.
pub fn wrap(term: &str, indent: &str, width: usize) -> String {
    let mut out = String::with_capacity(term.len() + term.len() / width * (indent.len() + 1));
    let mut col = indent.len();
    out.push_str(indent);
    let b = term.as_bytes();
    let mut i = 0;
    let mut in_str = false;
    while i < b.len() {
        let c = b[i];
        if in_str {
            if c == b'\\' {
                out.push(c as char);
                out.push(b[i + 1] as char);
                i += 2;
                col += 2;
                continue;
            }
            if c == b'"' {
                in_str = false;
            }
        } else if c == b'"' {
            in_str = true;
        } else if c == b' ' && col >= width && matches!(b.get(i + 1), Some(b'(' | b'[')) {
            out.push('\n');
            out.push_str(indent);
            col = indent.len();
            i += 1;
            continue;
        }
        out.push(c as char);
        col += 1;
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexp::parse_one;

    #[test]
    fn first_definition() {
        let e = parse_one("(typ \"N\" (inst (alias nat)))").unwrap();
        assert_eq!(
            def(&e).unwrap(),
            "(Def.typD \"N\" [] [(Inst.instD [] [] (DefTyp.aliasT (Typ.numT NumTyp.natT)))])"
        );
    }

    #[test]
    fn unquote_escapes() {
        assert_eq!(unquote("\"a\\\"b\\\\c\\n\"").as_deref(), Some("a\"b\\c\n"));
        assert_eq!(unquote("\"\\195\\169\"").as_deref(), Some("é"));
        assert_eq!(unquote("\"\\065\""), None);
    }

    #[test]
    fn hex_bytes() {
        assert_eq!(hex_byte("0x7F").as_deref(), Some("127"));
        assert_eq!(hex_byte("0x10FFFF").as_deref(), Some("1114111"));
        assert_eq!(hex_byte("0x7f"), None);
        assert_eq!(hex_byte("0x007F"), None);
    }
}
