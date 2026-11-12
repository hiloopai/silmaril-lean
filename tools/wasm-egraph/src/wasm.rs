//! A minimal Wasm binary reader and writer for straight-line integer functions:
//! `local.get`, `local.set`, `local.tee`, `drop`, `select`, `i32.const`, `i64.const`, the
//! integer test, comparison, unary and binary operators, `nop`, and the final `end`. Other
//! instructions make a function unsupported (it is reported, not proved). Untrusted I/O glue.

use crate::term::{Term, Ty, lift_flat};

pub struct Func {
    pub params: Vec<Ty>,
    pub results: Vec<Ty>,
    pub locals: Vec<Ty>,
    /// The body as flat WAT instructions, or why it is outside the fragment.
    pub body: Result<Vec<String>, String>,
}

impl Func {
    /// The types of all locals: parameters, then declared locals.
    pub fn frame(&self) -> Vec<Ty> {
        let mut v = self.params.clone();
        v.extend(&self.locals);
        v
    }

    /// The body as pass-1 terms (`nop` skipped; `local.set`, `local.tee`, `drop` and `select`
    /// are outside the term fragment).
    pub fn terms(&self) -> Result<Vec<Term>, String> {
        let body: Vec<String> = self
            .body
            .clone()?
            .into_iter()
            .filter(|s| s != "nop")
            .collect();
        lift_flat(&body.join("\n"))
    }
}

struct Reader<'a> {
    b: &'a [u8],
    p: usize,
}

impl Reader<'_> {
    fn byte(&mut self) -> Result<u8, String> {
        let x = *self.b.get(self.p).ok_or("unexpected end of module")?;
        self.p += 1;
        Ok(x)
    }
    fn uleb(&mut self) -> Result<u64, String> {
        let (mut r, mut s) = (0u64, 0);
        loop {
            let x = self.byte()?;
            r |= ((x & 0x7f) as u64) << s;
            if x & 0x80 == 0 {
                return Ok(r);
            }
            s += 7;
            if s > 63 {
                return Err("bad LEB128".into());
            }
        }
    }
    fn sleb(&mut self, bits: u32) -> Result<i64, String> {
        let (mut r, mut s) = (0i128, 0u32);
        loop {
            let x = self.byte()?;
            r |= ((x & 0x7f) as i128) << s;
            s += 7;
            if x & 0x80 == 0 {
                if s < 128 && x & 0x40 != 0 {
                    r |= -1i128 << s;
                }
                let _ = bits;
                return Ok(r as i64);
            }
            if s > 70 {
                return Err("bad LEB128".into());
            }
        }
    }
    fn ty(&mut self) -> Result<Ty, String> {
        match self.byte()? {
            0x7f => Ok(Ty::I32),
            0x7e => Ok(Ty::I64),
            t => Err(format!("unsupported value type 0x{t:02x}")),
        }
    }
}

const OPS: &[(u8, &str)] = &[
    (0x45, "i32.eqz"),
    (0x46, "i32.eq"),
    (0x47, "i32.ne"),
    (0x48, "i32.lt_s"),
    (0x49, "i32.lt_u"),
    (0x4a, "i32.gt_s"),
    (0x4b, "i32.gt_u"),
    (0x4c, "i32.le_s"),
    (0x4d, "i32.le_u"),
    (0x4e, "i32.ge_s"),
    (0x4f, "i32.ge_u"),
    (0x50, "i64.eqz"),
    (0x51, "i64.eq"),
    (0x52, "i64.ne"),
    (0x53, "i64.lt_s"),
    (0x54, "i64.lt_u"),
    (0x55, "i64.gt_s"),
    (0x56, "i64.gt_u"),
    (0x57, "i64.le_s"),
    (0x58, "i64.le_u"),
    (0x59, "i64.ge_s"),
    (0x5a, "i64.ge_u"),
    (0x67, "i32.clz"),
    (0x68, "i32.ctz"),
    (0x69, "i32.popcnt"),
    (0x6a, "i32.add"),
    (0x6b, "i32.sub"),
    (0x6c, "i32.mul"),
    (0x6d, "i32.div_s"),
    (0x6e, "i32.div_u"),
    (0x6f, "i32.rem_s"),
    (0x70, "i32.rem_u"),
    (0x71, "i32.and"),
    (0x72, "i32.or"),
    (0x73, "i32.xor"),
    (0x74, "i32.shl"),
    (0x75, "i32.shr_s"),
    (0x76, "i32.shr_u"),
    (0x77, "i32.rotl"),
    (0x78, "i32.rotr"),
    (0x79, "i64.clz"),
    (0x7a, "i64.ctz"),
    (0x7b, "i64.popcnt"),
    (0x7c, "i64.add"),
    (0x7d, "i64.sub"),
    (0x7e, "i64.mul"),
    (0x7f, "i64.div_s"),
    (0x80, "i64.div_u"),
    (0x81, "i64.rem_s"),
    (0x82, "i64.rem_u"),
    (0x83, "i64.and"),
    (0x84, "i64.or"),
    (0x85, "i64.xor"),
    (0x86, "i64.shl"),
    (0x87, "i64.shr_s"),
    (0x88, "i64.shr_u"),
    (0x89, "i64.rotl"),
    (0x8a, "i64.rotr"),
    (0xc0, "i32.extend8_s"),
    (0xc1, "i32.extend16_s"),
    (0xc2, "i64.extend8_s"),
    (0xc3, "i64.extend16_s"),
    (0xc4, "i64.extend32_s"),
];

fn body(r: &mut Reader, end: usize) -> Result<Vec<String>, String> {
    let mut out = vec![];
    while r.p < end {
        let op = r.byte()?;
        match op {
            0x0b if r.p == end => return Ok(out),
            0x01 => out.push("nop".into()),
            0x1a => out.push("drop".into()),
            0x1b => out.push("select".into()),
            0x20 => out.push(format!("local.get {}", r.uleb()?)),
            0x21 => out.push(format!("local.set {}", r.uleb()?)),
            0x22 => out.push(format!("local.tee {}", r.uleb()?)),
            0x41 => out.push(format!("i32.const {}", r.sleb(32)? as i32)),
            0x42 => out.push(format!("i64.const {}", r.sleb(64)?)),
            _ => match OPS.iter().find(|e| e.0 == op) {
                Some((_, n)) => out.push(n.to_string()),
                None => return Err(format!("unsupported opcode 0x{op:02x}")),
            },
        }
    }
    Err("body without end".into())
}

pub struct Module {
    pub funcs: Vec<Func>,
    /// Exported functions: name and function index.
    pub exports: Vec<(String, usize)>,
}

/// Read the functions and function exports of a module (imports are not supported).
pub fn read(bytes: &[u8]) -> Result<Module, String> {
    if bytes.get(0..8) != Some(&[0, 0x61, 0x73, 0x6d, 1, 0, 0, 0][..]) {
        return Err("not a Wasm 1.0 binary module".into());
    }
    let mut r = Reader { b: bytes, p: 8 };
    let mut types: Vec<(Vec<Ty>, Vec<Ty>)> = vec![];
    let mut fty: Vec<usize> = vec![];
    let mut funcs = vec![];
    let mut exports = vec![];
    while r.p < bytes.len() {
        let id = r.byte()?;
        let len = r.uleb()? as usize;
        let end = r.p + len;
        match id {
            1 => {
                for _ in 0..r.uleb()? {
                    if r.byte()? != 0x60 {
                        return Err("unsupported type form".into());
                    }
                    let np = r.uleb()?;
                    let ps = (0..np).map(|_| r.ty()).collect::<Result<_, _>>()?;
                    let nr = r.uleb()?;
                    let rs = (0..nr).map(|_| r.ty()).collect::<Result<_, _>>()?;
                    types.push((ps, rs));
                }
            }
            2 => return Err("modules with imports are not supported".into()),
            3 => {
                for _ in 0..r.uleb()? {
                    fty.push(r.uleb()? as usize);
                }
            }
            7 => {
                for _ in 0..r.uleb()? {
                    let len = r.uleb()? as usize;
                    let name =
                        String::from_utf8(r.b.get(r.p..r.p + len).ok_or("bad export")?.to_vec())
                            .map_err(|_| "bad name")?;
                    r.p += len;
                    let kind = r.byte()?;
                    let idx = r.uleb()? as usize;
                    if kind == 0 {
                        exports.push((name, idx));
                    }
                }
            }
            10 => {
                let n = r.uleb()? as usize;
                for i in 0..n {
                    let size = r.uleb()? as usize;
                    let fend = r.p + size;
                    let mut locals = vec![];
                    for _ in 0..r.uleb()? {
                        let k = r.uleb()?;
                        let t = r.ty()?;
                        locals.extend(std::iter::repeat_n(t, k as usize));
                    }
                    let (params, results) = types
                        .get(*fty.get(i).ok_or("function without type")?)
                        .cloned()
                        .ok_or("bad type index")?;
                    let b = body(&mut r, fend);
                    r.p = fend;
                    funcs.push(Func {
                        params,
                        results,
                        locals,
                        body: b,
                    });
                }
            }
            _ => {}
        }
        r.p = end;
    }
    Ok(Module { funcs, exports })
}

fn uleb(mut n: u64, out: &mut Vec<u8>) {
    loop {
        let mut b = (n & 0x7f) as u8;
        n >>= 7;
        if n != 0 {
            b |= 0x80;
        }
        out.push(b);
        if n == 0 {
            return;
        }
    }
}

fn sleb(mut v: i64, out: &mut Vec<u8>) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0) {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn section(id: u8, body: Vec<u8>, out: &mut Vec<u8>) {
    out.push(id);
    uleb(body.len() as u64, out);
    out.extend(body);
}

fn tybyte(t: Ty) -> u8 {
    match t {
        Ty::I32 => 0x7f,
        Ty::I64 => 0x7e,
    }
}

/// Encode a flat instruction.
fn instr(s: &str, out: &mut Vec<u8>) -> Result<(), String> {
    let mut w = s.split_whitespace();
    let name = w.next().unwrap_or("");
    let arg = w.next();
    match name {
        "local.get" | "local.set" | "local.tee" => {
            out.push(match name {
                "local.get" => 0x20,
                "local.set" => 0x21,
                _ => 0x22,
            });
            uleb(arg.ok_or("index")?.parse().map_err(|_| "index")?, out);
        }
        "drop" => out.push(0x1a),
        "nop" => out.push(0x01),
        "select" => out.push(0x1b),
        "i32.const" => {
            out.push(0x41);
            let v = crate::term::parse_const(Ty::I32, arg.ok_or("value")?)?;
            sleb(v as u32 as i32 as i64, out);
        }
        "i64.const" => {
            out.push(0x42);
            let v = crate::term::parse_const(Ty::I64, arg.ok_or("value")?)?;
            sleb(v as i64, out);
        }
        _ => out.push(
            OPS.iter()
                .find(|e| e.1 == name)
                .ok_or_else(|| format!("cannot encode {name}"))?
                .0,
        ),
    }
    Ok(())
}

/// A module of functions `f0`, `f1`, … (all exported), each with the given parameter
/// types, result types and flat body.
pub fn write(funcs: &[(Vec<Ty>, Vec<Ty>, Vec<String>)]) -> Result<Vec<u8>, String> {
    let with_locals: Vec<_> = funcs
        .iter()
        .map(|(p, r, b)| (p.clone(), r.clone(), vec![], b.clone()))
        .collect();
    write_locals(&with_locals)
}

/// A function to write: parameter types, result types, declared locals and flat body.
pub type FuncSpec = (Vec<Ty>, Vec<Ty>, Vec<Ty>, Vec<String>);

/// `write` with declared locals (after the parameters).
pub fn write_locals(funcs: &[FuncSpec]) -> Result<Vec<u8>, String> {
    let mut out = vec![0, 0x61, 0x73, 0x6d, 1, 0, 0, 0];
    let mut types = vec![];
    uleb(funcs.len() as u64, &mut types);
    for (ps, rs, _, _) in funcs {
        types.push(0x60);
        uleb(ps.len() as u64, &mut types);
        types.extend(ps.iter().map(|t| tybyte(*t)));
        uleb(rs.len() as u64, &mut types);
        types.extend(rs.iter().map(|t| tybyte(*t)));
    }
    section(1, types, &mut out);
    let mut fs = vec![];
    uleb(funcs.len() as u64, &mut fs);
    for i in 0..funcs.len() {
        uleb(i as u64, &mut fs);
    }
    section(3, fs, &mut out);
    let mut ex = vec![];
    uleb(funcs.len() as u64, &mut ex);
    for i in 0..funcs.len() {
        let name = format!("f{i}");
        uleb(name.len() as u64, &mut ex);
        ex.extend(name.bytes());
        ex.push(0x00);
        uleb(i as u64, &mut ex);
    }
    section(7, ex, &mut out);
    let mut code = vec![];
    uleb(funcs.len() as u64, &mut code);
    for (_, _, locals, body) in funcs {
        let mut b = vec![];
        uleb(locals.len() as u64, &mut b);
        for t in locals {
            b.push(0x01);
            b.push(tybyte(*t));
        }
        for s in body {
            instr(s, &mut b)?;
        }
        b.push(0x0b);
        uleb(b.len() as u64, &mut code);
        code.extend(b);
    }
    section(10, code, &mut out);
    Ok(out)
}

#[cfg(test)]
mod tests {
    #[test]
    fn roundtrip() {
        use crate::term::Ty;
        let body: Vec<String> = [
            "local.get 0",
            "i32.const -1",
            "i32.and",
            "i64.const -5",
            "i64.eqz",
            "i32.add",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let m = super::write(&[(vec![Ty::I32], vec![Ty::I32], body)]).unwrap();
        let fs = super::read(&m).unwrap().funcs;
        assert_eq!(fs.len(), 1);
        assert_eq!(fs[0].body.as_ref().unwrap()[1], "i32.const -1");
        assert_eq!(fs[0].body.as_ref().unwrap()[3], "i64.const -5");
    }
}
