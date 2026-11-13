//! Compiler-explorer correspondences and the program points of the Lean goals.
//!
//! A **range** is a maximal run of `.text` addresses that the line table attributes to one
//! source line (what a compiler explorer colours). A function's ranges become **segments** of
//! the Lean correspondence at one of two granularities:
//!
//! * `statement` (gcc `-O0`-style code): the first range is the prologue (entry point), every
//!   middle range starts a statement whose Core fragment is the only Core statement located on
//!   its line, and the last range is the epilogue (the return label's point); every object is
//!   in a DWARF frame slot (`DW_OP_fbreg`, frame base `DW_OP_call_frame_cfa`).
//! * `function`: one segment, the whole function, from its System V entry to its return. The
//!   per-line ranges are still reported, each `unsupported` at statement granularity with the
//!   first reason that ruled it out.
//!
//! The tool never guesses a per-line state relation: when a check fails it falls back to
//! `function` and says why.

use serde::Serialize;

use crate::obj::{FuncInfo, Location, ObjFile, Row};
use crate::sexp::{Proc, Sym};

#[derive(Clone, Debug, Serialize)]
pub struct Range {
    pub line: u64,
    pub start: u64,
    pub end: u64,
    /// AT&T text of the instructions (compiler-explorer view).
    pub asm: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Slot {
    pub name: String,
    #[serde(skip)]
    pub sym: Option<Sym>,
    pub off: i64,
    pub size: u64,
    pub signed: bool,
    pub param: bool,
    pub decl_line: u64,
    /// The object holds a value at the point (`Slot.defined` in Lean): a parameter, or a local
    /// whose declaration with an initialiser (a Core `int x = e;` statement, `Esseq`, at its
    /// declaration line) comes before the point's line. Only shapes the goals: a wrong flag
    /// makes a segment goal unprovable, not unsound.
    pub defined: bool,
}

#[derive(Clone, Debug, Serialize)]
pub enum PointKind {
    Entry,
    Slots(Vec<Slot>),
    Ret,
}

#[derive(Clone, Debug, Serialize)]
pub struct Point {
    pub index: usize,
    /// Offset of the point's machine address from the function's address.
    pub off: u64,
    pub line: u64,
    pub kind: PointKind,
}

#[derive(Clone, Debug, Serialize)]
pub struct Unsupported {
    pub line: u64,
    pub start: u64,
    pub end: u64,
    pub reason: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct FnCorr {
    pub name: String,
    pub off: u64,
    pub size: u64,
    pub ranges: Vec<Range>,
    pub granularity: &'static str,
    pub points: Vec<Point>,
    pub unsupported: Vec<Unsupported>,
    /// Why the whole function has no goal (no Core, an instruction outside the model, …).
    pub function_unsupported: Option<String>,
    /// The C signature as `Silmaril.C.Api.Scalar` names (`int32`, …) and the result's.
    pub sig: Option<(Vec<&'static str>, &'static str)>,
    /// Bytes below the entry `rsp` the function may write.
    pub frame: u64,
}

/// The line table's ranges inside `[lo, hi)`.
pub fn ranges(rows: &[Row], lo: u64, hi: u64) -> Vec<(u64, u64, u64)> {
    let mut rows: Vec<&Row> = rows
        .iter()
        .filter(|r| !r.end && r.addr >= lo && r.addr < hi)
        .collect();
    rows.sort_by_key(|r| r.addr);
    // the last row at an address wins (gcc emits several rows at one address at -O2: views)
    let mut points: Vec<(u64, u64)> = Vec::new();
    for r in rows {
        if let Some(last) = points.last_mut()
            && last.0 == r.addr
        {
            last.1 = r.line;
            continue;
        }
        points.push((r.addr, r.line));
    }
    let mut out: Vec<(u64, u64, u64)> = Vec::new();
    for (i, (a, line)) in points.iter().enumerate() {
        let end = points.get(i + 1).map(|p| p.0).unwrap_or(hi);
        if let Some(last) = out.last_mut()
            && last.0 == *line
            && last.2 == *a
        {
            last.2 = end;
            continue;
        }
        out.push((*line, *a, end));
    }
    out
}

/// The integer System V scalar of a DWARF base type.
pub fn scalar(base: Option<(u64, bool)>) -> Option<&'static str> {
    match base {
        Some((4, true)) => Some("int32"),
        Some((4, false)) => Some("uint32"),
        Some((8, true)) => Some("int64"),
        Some((8, false)) => Some("uint64"),
        _ => None,
    }
}

pub struct Input<'a> {
    pub obj: &'a ObjFile,
    pub name: &'a str,
    pub off: u64,
    pub size: u64,
    pub info: Option<&'a FuncInfo>,
    pub asm: Vec<(u64, String)>,
    /// Decoding refused (instruction outside the Lean decoder's forms).
    pub decode_error: Option<String>,
    pub core: Result<Proc, String>,
}

/// Bytes below the entry `rsp` an `-O0` leaf may write: the saved `rbp` (8) and the 128-byte
/// red zone below it.
pub const FRAME_O0: u64 = 136;

pub fn correspond(inp: &Input) -> FnCorr {
    let lo = inp.off;
    let hi = inp.off + inp.size;
    let rs: Vec<Range> = ranges(&inp.obj.rows, lo, hi)
        .into_iter()
        .map(|(line, start, end)| Range {
            line,
            start: start - lo,
            end: end - lo,
            asm: inp
                .asm
                .iter()
                .filter(|(a, _)| *a >= start && *a < end)
                .map(|(_, s)| s.clone())
                .collect(),
        })
        .collect();
    let sig = inp.info.and_then(|i| {
        let ps: Option<Vec<&'static str>> = i
            .vars
            .iter()
            .filter(|v| v.param)
            .map(|v| scalar(v.base))
            .collect();
        Some((ps?, scalar(i.return_base)?))
    });
    let mut c = FnCorr {
        name: inp.name.to_string(),
        off: inp.off,
        size: inp.size,
        ranges: rs.clone(),
        granularity: "function",
        points: vec![Point {
            index: 0,
            off: 0,
            line: inp.info.map(|i| i.decl_line).unwrap_or(0),
            kind: PointKind::Entry,
        }],
        unsupported: vec![],
        function_unsupported: None,
        sig,
        frame: FRAME_O0,
    };
    // Whole-function obstacles.
    let reloc = inp.obj.text_relocs.iter().find(|o| **o >= lo && **o < hi);
    let fatal = if let Some(e) = &inp.decode_error {
        Some(format!("machine code: {e}"))
    } else if let Some(o) = reloc {
        Some(format!(
            "a relocation patches the code at +{:#x} (calls and data references are not modelled)",
            o - lo
        ))
    } else if let Err(e) = &inp.core {
        Some(format!("C -> Core: {e}"))
    } else if c.sig.is_none() {
        Some("the C signature is not all int/unsigned/long scalars".into())
    } else if inp.asm.iter().any(|(_, s)| s.starts_with("call")) {
        Some("the function makes calls (leaf functions only)".into())
    } else {
        None
    };
    if let Some(f) = fatal {
        c.function_unsupported = Some(f.clone());
        for r in &rs {
            c.unsupported.push(Unsupported {
                line: r.line,
                start: r.start,
                end: r.end,
                reason: f.clone(),
            });
        }
        return c;
    }
    match statement_points(inp, &rs) {
        Ok(points) => {
            c.granularity = "statement";
            c.points = points;
        }
        Err(reason) => {
            for r in &rs {
                c.unsupported.push(Unsupported {
                    line: r.line,
                    start: r.start,
                    end: r.end,
                    reason: reason.clone(),
                });
            }
        }
    }
    c
}

fn statement_points(inp: &Input, rs: &[Range]) -> Result<Vec<Point>, String> {
    let info = inp.info.ok_or("no DWARF subprogram")?;
    let core = inp.core.as_ref().map_err(|e| e.clone())?;
    if !info.frame_base_cfa {
        return Err("the frame base is not DW_OP_call_frame_cfa".into());
    }
    if rs.len() < 3 {
        return Err("fewer than three line ranges (no prologue / statement / epilogue)".into());
    }
    let mut seen = std::collections::HashSet::new();
    for r in rs {
        if !seen.insert(r.line) {
            return Err(format!(
                "line {} has several address ranges (code split or merged: no per-line boundary state)",
                r.line
            ));
        }
    }
    let first = &rs[0];
    let ins0: Vec<&str> = first.asm.iter().map(|s| s.as_str()).collect();
    if ins0.len() < 2 || !ins0[0].starts_with("push %rbp") || !ins0[1].starts_with("mov %rsp,%rbp")
    {
        return Err(
            "the first range is not a frame-pointer prologue (push %rbp; mov %rsp,%rbp)".into(),
        );
    }
    if rs
        .iter()
        .flat_map(|r| r.asm.iter())
        .any(|s| s.starts_with("sub ") && s.ends_with(",%rsp"))
    {
        return Err("the function allocates stack below the red zone (sub ...,%rsp)".into());
    }
    let last = rs.last().unwrap();
    let insl: Vec<&str> = last.asm.iter().map(|s| s.as_str()).collect();
    if insl != ["pop %rbp", "ret"] {
        return Err(format!(
            "the last range is not the epilogue pop %rbp; ret ({insl:?})"
        ));
    }
    // Objects and their slots.
    let mut slots = Vec::new();
    for v in &info.vars {
        if v.nested {
            return Err(format!(
                "{} is declared in a nested block (one function scope only)",
                v.name
            ));
        }
        let Location::FrameSlot(off) = v.loc else {
            return Err(format!("{} has no frame slot ({:?})", v.name, v.loc));
        };
        let Some((size, signed)) = v.base else {
            return Err(format!("{} is not of a base integer type", v.name));
        };
        if size != 4 {
            return Err(format!("{} is not a 4-byte integer", v.name));
        }
        // inside the red zone below the saved rbp: [cfa - 16 - 128, cfa - 16)
        if off < -144 || off + size as i64 > -16 {
            return Err(format!(
                "{}'s slot fbreg {off} is outside the leaf frame",
                v.name
            ));
        }
        let pool: Vec<&Sym> = if v.param {
            core.params.iter().collect()
        } else {
            core.locals.iter().collect()
        };
        let syms: Vec<&Sym> = pool
            .into_iter()
            .filter(|s| s.desc.0 == "SD_ObjectAddress" && s.desc.1 == v.name)
            .collect();
        let sym = match syms.as_slice() {
            [s] => (*s).clone(),
            [] => return Err(format!("no Core object for {}", v.name)),
            _ => return Err(format!("several Core objects named {}", v.name)),
        };
        slots.push(Slot {
            name: v.name.clone(),
            sym: Some(sym),
            off,
            size,
            signed,
            param: v.param,
            decl_line: v.decl_line,
            defined: false,
        });
    }
    // Statements.
    let mut points = vec![Point {
        index: 0,
        off: 0,
        line: first.line,
        kind: PointKind::Entry,
    }];
    for r in &rs[1..rs.len() - 1] {
        let at: Vec<_> = core
            .stmts
            .iter()
            .filter(|s| s.first_line == r.line as i64)
            .collect();
        if at.len() != 1 {
            return Err(format!(
                "line {} has {} Core statements (one needed)",
                r.line,
                at.len()
            ));
        }
        let initialised = |line: u64| {
            core.stmts
                .iter()
                .any(|s| s.first_line == line as i64 && s.node == "Esseq")
        };
        let here = slots
            .iter()
            .map(|s| Slot {
                defined: s.param || (s.decl_line < r.line && initialised(s.decl_line)),
                ..s.clone()
            })
            .collect();
        points.push(Point {
            index: points.len(),
            off: r.start,
            line: r.line,
            kind: PointKind::Slots(here),
        });
    }
    if core.returns.len() != 1 || core.returns[0].1.len() != 1 {
        return Err("the procedure has no single one-parameter return label".into());
    }
    points.push(Point {
        index: points.len(),
        off: last.start,
        line: last.line,
        kind: PointKind::Ret,
    });
    Ok(points)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(addr: u64, line: u64) -> Row {
        Row {
            addr,
            line,
            column: 0,
            is_stmt: true,
            end: false,
        }
    }

    #[test]
    fn ranges_merge_and_last_row_wins() {
        // gcc -O2: several rows at one address (views); the last one names the range.
        let rows = vec![row(0, 2), row(0, 3), row(0, 4), row(2, 4), row(10, 5)];
        assert_eq!(ranges(&rows, 0, 11), vec![(4, 0, 10), (5, 10, 11)]);
    }

    #[test]
    fn ranges_split_lines_stay_split() {
        // gcc -O0 loop: the condition's line appears twice.
        let rows = vec![row(0, 3), row(7, 6), row(9, 7), row(13, 6), row(20, 10)];
        let r = ranges(&rows, 0, 22);
        assert_eq!(r.iter().filter(|x| x.0 == 6).count(), 2);
    }
}
