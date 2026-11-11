module

public import Silmaril.Wasm.FX.Asyncify.Tool.Run.Defs

/-!
# Eliding re-entry checks of the asyncify tool

The pass of `Silmaril.Wasm.FX.Asyncify.Tool.Pass` guards every pure statement with a re-entry check
`global.get state; i32.const 2; i32.ne; if … end`: while rewinding (`state = 2`) the statements
before the resume point are skipped. Two kinds of these checks are redundant:

* **adjacent pure statements**: `if state ≠ 2 { a }; if state ≠ 2 { b }` is `if state ≠ 2 { a b }`,
  because pure code does not write `state`;
* **pure statements after the last call statement**: a rewind always stops at a call statement
  (`state` is `0` again after it), so pure code after the last one never runs in rewind mode and
  needs no check.

`elideS` does both on the statement split, before the translation: it fuses runs of pure
statements and moves the trailing run into the (unguarded) tail. The flat code is unchanged
(`Silmaril.Wasm.FX.Asyncify.Tool.Elide.Thms`: `Prog.elide_env`), so the source program is the same
and `asyncify_beh` applies to `P.elide`; the result is a target with at most one guarded pure
statement per call statement (`elide_guards`). `asyncifyE` and `asyncifyBytesE` are the tool
with the elision (the default of `wasm-asyncify`; `--no-elide` gives the guarded pass).

The guards of call statements (`state ≠ 2 ∨ sel = k`, and the `state = 2` test at an import site)
and the prologue are kept: they are the resume dispatch.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- Fuse runs of pure statements, and move the pure statements after the last call statement into
the tail. -/
def elideS : List Stmt → List Instr → List Stmt × List Instr
  | [], tl => ([], tl)
  | .call f as rs :: r, tl => (.call f as rs :: (elideS r tl).1, (elideS r tl).2)
  | .pure is :: r, tl =>
    match elideS r tl with
    | ([], tl') => ([], is ++ tl')
    | (.pure js :: r', tl') => (.pure (is ++ js) :: r', tl')
    | (.call f as rs :: r', tl') => (.pure is :: .call f as rs :: r', tl')

/-- A function with elided checks. -/
def FnSrc.elide (fn : FnSrc) : FnSrc :=
  { fn with stmts := (elideS fn.stmts fn.tail).1, tail := (elideS fn.stmts fn.tail).2 }

/-- A program with elided checks. -/
def Prog.elide (P : Prog) : Prog := ⟨P.imps, P.fns.map FnSrc.elide⟩

/-- Pure statements: each gets one `state ≠ 2` check in the target. -/
def Stmt.isPure : Stmt → Bool
  | .pure _ => true
  | .call _ _ _ => false

/-- The number of `state ≠ 2` checks of pure statements in the translation of `ss`. -/
def pureChecks : List Stmt → Nat
  | [] => 0
  | .pure _ :: r => pureChecks r + 1
  | .call _ _ _ :: r => pureChecks r

/-- The number of call statements. -/
def callStmts : List Stmt → Nat
  | [] => 0
  | .pure _ :: r => callStmts r
  | .call _ _ _ :: r => callStmts r + 1

/-- The pass on modules with elided checks: recognise, elide, transform. -/
def asyncifyE (m : Module) (pages : Nat := 1) : Except String Module :=
  match recognize m with
  | .error e => .error e
  | .ok P =>
    if m.exports.any (fun e => e.name == stateExport || e.name == memoryExport) then
      .error "the module already exports asyncify_state or asyncify_memory"
    else if P.elide.sb + 4 * P.elide.frameWords ≤ 65536 * pages ∧ pages < 65536 then
      .ok (asyncifyModule m P.elide pages)
    else .error "the memory cannot hold the request area and one frame"

/-- Decode, asyncify with elided checks, encode. -/
def asyncifyBytesE (b : ByteArray) (pages : Nat := 1) : Except String ByteArray :=
  match Binary.Core.decode? b with
  | none => .error "the input does not decode as a Core module"
  | some m =>
    match asyncifyE m pages with
    | .error e => .error e
    | .ok m' =>
      match Binaryen.Exe.encodeModule? m' with
      | .ok bs => .ok ⟨bs.toArray⟩
      | .error e => .error s!"encoding failed: {e}"

end Silmaril.Wasm.FX.Asyncify.Tool
