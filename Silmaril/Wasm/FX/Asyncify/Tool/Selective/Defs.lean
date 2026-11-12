module

public import Silmaril.Wasm.FX.Asyncify.Tool.Run.Defs

/-!
# The asyncify tool, selective instrumentation (`--selective`)

Binaryen instruments only the functions that can reach a suspension (`asyncify-imports`). The
tool's selective mode does the same on its statement form:

* **The analysis** (`mayS P`): the least set of function indices that contains every import and
  every defined function with a call statement to a member, computed by `P.fns.length + 1`
  rounds from the imports (`suspSet`). A function outside it is *calm*: no run of it reaches an
  import call.
* **The pass** (`selProg P`): every call statement to a calm defined function becomes a *pure*
  statement with the same code. The whole-program pass then guards it like other pure code
  (`if state ≠ 2`) and adds no check after it: no `sel = k` dispatch, no `state = 1` test, no
  frame save. Calls to imports and to functions that may suspend are unchanged.

`selProg_env`: the machine program is unchanged (the reclassified statements have the same
code), so the selective output asyncifies **the same source program**. Its correctness on the
frame machine is `SelectiveBeh` (`Selective/Thms`), proved by a separate simulation
(`SelSim.Thms.selective_beh`), since the proof of `asyncify_beh` assumes pure statements of pure
instructions only. The family's selective
instance of the translated program is proved (`Bridge.tool_analyzed`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- One round of the analysis: imports, and functions calling a member of `S`. -/
def suspStep (P : Prog) (S : Nat → Bool) (f : Nat) : Bool :=
  if f < P.imps.length then true
  else
    match P.fns[f - P.imps.length]? with
    | none => false
    | some fn => fn.stmts.any fun
      | .call g _ _ => S g.value.val
      | .pure _ => false

/-- `n` rounds from the imports. -/
def suspSet (P : Prog) : Nat → Nat → Bool
  | 0 => fun f => decide (f < P.imps.length)
  | n + 1 => suspStep P (suspSet P n)

/-- **The functions that may suspend.** -/
def mayS (P : Prog) : Nat → Bool := suspSet P (P.fns.length + 1)

/-- A call statement to a calm defined function becomes a pure statement with the same code. -/
def selStmt (P : Prog) : Stmt → Stmt
  | .call f as rs =>
    if P.imps.length ≤ f.value.val ∧ mayS P f.value.val = false then .pure (Stmt.code (.call f as rs))
    else .call f as rs
  | st => st

/-- **The selective source program.** -/
def selProg (P : Prog) : Prog :=
  { P with fns := P.fns.map fun fn => { fn with stmts := fn.stmts.map (selStmt P) } }

/-- The number of call statements left instrumented (a measure of the saving). -/
def Prog.nCallStmts (P : Prog) : Nat :=
  (P.fns.map fun fn => (fn.stmts.filter fun | .call _ _ _ => true | .pure _ => false).length).sum

/-- The pass on modules, selective. -/
def asyncifySelective (m : Module) (pages : Nat := 1) : Except String Module :=
  match recognize m with
  | .error e => .error e
  | .ok P =>
    if m.exports.any (fun e => e.name == stateExport || e.name == memoryExport) then
      .error "the module already exports asyncify_state or asyncify_memory"
    else if P.sb + 4 * P.frameWords ≤ 65536 * pages ∧ pages < 65536 then
      .ok (asyncifyModule m (selProg P) pages)
    else .error "the memory cannot hold the request area and one frame"

/-- Decode, asyncify selectively, encode. -/
def asyncifyBytesSelective (b : ByteArray) (pages : Nat := 1) : Except String ByteArray :=
  match Binary.Core.decode? b with
  | none => .error "the input does not decode as a Core module"
  | some m =>
    match asyncifySelective m pages with
    | .error e => .error e
    | .ok m' =>
      match Binaryen.Exe.encodeModule? m' with
      | .ok bs => .ok ⟨bs.toArray⟩
      | .error e => .error s!"encoding failed: {e}"

end Silmaril.Wasm.FX.Asyncify.Tool
