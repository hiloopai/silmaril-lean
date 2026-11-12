module

public import Silmaril.Wasm.Auto.EquivXCex.Defs
import Silmaril.Proofs.Wasm.Auto.EquivXCex.Refute

/-!
# Counterexamples for the extended checker: results

For `Silmaril.Wasm.Auto.EquivXCex.Defs` (proofs in `Silmaril/Proofs/Wasm/Auto/EquivXCex/Refute`):

* `ctxOf_ok`: the canonical context of inputs `ρ` and memory bytes `B0` is a typed context
  (`XCtx.Ok`) for every `lt`, `st`, `gt` and `mem`;
* **`not_segEquivX_of_cex`**, **`not_outEquivX_of_cex`**: a counterexample found by `findCexX`
  (`cexAtX_of_findCexX`) or given by hand refutes `SegEquivX` / `OutEquivX`, a statement about
  silmaril-lean's small-step semantics through the every-run logic (total reading).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivXCex

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (Env envOf)
open Silmaril.Wasm.Auto.Equiv



theorem ctxOf_ok (lt st gt : List IntType) (mem : Bool) (ρ : Env) (B0 : ByteArray) :
    (ctxOf lt st gt ρ B0).Ok lt st gt mem :=
  Silmaril.Proofs.Wasm.Auto.EquivXCex.ctxOf_ok lt st gt mem ρ B0

/-- **Refutation of `SegEquivX` by a counterexample.** -/
theorem not_segEquivX_of_cex {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (xs : List Nat) (B0 : ByteArray) (h : cexAtX true lt st gt mem a b xs B0 = true) :
    ¬ SegEquivX lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.EquivXCex.not_segEquivX_of_cex xs B0 h

/-- **Refutation of `OutEquivX` by a counterexample** (locals not compared). -/
theorem not_outEquivX_of_cex {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (xs : List Nat) (B0 : ByteArray) (h : cexAtX false lt st gt mem a b xs B0 = true) :
    ¬ OutEquivX lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.EquivXCex.not_outEquivX_of_cex xs B0 h

/-- `findCexX` returns counterexamples. -/
theorem cexAtX_of_findCexX {loc : Bool} {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    {xs : List Nat} {k : Nat} (h : findCexX loc lt st gt mem a b = some (xs, k)) :
    cexAtX loc lt st gt mem a b xs (probeMems.getD k ByteArray.empty) = true :=
  Silmaril.Proofs.Wasm.Auto.EquivXCex.cexAtX_of_findCexX h

end Silmaril.Wasm.Auto.EquivXCex
