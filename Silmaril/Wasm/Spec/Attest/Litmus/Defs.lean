module

public import Silmaril.Wasm.Spec.Attest.Core.Defs

/-!
# Litmus tests for "may attest": formulas and valuations

* `T`, `F`: the Core programs of `ttMod` (export `fire` calls `attest`) and `ffMod` (export
  `idle` does nothing);
* `x0`, `x1`, `x2`: variables over `Fin 3`;
* `orF = x0 ∨ x1`, `andF = x0 ∧ x1`, `andAndF = (x0 ∧ x1) ∧ x2` (a conjunction whose left
  operand is itself linked to a gate), `orAndF = x0 ∨ (x1 ∧ x2)`, `andOrF = x0 ∧ (x1 ∨ x2)`;
* `val a b c`: the valuation sending `x0, x1, x2` to `a, b, c`.

The tests are in `Silmaril.Wasm.Spec.Attest.Litmus.Thms`. New (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Spec.Attest.Litmus

open Silmaril.Wasm.Spec.Attest Silmaril.Wasm.Spec.Attest.Core

/-- The `true` program. -/
def T : CoreLeaf := leafOf ttMod

/-- The `false` program. -/
def F : CoreLeaf := leafOf ffMod

/-- The variable `x0`. -/
def x0 : PForm (Fin 3) := .var 0
/-- The variable `x1`. -/
def x1 : PForm (Fin 3) := .var 1
/-- The variable `x2`. -/
def x2 : PForm (Fin 3) := .var 2

/-- `x0 ∨ x1`. -/
def orF : PForm (Fin 3) := .or x0 x1
/-- `x0 ∧ x1`. -/
def andF : PForm (Fin 3) := .and x0 x1
/-- `(x0 ∧ x1) ∧ x2`. -/
def andAndF : PForm (Fin 3) := .and (.and x0 x1) x2
/-- `x0 ∨ (x1 ∧ x2)`. -/
def orAndF : PForm (Fin 3) := .or x0 (.and x1 x2)
/-- `x0 ∧ (x1 ∨ x2)`. -/
def andOrF : PForm (Fin 3) := .and x0 (.or x1 x2)

/-- The valuation `x0 ↦ a`, `x1 ↦ b`, `x2 ↦ c`. -/
def val (a b c : CoreLeaf) : Fin 3 → CoreLeaf
  | 0 => a
  | 1 => b
  | 2 => c

end Silmaril.Wasm.Spec.Attest.Litmus
