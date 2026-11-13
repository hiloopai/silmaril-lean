module

public import Silmaril.Proofs.Wasm.Wasmi.Observed.Run
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Witness

/-!
# The wasmi 0.40.0 run of a rounding function on any input (proofs)

`RoundFn.model_run`: for every input `x`, the call `a x` of a function `local.get 0; t.op`
runs in the wasmi 0.40.0 model to `t.const (wUnOp t op x)`. On a NaN input of a rounding
operator this is the quirk run (`RoundFn.wasmi_run`); otherwise the operator redex is not
pending (`pending_op`) and the Core step to the deterministic result is a model step.
`model_returns` reads it on the witness store. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas Silmaril.Wasm.Wasmi.Observed

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The operator redex of a rounding-function run is pending exactly when the operator rounds
and the input is a NaN. -/
theorem pending_op {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp}
    (R : RoundFn s a t op) (x : FloatValue t) :
    pending (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]).code =
      (IsRound op && isNaNB t x) := by
  cases t <;> rfl

/-- **The wasmi 0.40.0 run on any input** returns `wUnOp t op x`. -/
theorem RoundFn.model_run {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp}
    (R : RoundFn s a t op) (x : FloatValue t) :
    Relation.ReflTransGen (Silmaril.Wasm.Wasmi.Observed.Step P host) (invoke s a [fval t x])
      ⟨s, {}, vals [fval t (wUnOp t op x)]⟩ := by
  by_cases hq : IsRound op = true ∧ isNaNB t x = true
  · have hw : wUnOp t op x = x := by simp [wUnOp, hq.1, hq.2]
    rw [hw]
    exact R.wasmi_run hq.1 hq.2
  · have hw : wUnOp t op x = floatUnOp t op x := by
      unfold wUnOp
      rw [ite_eq_right (by simpa using hq)]
    have hp : pending (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)]).code =
        false := by
      rw [pending_op R x]
      simpa using hq
    have hz : floatUnOpP P t op x (floatUnOp t op x) := by
      unfold floatUnOpP
      cases P.nan with
      | spec => exact floatUnOpRel_self t op x
      | canonical => rfl
    rw [hw]
    exact R.run_of (fun _ _ hp h => .inl ⟨hp, h⟩)
      (.inl ⟨hp, .ctxtFrame (.ctxtLabel (.numeric (.floatUnOp hz)))⟩)

/-- **On the witness store the model returns `wUnOp t op x`**, for every input. -/
theorem model_returns (P : Profile) {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps)
    (x : FloatValue t) :
    Behaviour.returns [fval t (wUnOp t op x)] ∈
      Silmaril.Wasm.Wasmi.Observed.obs P roundPt (roundAddr t op, [fval t x]) := by
  obtain ⟨R⟩ := roundFn_store (t := t) hop
  exact .inl ⟨_, .values [fval t (wUnOp t op x)], R.model_run x, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Wasmi.Observed
