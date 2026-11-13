module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Der10

/-!
# `otherwise` and `Step` across an involutive re-encoding (unrefined)

When `τ` is an involution, so is `swapX` (`swapX_swapX`), and a forward transfer is also a
backward one. That is what an `otherwise` premise needs: it says that no earlier rule fires on
any value with the same left-hand side. If an earlier rule fired at `w` next to `swapX v`, the
forward transfer would make it fire at `swapX w` next to `v` (`sameLhs_swap`), against the
hypothesis at `v`. By strong induction on the rule index (`otherwiseAtB_swap`).

**`sstepB_swap`**: in `utf8Env10T B`, a step `v ⟶ w` of SpecTec's 1.0 `Step` under the reading
`SStepB` gives the step `swapX v ⟶ swapX w`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ10

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll (Hyps gr10 gd10)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim (SameLhs noElse)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB RuleBodyB otherwiseAtB otherwiseB SStepB)

section Inv
variable (hinv : ∀ u, XTau.τ (XTau.τ u) = u)
include hinv

mutual
/-- **`swapX` is an involution when `τ` is.** -/
theorem swapX_swapX : ∀ v : Value, swapX (swapX v) = v
  | .bool _ | .num _ | .text _ | .opt none => rfl
  | .tuple vs => by simp only [swapX]; rw [swapXs_swapXs vs]
  | .case _ w => by simp only [swapX]; rw [swapX_swapX w]
  | .struct gs => by simp only [swapX]; rw [swapXf_swapXf gs]
  | .list vs => by simp only [swapX]; rw [swapXs_swapXs vs]
  | .opt (some w) => by simp only [swapX]; rw [swapX_swapX w]

theorem swapXs_swapXs : ∀ vs : List Value, swapXs (swapXs vs) = vs
  | [] => rfl
  | v :: vs => by simp only [swapXs]; rw [swapX_swapX v, swapXs_swapXs vs]

theorem swapXf_swapXf : ∀ gs : List (IL.AtomS × Value), swapXf (swapXf gs) = gs
  | [] => rfl
  | (a, v) :: gs => by
    simp only [swapXf]
    rw [swapXf_swapXf gs]
    by_cases ha : a = "EXPORTS"
    · simp only [ha, ite_true, hinv]
    · simp only [ha, ite_false, swapX_swapX v]
end

/-- **Same left-hand side, across the involution.** -/
theorem sameLhs_swap {v w : Value} (h : SameLhs (swapX v) w) : SameLhs v (swapX w) := by
  obtain ⟨a, b, c, hv, rfl⟩ := h
  have hv' : v = swapX (.tuple [a, b]) := by rw [← hv, swapX_swapX hinv]
  refine ⟨swapX a, swapX b, swapX c, ?_, ?_⟩
  · rw [hv']; simp [swapX, swapXs]
  · simp [swapX, swapXs]

end Inv

variable {B : Builtins} (H : Hyps QT gr10 gd10 (utf8Env10T B)) {K : Nat} (hK : ExpK B K)
  (hinv : ∀ u, XTau.τ (XTau.τ u) = u)
include H hK hinv

/-- **`otherwise` moves across the involution**, for the relations `Step` reaches. -/
theorem otherwiseAtB_swap {x : IL.Id} (hG : gr10 x = true) :
    ∀ i v, otherwiseAtB (utf8Env10T B) x [] i v → otherwiseAtB (utf8Env10T B) x [] i (swapX v) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro v hO
  refine Utf8Else.otherwiseAtB_unfold'.2 fun j hj ps op t rules r hrel hr w hsame hb => ?_
  have hm : r ∈ (ps, op, t, rules).2.2.2 := List.mem_of_getElem? hr
  have hb' := ruleBodyB_swap H hK hrel hG hm (fun h => ih j hj w h) hb
  exact Utf8Else.otherwiseAtB_unfold'.1 hO j hj ps op t rules r hrel hr (swapX w)
    (sameLhs_swap hinv hsame) hb'

/-- **SpecTec's 1.0 `Step` moves across an involutive re-encoding of export lists.** -/
theorem sstepB_swap {v w : Value} (h : SStepB (utf8Env10T B) v w) :
    SStepB (utf8Env10T B) (swapX v) (swapX w) := by
  have h' := dderivesB_swap H hK (O := otherwiseB (utf8Env10T B)) (O' := otherwiseB (utf8Env10T B))
    (fun x i v hG ho => otherwiseAtB_swap H hK hinv hG i v ho) h (by decide)
  simpa [SStepB, swapX, swapXs] using h'

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ10
