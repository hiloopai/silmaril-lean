module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Basic
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# Round 7, determination: the primitives' answers are `ExpFree`

One lemma per family of round 4's primitives (`Prims.call`): every answer is built by the value
encoders (`numV`, `floatV`, `bvV`, `pctV`, `tyV`, the instance encoders), which produce no
record with a non-empty `EXPORTS` field, or, for `$hostcall`, is export-free by
`Round7.ExpEnc.efB_hostcallCall` at an export-blind host. Each is checked by unfolding to `efB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

/-! ## `efB` is complete for `ExpFree` -/

mutual
theorem efB_of_expFree : ∀ {v : Value}, ExpFree v → efB v = true
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple _, h => efBs_of_expFree (ef_tuple.1 h)
  | .case _ w, h => efB_of_expFree (v := w) (ef_case.1 h)
  | .struct _, h => efBf_of_expFree (ef_struct.1 h).1 (ef_struct.1 h).2
  | .list _, h => efBs_of_expFree (ef_list.1 h)
  | .opt none, _ => rfl
  | .opt (some w), h => efB_of_expFree (v := w) (ef_optSome.1 h)

theorem efBs_of_expFree : ∀ {vs : List Value}, (∀ w ∈ vs, ExpFree w) → efBs vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [efBs, Bool.and_eq_true]
    exact ⟨efB_of_expFree (h v List.mem_cons_self),
      efBs_of_expFree fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

theorem efBf_of_expFree : ∀ {gs : List (IL.AtomS × Value)}, (∀ p ∈ gs, ExpFree p.2) →
    (∀ p ∈ gs, p.1 = "EXPORTS" → p.2 = .list []) → efBf gs = true
  | [], _, _ => rfl
  | (a, v) :: gs, h₁, h₂ => by
    simp only [efBf, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨efB_of_expFree (h₁ _ List.mem_cons_self), ?_⟩,
      efBf_of_expFree (fun p hp => h₁ p (List.mem_cons_of_mem _ hp))
        (fun p hp => h₂ p (List.mem_cons_of_mem _ hp))⟩
    by_cases ha : a = "EXPORTS"
    · have hv : v = .list [] := h₂ _ List.mem_cons_self ha
      exact Or.inr (by rw [hv]; rfl)
    · exact Or.inl ha
end

/-! ## Encoders -/

@[simp] theorem efB_bvV {N : Nat} (i : BitVec N) : efB (bvV i) = true := rfl

@[simp] theorem efB_pctV (n : Nat) : efB (pctV n) = true := rfl

theorem ef_of_efB_some {o : Option Value} {v : Value} (hs : o = some v)
    (h : ∀ w, o = some w → efB w = true) : ExpFree v := expFree_of_efB _ (h v hs)

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
