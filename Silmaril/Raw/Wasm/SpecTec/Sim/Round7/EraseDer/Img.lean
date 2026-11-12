module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Fwd

/-!
# Round 7, moving derivations across erasure: the erased side's swap set (unrefined)

The swap set of the erased side is `AllIn (EImg Q)`: every record with an `EXPORTS` field is the
erasure of a record of `Q`.

* `eraseV_idem`: erasing twice is erasing once.
* `allIn_eImg_eraseV`: erasures of swap-set values are in it.
* `unerase_eImg`: on it, `unerase Q` is a right inverse of `eraseV` that lands in the swap set
  (given that the records of `Q` are themselves in the swap set, as module images are).
* `qInj_eImg`, `qShape_eImg`: the erasure image is injective (everything in it is already erased)
  and keeps the module shape, so the evaluator-level hypotheses hold there as well
  (`hyps_eImg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (Hyps QShape Flat UpdSafe BIErase)

variable {Q : Value → Prop}

mutual
theorem eraseV_idem : ∀ v : Value, eraseV (eraseV v) = eraseV v
  | .bool _ => rfl
  | .num _ => rfl
  | .text _ => rfl
  | .tuple vs => by simp only [eraseV, eraseVs_idem vs]
  | .case _ w => by simp only [eraseV, eraseV_idem w]
  | .struct gs => by simp only [eraseV, eraseVf_idem gs]
  | .list vs => by simp only [eraseV, eraseVs_idem vs]
  | .opt none => rfl
  | .opt (some w) => by simp only [eraseV, eraseV_idem w]

theorem eraseVs_idem : ∀ vs : List Value, eraseVs (eraseVs vs) = eraseVs vs
  | [] => rfl
  | v :: vs => by simp only [eraseVs, eraseV_idem v, eraseVs_idem vs]

theorem eraseVf_idem : ∀ gs : List (IL.AtomS × Value), eraseVf (eraseVf gs) = eraseVf gs
  | [] => rfl
  | (a, v) :: gs => by
    simp only [eraseVf]
    by_cases ha : a = "EXPORTS"
    · simp [ha, eraseVf_idem gs]
    · simp [ha, eraseV_idem v, eraseVf_idem gs]
end

/-! ## Erasures are in the erased swap set -/

mutual
theorem allIn_eImg_eraseV : ∀ v : Value, AllIn Q v → AllIn (EImg Q) (eraseV v)
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => allIns_eImg_eraseVs vs h
  | .case _ w, h => allIn_eImg_eraseV w h
  | .struct gs, h => by
    refine ⟨fun he => ⟨.struct gs, h.1 (by simpa using he), rfl⟩, allInf_eImg_eraseVf gs h.2⟩
  | .list vs, h => allIns_eImg_eraseVs vs h
  | .opt none, _ => trivial
  | .opt (some w), h => allIn_eImg_eraseV w h

theorem allIns_eImg_eraseVs : ∀ vs : List Value, AllIns Q vs → AllIns (EImg Q) (eraseVs vs)
  | [], _ => trivial
  | v :: vs, h => ⟨allIn_eImg_eraseV v h.1, allIns_eImg_eraseVs vs h.2⟩

theorem allInf_eImg_eraseVf :
    ∀ gs : List (IL.AtomS × Value), AllInf Q gs → AllInf (EImg Q) (eraseVf gs)
  | [], _ => trivial
  | (a, v) :: gs, h => by
    refine ⟨?_, allInf_eImg_eraseVf gs h.2⟩
    by_cases ha : a = "EXPORTS"
    · simp only [ha, ite_true]; exact trivial
    · simp only [ha, ite_false]; exact allIn_eImg_eraseV v h.1
end

/-! ## Undoing erasure on the erased swap set -/

theorem hasExp_uneraseF : ∀ gs : List (IL.AtomS × Value), hasExp (uneraseF Q gs) = hasExp gs
  | [] => rfl
  | (a, v) :: gs => by simp only [uneraseF, hasExp_cons, hasExp_uneraseF gs]

section
set_option linter.unusedSectionVars false
variable (hQA : ∀ r, Q r → AllIn Q r)
include hQA

mutual
/-- **`unerase Q` inverts erasure on the erased swap set.** -/
theorem unerase_eImg : ∀ w : Value, AllIn (EImg Q) w →
    AllIn Q (unerase Q w) ∧ eraseV (unerase Q w) = w
  | .bool _, _ => ⟨trivial, rfl⟩
  | .num _, _ => ⟨trivial, rfl⟩
  | .text _, _ => ⟨trivial, rfl⟩
  | .tuple vs, h => by
    obtain ⟨h₁, h₂⟩ := uneraseS_eImg vs h
    exact ⟨h₁, by simp only [unerase, eraseV, h₂]⟩
  | .case _ w, h => by
    obtain ⟨h₁, h₂⟩ := unerase_eImg w h
    exact ⟨h₁, by simp only [unerase, eraseV, h₂]⟩
  | .struct gs, h => by
    by_cases hc : hasExp gs = true ∧ ∃ r, Q r ∧ eraseV r = .struct gs
    · simp only [unerase, dite_eq_left_of_eq_true (eq_true hc)]
      exact ⟨hQA _ hc.2.choose_spec.1, hc.2.choose_spec.2⟩
    · simp only [unerase, dite_eq_right_of_eq_false (eq_false hc)]
      have hne : hasExp gs = false := by
        cases he : hasExp gs
        · rfl
        · exact absurd ⟨he, h.1 he⟩ hc
      obtain ⟨h₁, h₂⟩ := uneraseF_eImg gs hne h.2
      refine ⟨⟨fun he => ?_, h₁⟩, by simp only [eraseV, h₂]⟩
      rw [hasExp_uneraseF, hne] at he
      cases he
  | .list vs, h => by
    obtain ⟨h₁, h₂⟩ := uneraseS_eImg vs h
    exact ⟨h₁, by simp only [unerase, eraseV, h₂]⟩
  | .opt none, _ => ⟨trivial, rfl⟩
  | .opt (some w), h => by
    obtain ⟨h₁, h₂⟩ := unerase_eImg w h
    exact ⟨h₁, by simp only [unerase, eraseV, h₂]⟩

theorem uneraseS_eImg : ∀ vs : List Value, AllIns (EImg Q) vs →
    AllIns Q (uneraseS Q vs) ∧ eraseVs (uneraseS Q vs) = vs
  | [], _ => ⟨trivial, rfl⟩
  | v :: vs, h => by
    obtain ⟨h₁, h₂⟩ := unerase_eImg v h.1
    obtain ⟨h₃, h₄⟩ := uneraseS_eImg vs h.2
    exact ⟨⟨h₁, h₃⟩, by simp only [uneraseS, eraseVs, h₂, h₄]⟩

theorem uneraseF_eImg : ∀ gs : List (IL.AtomS × Value), hasExp gs = false →
    AllInf (EImg Q) gs → AllInf Q (uneraseF Q gs) ∧ eraseVf (uneraseF Q gs) = gs
  | [], _, _ => ⟨trivial, rfl⟩
  | (a, v) :: gs, he, h => by
    simp only [hasExp_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at he
    obtain ⟨h₁, h₂⟩ := unerase_eImg v h.1
    obtain ⟨h₃, h₄⟩ := uneraseF_eImg gs he.2 h.2
    exact ⟨⟨h₁, h₃⟩, by simp only [uneraseF, eraseVf, he.1, ite_false, h₂, h₄]⟩
end

end

/-! ## The evaluator-level hypotheses at the erasure image -/

theorem eImg_erased {r : Value} (h : EImg Q r) : eraseV r = r := by
  obtain ⟨r₀, -, rfl⟩ := h
  exact eraseV_idem r₀

theorem qInj_eImg : QInj (EImg Q) := fun x y hx hy he => by
  rw [← eImg_erased hx, he, eImg_erased hy]

theorem mem_eraseVf : ∀ {gs : List (IL.AtomS × Value)} {p : IL.AtomS × Value}, p ∈ eraseVf gs →
    ∃ q ∈ gs, p = (q.1, if q.1 = "EXPORTS" then .list [] else eraseV q.2)
  | [], _, h => by cases h
  | (a, v) :: gs, p, h => by
    simp only [eraseVf, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨(a, v), List.mem_cons_self, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := mem_eraseVf h
      exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩

theorem flat_eraseV {u : Value} (h : Flat u) : Flat (eraseV u) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun gs => ?_, fun l => ?_⟩ <;>
    rcases u with _ | _ | _ | _ | _ | gs' | l' | (_ | _) <;> simp [eraseV] at h₁ h₂ ⊢

theorem qShape_eImg (hQ : QShape Q) : QShape (EImg Q) := by
  rintro r ⟨r₀, hr₀, rfl⟩
  obtain ⟨gs, rfl, hgs⟩ := hQ r₀ hr₀
  refine ⟨eraseVf gs, rfl, fun p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := mem_eraseVf hp
  obtain ⟨hm, hf⟩ := hgs q hq
  refine ⟨hm, fun hne => ?_⟩
  obtain ⟨us, hus, hu⟩ := hf hne
  refine ⟨us.map eraseV, ?_, fun u hu' => ?_⟩
  · simp only [hne, ite_false, hus, eraseV_list']
  · obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 hu'
    exact flat_eraseV (hu u₀ hu₀)

/-- **The evaluator-level hypotheses at the erasure image**, from those at `Q` and the builtins'
erasure there. -/
theorem hyps_eImg {gr gd : String → Bool} {env : Env} (H : Hyps Q gr gd env) (hS : QShape Q)
    (hb : BIErase (EImg Q) gd env) : Hyps (EImg Q) gr gd env :=
  ⟨qInj_eImg, H.defs, H.rels, hb, EraseAll.updSafe_of_shape (qShape_eImg hS)⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
