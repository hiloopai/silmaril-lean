module

public import Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.Defs

/-!
# Round 7, encoder lemma: `efB` is sound for `ExpFree`

* `expFree_of_efB`: `efB v = true → ExpFree v`.
* simp lemmas for `efB` on the value constructors and on mapped lists (`efB_list_map`,
  `efBs_map`), so that each encoder is checked by unfolding.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

theorem isNilList_eq {w : Value} (h : isNilList w = true) : w = .list [] := by
  match w, h with
  | .list [], _ => rfl

mutual
theorem expFree_of_efB : ∀ v : Value, efB v = true → ExpFree v
  | .bool _, _ => .bool _
  | .num _, _ => .num _
  | .text _, _ => .text _
  | .tuple vs, h => .tuple (expFree_of_efBs vs h)
  | .case _ w, h => .case _ (expFree_of_efB w h)
  | .struct gs, h => .struct (expFree_of_efBf gs h).1 (expFree_of_efBf gs h).2
  | .list vs, h => .list (expFree_of_efBs vs h)
  | .opt none, _ => .opt (by simp)
  | .opt (some w), h => .opt (by simpa using expFree_of_efB w h)

theorem expFree_of_efBs : ∀ vs : List Value, efBs vs = true → ∀ w ∈ vs, ExpFree w
  | [], _ => by simp
  | v :: vs, h => by
    simp only [efBs, Bool.and_eq_true] at h
    exact List.forall_mem_cons.2 ⟨expFree_of_efB v h.1, expFree_of_efBs vs h.2⟩

theorem expFree_of_efBf : ∀ gs : List (IL.AtomS × Value), efBf gs = true →
    (∀ p ∈ gs, ExpFree p.2) ∧ (∀ p ∈ gs, p.1 = "EXPORTS" → p.2 = .list [])
  | [], _ => by simp
  | (a, v) :: gs, h => by
    simp only [efBf, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hv, ha⟩, hg⟩ := h
    have ih := expFree_of_efBf gs hg
    refine ⟨List.forall_mem_cons.2 ⟨expFree_of_efB v hv, ih.1⟩,
      List.forall_mem_cons.2 ⟨fun hpa => ?_, ih.2⟩⟩
    rcases ha with ha | ha
    · exact absurd hpa ha
    · exact isNilList_eq ha
end

/-- Close `efB e = true` for an encoder applied to a constructor, splitting nested finite
arguments. -/
syntax "efb_leaf" : tactic
macro_rules
  | `(tactic| efb_leaf) => `(tactic| first | rfl | (rename_i x; cases x; all_goals efb_leaf))

/-! ## Unfolding `efB` -/

@[simp] theorem efB_bool (b : Bool) : efB (.bool b) = true := rfl
@[simp] theorem efB_num (n : IL.Num) : efB (.num n) = true := rfl
@[simp] theorem efB_text (t : IL.Text) : efB (.text t) = true := rfl
@[simp] theorem efB_tuple (vs : List Value) : efB (.tuple vs) = efBs vs := rfl
@[simp] theorem efB_case (op : IL.MixopS) (w : Value) : efB (.case op w) = efB w := rfl
@[simp] theorem efB_struct (gs : List (IL.AtomS × Value)) : efB (.struct gs) = efBf gs := rfl
@[simp] theorem efB_list (vs : List Value) : efB (.list vs) = efBs vs := rfl
@[simp] theorem efB_opt_none : efB (.opt none) = true := rfl
@[simp] theorem efB_opt_some (w : Value) : efB (.opt (some w)) = efB w := rfl
@[simp] theorem efBs_nil : efBs [] = true := rfl
@[simp] theorem efBs_cons (v : Value) (vs : List Value) :
    efBs (v :: vs) = (efB v && efBs vs) := rfl
@[simp] theorem efBf_nil : efBf [] = true := rfl
@[simp] theorem efBf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    efBf ((a, v) :: gs) = (efB v && (a != "EXPORTS" || isNilList v) && efBf gs) := rfl
@[simp] theorem isNilList_nil : isNilList (.list []) = true := rfl

theorem efBs_eq_all : ∀ vs : List Value, efBs vs = vs.all efB
  | [] => rfl
  | v :: vs => by simp [efBs_eq_all vs]

@[simp] theorem efBs_map {α : Type} (f : α → Value) (l : List α) :
    efBs (l.map f) = l.all fun a => efB (f a) := by
  rw [efBs_eq_all, List.all_map]; rfl

theorem efB_opt (o : Option Value) (h : ∀ w ∈ o, efB w = true) : efB (.opt o) = true := by
  cases o with
  | none => rfl
  | some w => exact h w rfl

@[simp] theorem efB_opt_map {α : Type} (f : α → Value) (o : Option α) :
    efB (.opt (o.map f)) = o.all fun a => efB (f a) := by
  cases o <;> rfl

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
