module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Basic

/-!
# Round 7, the export swap: `eraseV` is a partial bijection

* simp lemmas for `eraseV`, `nxB`, `AllIn` and `hasExp` on the value constructors;
* `eraseV_of_efB`: `eraseV` fixes values whose `EXPORTS` fields are already `[]`;
* `allIn_of_nxB`: a value without `EXPORTS` records is `AllIn Q` for every `Q`;
* `unerase_eraseV`, `eraseV_inj`: under `QInj Q`, `eraseV` is injective on `AllIn Q` values, with
  left inverse `unerase Q`;
* `AllIn.mono`: `AllIn` is monotone in `Q`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc (efB efBs efBf isNilList isNilList_eq)

/-! ## Unfolding -/

@[simp] theorem eraseV_bool (b : Bool) : eraseV (.bool b) = .bool b := rfl
@[simp] theorem eraseV_num (n : IL.Num) : eraseV (.num n) = .num n := rfl
@[simp] theorem eraseV_text (t : IL.Text) : eraseV (.text t) = .text t := rfl
@[simp] theorem eraseV_tuple (vs : List Value) : eraseV (.tuple vs) = .tuple (eraseVs vs) := rfl
@[simp] theorem eraseV_case (op : IL.MixopS) (w : Value) :
    eraseV (.case op w) = .case op (eraseV w) := rfl
@[simp] theorem eraseV_struct (gs : List (IL.AtomS × Value)) :
    eraseV (.struct gs) = .struct (eraseVf gs) := rfl
@[simp] theorem eraseV_list (vs : List Value) : eraseV (.list vs) = .list (eraseVs vs) := rfl
@[simp] theorem eraseV_opt_none : eraseV (.opt none) = .opt none := rfl
@[simp] theorem eraseV_opt_some (w : Value) : eraseV (.opt (some w)) = .opt (some (eraseV w)) :=
  rfl
@[simp] theorem eraseVf_nil : eraseVf [] = [] := rfl
@[simp] theorem eraseVf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    eraseVf ((a, v) :: gs) = (a, if a = "EXPORTS" then .list [] else eraseV v) :: eraseVf gs :=
  rfl

theorem eraseVs_eq_map : ∀ vs : List Value, eraseVs vs = vs.map eraseV
  | [] => rfl
  | v :: vs => by simp only [eraseVs, eraseVs_eq_map vs, List.map_cons]

@[simp] theorem eraseV_list' (vs : List Value) : eraseV (.list vs) = .list (vs.map eraseV) := by
  rw [eraseV_list, eraseVs_eq_map]

@[simp] theorem eraseV_tuple' (vs : List Value) : eraseV (.tuple vs) = .tuple (vs.map eraseV) := by
  rw [eraseV_tuple, eraseVs_eq_map]

@[simp] theorem eraseV_opt (o : Option Value) : eraseV (.opt o) = .opt (o.map eraseV) := by
  cases o <;> rfl

@[simp] theorem hasExp_nil : hasExp [] = false := rfl
@[simp] theorem hasExp_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    hasExp ((a, v) :: gs) = (a == "EXPORTS" || hasExp gs) := rfl

/-- `eraseVf` keeps the field names. -/
@[simp] theorem hasExp_eraseVf : ∀ gs : List (IL.AtomS × Value), hasExp (eraseVf gs) = hasExp gs
  | [] => rfl
  | (a, v) :: gs => by simp only [eraseVf_cons, hasExp_cons, hasExp_eraseVf gs]

@[simp] theorem AllIn_tuple (Q : Value → Prop) (vs : List Value) :
    AllIn Q (.tuple vs) = AllIns Q vs := rfl
@[simp] theorem AllIn_case (Q : Value → Prop) (op : IL.MixopS) (w : Value) :
    AllIn Q (.case op w) = AllIn Q w := rfl
@[simp] theorem AllIn_struct (Q : Value → Prop) (gs : List (IL.AtomS × Value)) :
    AllIn Q (.struct gs) = ((hasExp gs = true → Q (.struct gs)) ∧ AllInf Q gs) := rfl
@[simp] theorem AllIn_list (Q : Value → Prop) (vs : List Value) :
    AllIn Q (.list vs) = AllIns Q vs := rfl
@[simp] theorem AllIns_nil (Q : Value → Prop) : AllIns Q [] = True := rfl
@[simp] theorem AllIns_cons (Q : Value → Prop) (v : Value) (vs : List Value) :
    AllIns Q (v :: vs) = (AllIn Q v ∧ AllIns Q vs) := rfl
@[simp] theorem AllInf_nil (Q : Value → Prop) : AllInf Q [] = True := rfl
@[simp] theorem AllInf_cons (Q : Value → Prop) (a : IL.AtomS) (v : Value)
    (gs : List (IL.AtomS × Value)) : AllInf Q ((a, v) :: gs) = (AllIn Q v ∧ AllInf Q gs) := rfl

theorem allIns_iff (Q : Value → Prop) : ∀ vs : List Value, AllIns Q vs ↔ ∀ v ∈ vs, AllIn Q v
  | [] => by simp
  | v :: vs => by simp [allIns_iff Q vs]

@[simp] theorem nxB_bool (b : Bool) : nxB (.bool b) = true := rfl
@[simp] theorem nxB_num (n : IL.Num) : nxB (.num n) = true := rfl
@[simp] theorem nxB_text (t : IL.Text) : nxB (.text t) = true := rfl
@[simp] theorem nxB_tuple (vs : List Value) : nxB (.tuple vs) = nxBs vs := rfl
@[simp] theorem nxB_case (op : IL.MixopS) (w : Value) : nxB (.case op w) = nxB w := rfl
@[simp] theorem nxB_struct (gs : List (IL.AtomS × Value)) : nxB (.struct gs) = nxBf gs := rfl
@[simp] theorem nxB_list (vs : List Value) : nxB (.list vs) = nxBs vs := rfl
@[simp] theorem nxB_opt_none : nxB (.opt none) = true := rfl
@[simp] theorem nxB_opt_some (w : Value) : nxB (.opt (some w)) = nxB w := rfl
@[simp] theorem nxBs_nil : nxBs [] = true := rfl
@[simp] theorem nxBs_cons (v : Value) (vs : List Value) :
    nxBs (v :: vs) = (nxB v && nxBs vs) := rfl
@[simp] theorem nxBf_nil : nxBf [] = true := rfl
@[simp] theorem nxBf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    nxBf ((a, v) :: gs) = (nxB v && (a != "EXPORTS") && nxBf gs) := rfl

theorem nxBs_eq_all : ∀ vs : List Value, nxBs vs = vs.all nxB
  | [] => rfl
  | v :: vs => by simp [nxBs_eq_all vs]

@[simp] theorem nxBs_map {α : Type} (f : α → Value) (l : List α) :
    nxBs (l.map f) = l.all fun a => nxB (f a) := by
  rw [nxBs_eq_all, List.all_map]; rfl

@[simp] theorem nxB_opt_map {α : Type} (f : α → Value) (o : Option α) :
    nxB (.opt (o.map f)) = o.all fun a => nxB (f a) := by
  cases o <;> rfl

/-- Close `nxB e = true` for an encoder applied to a constructor, splitting nested finite
arguments. -/
syntax "nxb_leaf" : tactic
macro_rules
  | `(tactic| nxb_leaf) => `(tactic| first | rfl | (rename_i x; cases x; all_goals nxb_leaf))

/-! ## `eraseV` fixes export-free values -/

mutual
theorem eraseV_of_efB : ∀ v : Value, efB v = true → eraseV v = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by
    rw [eraseV_tuple, eraseVs_of_efBs vs h]
  | .case _ w, h => by
    rw [eraseV_case, eraseV_of_efB w h]
  | .struct gs, h => by
    rw [eraseV_struct, eraseVf_of_efBf gs h]
  | .list vs, h => by
    rw [eraseV_list, eraseVs_of_efBs vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by
    rw [eraseV_opt_some, eraseV_of_efB w h]

theorem eraseVs_of_efBs : ∀ vs : List Value, efBs vs = true → eraseVs vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [efBs, Bool.and_eq_true] at h
    simp only [eraseVs, eraseV_of_efB v h.1, eraseVs_of_efBs vs h.2]

theorem eraseVf_of_efBf : ∀ gs : List (IL.AtomS × Value), efBf gs = true → eraseVf gs = gs
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [efBf, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hv, ha⟩, hg⟩ := h
    rw [eraseVf_cons, eraseVf_of_efBf gs hg]
    by_cases hx : a = "EXPORTS"
    · rcases ha with ha | ha
      · exact absurd hx ha
      · rw [ite_eq_left hx, isNilList_eq ha]
    · rw [ite_eq_right hx, eraseV_of_efB v hv]
end

/-! ## Values without `EXPORTS` records -/

mutual
theorem allIn_of_nxB (Q : Value → Prop) : ∀ v : Value, nxB v = true → AllIn Q v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => allIns_of_nxBs Q vs h
  | .case _ w, h => allIn_of_nxB Q w h
  | .struct gs, h => ⟨fun he => absurd he (by rw [hasExp_false_of_nxBf gs h]; simp),
      allInf_of_nxBf Q gs h⟩
  | .list vs, h => allIns_of_nxBs Q vs h
  | .opt none, _ => trivial
  | .opt (some w), h => allIn_of_nxB Q w h

theorem allIns_of_nxBs (Q : Value → Prop) : ∀ vs : List Value, nxBs vs = true → AllIns Q vs
  | [], _ => trivial
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true] at h
    exact ⟨allIn_of_nxB Q v h.1, allIns_of_nxBs Q vs h.2⟩

theorem allInf_of_nxBf (Q : Value → Prop) :
    ∀ gs : List (IL.AtomS × Value), nxBf gs = true → AllInf Q gs
  | [], _ => trivial
  | (_, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true] at h
    exact ⟨allIn_of_nxB Q v h.1.1, allInf_of_nxBf Q gs h.2⟩

theorem hasExp_false_of_nxBf : ∀ gs : List (IL.AtomS × Value), nxBf gs = true → hasExp gs = false
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [hasExp_cons, hasExp_false_of_nxBf gs h.2, Bool.or_false, beq_eq_false_iff_ne,
      ne_eq]
    exact h.1.2
end

/-! ## `AllIn` is monotone -/

mutual
theorem AllIn.mono {Q Q' : Value → Prop} (hQ : ∀ r, Q r → Q' r) :
    ∀ v : Value, AllIn Q v → AllIn Q' v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => AllIns.mono hQ vs h
  | .case _ w, h => AllIn.mono hQ w h
  | .struct gs, h => ⟨fun he => hQ _ (h.1 he), AllInf.mono hQ gs h.2⟩
  | .list vs, h => AllIns.mono hQ vs h
  | .opt none, _ => trivial
  | .opt (some w), h => AllIn.mono hQ w h

theorem AllIns.mono {Q Q' : Value → Prop} (hQ : ∀ r, Q r → Q' r) :
    ∀ vs : List Value, AllIns Q vs → AllIns Q' vs
  | [], _ => trivial
  | v :: vs, h => ⟨AllIn.mono hQ v h.1, AllIns.mono hQ vs h.2⟩

theorem AllInf.mono {Q Q' : Value → Prop} (hQ : ∀ r, Q r → Q' r) :
    ∀ gs : List (IL.AtomS × Value), AllInf Q gs → AllInf Q' gs
  | [], _ => trivial
  | (_, v) :: gs, h => ⟨AllIn.mono hQ v h.1, AllInf.mono hQ gs h.2⟩
end

/-! ## `unerase` inverts `eraseV` -/

section Inverse

variable {Q : Value → Prop}

theorem unerase_struct_exp (hQ : QInj Q) {gs : List (IL.AtomS × Value)}
    (he : hasExp gs = true) (hq : Q (.struct gs)) :
    unerase Q (.struct (eraseVf gs)) = .struct gs := by
  have hex : hasExp (eraseVf gs) = true ∧
      ∃ r, Q r ∧ eraseV r = .struct (eraseVf gs) := ⟨by rw [hasExp_eraseVf]; exact he,
    ⟨.struct gs, hq, rfl⟩⟩
  simp only [unerase, dite_eq_left hex]
  obtain ⟨hr, hre⟩ := hex.2.choose_spec
  exact hQ _ _ hr hq hre

mutual
theorem unerase_eraseV (hQ : QInj Q) : ∀ v : Value, AllIn Q v → unerase Q (eraseV v) = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by
    simp only [eraseV_tuple, unerase, uneraseS_eraseVs hQ vs h]
  | .case _ w, h => by
    simp only [eraseV_case, unerase, unerase_eraseV hQ w h]
  | .struct gs, h => by
    by_cases he : hasExp gs = true
    · exact unerase_struct_exp hQ he (h.1 he)
    · have hn : ¬ (hasExp (eraseVf gs) = true ∧
          ∃ r, Q r ∧ eraseV r = .struct (eraseVf gs)) := by
        rw [hasExp_eraseVf]; exact fun h' => he h'.1
      simp only [eraseV_struct, unerase, dite_eq_right hn]
      rw [uneraseF_eraseVf hQ gs (by simpa using he) h.2]
  | .list vs, h => by
    simp only [eraseV_list, unerase, uneraseS_eraseVs hQ vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by
    simp only [eraseV_opt_some, unerase, unerase_eraseV hQ w h]

theorem uneraseS_eraseVs (hQ : QInj Q) :
    ∀ vs : List Value, AllIns Q vs → uneraseS Q (eraseVs vs) = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [eraseVs, uneraseS, unerase_eraseV hQ v h.1, uneraseS_eraseVs hQ vs h.2]

theorem uneraseF_eraseVf (hQ : QInj Q) :
    ∀ gs : List (IL.AtomS × Value), hasExp gs = false → AllInf Q gs →
      uneraseF Q (eraseVf gs) = gs
  | [], _, _ => rfl
  | (a, v) :: gs, he, h => by
    simp only [hasExp_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at he
    simp only [eraseVf_cons, ite_eq_right he.1, uneraseF, unerase_eraseV hQ v h.1,
      uneraseF_eraseVf hQ gs he.2 h.2]
end

/-- **`eraseV` is injective on `AllIn Q` values** when it is injective on `Q`. -/
theorem eraseV_inj (hQ : QInj Q) {v₁ v₂ : Value} (h₁ : AllIn Q v₁) (h₂ : AllIn Q v₂)
    (h : eraseV v₁ = eraseV v₂) : v₁ = v₂ := by
  rw [← unerase_eraseV hQ v₁ h₁, h, unerase_eraseV hQ v₂ h₂]

end Inverse

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
