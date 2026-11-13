module

public import Silmaril.Wasm.SpecTec.Sim20.XSwap.Defs

/-!
# function code erasure: `swapX` is injective (copied 's `Swap/Basic`)

Round 9 copy 's `Round8.CodeErase` (itself a copy 's export erasure) for
`EXPORTS` fields with an arbitrary injective replacement `XTau.τ` (`swapX`); the prose below,
written for the earlier copies, speaks of erasure. Every value is in the swap set (`fun _ => True`).

* simp lemmas for `swapX`, `nxX`, `AllIn` and `hasExpX` on the value constructors;
* `allIn_of_ncB`: a value without `EXPORTS` records is `AllIn Q` for every `Q`;
* `unerase_eraseC`, `swapX_inj`: under `QInj Q`, `swapX` is injective on `AllIn Q` values, with
  left inverse `unerase Q`;
* `AllIn.mono`: `AllIn` is monotone in `Q`;
* `codeN_inj`, `XTau.inj`, `swapX_injective`, `qInj`: `swapX` is injective, so `QInj Q`
  holds for every `Q`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Unfolding -/

@[simp] theorem swapX_bool (b : Bool) : swapX (.bool b) = .bool b := rfl
@[simp] theorem swapX_num (n : IL.Num) : swapX (.num n) = .num n := rfl
@[simp] theorem swapX_text (t : IL.Text) : swapX (.text t) = .text t := rfl
@[simp] theorem swapX_tuple (vs : List Value) : swapX (.tuple vs) = .tuple (swapXs vs) := rfl
@[simp] theorem swapX_case (op : IL.MixopS) (w : Value) :
    swapX (.case op w) = .case op (swapX w) := rfl
@[simp] theorem swapX_struct (gs : List (IL.AtomS × Value)) :
    swapX (.struct gs) = .struct (swapXf gs) := rfl
@[simp] theorem swapX_list (vs : List Value) : swapX (.list vs) = .list (swapXs vs) := rfl
@[simp] theorem swapX_opt_none : swapX (.opt none) = .opt none := rfl
@[simp] theorem swapX_opt_some (w : Value) : swapX (.opt (some w)) = .opt (some (swapX w)) :=
  rfl
@[simp] theorem swapXf_nil : swapXf [] = [] := rfl
@[simp] theorem swapXf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    swapXf ((a, v) :: gs) = (a, if a = "EXPORTS" then XTau.τ v else swapX v) :: swapXf gs :=
  rfl

theorem swapXs_eq_map : ∀ vs : List Value, swapXs vs = vs.map swapX
  | [] => rfl
  | v :: vs => by simp only [swapXs, swapXs_eq_map vs, List.map_cons]

@[simp] theorem swapX_list' (vs : List Value) : swapX (.list vs) = .list (vs.map swapX) := by
  rw [swapX_list, swapXs_eq_map]

@[simp] theorem swapX_tuple' (vs : List Value) : swapX (.tuple vs) = .tuple (vs.map swapX) := by
  rw [swapX_tuple, swapXs_eq_map]

@[simp] theorem swapX_opt (o : Option Value) : swapX (.opt o) = .opt (o.map swapX) := by
  cases o <;> rfl

@[simp] theorem hasExpX_nil : hasExpX [] = false := rfl
@[simp] theorem hasExpX_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    hasExpX ((a, v) :: gs) = (a == "EXPORTS" || hasExpX gs) := rfl

/-- `swapXf` keeps the field names. -/
@[simp] theorem hasExpX_eraseCf : ∀ gs : List (IL.AtomS × Value), hasExpX (swapXf gs) = hasExpX gs
  | [] => rfl
  | (a, v) :: gs => by simp only [swapXf_cons, hasExpX_cons, hasExpX_eraseCf gs]

@[simp] theorem AllIn_tuple (Q : Value → Prop) (vs : List Value) :
    AllIn Q (.tuple vs) = AllIns Q vs := rfl
@[simp] theorem AllIn_case (Q : Value → Prop) (op : IL.MixopS) (w : Value) :
    AllIn Q (.case op w) = AllIn Q w := rfl
@[simp] theorem AllIn_struct (Q : Value → Prop) (gs : List (IL.AtomS × Value)) :
    AllIn Q (.struct gs) = ((hasExpX gs = true → Q (.struct gs)) ∧ AllInf Q gs) := rfl
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

@[simp] theorem nxX_bool (b : Bool) : nxX (.bool b) = true := rfl
@[simp] theorem nxX_num (n : IL.Num) : nxX (.num n) = true := rfl
@[simp] theorem nxX_text (t : IL.Text) : nxX (.text t) = true := rfl
@[simp] theorem nxX_tuple (vs : List Value) : nxX (.tuple vs) = nxXs vs := rfl
@[simp] theorem nxX_case (op : IL.MixopS) (w : Value) : nxX (.case op w) = nxX w := rfl
@[simp] theorem nxX_struct (gs : List (IL.AtomS × Value)) : nxX (.struct gs) = nxXf gs := rfl
@[simp] theorem nxX_list (vs : List Value) : nxX (.list vs) = nxXs vs := rfl
@[simp] theorem nxX_opt_none : nxX (.opt none) = true := rfl
@[simp] theorem nxX_opt_some (w : Value) : nxX (.opt (some w)) = nxX w := rfl
@[simp] theorem nxXs_nil : nxXs [] = true := rfl
@[simp] theorem nxXs_cons (v : Value) (vs : List Value) :
    nxXs (v :: vs) = (nxX v && nxXs vs) := rfl
@[simp] theorem nxXf_nil : nxXf [] = true := rfl
@[simp] theorem nxXf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    nxXf ((a, v) :: gs) = (nxX v && (a != "EXPORTS") && nxXf gs) := rfl

theorem nxXs_eq_all : ∀ vs : List Value, nxXs vs = vs.all nxX
  | [] => rfl
  | v :: vs => by simp [nxXs_eq_all vs]

@[simp] theorem nxXs_map {α : Type} (f : α → Value) (l : List α) :
    nxXs (l.map f) = l.all fun a => nxX (f a) := by
  rw [nxXs_eq_all, List.all_map]; rfl

@[simp] theorem nxX_opt_map {α : Type} (f : α → Value) (o : Option α) :
    nxX (.opt (o.map f)) = o.all fun a => nxX (f a) := by
  cases o <;> rfl

/-- Close `nxX e = true` for an encoder applied to a constructor, splitting nested finite
arguments. -/
syntax "xswap_leaf" : tactic
macro_rules
  | `(tactic| xswap_leaf) => `(tactic| first | rfl | (rename_i x; cases x; all_goals xswap_leaf))

/-! ## Values without `EXPORTS` records -/

mutual
theorem allIn_of_ncB (Q : Value → Prop) : ∀ v : Value, nxX v = true → AllIn Q v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => allIns_of_ncBs Q vs h
  | .case _ w, h => allIn_of_ncB Q w h
  | .struct gs, h => ⟨fun he => absurd he (by rw [hasExpX_false_of_ncBf gs h]; simp),
      allInf_of_ncBf Q gs h⟩
  | .list vs, h => allIns_of_ncBs Q vs h
  | .opt none, _ => trivial
  | .opt (some w), h => allIn_of_ncB Q w h

theorem allIns_of_ncBs (Q : Value → Prop) : ∀ vs : List Value, nxXs vs = true → AllIns Q vs
  | [], _ => trivial
  | v :: vs, h => by
    simp only [nxXs, Bool.and_eq_true] at h
    exact ⟨allIn_of_ncB Q v h.1, allIns_of_ncBs Q vs h.2⟩

theorem allInf_of_ncBf (Q : Value → Prop) :
    ∀ gs : List (IL.AtomS × Value), nxXf gs = true → AllInf Q gs
  | [], _ => trivial
  | (_, v) :: gs, h => by
    simp only [nxXf, Bool.and_eq_true] at h
    exact ⟨allIn_of_ncB Q v h.1.1, allInf_of_ncBf Q gs h.2⟩

theorem hasExpX_false_of_ncBf : ∀ gs : List (IL.AtomS × Value), nxXf gs = true → hasExpX gs = false
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxXf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [hasExpX_cons, hasExpX_false_of_ncBf gs h.2, Bool.or_false, beq_eq_false_iff_ne,
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

/-! ## `unerase` inverts `swapX` -/

section Inverse

variable {Q : Value → Prop}

theorem unerase_struct_exp (hQ : QInj Q) {gs : List (IL.AtomS × Value)}
    (he : hasExpX gs = true) (hq : Q (.struct gs)) :
    unerase Q (.struct (swapXf gs)) = .struct gs := by
  have hex : hasExpX (swapXf gs) = true ∧
      ∃ r, Q r ∧ swapX r = .struct (swapXf gs) := ⟨by rw [hasExpX_eraseCf]; exact he,
    ⟨.struct gs, hq, rfl⟩⟩
  simp only [unerase, dite_eq_left hex]
  obtain ⟨hr, hre⟩ := hex.2.choose_spec
  exact hQ _ _ hr hq hre

mutual
theorem unerase_eraseC (hQ : QInj Q) : ∀ v : Value, AllIn Q v → unerase Q (swapX v) = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by
    simp only [swapX_tuple, unerase, uneraseS_eraseCs hQ vs h]
  | .case _ w, h => by
    simp only [swapX_case, unerase, unerase_eraseC hQ w h]
  | .struct gs, h => by
    by_cases he : hasExpX gs = true
    · exact unerase_struct_exp hQ he (h.1 he)
    · have hn : ¬ (hasExpX (swapXf gs) = true ∧
          ∃ r, Q r ∧ swapX r = .struct (swapXf gs)) := by
        rw [hasExpX_eraseCf]; exact fun h' => he h'.1
      simp only [swapX_struct, unerase, dite_eq_right hn]
      rw [uneraseF_eraseCf hQ gs (by simpa using he) h.2]
  | .list vs, h => by
    simp only [swapX_list, unerase, uneraseS_eraseCs hQ vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by
    simp only [swapX_opt_some, unerase, unerase_eraseC hQ w h]

theorem uneraseS_eraseCs (hQ : QInj Q) :
    ∀ vs : List Value, AllIns Q vs → uneraseS Q (swapXs vs) = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [swapXs, uneraseS, unerase_eraseC hQ v h.1, uneraseS_eraseCs hQ vs h.2]

theorem uneraseF_eraseCf (hQ : QInj Q) :
    ∀ gs : List (IL.AtomS × Value), hasExpX gs = false → AllInf Q gs →
      uneraseF Q (swapXf gs) = gs
  | [], _, _ => rfl
  | (a, v) :: gs, he, h => by
    simp only [hasExpX_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at he
    simp only [swapXf_cons, ite_eq_right he.1, uneraseF, unerase_eraseC hQ v h.1,
      uneraseF_eraseCf hQ gs he.2 h.2]
end

/-- **`swapX` is injective on `AllIn Q` values** when it is injective on `Q`. -/
theorem swapX_inj (hQ : QInj Q) {v₁ v₂ : Value} (h₁ : AllIn Q v₁) (h₂ : AllIn Q v₂)
    (h : swapX v₁ = swapX v₂) : v₁ = v₂ := by
  rw [← unerase_eraseC hQ v₁ h₁, h, unerase_eraseC hQ v₂ h₂]

end Inverse


/-! ## `swapX` is injective -/

mutual
theorem swapX_injective : ∀ {v w : Value}, swapX v = swapX w → v = w
  | .bool _, .bool _, h | .num _, .num _, h | .text _, .text _, h => by
    simpa using h
  | .tuple a, .tuple b, h => by
    simp only [swapX_tuple, Value.tuple.injEq] at h
    rw [swapXs_injective h]
  | .case o a, .case p b, h => by
    simp only [swapX_case, Value.case.injEq] at h
    rw [h.1, swapX_injective h.2]
  | .struct a, .struct b, h => by
    simp only [swapX_struct, Value.struct.injEq] at h
    rw [swapXf_injective h]
  | .list a, .list b, h => by
    simp only [swapX_list, Value.list.injEq] at h
    rw [swapXs_injective h]
  | .opt none, .opt none, _ => rfl
  | .opt (some a), .opt (some b), h => by
    simp only [swapX_opt_some, Value.opt.injEq, Option.some.injEq] at h
    rw [swapX_injective h]
  | .bool _, .num _, h | .bool _, .text _, h | .bool _, .tuple _, h | .bool _, .case _ _, h
  | .bool _, .struct _, h | .bool _, .list _, h | .bool _, .opt none, h
  | .bool _, .opt (some _), h
  | .num _, .bool _, h | .num _, .text _, h | .num _, .tuple _, h | .num _, .case _ _, h
  | .num _, .struct _, h | .num _, .list _, h | .num _, .opt none, h
  | .num _, .opt (some _), h
  | .text _, .bool _, h | .text _, .num _, h | .text _, .tuple _, h | .text _, .case _ _, h
  | .text _, .struct _, h | .text _, .list _, h | .text _, .opt none, h
  | .text _, .opt (some _), h
  | .tuple _, .bool _, h | .tuple _, .num _, h | .tuple _, .text _, h | .tuple _, .case _ _, h
  | .tuple _, .struct _, h | .tuple _, .list _, h | .tuple _, .opt none, h
  | .tuple _, .opt (some _), h
  | .case _ _, .bool _, h | .case _ _, .num _, h | .case _ _, .text _, h
  | .case _ _, .tuple _, h | .case _ _, .struct _, h | .case _ _, .list _, h
  | .case _ _, .opt none, h | .case _ _, .opt (some _), h
  | .struct _, .bool _, h | .struct _, .num _, h | .struct _, .text _, h
  | .struct _, .tuple _, h | .struct _, .case _ _, h | .struct _, .list _, h
  | .struct _, .opt none, h | .struct _, .opt (some _), h
  | .list _, .bool _, h | .list _, .num _, h | .list _, .text _, h | .list _, .tuple _, h
  | .list _, .case _ _, h | .list _, .struct _, h | .list _, .opt none, h
  | .list _, .opt (some _), h
  | .opt none, .bool _, h | .opt none, .num _, h | .opt none, .text _, h
  | .opt none, .tuple _, h | .opt none, .case _ _, h | .opt none, .struct _, h
  | .opt none, .list _, h | .opt none, .opt (some _), h
  | .opt (some _), .bool _, h | .opt (some _), .num _, h | .opt (some _), .text _, h
  | .opt (some _), .tuple _, h | .opt (some _), .case _ _, h | .opt (some _), .struct _, h
  | .opt (some _), .list _, h | .opt (some _), .opt none, h => by
    simp at h

theorem swapXs_injective : ∀ {vs ws : List Value}, swapXs vs = swapXs ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [swapXs] at h
  | _ :: _, [], h => by simp [swapXs] at h
  | v :: vs, w :: ws, h => by
    simp only [swapXs, List.cons.injEq] at h
    rw [swapX_injective h.1, swapXs_injective h.2]

theorem swapXf_injective :
    ∀ {gs hs : List (IL.AtomS × Value)}, swapXf gs = swapXf hs → gs = hs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [swapXf] at h
  | _ :: _, [], h => by simp [swapXf] at h
  | (a, v) :: gs, (b, w) :: hs, h => by
    simp only [swapXf_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, hv⟩, hg⟩ := h
    rw [swapXf_injective hg]
    by_cases ha : a = "EXPORTS"
    · rw [ite_eq_left ha, ite_eq_left ha] at hv
      rw [XTau.inj hv]
    · rw [ite_eq_right ha, ite_eq_right ha] at hv
      rw [swapX_injective hv]
end

/-- **`QInj Q` holds for every `Q`.** -/
theorem qInj (Q : Value → Prop) : QInj Q := fun _ _ _ _ h => swapX_injective h

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
