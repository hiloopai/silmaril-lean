module

public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs

/-!
# Round 8, function code erasure: `eraseC` is injective (copied from round 7's `Swap/Basic`)

Copied mechanically from round 7 (export erasure) with `EXPORTS` read as `CODE` and
`eraseV` as `eraseC`; where the prose below speaks of export lists, module records or the swap
set `QC c`, it describes the original. Here every value is in the swap set (`fun _ => True`).

* simp lemmas for `eraseC`, `ncB`, `AllIn` and `hasCode` on the value constructors;
* `allIn_of_ncB`: a value without `CODE` records is `AllIn Q` for every `Q`;
* `unerase_eraseC`, `eraseC_inj`: under `QInj Q`, `eraseC` is injective on `AllIn Q` values, with
  left inverse `unerase Q`;
* `AllIn.mono`: `AllIn` is monotone in `Q`;
* `codeN_inj`, `hostC_inj`, `eraseC_injective`, `qInj`: `eraseC` is injective, so `QInj Q`
  holds for every `Q`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## Unfolding -/

@[simp] theorem eraseC_bool (b : Bool) : eraseC (.bool b) = .bool b := rfl
@[simp] theorem eraseC_num (n : IL.Num) : eraseC (.num n) = .num n := rfl
@[simp] theorem eraseC_text (t : IL.Text) : eraseC (.text t) = .text t := rfl
@[simp] theorem eraseC_tuple (vs : List Value) : eraseC (.tuple vs) = .tuple (eraseCs vs) := rfl
@[simp] theorem eraseC_case (op : IL.MixopS) (w : Value) :
    eraseC (.case op w) = .case op (eraseC w) := rfl
@[simp] theorem eraseC_struct (gs : List (IL.AtomS × Value)) :
    eraseC (.struct gs) = .struct (eraseCf gs) := rfl
@[simp] theorem eraseC_list (vs : List Value) : eraseC (.list vs) = .list (eraseCs vs) := rfl
@[simp] theorem eraseC_opt_none : eraseC (.opt none) = .opt none := rfl
@[simp] theorem eraseC_opt_some (w : Value) : eraseC (.opt (some w)) = .opt (some (eraseC w)) :=
  rfl
@[simp] theorem eraseCf_nil : eraseCf [] = [] := rfl
@[simp] theorem eraseCf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    eraseCf ((a, v) :: gs) = (a, if a = "CODE" then hostC v else eraseC v) :: eraseCf gs :=
  rfl

theorem eraseCs_eq_map : ∀ vs : List Value, eraseCs vs = vs.map eraseC
  | [] => rfl
  | v :: vs => by simp only [eraseCs, eraseCs_eq_map vs, List.map_cons]

@[simp] theorem eraseC_list' (vs : List Value) : eraseC (.list vs) = .list (vs.map eraseC) := by
  rw [eraseC_list, eraseCs_eq_map]

@[simp] theorem eraseC_tuple' (vs : List Value) : eraseC (.tuple vs) = .tuple (vs.map eraseC) := by
  rw [eraseC_tuple, eraseCs_eq_map]

@[simp] theorem eraseC_opt (o : Option Value) : eraseC (.opt o) = .opt (o.map eraseC) := by
  cases o <;> rfl

@[simp] theorem hasCode_nil : hasCode [] = false := rfl
@[simp] theorem hasCode_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    hasCode ((a, v) :: gs) = (a == "CODE" || hasCode gs) := rfl

/-- `eraseCf` keeps the field names. -/
@[simp] theorem hasCode_eraseCf : ∀ gs : List (IL.AtomS × Value), hasCode (eraseCf gs) = hasCode gs
  | [] => rfl
  | (a, v) :: gs => by simp only [eraseCf_cons, hasCode_cons, hasCode_eraseCf gs]

@[simp] theorem AllIn_tuple (Q : Value → Prop) (vs : List Value) :
    AllIn Q (.tuple vs) = AllIns Q vs := rfl
@[simp] theorem AllIn_case (Q : Value → Prop) (op : IL.MixopS) (w : Value) :
    AllIn Q (.case op w) = AllIn Q w := rfl
@[simp] theorem AllIn_struct (Q : Value → Prop) (gs : List (IL.AtomS × Value)) :
    AllIn Q (.struct gs) = ((hasCode gs = true → Q (.struct gs)) ∧ AllInf Q gs) := rfl
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

@[simp] theorem ncB_bool (b : Bool) : ncB (.bool b) = true := rfl
@[simp] theorem ncB_num (n : IL.Num) : ncB (.num n) = true := rfl
@[simp] theorem ncB_text (t : IL.Text) : ncB (.text t) = true := rfl
@[simp] theorem ncB_tuple (vs : List Value) : ncB (.tuple vs) = ncBs vs := rfl
@[simp] theorem ncB_case (op : IL.MixopS) (w : Value) : ncB (.case op w) = ncB w := rfl
@[simp] theorem ncB_struct (gs : List (IL.AtomS × Value)) : ncB (.struct gs) = ncBf gs := rfl
@[simp] theorem ncB_list (vs : List Value) : ncB (.list vs) = ncBs vs := rfl
@[simp] theorem ncB_opt_none : ncB (.opt none) = true := rfl
@[simp] theorem ncB_opt_some (w : Value) : ncB (.opt (some w)) = ncB w := rfl
@[simp] theorem ncBs_nil : ncBs [] = true := rfl
@[simp] theorem ncBs_cons (v : Value) (vs : List Value) :
    ncBs (v :: vs) = (ncB v && ncBs vs) := rfl
@[simp] theorem ncBf_nil : ncBf [] = true := rfl
@[simp] theorem ncBf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    ncBf ((a, v) :: gs) = (ncB v && (a != "CODE") && ncBf gs) := rfl

theorem ncBs_eq_all : ∀ vs : List Value, ncBs vs = vs.all ncB
  | [] => rfl
  | v :: vs => by simp [ncBs_eq_all vs]

@[simp] theorem ncBs_map {α : Type} (f : α → Value) (l : List α) :
    ncBs (l.map f) = l.all fun a => ncB (f a) := by
  rw [ncBs_eq_all, List.all_map]; rfl

@[simp] theorem ncB_opt_map {α : Type} (f : α → Value) (o : Option α) :
    ncB (.opt (o.map f)) = o.all fun a => ncB (f a) := by
  cases o <;> rfl

/-- Close `ncB e = true` for an encoder applied to a constructor, splitting nested finite
arguments. -/
syntax "nxb_leaf" : tactic
macro_rules
  | `(tactic| nxb_leaf) => `(tactic| first | rfl | (rename_i x; cases x; all_goals nxb_leaf))

/-! ## Values without `CODE` records -/

mutual
theorem allIn_of_ncB (Q : Value → Prop) : ∀ v : Value, ncB v = true → AllIn Q v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => allIns_of_ncBs Q vs h
  | .case _ w, h => allIn_of_ncB Q w h
  | .struct gs, h => ⟨fun he => absurd he (by rw [hasCode_false_of_ncBf gs h]; simp),
      allInf_of_ncBf Q gs h⟩
  | .list vs, h => allIns_of_ncBs Q vs h
  | .opt none, _ => trivial
  | .opt (some w), h => allIn_of_ncB Q w h

theorem allIns_of_ncBs (Q : Value → Prop) : ∀ vs : List Value, ncBs vs = true → AllIns Q vs
  | [], _ => trivial
  | v :: vs, h => by
    simp only [ncBs, Bool.and_eq_true] at h
    exact ⟨allIn_of_ncB Q v h.1, allIns_of_ncBs Q vs h.2⟩

theorem allInf_of_ncBf (Q : Value → Prop) :
    ∀ gs : List (IL.AtomS × Value), ncBf gs = true → AllInf Q gs
  | [], _ => trivial
  | (_, v) :: gs, h => by
    simp only [ncBf, Bool.and_eq_true] at h
    exact ⟨allIn_of_ncB Q v h.1.1, allInf_of_ncBf Q gs h.2⟩

theorem hasCode_false_of_ncBf : ∀ gs : List (IL.AtomS × Value), ncBf gs = true → hasCode gs = false
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [ncBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [hasCode_cons, hasCode_false_of_ncBf gs h.2, Bool.or_false, beq_eq_false_iff_ne,
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

/-! ## `unerase` inverts `eraseC` -/

section Inverse

variable {Q : Value → Prop}

theorem unerase_struct_exp (hQ : QInj Q) {gs : List (IL.AtomS × Value)}
    (he : hasCode gs = true) (hq : Q (.struct gs)) :
    unerase Q (.struct (eraseCf gs)) = .struct gs := by
  have hex : hasCode (eraseCf gs) = true ∧
      ∃ r, Q r ∧ eraseC r = .struct (eraseCf gs) := ⟨by rw [hasCode_eraseCf]; exact he,
    ⟨.struct gs, hq, rfl⟩⟩
  simp only [unerase, dite_eq_left hex]
  obtain ⟨hr, hre⟩ := hex.2.choose_spec
  exact hQ _ _ hr hq hre

mutual
theorem unerase_eraseC (hQ : QInj Q) : ∀ v : Value, AllIn Q v → unerase Q (eraseC v) = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by
    simp only [eraseC_tuple, unerase, uneraseS_eraseCs hQ vs h]
  | .case _ w, h => by
    simp only [eraseC_case, unerase, unerase_eraseC hQ w h]
  | .struct gs, h => by
    by_cases he : hasCode gs = true
    · exact unerase_struct_exp hQ he (h.1 he)
    · have hn : ¬ (hasCode (eraseCf gs) = true ∧
          ∃ r, Q r ∧ eraseC r = .struct (eraseCf gs)) := by
        rw [hasCode_eraseCf]; exact fun h' => he h'.1
      simp only [eraseC_struct, unerase, dite_eq_right hn]
      rw [uneraseF_eraseCf hQ gs (by simpa using he) h.2]
  | .list vs, h => by
    simp only [eraseC_list, unerase, uneraseS_eraseCs hQ vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by
    simp only [eraseC_opt_some, unerase, unerase_eraseC hQ w h]

theorem uneraseS_eraseCs (hQ : QInj Q) :
    ∀ vs : List Value, AllIns Q vs → uneraseS Q (eraseCs vs) = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [eraseCs, uneraseS, unerase_eraseC hQ v h.1, uneraseS_eraseCs hQ vs h.2]

theorem uneraseF_eraseCf (hQ : QInj Q) :
    ∀ gs : List (IL.AtomS × Value), hasCode gs = false → AllInf Q gs →
      uneraseF Q (eraseCf gs) = gs
  | [], _, _ => rfl
  | (a, v) :: gs, he, h => by
    simp only [hasCode_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at he
    simp only [eraseCf_cons, ite_eq_right he.1, uneraseF, unerase_eraseC hQ v h.1,
      uneraseF_eraseCf hQ gs he.2 h.2]
end

/-- **`eraseC` is injective on `AllIn Q` values** when it is injective on `Q`. -/
theorem eraseC_inj (hQ : QInj Q) {v₁ v₂ : Value} (h₁ : AllIn Q v₁) (h₂ : AllIn Q v₂)
    (h : eraseC v₁ = eraseC v₂) : v₁ = v₂ := by
  rw [← unerase_eraseC hQ v₁ h₁, h, unerase_eraseC hQ v₂ h₂]

end Inverse


/-! ## `eraseC` is injective -/

theorem natsN_inj : ∀ {xs ys : List ℕ}, natsN xs = natsN ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [natsN] at h
  | _ :: _, [], h => by simp [natsN] at h
  | x :: xs, y :: ys, h => by
    simp only [natsN, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    rw [h.1, natsN_inj h.2]

theorem strN_inj {s t : String} (h : strN s = strN t) : s = t := by
  have h' := List.map_injective_iff.2 (fun a b (hab : Char.toNat a = Char.toNat b) =>
    Char.ext (UInt32.toNat_inj.1 hab)) (natsN_inj h)
  exact String.toList_inj.1 h'

theorem intN_inj {i j : Int} (h : intN i = intN j) : i = j := by
  simp only [intN, Nat.pair_eq_pair] at h
  omega

theorem numN_inj : ∀ {m n : IL.Num}, numN m = numN n → m = n := by
  intro m n h
  cases m <;> cases n <;> simp only [numN, Nat.pair_eq_pair] at h <;>
    try (obtain ⟨h₀, -⟩ := h; omega)
  · rw [h.2]
  · rw [intN_inj h.2]
  · obtain ⟨-, h₁, h₂⟩ := h
    rw [Rat.ext (intN_inj h₁) h₂]
  · rw [strN_inj h.2]

mutual
theorem codeN_inj : ∀ {v w : Value}, codeN v = codeN w → v = w
  | .bool a, .bool b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    cases a <;> cases b <;> simp_all
  | .num a, .num b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [numN_inj h.2]
  | .text a, .text b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [strN_inj h.2]
  | .tuple a, .tuple b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [codeNs_inj h.2]
  | .case o a, .case p b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [strN_inj h.2.1, codeN_inj h.2.2]
  | .struct a, .struct b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [codeNf_inj h.2]
  | .list a, .list b, h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [codeNs_inj h.2]
  | .opt none, .opt none, _ => rfl
  | .opt (some a), .opt (some b), h => by
    simp only [codeN, Nat.pair_eq_pair] at h
    rw [codeN_inj h.2]
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
    simp only [codeN, Nat.pair_eq_pair] at h
    omega

theorem codeNs_inj : ∀ {vs ws : List Value}, codeNs vs = codeNs ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [codeNs] at h
  | _ :: _, [], h => by simp [codeNs] at h
  | v :: vs, w :: ws, h => by
    simp only [codeNs, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    rw [codeN_inj h.1, codeNs_inj h.2]

theorem codeNf_inj : ∀ {gs hs : List (IL.AtomS × Value)}, codeNf gs = codeNf hs → gs = hs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [codeNf] at h
  | _ :: _, [], h => by simp [codeNf] at h
  | (a, v) :: gs, (b, w) :: hs, h => by
    simp only [codeNf, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    rw [strN_inj h.1.1, codeN_inj h.1.2, codeNf_inj h.2]
end

theorem enc_inj {v w : Value} (h : enc v = enc w) : v = w := by
  have := congrArg String.length h
  simp only [enc, String.length_ofList, List.length_replicate] at this
  exact codeN_inj this

theorem hostC_inj {v w : Value} (h : hostC v = hostC w) : v = w := by
  simp only [hostC, Value.case.injEq, Value.text.injEq, true_and] at h
  exact enc_inj h

mutual
theorem eraseC_injective : ∀ {v w : Value}, eraseC v = eraseC w → v = w
  | .bool _, .bool _, h | .num _, .num _, h | .text _, .text _, h => by
    simpa using h
  | .tuple a, .tuple b, h => by
    simp only [eraseC_tuple, Value.tuple.injEq] at h
    rw [eraseCs_injective h]
  | .case o a, .case p b, h => by
    simp only [eraseC_case, Value.case.injEq] at h
    rw [h.1, eraseC_injective h.2]
  | .struct a, .struct b, h => by
    simp only [eraseC_struct, Value.struct.injEq] at h
    rw [eraseCf_injective h]
  | .list a, .list b, h => by
    simp only [eraseC_list, Value.list.injEq] at h
    rw [eraseCs_injective h]
  | .opt none, .opt none, _ => rfl
  | .opt (some a), .opt (some b), h => by
    simp only [eraseC_opt_some, Value.opt.injEq, Option.some.injEq] at h
    rw [eraseC_injective h]
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

theorem eraseCs_injective : ∀ {vs ws : List Value}, eraseCs vs = eraseCs ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eraseCs] at h
  | _ :: _, [], h => by simp [eraseCs] at h
  | v :: vs, w :: ws, h => by
    simp only [eraseCs, List.cons.injEq] at h
    rw [eraseC_injective h.1, eraseCs_injective h.2]

theorem eraseCf_injective :
    ∀ {gs hs : List (IL.AtomS × Value)}, eraseCf gs = eraseCf hs → gs = hs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eraseCf] at h
  | _ :: _, [], h => by simp [eraseCf] at h
  | (a, v) :: gs, (b, w) :: hs, h => by
    simp only [eraseCf_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, hv⟩, hg⟩ := h
    rw [eraseCf_injective hg]
    by_cases ha : a = "CODE"
    · rw [ite_eq_left ha, ite_eq_left ha] at hv
      rw [hostC_inj hv]
    · rw [ite_eq_right ha, ite_eq_right ha] at hv
      rw [eraseC_injective hv]
end

/-- **`QInj Q` holds for every `Q`.** -/
theorem qInj (Q : Value → Prop) : QInj Q := fun _ _ _ _ h => eraseC_injective h

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
