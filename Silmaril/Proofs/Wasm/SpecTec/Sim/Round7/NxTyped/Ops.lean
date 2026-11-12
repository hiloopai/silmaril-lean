module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxTyped.Value
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# Round 7, REH route 2: the value operations of the evaluator preserve conformance

For each value operation the evaluator applies, the conformance of the result follows from that
of the operands, at the abstract types the flow check assigns:

* reading: `vtB_field?` (`DotE`), `vtB_asCase?` (`UncaseE`), `vtB_proj` (`ProjE`),
  `vtB_elem` and `vtB_elemOpt` (`IdxE`, `TheE`, iteration domains), `vtB_elemOf`;
* building: `vtB_take`, `vtB_drop`, `vtB_slice?` (`SliceE`), `vtB_cat?` (`CatE`), `vtB_comp?`
  (`CompE`), `vtB_lift` (`LiftE`);
* writing: `vtB_setField`, `vtB_setIdx`, `vtB_setSlice` (`UpdE`, `ExtE`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {S : Sig}

/-! ## Unfolding conformance and element types -/

theorem elemAT_of_iter {a b : AT} (hu : unf S a = .iter b) : elemAT S a = b := by
  have h : unalias S 8 a = .iter b := hu
  simp only [elemAT, h]

theorem elemAT_of_not_iter {a : AT} (hu : ∀ b, unf S a ≠ .iter b) : elemAT S a = .unk := by
  have h : ∀ b, unalias S 8 a ≠ .iter b := hu
  unfold elemAT
  split
  · rename_i t ht
    exact absurd ht (h t)
  · rfl

theorem elemOf_of_iter {a b : AT} (ha : nxAT S.good a = false) (hu : unf S a = .iter b) :
    elemOf S a = b := by
  simp only [elemOf, ha, Bool.false_eq_true, ↓reduceIte, elemAT_of_iter hu]

theorem elemOf_of_not_iter {a : AT} (ha : nxAT S.good a = false)
    (hu : ∀ b, unf S a ≠ .iter b) : elemOf S a = .unk := by
  simp only [elemOf, ha, Bool.false_eq_true, ↓reduceIte, elemAT_of_not_iter hu]

theorem elemOf_of_nx {a : AT} (ha : nxAT S.good a = true) : elemOf S a = .base := by
  simp [elemOf, ha]

theorem vtB_base_iff {v : Value} : vtB S .base v = true ↔ nxB v = true :=
  ⟨nxB_of_vtB rfl, vtB_of_nxB S .base v⟩

theorem vtB_list_nx {a : AT} (ha : nxAT S.good a = true) (vs : List Value) :
    vtB S a (.list vs) = nxBs vs := by
  simp [vtB, ha]

theorem vtB_list_iter {a b : AT} (ha : nxAT S.good a = false) (hu : unf S a = .iter b)
    (vs : List Value) : vtB S a (.list vs) = vtL S b vs := by
  simp [vtB, ha, hu]

theorem vtB_list_not_iter {a : AT} (ha : nxAT S.good a = false)
    (hu : ∀ b, unf S a ≠ .iter b) (vs : List Value) : vtB S a (.list vs) = true := by
  cases h : unf S a <;> simp_all [vtB]

theorem vtB_optSome_nx {a : AT} (ha : nxAT S.good a = true) (w : Value) :
    vtB S a (.opt (some w)) = nxB w := by
  simp [vtB, ha]

theorem vtB_optSome_iter {a b : AT} (ha : nxAT S.good a = false) (hu : unf S a = .iter b)
    (w : Value) : vtB S a (.opt (some w)) = vtB S b w := by
  simp [vtB, ha, hu]

theorem vtB_optSome_not_iter {a : AT} (ha : nxAT S.good a = false)
    (hu : ∀ b, unf S a ≠ .iter b) (w : Value) : vtB S a (.opt (some w)) = true := by
  cases h : unf S a <;> simp_all [vtB]

/-! ## Lists of conforming values -/

theorem vtL_iff (b : AT) : ∀ vs : List Value, vtL S b vs = true ↔ ∀ w ∈ vs, vtB S b w = true
  | [] => by simp [vtL]
  | v :: vs => by simp [vtL, vtL_iff b vs]

theorem nxBs_iff (vs : List Value) : nxBs vs = true ↔ ∀ w ∈ vs, nxB w = true := by
  rw [Swap.nxBs_eq_all, List.all_eq_true]

/-- **A list conforms to `a` when its elements conform to the element type.** -/
theorem vtB_list_of {a : AT} {vs : List Value}
    (h : ∀ w ∈ vs, vtB S (elemOf S a) w = true) : vtB S a (.list vs) = true := by
  cases ha : nxAT S.good a
  · by_cases hi : ∃ b, unf S a = .iter b
    · obtain ⟨b, hu⟩ := hi
      rw [vtB_list_iter ha hu, vtL_iff]
      exact fun w hw => elemOf_of_iter ha hu ▸ h w hw
    · exact vtB_list_not_iter ha (fun b hb => hi ⟨b, hb⟩) vs
  · rw [vtB_list_nx ha, nxBs_iff]
    exact fun w hw => vtB_base_iff.1 (elemOf_of_nx ha ▸ h w hw)

/-- **The elements of a conforming list conform to the element type.** -/
theorem vtB_elem {a : AT} {vs : List Value} (h : vtB S a (.list vs) = true) :
    ∀ w ∈ vs, vtB S (elemOf S a) w = true := by
  intro w hw
  cases ha : nxAT S.good a
  · by_cases hi : ∃ b, unf S a = .iter b
    · obtain ⟨b, hu⟩ := hi
      rw [vtB_list_iter ha hu, vtL_iff] at h
      exact (elemOf_of_iter ha hu).symm ▸ h w hw
    · exact (elemOf_of_not_iter ha (fun b hb => hi ⟨b, hb⟩)).symm ▸ vtB_unk S w
  · rw [vtB_list_nx ha, nxBs_iff] at h
    exact vtB_of_nxB S _ w (h w hw)

/-- **The element of a conforming option conforms to the element type.** -/
theorem vtB_elemOpt {a : AT} {w : Value} (h : vtB S a (.opt (some w)) = true) :
    vtB S (elemOf S a) w = true := by
  cases ha : nxAT S.good a
  · by_cases hi : ∃ b, unf S a = .iter b
    · obtain ⟨b, hu⟩ := hi
      rw [vtB_optSome_iter ha hu] at h
      exact (elemOf_of_iter ha hu).symm ▸ h
    · exact (elemOf_of_not_iter ha (fun b hb => hi ⟨b, hb⟩)).symm ▸ vtB_unk S w
  · rw [vtB_optSome_nx ha] at h
    exact vtB_of_nxB S _ w h

/-- **An option conforms when its element conforms to the element type.** -/
theorem vtB_optSome_of {a : AT} {w : Value} (h : vtB S (elemOf S a) w = true) :
    vtB S a (.opt (some w)) = true := by
  cases ha : nxAT S.good a
  · by_cases hi : ∃ b, unf S a = .iter b
    · obtain ⟨b, hu⟩ := hi
      rw [vtB_optSome_iter ha hu]
      exact elemOf_of_iter ha hu ▸ h
    · exact vtB_optSome_not_iter ha (fun b hb => hi ⟨b, hb⟩) w
  · rw [vtB_optSome_nx ha]
    exact vtB_base_iff.1 (elemOf_of_nx ha ▸ h)

/-- Conforming to `elemOf` implies conforming to `elemAT`. -/
theorem vtB_elemAT_of_elemOf {a : AT} {w : Value} (h : vtB S (elemOf S a) w = true) :
    vtB S (elemAT S a) w = true := by
  cases ha : nxAT S.good a
  · simpa [elemOf, ha] using h
  · exact vtB_of_nxB S _ w (vtB_base_iff.1 (elemOf_of_nx ha ▸ h))

/-! ## Sublists and concatenation -/

theorem vtB_sublist {a : AT} {vs ws : List Value} (h : vtB S a (.list vs) = true)
    (hs : ∀ w ∈ ws, w ∈ vs) : vtB S a (.list ws) = true :=
  vtB_list_of fun w hw => vtB_elem h w (hs w hw)

theorem vtB_take {a : AT} {vs : List Value} (h : vtB S a (.list vs) = true) (k : Nat) :
    vtB S a (.list (vs.take k)) = true :=
  vtB_sublist h fun _ hw => List.mem_of_mem_take hw

theorem vtB_drop {a : AT} {vs : List Value} (h : vtB S a (.list vs) = true) (k : Nat) :
    vtB S a (.list (vs.drop k)) = true :=
  vtB_sublist h fun _ hw => List.mem_of_mem_drop hw

theorem vtB_slice? {a : AT} {v u : Value} {i k : Nat} (h : vtB S a v = true)
    (hs : v.slice? i k = some u) : vtB S a u = true := by
  cases v with
  | list vs =>
    simp only [Value.slice?] at hs
    split at hs
    · cases hs
      exact vtB_take (vtB_drop h i) k
    · cases hs
  | _ => simp [Value.slice?] at hs

theorem vtB_append {a : AT} {vs ws : List Value} (h₁ : vtB S a (.list vs) = true)
    (h₂ : vtB S a (.list ws) = true) : vtB S a (.list (vs ++ ws)) = true := by
  refine vtB_list_of fun w hw => ?_
  rcases List.mem_append.1 hw with hw | hw
  · exact vtB_elem h₁ w hw
  · exact vtB_elem h₂ w hw

theorem vtB_cat? {a : AT} {v₁ v₂ u : Value} (h₁ : vtB S a v₁ = true) (h₂ : vtB S a v₂ = true)
    (hc : Value.cat? v₁ v₂ = some u) : vtB S a u = true := by
  unfold Value.cat? at hc
  split at hc
  · cases hc
    exact vtB_append h₁ h₂
  · cases hc
    exact h₂
  · cases hc
    exact h₁
  · cases hc

/-- `LiftE` turns a conforming option into a conforming list, at an iteration type. -/
theorem vtB_lift {a : AT} {o : Option Value} (h : vtB S a (.opt o) = true) :
    vtB S a (.list o.toList) = true := by
  cases o with
  | none => exact vtB_list_of (by simp)
  | some w => exact vtB_list_of (by simpa using vtB_elemOpt h)

/-! ## Reading parts of a value -/

/-- The type a field projection gives, as `NxSites.tyOf` reads it. -/
def fieldTy (S : Sig) (a : AT) (k : String) : AT :=
  match unf S a with
  | .name n _ => fieldAT S n k
  | _ => .unk

theorem vtF_find {n : String} {k : AtomS} :
    ∀ {gs : List (AtomS × Value)} {g : AtomS × Value}, vtF S n gs = true →
      gs.find? (·.1 = k) = some g → vtB S (fieldAT S n k) g.2 = true
  | [], _, _, hf => by simp at hf
  | (k', v) :: gs, g, h, hf => by
    simp only [vtF, Bool.and_eq_true] at h
    by_cases hk : k' = k
    · simp only [List.find?_cons, hk, decide_true, Option.some.injEq] at hf
      subst hf
      exact hk ▸ h.1
    · simp only [List.find?_cons, hk, decide_false] at hf
      exact vtF_find h.2 hf

theorem nxBf_find {k : AtomS} :
    ∀ {gs : List (AtomS × Value)} {g : AtomS × Value}, nxBf gs = true →
      gs.find? (·.1 = k) = some g → nxB g.2 = true
  | [], _, _, hf => by simp at hf
  | (k', v) :: gs, g, h, hf => by
    simp only [Swap.nxBf, Bool.and_eq_true] at h
    by_cases hk : k' = k
    · simp only [List.find?_cons, hk, decide_true, Option.some.injEq] at hf
      subst hf
      exact h.1.1
    · simp only [List.find?_cons, hk, decide_false] at hf
      exact nxBf_find h.2 hf

theorem vtB_struct_nx {a : AT} (ha : nxAT S.good a = true) (gs : List (AtomS × Value)) :
    vtB S a (.struct gs) = nxBf gs := by
  simp [vtB, ha]

theorem vtB_struct_name {a : AT} {n : String} {xs : List AT} (ha : nxAT S.good a = false)
    (hu : unf S a = .name n xs) (gs : List (AtomS × Value)) :
    vtB S a (.struct gs) = vtF S n gs := by
  simp [vtB, ha, hu]

theorem fieldTy_of_name {a : AT} {n : String} {xs : List AT} (hu : unf S a = .name n xs)
    (k : String) : fieldTy S a k = fieldAT S n k := by
  simp [fieldTy, hu]

theorem fieldTy_of_not_name {a : AT} (hu : ∀ n xs, unf S a ≠ .name n xs) (k : String) :
    fieldTy S a k = .unk := by
  unfold fieldTy
  split
  · rename_i n xs h
    exact absurd h (hu n xs)
  · rfl

/-- **`DotE`**: a field of a conforming value conforms to the field type. -/
theorem vtB_field? {a : AT} {v w : Value} {k : AtomS} (h : vtB S a v = true)
    (hf : v.field? k = some w) : vtB S (fieldTy S a k) w = true := by
  cases v with
  | struct gs =>
    have hf' : ∃ k', gs.find? (·.1 = k) = some (k', w) := by simpa using hf
    obtain ⟨k', hg⟩ := hf'
    cases ha : nxAT S.good a
    · by_cases hi : ∃ n xs, unf S a = .name n xs
      · obtain ⟨n, xs, hu⟩ := hi
        rw [vtB_struct_name ha hu] at h
        exact (fieldTy_of_name hu k).symm ▸ vtF_find h hg
      · exact (fieldTy_of_not_name (fun n xs hn => hi ⟨n, xs, hn⟩) k).symm ▸ vtB_unk S w
    · rw [vtB_struct_nx ha] at h
      exact vtB_of_nxB S _ _ (nxBf_find h hg)
  | _ => simp [Value.field?] at hf

/-! ## Cases and tuples -/

/-- The type a case projection gives, as `NxSites.tyOf` reads it. -/
def caseTy (S : Sig) (a : AT) (op : String) : AT :=
  match unf S a with
  | .name n _ => caseAT S n op
  | _ => .unk

theorem vtB_case_nx {a : AT} (ha : nxAT S.good a = true) (op : MixopS) (w : Value) :
    vtB S a (.case op w) = nxB w := by
  simp [vtB, ha]

theorem vtB_case_name {a : AT} {n : String} {xs : List AT} (ha : nxAT S.good a = false)
    (hu : unf S a = .name n xs) (op : MixopS) (w : Value) :
    vtB S a (.case op w) = vtB S (caseAT S n op) w := by
  simp [vtB, ha, hu]

/-- **`UncaseE`**: the payload of a conforming case conforms to the case type. -/
theorem vtB_payload {a : AT} {op : MixopS} {w : Value} (h : vtB S a (.case op w) = true) :
    vtB S (caseTy S a op) w = true := by
  cases ha : nxAT S.good a
  · by_cases hi : ∃ n xs, unf S a = .name n xs
    · obtain ⟨n, xs, hu⟩ := hi
      rw [vtB_case_name ha hu] at h
      have he : caseTy S a op = caseAT S n op := by simp [caseTy, hu]
      exact he ▸ h
    · have he : caseTy S a op = .unk := by
        unfold caseTy
        split
        · rename_i n xs hn
          exact absurd ⟨n, xs, hn⟩ hi
        · rfl
      exact he ▸ vtB_unk S w
  · rw [vtB_case_nx ha] at h
    exact vtB_of_nxB S _ w h

theorem vtT_get : ∀ {xs : List AT} {vs : List Value} {j : Nat} {w : Value},
    vtT S xs vs = true → vs[j]? = some w → vtB S (xs.getD j .unk) w = true
  | _, [], _, _, _, hj => by simp at hj
  | xs, v :: vs, 0, w, h, hj => by
    simp only [vtT, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    cases xs with
    | nil => exact vtB_unk S v
    | cons x xs => exact h.1
  | xs, v :: vs, j + 1, w, h, hj => by
    simp only [vtT, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at hj
    have ih := vtT_get h.2 hj
    cases xs with
    | nil => exact vtB_unk S w
    | cons x xs => simpa using ih

/-- The type a tuple projection gives, as `NxSites.tyOf` reads it. -/
def compTy (S : Sig) (a : AT) (j : Nat) : AT :=
  match unf S a with
  | .tup xs => xs.getD j .unk
  | _ => .unk

/-- **`ProjE`**: a component of a conforming tuple conforms to the component type. -/
theorem vtB_proj {a : AT} {vs : List Value} {j : Nat} {w : Value}
    (h : vtB S a (.tuple vs) = true) (hj : vs[j]? = some w) : vtB S (compTy S a j) w = true := by
  cases ha : nxAT S.good a
  · by_cases hi : ∃ xs, unf S a = .tup xs
    · obtain ⟨xs, hu⟩ := hi
      have h' : vtT S xs vs = true := by simpa [vtB, ha, hu] using h
      have he : compTy S a j = xs.getD j .unk := by simp [compTy, hu]
      exact he ▸ vtT_get h' hj
    · have he : compTy S a j = .unk := by
        unfold compTy
        split
        · rename_i xs hx
          exact absurd ⟨xs, hx⟩ hi
        · rfl
      exact he ▸ vtB_unk S w
  · have h' : nxBs vs = true := by simpa [vtB, ha] using h
    exact vtB_of_nxB S _ w ((nxBs_iff vs).1 h' w (List.mem_of_getElem? hj))

/-! ## Writing -/

/-- **`IdxP`**: writing a conforming element keeps a list conforming. -/
theorem vtB_set {a : AT} {vs : List Value} {w : Value} (h : vtB S a (.list vs) = true)
    (hw : vtB S (elemOf S a) w = true) (i : Nat) : vtB S a (.list (vs.set i w)) = true := by
  refine vtB_list_of fun u hu => ?_
  rcases List.mem_or_eq_of_mem_set hu with hu | rfl
  · exact vtB_elem h u hu
  · exact hw

theorem vtB_setIdx {a : AT} {v w u : Value} {i : Nat} (h : vtB S a v = true)
    (hw : vtB S (elemOf S a) w = true) (hs : v.setIdx i w = some u) : vtB S a u = true := by
  cases v with
  | list vs =>
    simp only [Value.setIdx] at hs
    split at hs
    · cases hs
      exact vtB_set h hw i
    · cases hs
  | _ => simp [Value.setIdx] at hs

/-- **`SliceP`**: writing a conforming list into a slice keeps a list conforming. -/
theorem vtB_setSlice {a : AT} {v w u : Value} {i k : Nat} (h : vtB S a v = true)
    (hw : vtB S a w = true) (hs : v.setSlice i k w = some u) : vtB S a u = true := by
  unfold Value.setSlice at hs
  split at hs
  · rename_i vs ws
    split at hs
    · cases hs
      exact vtB_append (vtB_append (vtB_take h i) hw) (vtB_drop h (i + k))
    · cases hs
  · cases hs

/-- The field type the flow check uses for paths. -/
theorem fieldOf'_eq {a : AT} (ha : nxAT S.good a = false) (k : String) :
    fieldOf' S a k = fieldTy S a k := by
  simp only [fieldOf', ha, Bool.false_eq_true, ↓reduceIte, fieldTy]
  rfl

theorem vtF_map {n k : String} {w : Value} (hw : vtB S (fieldAT S n k) w = true) :
    ∀ gs : List (AtomS × Value), vtF S n gs = true →
      vtF S n (gs.map fun f => if f.1 = k then (f.1, w) else f) = true
  | [], _ => rfl
  | (k', v) :: gs, h => by
    simp only [vtF, Bool.and_eq_true] at h
    by_cases hk : k' = k
    · subst hk
      simp [vtF, hw, vtF_map hw gs h.2]
    · simp [vtF, hk, h.1, vtF_map hw gs h.2]

theorem nxBf_map {k : String} {w : Value} (hw : nxB w = true) :
    ∀ gs : List (AtomS × Value), nxBf gs = true →
      nxBf (gs.map fun f => if f.1 = k then (f.1, w) else f) = true
  | [], _ => rfl
  | (k', v) :: gs, h => by
    simp only [Swap.nxBf, Bool.and_eq_true] at h
    by_cases hk : k' = k
    · subst hk
      simp [hw, h.1.2, nxBf_map hw gs h.2]
    · simp [hk, h.1.1, h.1.2, nxBf_map hw gs h.2]

/-- **`DotP`**: writing a value conforming to the field type keeps a record conforming. -/
theorem vtB_setField {a : AT} {v w u : Value} {k : AtomS} (h : vtB S a v = true)
    (hw : vtB S (fieldOf' S a k) w = true) (hs : v.setField k w = some u) :
    vtB S a u = true := by
  cases v with
  | struct gs =>
    simp only [Value.setField_struct, Option.some.injEq] at hs
    subst hs
    cases ha : nxAT S.good a
    · rw [fieldOf'_eq ha] at hw
      by_cases hi : ∃ n xs, unf S a = .name n xs
      · obtain ⟨n, xs, hu⟩ := hi
        rw [vtB_struct_name ha hu] at h ⊢
        exact vtF_map ((fieldTy_of_name hu k) ▸ hw) gs h
      · have hu : ∀ n xs, unf S a ≠ .name n xs := fun n xs hn => hi ⟨n, xs, hn⟩
        cases hU : unf S a <;> simp_all [vtB]
    · rw [vtB_struct_nx ha] at h ⊢
      have hb : fieldOf' S a k = .base := by simp [fieldOf', ha]
      have hw' : nxB w = true := nxB_of_vtB (a := .base) rfl (hb ▸ hw)
      exact nxBf_map hw' gs h
  | _ => simp [Value.setField] at hs

/-! ## Record composition -/

/-- `vtB_comp?` on two records, given it on their fields. -/
theorem vtB_comp?_struct {a : AT} {f₁ : List (AtomS × Value)} {v₂ u : Value}
    (hF : ∀ n f₂ f, vtF S n f₁ = true → vtF S n f₂ = true → Value.compFields? f₁ f₂ = some f →
      vtF S n f = true)
    (h₁ : vtB S a (.struct f₁) = true) (h₂ : vtB S a v₂ = true)
    (hc : Value.comp? (.struct f₁) v₂ = some u) : vtB S a u = true := by
  cases v₂ with
  | struct f₂ =>
    have hc' : ∃ f, Value.compFields? f₁ f₂ = some f ∧ Value.struct f = u := by
      simpa [Value.comp?] using hc
    obtain ⟨f, hf, rfl⟩ := hc'
    cases ha : nxAT S.good a
    · by_cases hi : ∃ n xs, unf S a = .name n xs
      · obtain ⟨n, xs, hu⟩ := hi
        rw [vtB_struct_name ha hu] at h₁ h₂ ⊢
        exact hF n f₂ f h₁ h₂ hf
      · cases hU : unf S a <;> simp_all [vtB]
    · exact vtB_of_nxB S a _ (Swap.nxB_comp? _ _ _ (nxB_of_vtB ha h₁) (nxB_of_vtB ha h₂) hc)
  | _ => simp [Value.comp?] at hc

/-- `vtB_comp?` on two lists. -/
theorem vtB_comp?_list {a : AT} {l₁ : List Value} {v₂ u : Value}
    (h₁ : vtB S a (.list l₁) = true) (h₂ : vtB S a v₂ = true)
    (hc : Value.comp? (.list l₁) v₂ = some u) : vtB S a u = true := by
  cases v₂ with
  | list l₂ =>
    have hu : Value.list (l₁ ++ l₂) = u := by simpa using hc
    exact hu ▸ vtB_append h₁ h₂
  | _ => simp [Value.comp?] at hc

/-- `vtB_comp?` on two options. -/
theorem vtB_comp?_opt {a : AT} {o₁ : Option Value} {v₂ u : Value}
    (h₁ : vtB S a (.opt o₁) = true) (h₂ : vtB S a v₂ = true)
    (hc : Value.comp? (.opt o₁) v₂ = some u) : vtB S a u = true := by
  cases v₂ with
  | opt o₂ =>
    cases o₁ with
    | none =>
      have hu : Value.opt o₂ = u := by simpa using hc
      exact hu ▸ h₂
    | some w =>
      cases o₂ with
      | none =>
        have hu : Value.opt (some w) = u := by simpa [Value.comp?] using hc
        exact hu ▸ h₁
      | some _ => simp [Value.comp?] at hc
  | _ => simp [Value.comp?] at hc

mutual
/-- **`CompE`**: composing two values conforming to `a` gives a value conforming to `a`. -/
theorem vtB_comp? (a : AT) : ∀ (v₁ v₂ u : Value), vtB S a v₁ = true → vtB S a v₂ = true →
    Value.comp? v₁ v₂ = some u → vtB S a u = true
  | .struct f₁, _, _, h₁, h₂, hc =>
    vtB_comp?_struct (fun n f₂ f => vtF_compFields? n f₁ f₂ f) h₁ h₂ hc
  | .list _, _, _, h₁, h₂, hc => vtB_comp?_list h₁ h₂ hc
  | .opt _, _, _, h₁, h₂, hc => vtB_comp?_opt h₁ h₂ hc
  | .bool _, _, _, _, _, hc => by simp [Value.comp?] at hc
  | .num _, _, _, _, _, hc => by simp [Value.comp?] at hc
  | .text _, _, _, _, _, hc => by simp [Value.comp?] at hc
  | .tuple _, _, _, _, _, hc => by simp [Value.comp?] at hc
  | .case _ _, _, _, _, _, hc => by simp [Value.comp?] at hc

/-- `vtB_comp?` on the fields of two records of type `n`. -/
theorem vtF_compFields? (n : String) : ∀ (f₁ f₂ f : List (AtomS × Value)),
    vtF S n f₁ = true → vtF S n f₂ = true → Value.compFields? f₁ f₂ = some f →
      vtF S n f = true
  | [], [], f, _, _, hc => by
    simp only [Value.compFields?_nil, Option.some.injEq] at hc
    subst hc
    rfl
  | (k₁, v₁) :: f₁, (k₂, v₂) :: f₂, f, h₁, h₂, hc => by
    simp only [vtF, Bool.and_eq_true] at h₁ h₂
    simp only [Value.compFields?] at hc
    split at hc
    · rename_i hk
      subst hk
      split at hc
      · rename_i v f' hv hf
        simp only [Option.some.injEq] at hc
        subst hc
        simp only [vtF, Bool.and_eq_true]
        exact ⟨vtB_comp? _ v₁ v₂ v h₁.1 h₂.1 hv, vtF_compFields? n f₁ f₂ f' h₁.2 h₂.2 hf⟩
      · cases hc
    · cases hc
  | [], _ :: _, _, _, _, hc => by simp [Value.compFields?] at hc
  | _ :: _, [], _, _, _, hc => by simp [Value.compFields?] at hc
end

end Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
