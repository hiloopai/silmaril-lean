module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Defs

/-!
# Round 7, REH route 2: conformance of values, basic facts

* `vtB_of_nxB`: an export-free value conforms to every abstract type;
* `nxB_of_vtB`: a value conforming to an export-free type is export-free;
* `vtB_unk`, `vtB_of_triv`: every value conforms to `.unk` and to every `triv` type;
* `atEq_iff`: `NxSites.atEq` is equality;
* `vtB_congr`, `vtB_iter`, `vtB_tup`, `vtB_name`: conformance read off the unfolded type;
* `vtB_of_atLe`: `atLe` is sound: conformance to `a` implies conformance to `b`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## `atEq` is equality -/

mutual
theorem atEq_iff : ∀ a b : AT, atEq a b = true ↔ a = b
  | .base, .base => by simp [atEq]
  | .base, .name _ _ => by simp [atEq]
  | .base, .iter _ => by simp [atEq]
  | .base, .tup _ => by simp [atEq]
  | .base, .unk => by simp [atEq]
  | .name _ _, .base => by simp [atEq]
  | .name n xs, .name m ys => by
    simp only [atEq, Bool.and_eq_true, beq_iff_eq, atEqL_iff xs ys, AT.name.injEq]
  | .name _ _, .iter _ => by simp [atEq]
  | .name _ _, .tup _ => by simp [atEq]
  | .name _ _, .unk => by simp [atEq]
  | .iter _, .base => by simp [atEq]
  | .iter _, .name _ _ => by simp [atEq]
  | .iter a, .iter b => by simp only [atEq, atEq_iff a b, AT.iter.injEq]
  | .iter _, .tup _ => by simp [atEq]
  | .iter _, .unk => by simp [atEq]
  | .tup _, .base => by simp [atEq]
  | .tup _, .name _ _ => by simp [atEq]
  | .tup _, .iter _ => by simp [atEq]
  | .tup xs, .tup ys => by simp only [atEq, atEqL_iff xs ys, AT.tup.injEq]
  | .tup _, .unk => by simp [atEq]
  | .unk, .base => by simp [atEq]
  | .unk, .name _ _ => by simp [atEq]
  | .unk, .iter _ => by simp [atEq]
  | .unk, .tup _ => by simp [atEq]
  | .unk, .unk => by simp [atEq]

theorem atEqL_iff : ∀ xs ys : List AT, atEqL xs ys = true ↔ xs = ys
  | [], [] => by simp [atEqL]
  | [], _ :: _ => by simp [atEqL]
  | _ :: _, [] => by simp [atEqL]
  | a :: xs, b :: ys => by
    simp only [atEqL, Bool.and_eq_true, atEq_iff a b, atEqL_iff xs ys, List.cons.injEq]
end

/-! ## Export-free values conform to everything -/

mutual
theorem vtB_of_nxB (S : Sig) : ∀ (a : AT) (v : Value), nxB v = true → vtB S a v = true
  | _, .bool _, _ => by simp [vtB]
  | _, .num _, _ => by simp [vtB]
  | _, .text _, _ => by simp [vtB]
  | _, .opt none, _ => by simp [vtB]
  | a, .struct gs, h => by
    have h' : nxBf gs = true := h
    unfold vtB
    split
    · exact h'
    · split
      · exact vtF_of_nxBf S _ gs h'
      · rfl
  | a, .case op w, h => by
    have h' : nxB w = true := h
    unfold vtB
    split
    · exact h'
    · split
      · exact vtB_of_nxB S _ w h'
      · rfl
  | a, .list vs, h => by
    have h' : nxBs vs = true := h
    unfold vtB
    split
    · exact h'
    · split
      · exact vtL_of_nxBs S _ vs h'
      · rfl
  | a, .opt (some w), h => by
    have h' : nxB w = true := h
    unfold vtB
    split
    · exact h'
    · split
      · exact vtB_of_nxB S _ w h'
      · rfl
  | a, .tuple vs, h => by
    have h' : nxBs vs = true := h
    unfold vtB
    split
    · exact h'
    · split
      · exact vtT_of_nxBs S _ vs h'
      · rfl

theorem vtL_of_nxBs (S : Sig) (b : AT) : ∀ vs : List Value, nxBs vs = true → vtL S b vs = true
  | [], _ => by simp [vtL]
  | v :: vs, h => by
    simp only [Swap.nxBs, Bool.and_eq_true] at h
    simp only [vtL, vtB_of_nxB S b v h.1, vtL_of_nxBs S b vs h.2, Bool.and_self]

theorem vtF_of_nxBf (S : Sig) (n : String) :
    ∀ gs : List (AtomS × Value), nxBf gs = true → vtF S n gs = true
  | [], _ => by simp [vtF]
  | (k, v) :: gs, h => by
    simp only [Swap.nxBf, Bool.and_eq_true] at h
    simp only [vtF, vtB_of_nxB S _ v h.1.1, vtF_of_nxBf S n gs h.2, Bool.and_self]

theorem vtT_of_nxBs (S : Sig) : ∀ (xs : List AT) (vs : List Value), nxBs vs = true →
    vtT S xs vs = true
  | _, [], _ => by simp [vtT]
  | xs, v :: vs, h => by
    simp only [Swap.nxBs, Bool.and_eq_true] at h
    simp only [vtT, vtB_of_nxB S _ v h.1, vtT_of_nxBs S xs.tail vs h.2, Bool.and_self]
end

/-- **A value conforming to an export-free type is export-free.** -/
theorem nxB_of_vtB {S : Sig} {a : AT} (ha : nxAT S.good a = true) :
    ∀ {v : Value}, vtB S a v = true → nxB v = true
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .opt none, _ => rfl
  | .struct gs, h => by show nxBf gs = true; simpa [vtB, ha] using h
  | .case op w, h => by show nxB w = true; simpa [vtB, ha] using h
  | .list vs, h => by show nxBs vs = true; simpa [vtB, ha] using h
  | .opt (some w), h => by show nxB w = true; simpa [vtB, ha] using h
  | .tuple vs, h => by show nxBs vs = true; simpa [vtB, ha] using h

/-! ## Trivial types -/

theorem unf_unk (S : Sig) : unf S .unk = .unk := by
  simp [unf, unalias]

/-- **Every value conforms to `.unk`.** -/
theorem vtB_unk (S : Sig) (v : Value) : vtB S .unk v = true := by
  cases v with
  | opt o => cases o <;> simp [vtB, nxAT, unf_unk]
  | _ => simp [vtB, nxAT, unf_unk]

theorem vtL_unk (S : Sig) : ∀ vs : List Value, vtL S .unk vs = true
  | [] => rfl
  | v :: vs => by simp [vtL, vtB_unk, vtL_unk S vs]

/-- A type name without field entries gives `.unk` field types. -/
theorem fieldAT_unk {S : Sig} {n : String} (h : (S.fields.any fun p => p.1 == n) = false)
    (k : String) : fieldAT S n k = .unk := by
  unfold fieldAT
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    have hc := List.find?_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have : (S.fields.any fun p => p.1 == n) = true := List.any_eq_true.2 ⟨p, hm, by simp [hc.1]⟩
    simp [h] at this
  · rfl

/-- A type name without case entries gives `.unk` case types. -/
theorem caseAT_unk {S : Sig} {n : String} (h : (S.cases.any fun p => p.1 == n) = false)
    (op : String) : caseAT S n op = .unk := by
  unfold caseAT
  split
  · rename_i p hp
    have hm := List.mem_of_find?_eq_some hp
    have hc := List.find?_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have : (S.cases.any fun p => p.1 == n) = true := List.any_eq_true.2 ⟨p, hm, by simp [hc.1]⟩
    simp [h] at this
  · rfl

theorem vtF_unkFields {S : Sig} {n : String} (h : (S.fields.any fun p => p.1 == n) = false) :
    ∀ gs : List (AtomS × Value), vtF S n gs = true
  | [] => rfl
  | (k, v) :: gs => by simp [vtF, fieldAT_unk h, vtB_unk, vtF_unkFields h gs]

/-- `vtT` holds when every listed type is trivial for every value. -/
theorem vtT_of_all {S : Sig} (P : AT → Prop) (hP : ∀ a, P a → ∀ v, vtB S a v = true)
    (hu : P .unk) : ∀ (xs : List AT) (vs : List Value), (∀ a ∈ xs, P a) → vtT S xs vs = true
  | _, [], _ => rfl
  | xs, v :: vs, h => by
    have h1 : P (xs.headD .unk) := by
      cases xs with
      | nil => exact hu
      | cons a xs => exact h a (List.mem_cons_self ..)
    have h2 : ∀ a ∈ xs.tail, P a := by
      cases xs with
      | nil => simp
      | cons a xs => exact fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [vtT, hP _ h1 v, vtT_of_all P hP hu xs.tail vs h2, Bool.and_self]

/-- **`trivK` is sound**: every value conforms to a trivial type. -/
theorem vtB_of_trivK (S : Sig) : ∀ (k : Nat) (a : AT), trivK S k a = true → ∀ v, vtB S a v = true
  | 0, _, h, _ => by simp [trivK] at h
  | k + 1, a, h, v => by
    simp only [trivK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hnx, hu⟩ := h
    have hL : ∀ b vs, trivK S k b = true → vtL S b vs = true := by
      intro b vs hb
      induction vs with
      | nil => rfl
      | cons w vs ih => simp [vtL, vtB_of_trivK S k b hb w, ih]
    have hT : ∀ xs : List AT, (xs.all fun b => trivK S k b) = true → ∀ vs, vtT S xs vs = true :=
      fun xs hxs vs => vtT_of_all (fun b => ∀ w, vtB S b w = true) (fun _ hb => hb)
        (vtB_unk S) xs vs (fun b hb => vtB_of_trivK S k b (List.all_eq_true.1 hxs b hb))
    cases v with
    | bool => simp [vtB]
    | num => simp [vtB]
    | text => simp [vtB]
    | opt o =>
      cases o with
      | none => simp [vtB]
      | some w =>
        cases hU : unf S a <;> rw [hU] at hu <;> simp only [vtB, hnx, hU, Bool.false_eq_true,
          ↓reduceIte]
        exact vtB_of_trivK S k _ hu w
    | list vs =>
      cases hU : unf S a <;> rw [hU] at hu <;> simp only [vtB, hnx, hU, Bool.false_eq_true,
        ↓reduceIte]
      exact hL _ vs hu
    | tuple vs =>
      cases hU : unf S a <;> rw [hU] at hu <;> simp only [vtB, hnx, hU, Bool.false_eq_true,
        ↓reduceIte]
      exact hT _ hu vs
    | case op w =>
      cases hU : unf S a <;> rw [hU] at hu <;> simp only [vtB, hnx, hU, Bool.false_eq_true,
        ↓reduceIte]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hu
      simp [caseAT_unk hu.2, vtB_unk]
    | struct gs =>
      cases hU : unf S a <;> rw [hU] at hu <;> simp only [vtB, hnx, hU, Bool.false_eq_true,
        ↓reduceIte]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hu
      exact vtF_unkFields hu.1 gs

/-- **`triv` is sound.** -/
theorem vtB_of_triv {S : Sig} {a : AT} (h : triv S a = true) (v : Value) : vtB S a v = true :=
  vtB_of_trivK S 8 a h v

/-! ## `atLe` is sound -/

/-- Conformance depends only on export-freedom and the unfolded form. -/
theorem vtB_congr {S : Sig} {a b : AT} (h₁ : nxAT S.good a = nxAT S.good b)
    (h₂ : unf S a = unf S b) (v : Value) : vtB S a v = vtB S b v := by
  cases v with
  | opt o => cases o <;> simp [vtB, h₁, h₂]
  | _ => simp [vtB, h₁, h₂]

/-- Conformance to a non-export-free type whose unfolded form is an iteration. -/
theorem vtB_iter {S : Sig} {a b : AT} (hnx : nxAT S.good a = false) (hu : unf S a = .iter b)
    (v : Value) : vtB S a v = match v with
      | .list vs => vtL S b vs
      | .opt (some w) => vtB S b w
      | _ => true := by
  cases v with
  | opt o => cases o <;> simp [vtB, hnx, hu]
  | _ => simp [vtB, hnx, hu]

/-- Conformance to a non-export-free type whose unfolded form is a tuple type. -/
theorem vtB_tup {S : Sig} {a : AT} {xs : List AT} (hnx : nxAT S.good a = false)
    (hu : unf S a = .tup xs) (v : Value) : vtB S a v = match v with
      | .tuple vs => vtT S xs vs
      | _ => true := by
  cases v with
  | opt o => cases o <;> simp [vtB, hnx, hu]
  | _ => simp [vtB, hnx, hu]

/-- Conformance to a non-export-free type whose unfolded form is a type name. -/
theorem vtB_name {S : Sig} {a : AT} {n : String} {xs : List AT} (hnx : nxAT S.good a = false)
    (hu : unf S a = .name n xs) (v : Value) : vtB S a v = match v with
      | .struct gs => vtF S n gs
      | .case op w => vtB S (caseAT S n op) w
      | _ => true := by
  cases v with
  | opt o => cases o <;> simp [vtB, hnx, hu]
  | _ => simp [vtB, hnx, hu]

theorem vtL_mono {S : Sig} {a b : AT} (h : ∀ v, vtB S a v = true → vtB S b v = true) :
    ∀ vs, vtL S a vs = true → vtL S b vs = true
  | [], _ => rfl
  | v :: vs, hv => by
    simp only [vtL, Bool.and_eq_true] at hv ⊢
    exact ⟨h v hv.1, vtL_mono h vs hv.2⟩

theorem vtT_mono {S : Sig} (R : AT → AT → Prop)
    (h : ∀ a b, R a b → ∀ v, vtB S a v = true → vtB S b v = true) (hu : R .unk .unk) :
    ∀ (xs ys : List AT), xs.length = ys.length → (∀ p ∈ xs.zip ys, R p.1 p.2) →
      ∀ vs, vtT S xs vs = true → vtT S ys vs = true
  | _, _, _, _, [], _ => rfl
  | [], [], _, _, v :: vs, hv => hv
  | [], _ :: _, hl, _, _ :: _, _ => by simp at hl
  | _ :: _, [], hl, _, _ :: _, _ => by simp at hl
  | x :: xs, y :: ys, hl, hR, v :: vs, hv => by
    simp only [vtT, List.headD_cons, List.tail_cons, Bool.and_eq_true] at hv ⊢
    have hR' : ∀ p ∈ xs.zip ys, R p.1 p.2 := fun p hp => hR p (List.mem_cons_of_mem _ hp)
    exact ⟨h x y (hR (x, y) (List.mem_cons_self ..)) v hv.1,
      vtT_mono R h hu xs ys (by simpa using hl) hR' vs hv.2⟩

/-- The structural part of `atLe`, read off. -/
theorem atLe_struct {S : Sig} {k : Nat} {a b : AT}
    (h : (match unf S a, unf S b with
      | .iter a', .iter b' => atLe S k a' b'
      | .tup xs, .tup ys => xs.length == ys.length && (xs.zip ys).all fun p => atLe S k p.1 p.2
      | .name n _, .name m _ => n == m
      | _, _ => false) = true) :
    (∃ a' b', unf S a = .iter a' ∧ unf S b = .iter b' ∧ atLe S k a' b' = true) ∨
    (∃ xs ys, unf S a = .tup xs ∧ unf S b = .tup ys ∧ xs.length = ys.length ∧
      ∀ p ∈ xs.zip ys, atLe S k p.1 p.2 = true) ∨
    (∃ n xs ys, unf S a = .name n xs ∧ unf S b = .name n ys) := by
  split at h
  · rename_i a' b' ha hb
    exact .inl ⟨a', b', ha, hb, h⟩
  · rename_i xs ys ha hb
    have h' : xs.length = ys.length ∧ ∀ p ∈ xs.zip ys, atLe S k p.1 p.2 = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] using h
    exact .inr (.inl ⟨xs, ys, ha, hb, h'.1, h'.2⟩)
  · rename_i n xs m ys ha hb
    have h' : n = m := by simpa only [beq_iff_eq] using h
    exact .inr (.inr ⟨n, xs, ys, ha, h' ▸ hb⟩)
  · exact absurd h (by simp)

/-- Conformance moves along iterations whose element types do. -/
theorem vtB_mono_iter {S : Sig} {a b a' b' : AT} (ha : nxAT S.good a = false)
    (hb : nxAT S.good b = false) (hua : unf S a = .iter a') (hub : unf S b = .iter b')
    (ih : ∀ v, vtB S a' v = true → vtB S b' v = true) (v : Value) (hv : vtB S a v = true) :
    vtB S b v = true := by
  rw [vtB_iter ha hua] at hv
  rw [vtB_iter hb hub]
  cases v with
  | list vs => exact vtL_mono ih vs hv
  | opt o => cases o with
    | none => rfl
    | some w => exact ih w hv
  | _ => rfl

/-- Conformance moves along tuple types whose components do. -/
theorem vtB_mono_tup {S : Sig} {k : Nat} {a b : AT} {xs ys : List AT}
    (ha : nxAT S.good a = false) (hb : nxAT S.good b = false) (hua : unf S a = .tup xs)
    (hub : unf S b = .tup ys) (hl : xs.length = ys.length)
    (hR : ∀ p ∈ xs.zip ys, atLe S k p.1 p.2 = true)
    (ih : ∀ a b, atLe S k a b = true → ∀ v, vtB S a v = true → vtB S b v = true)
    (v : Value) (hv : vtB S a v = true) : vtB S b v = true := by
  rw [vtB_tup ha hua] at hv
  rw [vtB_tup hb hub]
  have hu : atLe S k .unk .unk = true := by cases k <;> simp [atLe, triv, trivK, nxAT, unf_unk]
  cases v with
  | tuple vs => exact vtT_mono (fun a b => atLe S k a b = true) ih hu xs ys hl hR vs hv
  | _ => rfl

/-- Conformance moves between types unfolding to the same type name. -/
theorem vtB_mono_name {S : Sig} {a b : AT} {n : String} {xs ys : List AT}
    (ha : nxAT S.good a = false) (hb : nxAT S.good b = false) (hua : unf S a = .name n xs)
    (hub : unf S b = .name n ys) (v : Value) (hv : vtB S a v = true) : vtB S b v = true := by
  rw [vtB_name ha hua] at hv
  rwa [vtB_name hb hub]

/-- `atLe` at fuel `0` is sound. -/
theorem vtB_of_atLe_zero {S : Sig} {a b : AT} (h : atLe S 0 a b = true) (v : Value)
    (hv : vtB S a v = true) : vtB S b v = true := by
  have h' : nxAT S.good a = true ∨ triv S b = true := by
    simpa only [atLe, Bool.or_eq_true] using h
  rcases h' with h' | h'
  · exact vtB_of_nxB S b v (nxB_of_vtB h' hv)
  · exact vtB_of_triv h' v

/-- `atLe` at fuel `k + 1` is sound when it is at fuel `k`. -/
theorem vtB_of_atLe_succ {S : Sig} {k : Nat}
    (ih : ∀ a b, atLe S k a b = true → ∀ v, vtB S a v = true → vtB S b v = true) {a b : AT}
    (h : atLe S (k + 1) a b = true) (v : Value) (hv : vtB S a v = true) : vtB S b v = true := by
  by_cases ha : nxAT S.good a = true
  · exact vtB_of_nxB S b v (nxB_of_vtB ha hv)
  have ha' : nxAT S.good a = false := by simpa using ha
  unfold atLe at h
  simp only [ha', Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  rcases h with (h | ⟨hb, h⟩) | ⟨hb, h⟩
  · exact vtB_of_triv h v
  · have hu : unf S a = unf S b := (atEq_iff _ _).1 h
    exact (vtB_congr (by rw [ha', hb]) hu v) ▸ hv
  · rcases atLe_struct h with ⟨a', b', hua, hub, hk⟩ | ⟨xs, ys, hua, hub, hl, hR⟩ |
      ⟨n, xs, ys, hua, hub⟩
    · exact vtB_mono_iter ha' hb hua hub (ih a' b' hk) v hv
    · exact vtB_mono_tup ha' hb hua hub hl hR ih v hv
    · exact vtB_mono_name ha' hb hua hub v hv

/-- **`atLe` is sound**: a value conforming to `a` conforms to `b`. -/
theorem vtB_of_atLe (S : Sig) : ∀ (k : Nat) (a b : AT), atLe S k a b = true →
    ∀ v, vtB S a v = true → vtB S b v = true
  | 0, _, _, h, v, hv => vtB_of_atLe_zero h v hv
  | k + 1, _, _, h, v, hv => vtB_of_atLe_succ (vtB_of_atLe S k) h v hv

end Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
