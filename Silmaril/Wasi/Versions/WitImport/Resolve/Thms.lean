module

public import Silmaril.Wasi.Versions.WitImport.Resolve.Defs

/-!
# The resolved WIT typing refines the unresolved one

* **`tyOkR_tyOk`**: a value of a resolved type has the type for `tyOk` (where every named type
  accepts every value). So resolving named types only removes values.
* `argsOkR_argsOk`, `resOkR_resOk`: the same for arguments and answers.
* **`witROk_witOk`**: on calls whose arguments have the resolved parameter types, the resolved
  typing implies the unresolved one for `strip`. (Without that condition it does not follow: a
  call whose arguments are typed for `tyOk` but not resolved-typed is unconstrained by `witROk`
  and constrained by `witOk`.)
* `lookup_strip`, `lookup_rrestrict`: lookups in `strip` and `rrestrict`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)

theorem zipOk_tysOk {f : Binary.Ty → Val → Bool} (hf : ∀ t v, f t v = true → tyOk t v = true) :
    ∀ (ts : List Binary.Ty) (vs : List Val), zipOk f ts vs = true → tysOk ts vs = true
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [zipOk] at h
  | _ :: _, [], h => by simp [zipOk] at h
  | t :: ts, v :: vs, h => by
    simp only [zipOk, Bool.and_eq_true] at h
    simp [tysOk, hf t v h.1, zipOk_tysOk hf ts vs h.2]

theorem all_tyAll {g : Val → Bool} {t : Binary.Ty} (hg : ∀ v, g v = true → tyOk t v = true) :
    ∀ vs : List Val, vs.all g = true → tyAll t vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [tyAll, hg v h.1, all_tyAll hg vs h.2]

theorem all_pairsOk {f : Binary.Ty → Val → Bool} (hf : ∀ t v, f t v = true → tyOk t v = true)
    (k w : Binary.Ty) : ∀ vs : List Val, vs.all (pairOk f k w) = true → pairsOk k w vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    unfold pairOk at h1
    split at h1
    · simp only [Bool.and_eq_true] at h1
      simp [pairsOk, hf k _ h1.1, hf w _ h1.2, all_pairsOk hf k w vs h2]
    · exact absurd h1 Bool.false_ne_true

theorem optOk_tyOpt {f : Binary.Ty → Val → Bool} (hf : ∀ t v, f t v = true → tyOk t v = true) :
    ∀ (a : Option Binary.Ty) (p : Option Val), optOk f a p = true → tyOpt a p = true
  | none, none, _ => rfl
  | some t, some v, h => by simpa [tyOpt] using hf t v h
  | none, some _, h => by simp [optOk] at h
  | some _, none, h => by simp [optOk] at h

/-! ## Equations of the resolved typing -/

section Eqns

variable {E : TyEnv} {n : Nat} {c : Binary.IfaceName} {v : Val}

theorem tyOkR_zero (t : Binary.Ty) : tyOkR E 0 c t v = false := rfl
theorem tyOkR_prim (p : Silmaril.Wasm.Component.Binary.PrimValType) :
    tyOkR E (n + 1) c (.prim p) v = primOk p v := rfl
theorem tyOkR_ref {r : Binary.TyRef} {j : Binary.IfaceName} {k : Binary.TyDefKind}
    (h : findTy E c r = some (j, k)) : tyOkR E (n + 1) c (.ref r) v = kindOk (tyOkR E n) j k v := by
  simp only [tyOkR, h]
theorem tyOkR_list (t : Binary.Ty) : tyOkR E (n + 1) c (.list t) v = recV (tyOkR E n c t) v := rfl
theorem tyOkR_option (t : Binary.Ty) : tyOkR E (n + 1) c (.option t) v = optV (tyOkR E n c t) v :=
  rfl
theorem tyOkR_result (a b : Option Binary.Ty) :
    tyOkR E (n + 1) c (.result a b) v = resV (tyOkR E n c) a b v := rfl
theorem tyOkR_own (r : Binary.TyRef) : tyOkR E (n + 1) c (.own r) v = isU32 v := rfl
theorem tyOkR_borrow (r : Binary.TyRef) : tyOkR E (n + 1) c (.borrow r) v = isU32 v := rfl
theorem tyOkR_tuple (ts : List Binary.Ty) (vs : List Val) :
    tyOkR E (n + 1) c (.tuple ts) (.record vs) = zipOk (tyOkR E n c) ts vs := rfl

end Eqns

theorem recV_tyAll {g : Val → Bool} {t : Binary.Ty} (hg : ∀ v, g v = true → tyOk t v = true)
    {v : Val} (h : recV g v = true) : tyOk (.list t) v = true := by
  cases v <;> simp only [recV] at h <;> try exact absurd h Bool.false_ne_true
  simpa [tyOk] using all_tyAll hg _ h

/-- **The resolved typing refines `tyOk`.** -/
theorem tyOkR_tyOk (E : TyEnv) :
    ∀ (n : Nat) (cur : Binary.IfaceName) (t : Binary.Ty) (v : Val),
      tyOkR E n cur t v = true → tyOk t v = true
  | 0, _, _, _, h => by simp [tyOkR] at h
  | n + 1, cur, t, v, h => by
    have ih : ∀ c t v, tyOkR E n c t v = true → tyOk t v = true := tyOkR_tyOk E n
    cases t with
    | prim p => simpa [tyOk, tyOkR_prim] using h
    | ref r => simp [tyOk]
    | list t => exact recV_tyAll (ih cur t) h
    | fixedList t k =>
      cases v <;> simp only [tyOkR] at h <;> try exact absurd h Bool.false_ne_true
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      simp [tyOk, h.1, all_tyAll (ih cur _) _ h.2]
    | map k w =>
      cases v <;> simp only [tyOkR, recV] at h <;> try exact absurd h Bool.false_ne_true
      simpa [tyOk] using all_pairsOk (ih cur) _ _ _ h
    | option t =>
      simp only [tyOkR_option, optV] at h
      split at h
      · simp [tyOk]
      · simpa [tyOk] using ih cur _ _ h
      · exact absurd h Bool.false_ne_true
    | result a b =>
      simp only [tyOkR_result, resV] at h
      split at h
      · simpa [tyOk] using optOk_tyOpt (ih cur) _ _ h
      · simpa [tyOk] using optOk_tyOpt (ih cur) _ _ h
      · exact absurd h Bool.false_ne_true
    | tuple ts =>
      cases v <;> simp only [tyOkR] at h <;> try exact absurd h Bool.false_ne_true
      simpa [tyOk] using zipOk_tysOk (ih cur) _ _ h
    | own r => cases v <;> simp_all [tyOkR, isU32, tyOk]
    | borrow r => cases v <;> simp_all [tyOkR, isU32, tyOk]
    | future r => cases v <;> simp_all [tyOkR, isU32, tyOk]
    | stream r => cases v <;> simp_all [tyOkR, isU32, tyOk]

theorem argsOkR_argsOk {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig} {a : List Val}
    (h : argsOkR E i s a = true) : argsOk s a = true :=
  zipOk_tysOk (tyOkR_tyOk E fuel i) _ _ h

theorem resOkR_resOk {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig}
    {r : Option (List Val)} (h : resOkR E i s r = true) : resOk s r = true := by
  rcases r with _ | vs
  · exact absurd h Bool.false_ne_true
  · simp only [resOkR] at h
    simp only [resOk]
    split at h
    · simp_all
    · split at h
      · simp_all [tyOkR_tyOk E fuel i _ _ h]
      · exact absurd h Bool.false_ne_true

theorem lookup_strip (R : RTable) (f : FnName) :
    (strip R).lookup f = (R.lookup f).map (·.2) := by
  induction R with
  | nil => rfl
  | cons x R ih =>
    obtain ⟨g, i, s⟩ := x
    by_cases h : f = g
    · subst h; simp [strip, List.lookup]
    · simp only [strip] at ih ⊢
      simp [List.lookup, beq_false_of_ne h, ih]

theorem lookup_rrestrict (P : RPkg) (L : List FnName) (f : FnName) :
    (rrestrict P L).1.lookup f = if f ∈ L then P.1.lookup f else none := by
  obtain ⟨R, E⟩ := P
  simp only [rrestrict]
  induction R with
  | nil => simp [List.lookup]
  | cons x R ih =>
    obtain ⟨g, i, s⟩ := x
    by_cases hg : g ∈ L
    · by_cases h : f = g
      · subst h; simp [List.lookup, List.filter, hg]
      · simp [List.filter, hg, List.lookup, beq_false_of_ne h, ih]
    · by_cases h : f = g
      · subst h; simp [List.filter, hg, ih]
      · simp [List.filter, hg, List.lookup, beq_false_of_ne h, ih]

/-- **On resolved-typed arguments, the resolved typing implies the unresolved one.** -/
theorem witROk_witOk {P : RPkg} {f : FnName} {a : List Val} {r : Option (List Val)}
    (ha : ∀ i s, P.1.lookup f = some (i, s) → argsOkR P.2 i s a = true)
    (h : witROk P (.imp f a r) = true) : witOk (strip P.1) (.imp f a r) = true := by
  simp only [witOk, lookup_strip]
  cases hl : P.1.lookup f with
  | none => rfl
  | some x =>
    obtain ⟨i, s⟩ := x
    simp only [witROk, hl, ha i s hl, Bool.not_true, Bool.false_or] at h
    simp [resOkR_resOk h]

end Silmaril.Wasi.Versions.WitImport
