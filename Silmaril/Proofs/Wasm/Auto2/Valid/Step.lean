module

public import Silmaril.Wasm.Auto2.Valid.Defs

/-!
# The fragment checker against silmaril-lean's instruction checker

`checkSeq_of_seqF`: when `seqF` accepts a sequence from the stack `t` (top first), silmaril-lean's
`checkSeq atomC tyOkC` accepts it from `t.reverse` (bottom first), for every goal the final stack
matches; `exprC_of_exprF`, `funcCheck_of_funcF`: hence `exprF` and `funcF` imply the default
expression and function checkers.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Valid

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Valid

/-! ## Number types -/

theorem ntEq_eq {a b : NumType} (h : ntEq a b = true) : a = b := by
  cases a <;> cases b <;> rename_i x y <;> cases x <;> cases y <;> simp_all [ntEq, itEq]

theorem numIs_eq {a b : CValType} (h : numIs a b = true) : a = b ∧ ∃ n, a = .num n := by
  cases a <;> cases b <;> simp only [numIs, Bool.false_eq_true] at h
  exact ⟨congrArg _ (ntEq_eq h), _, rfl⟩

theorem allNum_append {l r : List CValType} : allNum (l ++ r) = (allNum l && allNum r) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp [allNum, ih]

theorem allNum_reverse {l : List CValType} : allNum l.reverse = allNum l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, allNum_append, ih]
    cases a <;> simp [allNum, Bool.and_comm]

/-- `popsF ps t`: `t` is `ps` followed by the rest, and `ps` are number types. -/
theorem popsF_spec : ∀ {ps t : List CValType}, popsF ps t = true →
    ∃ r, t = ps ++ r ∧ allNum ps = true
  | [], t, _ => ⟨t, rfl, rfl⟩
  | p :: ps, a :: t, h => by
    simp only [popsF, Bool.and_eq_true] at h
    obtain ⟨hap, n, han⟩ := numIs_eq h.1
    subst hap
    subst han
    obtain ⟨r, rfl, hn⟩ := popsF_spec h.2
    exact ⟨r, rfl, by simpa [allNum] using hn⟩
  | _ :: _, [], h => by simp [popsF] at h

theorem numsEq_spec : ∀ {l r : List CValType}, numsEq l r = true → l = r ∧ allNum l = true
  | [], [], _ => ⟨rfl, rfl⟩
  | a :: l, b :: r, h => by
    simp only [numsEq, Bool.and_eq_true] at h
    obtain ⟨hab, n, han⟩ := numIs_eq h.1
    subst hab
    subst han
    obtain ⟨rfl, hn⟩ := numsEq_spec h.2
    exact ⟨rfl, by simpa [allNum] using hn⟩
  | [], _ :: _, h => by simp [numsEq] at h
  | _ :: _, [], h => by simp [numsEq] at h

/-! ## Subtyping and type validity on number types -/

theorem sub_num (Δ : TypeCtx) (n : NumType) : Sub.check Δ (.num n : CValType) (.num n) = true := by
  simp [Sub.check, Sub.checkK, TypeCtx.checkVal]

theorem checkResultSub_self (Δ : TypeCtx) :
    ∀ {l : List CValType}, allNum l = true → checkResultSub Δ l l = true
  | [], _ => rfl
  | .num n :: l, h => by
    simp only [allNum] at h
    simp [checkResultSub, sub_num, checkResultSub_self Δ h]

theorem forall2B_self (Δ : TypeCtx) :
    ∀ {l : List CValType}, allNum l = true → forall2B (Sub.checkK Δ .val) l l = true
  | [], _ => rfl
  | .num n :: l, h => by
    simp only [allNum] at h
    simp only [forall2B, forall2B_self Δ h, Bool.and_true]
    exact sub_num Δ n

theorem resSub_self (Δ : TypeCtx) {l : List CValType} (h : allNum l = true) :
    resSub Δ l l = true := by
  simp only [resSub, Sub.check, Sub.checkK, Ty.toList_ofList]
  exact forall2B_self Δ h

theorem resOk_num (Δ : TypeCtx) : ∀ {l : List CValType}, allNum l = true → resOk tyOkC Δ l = true
  | [], _ => rfl
  | .num n :: l, h => by
    simp only [allNum] at h
    have := resOk_num Δ h
    simp only [resOk, List.all_cons] at this ⊢
    rw [this]
    rfl

theorem popOk_of {Δ : TypeCtx} {ps r : List CValType} (h : allNum ps = true) :
    popOk Δ (r ++ ps) ps = true := by
  have hd : (r ++ ps).drop ((r ++ ps).length - ps.length) = ps := by
    simp
  unfold popOk
  rw [hd, checkResultSub_self Δ h]
  simp

/-! ## One instruction -/

/-- `checkInstr` on an instruction it hands to the oracle. -/
theorem checkInstr_of_atom {C : Context} {S : List CValType} {i : Instr} {n : Nat}
    {xs : List Nat} {out : List CValType}
    (hi : checkInstr atomC tyOkC C S i =
      match atomC C S i with
      | some (n, xs, out) => some (.normal n xs out)
      | none => none)
    (h : atomC C S i = some (n, xs, out)) :
    checkInstr atomC tyOkC C S i = some (.normal n xs out) := by
  rw [hi, h]

theorem atomC_of_numeric {C : Context} {S : List CValType} {i : Instr}
    {r : Nat × List Nat × List CValType}
    (hp : parametricCheck? (@tyOkC C.toTypeCtx) C S i = none) (hn : numericCheck? C S i = some r) :
    atomC C S i = some r := by
  simp [atomC, atomicA?, hp, hn]

theorem atomC_of_variable {C : Context} {S : List CValType} {i : Instr}
    {r : Nat × List Nat × List CValType}
    (hp : parametricCheck? (@tyOkC C.toTypeCtx) C S i = none) (hn : numericCheck? C S i = none)
    (hv : variableCheck? C S i = some r) :
    atomC C S i = some r := by
  simp [atomC, atomicA?, hp, hn, hv]

theorem atomC_of_parametric {C : Context} {S : List CValType} {i : Instr}
    {r : Nat × List Nat × List CValType}
    (hp : parametricCheck? (@tyOkC C.toTypeCtx) C S i = some r) :
    atomC C S i = some r := by
  simp [atomC, atomicA?, hp]

theorem numericType?_inits {i : Instr} {it : InstrType} (h : numericType? i = some it) :
    it.inits = [] := by
  unfold numericType? at h
  split at h <;> (try split at h) <;> cases h <;> rfl

set_option linter.unusedTactic false in
/-- **One fragment instruction**: silmaril-lean's checker takes the step `sigF` describes. -/
theorem checkInstr_of_sigF {C : Context} {t : List CValType} {i : Instr} {it : InstrType}
    (hs : sigF C.locals t i = some it) (hp : popOk C.toTypeCtx t.reverse it.params = true) :
    checkInstr atomC tyOkC C t.reverse i = some (.normal it.params.length it.inits it.results) := by
  have hfin : finishCheck C t.reverse it = some (it.params.length, it.inits, it.results) := by
    simp [finishCheck, hp]
  unfold sigF at hs
  split at hs <;> (try split at hs) <;> (try cases hs)
  all_goals first
    | (refine checkInstr_of_atom ?_ (atomC_of_variable ?_ ?_ ?_) <;>
        first | rfl | (simp [variableCheck?, variableType?, *]; done))
    | (refine checkInstr_of_atom ?_ (atomC_of_parametric ?_) <;>
        first | rfl | simpa [parametricCheck?, parametricType?, tyOkC, TyOk.check, tyChk] using hfin)
    | (unfold numericType? at hs
       split at hs <;> (try split at hs) <;> (try cases hs) <;>
       (refine checkInstr_of_atom ?_ (atomC_of_numeric ?_ ?_) <;>
         first | rfl | exact hfin | simp [numericCheck?, numericType?, *]))

/-- An initialised numeric local is initialised again without change. -/
theorem initLocals_set {C : Context} {x : Nat} {a : NumType}
    (h : C.locals[x]? = some ⟨.set, .num a⟩) :
    localsOk C [x] = true ∧ (C.initLocals [x]).locals = C.locals := by
  obtain ⟨hx, hget⟩ := List.getElem?_eq_some_iff.mp h
  have hl : localsOk C [x] = true := by simp [localsOk, h]
  have hset : C.locals.set x ⟨.set, .num a⟩ = C.locals := by
    rw [← hget]
    exact List.set_getElem_self hx
  refine ⟨hl, ?_⟩
  simpa only [Context.initLocals, List.map_cons, List.map_nil, h, Option.map_some,
    Option.getD_some, Context.withLocals, Context.setLocal] using hset

/-- The locals a fragment instruction initialises are initialised numeric locals already. -/
theorem sigF_inits {C : Context} {t : List CValType} {i : Instr} {it : InstrType}
    (hs : sigF C.locals t i = some it) :
    localsOk C it.inits = true ∧ (C.initLocals it.inits).locals = C.locals := by
  have nil : localsOk C [] = true ∧ (C.initLocals []).locals = C.locals := ⟨rfl, rfl⟩
  unfold sigF at hs
  split at hs <;> (try split at hs) <;> (try cases hs)
  all_goals first
    | exact nil
    | exact initLocals_set ‹_›
    | (rw [numericType?_inits hs]; exact nil)

set_option linter.unusedTactic false in
/-- One step of `stepF`, as silmaril-lean's sequence checker takes it. -/
theorem step_of_stepF {C : Context} {t t₁ : List CValType} {i : Instr}
    (h : stepF C.locals t i = some t₁) :
    ∃ n xs out, checkInstr atomC tyOkC C t.reverse i = some (.normal n xs out) ∧
      localsOk C xs = true ∧ resOk tyOkC C.toTypeCtx out = true ∧
      t.reverse.take (t.reverse.length - n) ++ out = t₁.reverse ∧
      (C.initLocals xs).locals = C.locals := by
  unfold stepF at h
  split at h <;> (try split at h) <;> (try cases h)
  rename_i it hs hc
  obtain ⟨hc1, hc2⟩ : popsF it.params.reverse t = true ∧ allNum it.results = true := by
    simpa only [Bool.and_eq_true] using hc
  obtain ⟨r, hr, hn⟩ := popsF_spec hc1
  have ht : t.reverse = r.reverse ++ it.params := by simp [hr]
  have hp : popOk C.toTypeCtx t.reverse it.params = true := by
    rw [ht]
    exact popOk_of (by rwa [allNum_reverse] at hn)
  obtain ⟨hl, hi⟩ := sigF_inits hs
  have hd : t.drop it.params.length = r := by simp [hr]
  have hst : t.reverse.take (t.reverse.length - it.params.length) ++ it.results =
      (it.results.reverse ++ t.drop it.params.length).reverse := by
    rw [ht, hd]
    simp
  exact ⟨_, _, _, checkInstr_of_sigF hs hp, hl, resOk_num _ hc2, hst, hi⟩

/-! ## Sequences, expressions, functions -/

/-- **`seqF` is sound against `checkSeq`**: when `seqF` accepts `is` from `t` ending at `t'`,
silmaril-lean's sequence checker accepts it from `t.reverse`, for every goal that `t'` matches. -/
theorem checkSeq_of_seqF : ∀ (is : List Instr) (C : Context) (t t' : List CValType)
    (goal : Option (List CValType)), seqF C.locals t is = some t' →
    (∀ g, goal = some g → numsEq t'.reverse g = true) →
    (checkSeq atomC tyOkC C t.reverse false goal is).isSome = true
  | [], C, t, t', goal, h, hg => by
    simp only [seqF, Option.some.injEq] at h
    subst h
    cases goal with
    | none => rfl
    | some g =>
      obtain ⟨heq, hn⟩ := numsEq_spec (hg g rfl)
      have hr : resSub C.toTypeCtx (List.replicate (endPad false t.reverse g) .botv ++ t.reverse)
          g = true := by
        simp only [endPad, Bool.false_eq_true, ite_false, List.replicate_zero, List.nil_append]
        rw [heq]
        exact resSub_self _ (heq ▸ hn)
      simp [checkSeq, hr, resOk_num _ (heq ▸ hn)]
  | i :: is, C, t, t', goal, h, hg => by
    simp only [seqF] at h
    split at h
    · rename_i t₁ h₁
      obtain ⟨n, xs, out, hc, hl, hr, hs, hi⟩ := step_of_stepF h₁
      have ih := checkSeq_of_seqF is (C.initLocals xs) t₁ t' goal (by rw [hi]; exact h) hg
      obtain ⟨r, hrr⟩ := Option.isSome_iff_exists.mp ih
      have hpad : padStack (padFor C false i) t.reverse = t.reverse := by
        simp [padFor, padStack]
      simp only [checkSeq, hpad, hc, hl, hr, Bool.and_self, ite_true, hs, hrr]
      rfl
    · cases h

/-- **`exprF` implies the default expression checker.** -/
theorem exprC_of_exprF {C : Context} {e : Expr} {ts : List CValType} (h : exprF C e ts = true) :
    exprC C e ts = true := by
  simp only [exprF, Bool.and_eq_true] at h
  obtain ⟨hn, hs⟩ := h
  split at hs
  · rename_i t ht
    have hc := checkSeq_of_seqF e C [] t (some ts) ht (fun g hg => by cases hg; exact hs)
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hc
    simp only [List.reverse_nil] at hr
    simp [exprC, checkExpr?, resOk_num _ hn, hr]
  · cases hs

/-- `funcCheck` is monotone in its expression checker. -/
theorem funcCheck_mono {e₁ e₂ : Context → Expr → List CValType → Bool}
    (he : ∀ C e ts, e₁ C e ts = true → e₂ C e ts = true) {C : Context} {f : Func} {d : DefType}
    (h : funcCheck tyOkC e₁ C f d = true) : funcCheck tyOkC e₂ C f d = true := by
  revert h
  unfold funcCheck
  split
  · split
    · split
      · exact he _ _ _
      · exact id
    · exact id
  · exact id

/-- **`funcF` implies the default function checker.** -/
theorem funcCheck_of_funcF {C : Context} {f : Func} {d : DefType} (h : funcF C f d = true) :
    defaultCheckers.func C f d = true :=
  funcCheck_mono (fun _ _ _ => exprC_of_exprF) h

end Silmaril.Proofs.Wasm.Auto2.Valid
