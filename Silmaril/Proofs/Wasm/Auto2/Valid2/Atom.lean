module

public import Silmaril.Wasm.Auto2.Valid2.Defs
public import Silmaril.Wasm.Auto2.Valid.Thms

/-!
# The extended checker's atoms against silmaril-lean's instruction checker

`atomG_sound`: when `atomG` (`Valid`'s `stepF`, else `stepM`: globals, `select`, memory) takes a
step, silmaril-lean's `checkInstr atomC tyOkC` takes the same step on the reversed stack, and the
locals it initialises are already set (`SetIn`). `instrC_atom`: the direct cases of `instrC` are
steps of `atomG`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Valid2

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Valid Silmaril.Wasm.Auto2.Valid2
open Silmaril.Proofs.Wasm.Auto2.Valid

/-! ## Initialised locals -/

/-- Every local of `xs` is already set in `C`. -/
def SetIn (C : Context) (xs : List Nat) : Prop := ∀ x ∈ xs, ∃ a, C.locals[x]? = some ⟨.set, a⟩

theorem SetIn.nil (C : Context) : SetIn C [] := fun _ h => by cases h

theorem SetIn.append {C : Context} {xs ys : List Nat} (h₁ : SetIn C xs) (h₂ : SetIn C ys) :
    SetIn C (xs ++ ys) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

theorem localsOk_of_setIn {C : Context} {xs : List Nat} (h : SetIn C xs) : localsOk C xs = true := by
  simp only [localsOk, List.all_eq_true]
  intro x hx
  obtain ⟨a, ha⟩ := h x hx
  simp [ha]

theorem setLocal_self {C : Context} {x : Nat} {lt : LocalType} (h : C.locals[x]? = some lt) :
    C.setLocal x lt = C := by
  obtain ⟨hx, hget⟩ := List.getElem?_eq_some_iff.mp h
  have hset : C.locals.set x lt = C.locals := by
    rw [← hget]
    exact List.set_getElem_self hx
  unfold Context.setLocal
  rw [hset]

theorem withLocals_self (C : Context) :
    ∀ xs : List Nat, SetIn C xs →
      C.withLocals xs (xs.map fun x => ⟨.set, ((C.locals[x]?).map LocalType.type).getD default⟩) =
        C
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨a, ha⟩ := h x (List.mem_cons_self ..)
    have hs : C.setLocal x ⟨.set, ((C.locals[x]?).map LocalType.type).getD default⟩ = C := by
      rw [ha]
      exact setLocal_self ha
    simp only [List.map_cons, Context.withLocals, hs]
    exact withLocals_self C xs fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Initialising locals that are already set leaves the context unchanged. -/
theorem initLocals_self {C : Context} {xs : List Nat} (h : SetIn C xs) : C.initLocals xs = C :=
  withLocals_self C xs h

/-! ## Stacks of number types -/

theorem ntEq_refl : ∀ a : NumType, ntEq a a = true
  | .int .i32 => rfl
  | .int .i64 => rfl
  | .float .f32 => rfl
  | .float .f64 => rfl

theorem topSub_app (Δ : TypeCtx) {ps : List CValType} (h : allNum ps = true) (r : List CValType) :
    topSub Δ (r ++ ps) ps = true := by
  have hd : (r ++ ps).drop ((r ++ ps).length - ps.length) = ps := by simp
  simp only [topSub, hd, resSub_self Δ h, Bool.and_true, decide_eq_true_eq]
  simp

theorem stepA_app (Δ : TypeCtx) {ps : List CValType} (h : allNum ps = true) (r : List CValType)
    (xs : List Nat) (out : List CValType) :
    stepA Δ (r ++ ps) ps xs out = some (.normal ps.length xs out) := by
  simp [stepA, topSub_app Δ h]

theorem stepB_app (Δ : TypeCtx) {ps : List CValType} (h : allNum ps = true) (r : List CValType) :
    stepB Δ (r ++ ps) ps = some (.poly ps) := by
  simp [stepB, topSub_app Δ h]

theorem listSubCheck_self (Δ : TypeCtx) :
    ∀ {l : List CValType}, allNum l = true → listSubCheck Δ l l = true
  | [], _ => rfl
  | .num n :: l, h => by
    simp only [allNum] at h
    simp [listSubCheck, sub_num, listSubCheck_self Δ h]

theorem popsOk_app (Δ : TypeCtx) {ps : List CValType} (h : allNum ps = true) (r : List CValType) :
    popsOk Δ (r ++ ps) ps = true := by
  have hd : (r ++ ps).drop ((r ++ ps).length - ps.length) = ps := by simp
  simp only [popsOk, hd, listSubCheck_self Δ h, Bool.and_true, decide_eq_true_eq]
  simp

/-- A stack accepted by `popsF ps` (top first), reversed: the reversed parameters on top. -/
theorem rev_of_popsF {ps t : List CValType} (h : popsF ps.reverse t = true) :
    ∃ r, t.reverse = r ++ ps ∧ t.drop ps.length = r.reverse ∧ allNum ps = true := by
  obtain ⟨r, rfl, hn⟩ := popsF_spec h
  refine ⟨r.reverse, by simp, by simp, ?_⟩
  rwa [allNum_reverse] at hn

/-- The stack after popping `ps` and pushing `out`, as `checkSeq` computes it. -/
theorem stack_after {ps out t : List CValType} {r : List CValType} (ht : t.reverse = r ++ ps)
    (hd : t.drop ps.length = r.reverse) :
    t.reverse.take (t.reverse.length - ps.length) ++ out = (out.reverse ++ t.drop ps.length).reverse := by
  rw [ht, hd]
  simp

/-! ## The atoms of `atomG` -/

/-- What a normal step of the extended checker promises: silmaril-lean's step on the reversed
stack, already-set locals, valid results, and the new stack. -/
def NextOk (C : Context) (t : List CValType) (i : Instr) (t' : List CValType) : Prop :=
  ∃ n xs out, checkInstr atomC tyOkC C t.reverse i = some (.normal n xs out) ∧ SetIn C xs ∧
    resOk tyOkC C.toTypeCtx out = true ∧ t.reverse.take (t.reverse.length - n) ++ out = t'.reverse

theorem sigF_setIn {L : List LocalType} {t : List CValType} {i : Instr} {it : InstrType}
    (hs : sigF L t i = some it) : ∀ x ∈ it.inits, ∃ a, L[x]? = some ⟨.set, a⟩ := by
  unfold sigF at hs
  split at hs <;> (try split at hs) <;> (try cases hs)
  all_goals first
    | (intro x hx; simp at hx; done)
    | (intro x hx
       simp only [List.mem_singleton] at hx
       rw [hx]
       exact ⟨_, by assumption⟩)
    | (rw [numericType?_inits hs]; intro x hx; simp at hx)

set_option linter.unusedTactic false in
/-- A step of `Valid`'s fragment (`stepF`). -/
theorem nextOk_of_stepF {C : Context} {t t' : List CValType} {i : Instr}
    (h : stepF C.locals t i = some t') : NextOk C t i t' := by
  unfold stepF at h
  split at h <;> (try split at h) <;> (try cases h)
  rename_i it hs hc
  obtain ⟨hc1, hc2⟩ : popsF it.params.reverse t = true ∧ allNum it.results = true := by
    simpa only [Bool.and_eq_true] using hc
  obtain ⟨r, hr, hd, hn⟩ := rev_of_popsF (by simpa using hc1)
  have hp : popOk C.toTypeCtx t.reverse it.params = true := by
    rw [hr]
    exact popOk_of hn
  exact ⟨_, _, _, checkInstr_of_sigF hs hp, sigF_setIn hs, resOk_num _ hc2,
    stack_after hr hd⟩

set_option linter.unusedTactic false in
theorem sigM_inits {C : Context} {t : List CValType} {i : Instr} {it : InstrType}
    (hs : sigM C t i = some it) : it.inits = [] := by
  unfold sigM at hs
  repeat (first | (cases hs <;> rfl) | (split at hs) | (unfold memorySig? at hs))

/-- `checkInstr` on a memory instruction: families A do not apply, nor do table instructions. -/
theorem checkInstr_of_mem {C : Context} {S : List CValType} {i : Instr} {it : InstrType}
    (hi : checkInstr atomC tyOkC C S i =
      match atomC C S i with
      | some (n, xs, out) => some (.normal n xs out)
      | none => none)
    (ha : atomicA? (@tyOkC C.toTypeCtx) C S i = none) (ht : tableSig? C i = none)
    (hs : memorySig? C i = some it) (hp : popsOk C.toTypeCtx S it.params = true) :
    checkInstr atomC tyOkC C S i = some (.normal it.params.length it.inits it.results) := by
  rw [hi]
  simp [atomC, ha, atomicB?, tableCheck?, ht, memoryCheck?, checkBySig, hs, hp]

theorem stepA_select_none (Δ : TypeCtx) (r : List CValType) (a : NumType) :
    stepA Δ (r ++ [.num a, .num a, Ty.i32]) [.botv, .botv, Ty.i32] [] [.botv] = none := by
  simp [stepA, topSub, resSub, Sub.check, Sub.checkK, TypeCtx.checkVal, forall2B]

/-- `checkInstr` on an untyped `select` of two operands of number type `b`. -/
theorem checkInstr_select {C : Context} {b : NumType} (r : List CValType) :
    checkInstr atomC tyOkC C (r ++ [.num b, .num b, Ty.i32]) (.select none) =
      some (.normal 3 [] [.num b]) := by
  have hsel : selectImplType? (r ++ [.num b, .num b, Ty.i32]) = some (.num b) := by
    simp [selectImplType?, Ty.IsNumOrVec]
  have hp : popOk C.toTypeCtx (r ++ [.num b, .num b, Ty.i32]) [.num b, .num b, Ty.i32] = true :=
    popOk_of (by rfl)
  have hpar : parametricCheck? (@tyOkC C.toTypeCtx) C (r ++ [.num b, .num b, Ty.i32])
      (.select none) = some (3, [], [.num b]) := by
    simp only [parametricCheck?, parametricType?, hsel, Option.bind_some, finishCheck, hp]
    rfl
  simp only [checkInstr]
  rw [stepA_select_none]
  simp only [directStep, atomC, atomicA?, hpar]
  rfl

/-- **One atom of `sigM`**: silmaril-lean's checker takes the step `sigM` describes. -/
theorem checkInstr_of_sigM {C : Context} {t r : List CValType} {i : Instr} {it : InstrType}
    (hs : sigM C t i = some it) (hr : t.reverse = r ++ it.params) (hn : allNum it.params = true) :
    checkInstr atomC tyOkC C t.reverse i = some (.normal it.params.length it.inits it.results) := by
  have hp : popOk C.toTypeCtx t.reverse it.params = true := by rw [hr]; exact popOk_of hn
  have hq : popsOk C.toTypeCtx t.reverse it.params = true := by rw [hr]; exact popsOk_app _ hn _
  have hfin : finishCheck C t.reverse it = some (it.params.length, it.inits, it.results) := by
    simp [finishCheck, hp]
  unfold sigM at hs
  split at hs
  all_goals first
    | (split at hs <;> cases hs
       exact checkInstr_of_atom rfl (atomC_of_variable rfl rfl (by
         simpa [variableCheck?, variableType?, *] using hfin)))
    | (split at hs <;> (try split at hs) <;> cases hs
       obtain rfl := ntEq_eq ‹_›
       rw [hr]
       exact checkInstr_select r)
    | cases hs
    | exact checkInstr_of_mem rfl rfl rfl hs hq

set_option linter.unusedTactic false in
/-- A step of `sigM` (globals, `select`, memory). -/
theorem nextOk_of_stepM {C : Context} {t t' : List CValType} {i : Instr}
    (h : stepM C t i = some t') : NextOk C t i t' := by
  unfold stepM at h
  split at h <;> (try split at h) <;> (try cases h)
  rename_i it hs hc
  obtain ⟨hc1, hc2⟩ : popsF it.params.reverse t = true ∧ allNum it.results = true := by
    simpa only [Bool.and_eq_true] using hc
  obtain ⟨r, hr, hd, hn⟩ := rev_of_popsF (by simpa using hc1)
  refine ⟨_, _, _, checkInstr_of_sigM hs hr hn, ?_, resOk_num _ hc2, stack_after hr hd⟩
  rw [sigM_inits hs]
  exact SetIn.nil C

/-- **A step of `atomG`**. -/
theorem nextOk_of_atomG {C : Context} {t t' : List CValType} {i : Instr}
    (h : atomG C t i = some t') : NextOk C t i t' := by
  unfold atomG at h
  split at h
  · cases h
    exact nextOk_of_stepF ‹_›
  · exact nextOk_of_stepM h

end Silmaril.Proofs.Wasm.Auto2.Valid2
