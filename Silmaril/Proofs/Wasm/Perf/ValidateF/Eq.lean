module

public import Silmaril.Wasm.Perf.ValidateF.Defs
import Std.Data.HashSet

/-!
# The validator with array lookups is silmaril's validator: proofs

The statements are restated in `Silmaril.Wasm.Perf.ValidateF.Thms`.

Under the invariant `fa.toList = C.funcs` (which `withLabel` and `initLocals` keep):
`directStepF_eq`, `padForF_eq`, and by mutual induction on instructions `checkInstrF_eq`,
`checkSeqF_eq`; then `checkExprF_eq`, `exportCheckF_eq`, `nodupF_eq` and
**`validateF_eq : validateF = validate?`**.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.ValidateF

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs
open Silmaril.Wasm.Perf.ValidateF

theorem withLabel_funcs (C : Context) (ts : List CValType) : (C.withLabel ts).funcs = C.funcs :=
  rfl

theorem withLocals_funcs : ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
    (C.withLocals xs lts).funcs = C.funcs
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | C, x :: xs, lt :: lts => withLocals_funcs (C.setLocal x lt) xs lts

theorem initLocals_funcs (C : Context) (xs : List Nat) : (C.initLocals xs).funcs = C.funcs :=
  withLocals_funcs C xs _

theorem withLocals_refs : ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
    (C.withLocals xs lts).refs = C.refs
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | C, x :: xs, lt :: lts => withLocals_refs (C.setLocal x lt) xs lts

theorem initLocals_refs (C : Context) (xs : List Nat) : (C.initLocals xs).refs = C.refs :=
  withLocals_refs C xs _

/-- The invariant of the hash set of `C.refs`. -/
abbrev RefsInv (rs : Std.HashSet Nat) (C : Context) : Prop :=
  ∀ n, rs.contains n = decide (n ∈ C.refs)

theorem refsInv_ofList (C : Context) : RefsInv (Std.HashSet.ofList C.refs) C := fun n => by
  rw [Std.HashSet.contains_ofList, List.contains_eq_mem]

theorem lookup_fa {fa : Array DefType} {C : Context} (h : fa.toList = C.funcs) (n : Nat) :
    fa[n]? = C.funcs[n]? := by
  rw [← h, Array.getElem?_toList]

/-! ## The locals in an array -/

/-- The context the fast functions see: the specification's, with its list of locals emptied
(the locals live in an array beside it). -/
abbrev reset (C : Context) : Context := { C with locals := [] }

theorem withLocals_eq : ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
    C.withLocals xs lts = { C with locals := (C.withLocals xs lts).locals }
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | C, x :: xs, lt :: lts => by
    show (C.setLocal x lt).withLocals xs lts = _
    rw [withLocals_eq (C.setLocal x lt) xs lts]
    rfl

theorem initLocals_reset (C : Context) (xs : List Nat) : reset (C.initLocals xs) = reset C := by
  unfold Context.initLocals
  rw [withLocals_eq]

theorem lookupL {la : Array LocalType} {C : Context} (hl : la.toList = C.locals) (n : Nat) :
    la[n]? = C.locals[n]? := by
  rw [← hl, Array.getElem?_toList]

theorem withLocalsL_toList : ∀ (la : Array LocalType) (C : Context) (xs : List Nat)
    (lts : List LocalType), la.toList = C.locals →
      (withLocalsL la xs lts).toList = (C.withLocals xs lts).locals
  | la, C, x :: xs, lt :: lts, hl =>
    withLocalsL_toList (la.setIfInBounds x lt) (C.setLocal x lt) xs lts
      (by rw [Array.toList_setIfInBounds, hl]; rfl)
  | _, _, [], _, hl => hl
  | _, _, _ :: _, [], hl => hl

theorem initLocalsL_toList {la : Array LocalType} {C : Context} (hl : la.toList = C.locals)
    (xs : List Nat) : (initLocalsL la xs).toList = (C.initLocals xs).locals := by
  unfold initLocalsL Context.initLocals
  simp only [lookupL hl]
  exact withLocalsL_toList la C xs _ hl

theorem localsOkL_eq {la : Array LocalType} {C : Context} (hl : la.toList = C.locals)
    (xs : List Nat) : localsOkL la xs = localsOk C xs := by
  unfold localsOkL localsOk
  simp only [lookupL hl]

/-- At a local instruction the atom oracle is `variableCheck?`. -/
theorem atomC_local (C : Context) (S : List CValType) (i : Instr)
    (h : (∃ x, i = .localGet x) ∨ (∃ x, i = .localSet x) ∨ (∃ x, i = .localTee x)) :
    atomC C S i = (variableType? C i).bind (finishCheck C S) := by
  rcases h with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
  · unfold atomC atomicA? variableCheck?
    cases (variableType? C _).bind (finishCheck C S) <;> rfl

/-- `directStep` at an instruction it leaves to the atom oracle. -/
theorem directStep_atom (C : Context) (S : List CValType) (i : Instr)
    (h : (∃ x, i = .localGet x) ∨ (∃ x, i = .localSet x) ∨ (∃ x, i = .localTee x)) :
    directStep atomC tyOkC C S i =
      (match atomC C S i with
       | some (n, xs, out) => some (.normal n xs out)
       | none => none) := by
  rcases h with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rfl

theorem localType_eq {la : Array LocalType} {C : Context} (hl : la.toList = C.locals)
    (i : Instr)
    (hi : (∃ x, i = .localGet x) ∨ (∃ x, i = .localSet x) ∨ (∃ x, i = .localTee x)) :
    localType la i = variableType? C i := by
  rcases hi with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
  · simp only [localType, variableType?, lookupL hl]
    rfl

/-- Away from the local instructions, `directStep` does not read the context's locals. -/
theorem directStep_locals (C : Context) (S : List CValType) (i : Instr)
    (hg : ∀ x, i = .localGet x → False) (hs : ∀ x, i = .localSet x → False)
    (ht : ∀ x, i = .localTee x → False) :
    directStep atomC tyOkC (reset C) S i = directStep atomC tyOkC C S i := by
  cases i
  all_goals first
    | rfl
    | (exfalso; first | exact hg _ rfl | exact hs _ rfl | exact ht _ rfl)

/-! ## The fast step -/

/-- `directStep` at `ref.func`, unfolded through the atom oracle. -/
theorem directStep_refFunc (C : Context) (S : List CValType) (x : FuncIdx) :
    directStep atomC tyOkC C S (.refFunc x) =
      (match checkBySig C.toTypeCtx (refSig? (tyOkC C.toTypeCtx) C S.getLast? (.refFunc x)) S with
       | some (n, xs, out) => some (.normal n xs out)
       | none => none) := rfl

theorem refFuncSig_eq {fa : Array DefType} {rs : Std.HashSet Nat} {C : Context}
    (h : fa.toList = C.funcs) (hr : RefsInv rs C) (x : FuncIdx) (top : Option CValType) :
    refFuncSig fa rs x = refSig? (tyOkC C.toTypeCtx) C top (.refFunc x) := by
  unfold refFuncSig refSig?
  simp only [lookup_fa h, hr, decide_eq_true_eq]
  rfl

/-- The step at a local instruction. -/
theorem directStepF_local {la : Array LocalType} {C : Context} (hl : la.toList = C.locals) (S : List CValType) (i : Instr)
    (hi : (∃ x, i = .localGet x) ∨ (∃ x, i = .localSet x) ∨ (∃ x, i = .localTee x)) :
    (match (localType la i).bind (finishCheck (reset C) S) with
     | some (n, xs, out) => some (StepRes.normal n xs out)
     | none => none) = directStep atomC tyOkC C S i := by
  rw [directStep_atom C S i hi, atomC_local C S i hi, localType_eq hl i hi]
  rfl

theorem directStepF_eq {fa : Array DefType} {rs : Std.HashSet Nat} {la : Array LocalType}
    {C : Context} (h : fa.toList = C.funcs) (hr : RefsInv rs C) (hl : la.toList = C.locals)
    (S : List CValType) (i : Instr) :
    directStepF fa rs la (reset C) S i = directStep atomC tyOkC C S i := by
  unfold directStepF
  split
  · exact directStepF_local hl S _ (Or.inl ⟨_, rfl⟩)
  · exact directStepF_local hl S _ (Or.inr (Or.inl ⟨_, rfl⟩))
  · exact directStepF_local hl S _ (Or.inr (Or.inr ⟨_, rfl⟩))
  · simp only [directStep, lookup_fa h]
    rfl
  · simp only [directStep, lookup_fa h]
    rfl
  · rename_i x
    rw [directStep_refFunc, refFuncSig_eq h hr x S.getLast?]
    rfl
  · apply directStep_locals <;> assumption

theorem padForF_eq {fa : Array DefType} {C : Context} (h : fa.toList = C.funcs) (poly : Bool)
    (i : Instr) : padForF fa (reset C) poly i = padFor C poly i := by
  unfold padForF padFor
  cases poly with
  | false => rfl
  | true =>
    simp only [ite_true]
    split
    · simp only [arityBound, extraArity, funcArity, lookup_fa h]
    · simp only [arityBound, extraArity, funcArity, lookup_fa h]
    · rfl

mutual

set_option linter.unusedTactic false in
theorem checkInstrF_eq (fa : Array DefType) (rs : Std.HashSet Nat) (i : Instr) :
    ∀ (C : Context) (la : Array LocalType), fa.toList = C.funcs → RefsInv rs C →
      la.toList = C.locals → ∀ (S : List CValType),
      checkInstrF fa rs la (reset C) S i = checkInstr atomC tyOkC C S i := by
  intro C la h hr hl S
  cases hi : i
  case block bt body =>
    have ih' : ∀ ts s p g, checkSeqF fa rs la ((reset C).withLabel ts) s p g body =
        checkSeq atomC tyOkC (C.withLabel ts) s p g body := fun ts =>
      checkSeqF_eq fa rs body (C.withLabel ts) la h hr hl
    simp only [checkInstrF, checkInstr, ih', localsOkL_eq hl]
    rfl
  case loop bt body =>
    have ih' : ∀ ts s p g, checkSeqF fa rs la ((reset C).withLabel ts) s p g body =
        checkSeq atomC tyOkC (C.withLabel ts) s p g body := fun ts =>
      checkSeqF_eq fa rs body (C.withLabel ts) la h hr hl
    simp only [checkInstrF, checkInstr, ih', localsOkL_eq hl]
    rfl
  case if_ bt b₁ b₂ =>
    show checkInstrF fa rs la (reset C) S (.if_ bt b₁ b₂) = checkInstr atomC tyOkC C S (.if_ bt b₁ b₂)
    have ih₁' : ∀ ts s p g, checkSeqF fa rs la ((reset C).withLabel ts) s p g b₁ =
        checkSeq atomC tyOkC (C.withLabel ts) s p g b₁ := fun ts =>
      checkSeqF_eq fa rs b₁ (C.withLabel ts) la h hr hl
    have ih₂' : ∀ ts s p g, checkSeqF fa rs la ((reset C).withLabel ts) s p g b₂ =
        checkSeq atomC tyOkC (C.withLabel ts) s p g b₂ := fun ts =>
      checkSeqF_eq fa rs b₂ (C.withLabel ts) la h hr hl
    simp only [checkInstrF, checkInstr, ih₁', ih₂', localsOkL_eq hl]
    rfl
  case tryTable bt cs body =>
    have ih' : ∀ ts s p g, checkSeqF fa rs la ((reset C).withLabel ts) s p g body =
        checkSeq atomC tyOkC (C.withLabel ts) s p g body := fun ts =>
      checkSeqF_eq fa rs body (C.withLabel ts) la h hr hl
    simp only [checkInstrF, checkInstr, ih', localsOkL_eq hl]
    rfl
  case select ts =>
    cases ts with
    | none =>
      simp only [checkInstrF, checkInstr]
      rfl
    | some ts => exact directStepF_eq h hr hl S _
  all_goals (subst hi; exact directStepF_eq h hr hl S _)
termination_by sizeOf i
decreasing_by all_goals (subst_vars; simp; all_goals omega)

set_option linter.unusedTactic false in
theorem checkSeqF_eq (fa : Array DefType) (rs : Std.HashSet Nat) (l : List Instr) :
    ∀ (C : Context) (la : Array LocalType), fa.toList = C.funcs → RefsInv rs C →
      la.toList = C.locals → ∀ (s : List CValType) (poly : Bool) (goal : Option (List CValType)),
      checkSeqF fa rs la (reset C) s poly goal l = checkSeq atomC tyOkC C s poly goal l := by
  intro C la h hr hl s poly goal
  match l with
  | [] => rfl
  | i :: rest =>
    have ihi : ∀ S, checkInstrF fa rs la (reset C) S i = checkInstr atomC tyOkC C S i :=
      checkInstrF_eq fa rs i C la h hr hl
    have ihs : ∀ s p g, checkSeqF fa rs la (reset C) s p g rest =
        checkSeq atomC tyOkC C s p g rest :=
      checkSeqF_eq fa rs rest C la h hr hl
    have ihs' : ∀ xs s p g, checkSeqF fa rs (initLocalsL la xs) (reset C) s p g rest =
        checkSeq atomC tyOkC (C.initLocals xs) s p g rest := fun xs => by
      rw [← initLocals_reset C xs]
      exact checkSeqF_eq fa rs rest (C.initLocals xs) (initLocalsL la xs)
        ((initLocals_funcs C xs).symm ▸ h) (fun n => by rw [initLocals_refs]; exact hr n)
        (initLocalsL_toList hl xs)
    simp only [checkSeqF, checkSeq, padForF_eq h, ihi, ihs, ihs', localsOkL_eq hl]
    rfl
termination_by sizeOf l
decreasing_by all_goals (simp_wf; all_goals omega)

end

theorem checkExprF_eq {fa : Array DefType} {rs : Std.HashSet Nat} {C : Context}
    (h : fa.toList = C.funcs) (hr : RefsInv rs C) (e : Expr) (ts : List CValType) :
    checkExprF fa rs C e ts = exprC C e ts := by
  unfold checkExprF exprC checkExpr?
  rw [checkSeqF_eq fa rs e C C.locals.toArray h hr List.toList_toArray]
  rfl

theorem funcCheck_eq {fa : Array DefType} {rs : Std.HashSet Nat} {C : Context}
    (h : fa.toList = C.funcs) (hr : RefsInv rs C) (f : Func) (d : DefType) :
    funcCheck tyOkC (checkExprF fa rs) C f d = funcCheck tyOkC exprC C f d := by
  unfold funcCheck
  split
  · split
    · rename_i ps rs _
      split
      · rename_i lts _
        exact checkExprF_eq (C := C.funcBody ps.toList rs.toList lts) h hr _ _
      · rfl
    · rfl
  · rfl

theorem elemCheckF_eq {fa : Array DefType} {rs : Std.HashSet Nat} {C : Context}
    (h : fa.toList = C.funcs) (hr : RefsInv rs C) (e : Elem) :
    elemCheck? tyOkC (constOk (checkExprF fa rs)) C e = defaultCheckers.elem? C e := by
  have hc : ∀ ex t, constOk (checkExprF fa rs) C ex t = constC C ex t := fun ex t => by
    unfold constOk constC constOk
    rw [checkExprF_eq h hr]
  show _ = elemCheck? tyOkC constC C e
  unfold elemCheck? elemModeCheck
  simp only [hc]

theorem exportCheckF_eq {fa : Array DefType} {C : Context} (h : fa.toList = C.funcs)
    (e : Export) : exportCheckF fa C e = exportCheck? C e := by
  unfold exportCheckF exportCheck?
  split
  · rename_i x hx
    rw [hx, externIdxCheck?, lookup_fa h]
  · rfl

theorem nodupGo_eq : ∀ (seen : Std.HashSet String) (l : List String),
    nodupGo seen l = decide (l.Nodup ∧ ∀ x ∈ l, x ∉ seen)
  | seen, [] => by simp [nodupGo]
  | seen, x :: xs => by
    unfold nodupGo
    rw [nodupGo_eq (seen.insert x) xs]
    by_cases hx : x ∈ seen
    · have hc : seen.contains x = true := Std.HashSet.contains_iff_mem.mpr hx
      simp [hc, hx]
    · have hc : seen.contains x = false := by
        cases hcx : seen.contains x with
        | false => rfl
        | true => exact absurd (Std.HashSet.contains_iff_mem.mp hcx) hx
      have hins : ∀ y, y ∈ seen.insert x ↔ x = y ∨ y ∈ seen := fun y => by
        rw [Std.HashSet.mem_insert, beq_iff_eq]
      simp only [hc, Bool.false_eq_true, ite_false, List.nodup_cons, List.mem_cons,
        forall_eq_or_imp, hins]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨hn, hs⟩
        refine ⟨⟨fun hm => (hs x hm) (Or.inl rfl), hn⟩, hx, fun y hy => ?_⟩
        intro hy'
        exact hs y hy (Or.inr hy')
      · rintro ⟨⟨hnx, hn⟩, _, hs⟩
        refine ⟨hn, fun y hy hor => ?_⟩
        rcases hor with hxy | hy'
        · subst hxy
          exact hnx hy
        · exact hs y hy hy'

theorem nodupF_eq (l : List String) : nodupF l = decide l.Nodup := by
  unfold nodupF
  rw [nodupGo_eq]
  have he : ∀ x, x ∉ (∅ : Std.HashSet String) := fun _ => Std.HashSet.not_mem_empty
  simp only [he, not_false_eq_true, implies_true, and_true]

/-- **`validateF` is silmaril's `validate?`.** -/
theorem validateF_eq : validateF = validate? := by
  funext m
  have hfa : ∀ C : Context, C.funcs.toArray.toList = C.funcs := fun _ => List.toList_toArray
  have hf : ∀ (C : Context) (fdts : List DefType),
      allPairs (funcCheck tyOkC (checkExprF C.funcs.toArray (Std.HashSet.ofList C.refs)) C)
        m.funcs fdts = allPairs (defaultCheckers.func C) m.funcs fdts := fun C fdts =>
    congrArg (fun p => allPairs p m.funcs fdts) (funext fun f => funext fun d =>
      funcCheck_eq (hfa C) (refsInv_ofList C) f d)
  have hel : ∀ (C : Context) (rts : List CRefType),
      allPairs (fun e rt => elemCheck? tyOkC
          (constOk (checkExprF C.funcs.toArray (Std.HashSet.ofList C.refs))) C e == some rt)
        m.elems rts = allPairs (fun e rt => defaultCheckers.elem? C e == some rt) m.elems rts :=
    fun C rts => congrArg (fun p => allPairs p m.elems rts) (funext fun e => funext fun rt => by
      rw [elemCheckF_eq (hfa C) (refsInv_ofList C) e])
  have he : ∀ C : Context, m.exports.mapM (exportCheckF C.funcs.toArray C) =
      m.exports.mapM (defaultCheckers.export? C) := fun C =>
    congrArg (fun g => m.exports.mapM g) (funext fun e => exportCheckF_eq (hfa C) e)
  show checkModuleF m = checkModule? defaultCheckers m
  unfold checkModuleF checkModule?
  simp only [hf, hel, he, nodupF_eq, decide_eq_true_eq]

end Silmaril.Proofs.Wasm.Perf.ValidateF
