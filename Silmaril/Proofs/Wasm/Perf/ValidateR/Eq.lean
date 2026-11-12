module

public import Silmaril.Wasm.Perf.ValidateR.Defs
public import Silmaril.Wasm.Perf.ValidateF.Thms

/-!
# The reversed-stack validator is silmaril's validator: proofs

The statements are restated in `Silmaril.Wasm.Perf.ValidateR.Thms`.

* Stack reading: `prefixSub_eq` (`prefixSub Δ R t.reverse` is `topSub Δ R.reverse t`), so
  `stepAR_eq`, `stepBR_eq`, `finishCheckR_eq`, `checkBySigR_eq`, `topHeapR_eq`;
* the atom oracle and the direct step: `atomR_eq`, `directStepGR_eq`, `directStepR_eq`;
* the direct paths: `fastR_cases` (`fastR` is `slow`, or the general step read as an `FStep`);
* by mutual induction on instructions, `checkInstrR_eq` and **`checkSeqR_eq`**:
  `checkSeqR … r r.length poly goal acc l` is `checkSeqF … r.reverse poly goal l` with the
  dead-code count dropped and the locals reversed onto `acc`;
* **`validateR_eq : validateR = validate?`**, registered with `@[csimp]`
  (`validate?_eq_validateR`, in the header).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.ValidateR

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs
open Silmaril.Wasm.Perf.ValidateF Silmaril.Wasm.Perf.ValidateR

/-! ## Reading operands from the head -/

/-- The pointwise test every stack reader of silmaril reduces to. -/
def topSubF (Δ : TypeCtx) (S t : List CValType) : Bool :=
  decide (t.length ≤ S.length) && forall2B Δ.checkVal (S.drop (S.length - t.length)) t

theorem forall2B_snoc (f : CValType → CValType → Bool) (x y : CValType) :
    ∀ a b : List CValType, forall2B f (a ++ [x]) (b ++ [y]) = (forall2B f a b && f x y)
  | [], [] => by simp [forall2B]
  | [], _ :: b => by cases b <;> simp [forall2B]
  | _ :: a, [] => by cases a <;> simp [forall2B]
  | p :: a, q :: b => by
    simp only [List.cons_append, forall2B, forall2B_snoc f x y a b, Bool.and_assoc]

theorem forall2B_reverse (f : CValType → CValType → Bool) :
    ∀ a b : List CValType, forall2B f a.reverse b.reverse = forall2B f a b
  | [], [] => rfl
  | [], q :: b => by
    simp only [List.reverse_nil, List.reverse_cons]
    cases b.reverse <;> rfl
  | p :: a, [] => by
    simp only [List.reverse_nil, List.reverse_cons]
    cases a.reverse <;> rfl
  | p :: a, q :: b => by
    simp only [List.reverse_cons, forall2B_snoc, forall2B_reverse f a b, forall2B, Bool.and_comm]

theorem prefixSub_take (Δ : TypeCtx) : ∀ (R u : List CValType),
    prefixSub Δ R u = (decide (u.length ≤ R.length) && forall2B Δ.checkVal (R.take u.length) u)
  | _, [] => by simp [prefixSub, forall2B]
  | [], _ :: _ => by simp [prefixSub]
  | x :: R, p :: u => by
    simp only [prefixSub, prefixSub_take Δ R u, List.length_cons, List.take_succ_cons, forall2B,
      Nat.add_le_add_iff_right]
    cases decide (u.length ≤ R.length) <;> simp

theorem reverse_drop_sub (R : List CValType) (n : Nat) :
    R.reverse.drop (R.length - n) = (R.take n).reverse := by
  rw [List.drop_reverse]
  by_cases h : n ≤ R.length
  · rw [Nat.sub_sub_self h]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- **Operands at the head of the reversed stack.** -/
theorem prefixSub_eq (Δ : TypeCtx) (R t : List CValType) :
    prefixSub Δ R t.reverse = topSubF Δ R.reverse t := by
  unfold topSubF
  simp only [prefixSub_take, List.length_reverse]
  rw [reverse_drop_sub, ← forall2B_reverse Δ.checkVal (R.take t.length).reverse t,
    List.reverse_reverse]

theorem resSub_eq (Δ : TypeCtx) (a b : List CValType) :
    resSub Δ a b = forall2B Δ.checkVal a b := by
  simp only [resSub, Sub.check, Sub.checkK, Silmaril.Wasm.Validation.Ty.toList_ofList]

theorem checkResultSub_eq (Δ : TypeCtx) :
    ∀ a b : List CValType, checkResultSub Δ a b = forall2B Δ.checkVal a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: a, _ :: b => by
    simp only [checkResultSub, forall2B, checkResultSub_eq Δ a b]
    rfl

theorem listSubCheck_eq (Δ : TypeCtx) :
    ∀ a b : List CValType, listSubCheck Δ a b = forall2B Δ.checkVal a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: a, _ :: b => by
    simp only [listSubCheck, forall2B, listSubCheck_eq Δ a b]
    rfl

theorem topSub_eq (Δ : TypeCtx) (S t : List CValType) : topSub Δ S t = topSubF Δ S t := by
  simp only [topSub, topSubF, resSub_eq]

theorem popOk_eq (Δ : TypeCtx) (S t : List CValType) : popOk Δ S t = topSubF Δ S t := by
  simp only [popOk, topSubF, checkResultSub_eq]

theorem popsOk_eq (Δ : TypeCtx) (S t : List CValType) : popsOk Δ S t = topSubF Δ S t := by
  simp only [popsOk, topSubF, listSubCheck_eq]

theorem stepAR_eq (Δ : TypeCtx) (R t₁ : List CValType) (xs : List Nat) (out : List CValType) :
    stepAR Δ R t₁ xs out = stepA Δ R.reverse t₁ xs out := by
  simp only [stepAR, stepA, prefixSub_eq, topSub_eq]

theorem stepBR_eq (Δ : TypeCtx) (R t₁ : List CValType) :
    stepBR Δ R t₁ = stepB Δ R.reverse t₁ := by
  simp only [stepBR, stepB, prefixSub_eq, topSub_eq]

theorem finishCheckR_eq (C : Context) (R : List CValType) :
    finishCheckR C R = finishCheck C R.reverse := by
  funext it
  simp only [finishCheckR, finishCheck, prefixSub_eq, popOk_eq]

theorem checkBySigR_eq (Δ : TypeCtx) (sig : Option InstrType) (R : List CValType) :
    checkBySigR Δ sig R = checkBySig Δ sig R.reverse := by
  cases sig <;> simp only [checkBySigR, checkBySig, prefixSub_eq, popsOk_eq]

theorem topHeapR_eq (R : List CValType) : topHeapR R = topHeap R.reverse := by
  simp only [topHeapR, topHeap, List.getLast?_reverse]
  rfl

theorem selectImplTypeR_eq (R : List CValType) :
    selectImplTypeR R = selectImplType? R.reverse := by
  simp only [selectImplTypeR, selectImplType?, List.reverse_reverse]
  rfl

theorem brTableTs_eq (R : List CValType) (m : Nat) :
    brTableTs R m = (R.reverse.drop (R.reverse.length - (m + 1))).take m := by
  rw [List.length_reverse, reverse_drop_sub]
  rfl

/-! ## The atom oracle and the direct step -/

theorem parametricTypeR_eq (tyOk : {k : TKind} → Silmaril.Wasm.Validation.Ty k → Bool) (C : Context)
    (R : List CValType) (i : Instr) :
    parametricTypeR tyOk C R i = parametricType? tyOk C R.reverse i := by
  cases i with
  | drop =>
    simp only [parametricTypeR, parametricType?, List.getLast?_reverse]
    rfl
  | select ts =>
    rcases ts with _ | _ | ⟨t, _ | _⟩
    · simp only [parametricTypeR, parametricType?, selectImplTypeR_eq]
      rfl
    all_goals rfl
  | _ => rfl

theorem atomR_eq (C : Context) (R : List CValType) (i : Instr) :
    atomR C R i = atomC C R.reverse i := by
  simp only [atomR, atomC, atomicAR, atomicA?, atomicBR, atomicB?, parametricCheck?,
    numericCheck?, variableCheck?, vectorCheck?, tableCheck?, memoryCheck?, refCheck?,
    parametricTypeR_eq, finishCheckR_eq, checkBySigR_eq, List.getLast?_reverse]
  rfl

theorem directStepGR_eq (C : Context) (R : List CValType) (i : Instr) :
    directStepGR C R i = directStep atomC tyOkC C R.reverse i := by
  cases i <;> simp only [directStepGR, directStep, stepAR_eq, stepBR_eq, atomR_eq, topHeapR_eq,
    brTableTs_eq, List.length_reverse] <;> rfl

theorem directStepR_eq (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (i : Instr) :
    directStepR fa rs la C R i = directStepF fa rs la C R.reverse i := by
  cases i <;> simp only [directStepR, directStepF, directStepGR_eq, stepAR_eq, stepBR_eq,
    finishCheckR_eq, checkBySigR_eq] <;> rfl

/-! ## The direct paths -/

/-- The general step's result read as an `FStep` (what `checkSeqR` does with it). -/
def toF (la : Array LocalType) (C : Context) (R : List CValType) : Option StepRes → FStep
  | some (.normal n xs out) =>
    if localsOkL la xs && resOk tyOkC C.toTypeCtx out then
      .next xs (out.reverse ++ R.drop n) (R.length - n + out.length)
    else .fail
  | some (.poly _) => .slow
  | none => .fail

theorem checkVal_num (Δ : TypeCtx) (u : CValType) (n : NumType) :
    Δ.checkVal u (.num n) = subNum u n := by
  cases u <;> rfl

theorem tyOkC_num (Δ : TypeCtx) (n : NumType) : tyOkC Δ (.num n) = true := by
  simp only [tyOkC, TyOk.check, tyChk]

theorem tyOkV_eq (Δ : TypeCtx) (t : CValType) : tyOkV Δ t = tyOkC Δ t := by
  cases t <;> simp only [tyOkV, tyOkC_num]

/-- The simp set that unfolds the general step at an instruction with a direct path. -/
theorem fastR_numeric (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (i : Instr) (hp : parametricTypeR (@tyOkC C.toTypeCtx) C R i = none)
    (hd : directStepR fa rs la C R i = directStepGR C R i)
    (hg : directStepGR C R i = match atomR C R i with
      | some (n, xs, out) => some (.normal n xs out)
      | none => none) (it : InstrType) (hn : numericType? i = some it)
    (hv : variableType? C i = none) (hw : vectorType? i = none)
    (hb : atomicBR (@tyOkC C.toTypeCtx) C R i = none) :
    directStepR fa rs la C R i =
      match finishCheckR C R it with
      | some (n, xs, out) => some (.normal n xs out)
      | none => none := by
  rw [hd, hg]
  simp only [atomR, atomicAR, hp, hn, hv, hw, hb, Option.bind_none, Option.bind_some]
  cases finishCheckR C R it <;> rfl

/-- The hypotheses under which `directStepR` at `i` is `finishCheckR` of the signature `it`. -/
structure NumAt (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context)
    (i : Instr) (it : InstrType) : Prop where
  hp : ∀ R, parametricTypeR (@tyOkC C.toTypeCtx) C R i = none
  hd : ∀ R, directStepR fa rs la C R i = directStepGR C R i
  hg : ∀ R, directStepGR C R i = match atomR C R i with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none
  hn : numericType? i = some it
  hv : variableType? C i = none
  hw : vectorType? i = none
  hb : ∀ R, atomicBR (@tyOkC C.toTypeCtx) C R i = none

theorem NumAt.step {fa : Array DefType} {rs : Std.HashSet Nat} {la : Array LocalType}
    {C : Context} {i : Instr} {it : InstrType} (h : NumAt fa rs la C i it) (R : List CValType) :
    directStepR fa rs la C R i =
      match finishCheckR C R it with
      | some (n, xs, out) => some (.normal n xs out)
      | none => none :=
  fastR_numeric fa rs la C R i (h.hp R) (h.hd R) (h.hg R) it h.hn h.hv h.hw (h.hb R)

/-- A direct path of two numeric operands of type `n` and one result `o`. -/
theorem fast_bin {fa : Array DefType} {rs : Std.HashSet Nat} {la : Array LocalType}
    {C : Context} {i : Instr} (n : NumType) (o : NumType)
    (h : NumAt fa rs la C i (.plain [.num n, .num n] [.num o]))
    (hf : ∀ R, fastR la C R R.length i = match R with
      | u :: v :: R' =>
        if subNum v n && subNum u n then .next [] (.num o :: R') ((u :: v :: R').length - 1)
        else .fail
      | _ => .fail) (R : List CValType) :
    fastR la C R R.length i = toF la C R (directStepR fa rs la C R i) := by
  rw [h.step R, hf R]
  rcases R with _ | ⟨u, _ | ⟨v, R'⟩⟩
  · rfl
  · simp [toF, finishCheckR, prefixSub]
  · cases hu : subNum u n <;> cases hv : subNum v n <;>
      simp [toF, finishCheckR, prefixSub, checkVal_num, tyOkC_num, localsOkL, resOk, hu, hv]

/-- A direct path of one numeric operand of type `n` and one result `o`. -/
theorem fast_un {fa : Array DefType} {rs : Std.HashSet Nat} {la : Array LocalType}
    {C : Context} {i : Instr} (n : NumType) (o : NumType)
    (h : NumAt fa rs la C i (.plain [.num n] [.num o]))
    (hf : ∀ R, fastR la C R R.length i = match R with
      | u :: R' =>
        if subNum u n then .next [] (.num o :: R') (u :: R').length else .fail
      | [] => .fail) (R : List CValType) :
    fastR la C R R.length i = toF la C R (directStepR fa rs la C R i) := by
  rw [h.step R, hf R]
  rcases R with _ | ⟨u, R'⟩
  · rfl
  · cases hu : subNum u n <;>
      simp [toF, finishCheckR, prefixSub, checkVal_num, tyOkC_num, localsOkL, resOk, hu]

/-- A direct path of no operand and one numeric result `o`. -/
theorem fast_const {fa : Array DefType} {rs : Std.HashSet Nat} {la : Array LocalType}
    {C : Context} {i : Instr} (o : NumType) (h : NumAt fa rs la C i (.plain [] [.num o]))
    (hf : ∀ R, fastR la C R R.length i = .next [] (.num o :: R) (R.length + 1))
    (R : List CValType) :
    fastR la C R R.length i = toF la C R (directStepR fa rs la C R i) := by
  rw [h.step R, hf R]
  simp [toF, finishCheckR, prefixSub, tyOkC_num, localsOkL, resOk]

theorem fast_localGet (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (x : LocalIdx) :
    fastR la C R R.length (.localGet x) = toF la C R (directStepR fa rs la C R (.localGet x)) := by
  show _ = toF la C R (match (localType la (.localGet x)).bind (finishCheckR C R) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none)
  rcases hx : la[x.toNat]? with _ | ⟨_ | _, t⟩
  · simp [fastR, toF, localType, hx]
  · cases ht : tyOkC C.toTypeCtx t <;>
      simp [fastR, toF, localType, hx, finishCheckR, prefixSub, tyOkV_eq, localsOkL, resOk, ht]
  · simp [fastR, toF, localType, hx]

theorem fast_localSet (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (x : LocalIdx) :
    fastR la C R R.length (.localSet x) = toF la C R (directStepR fa rs la C R (.localSet x)) := by
  show _ = toF la C R (match (localType la (.localSet x)).bind (finishCheckR C R) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none)
  rcases hx : la[x.toNat]? with _ | ⟨_, t⟩
  · simp [fastR, toF, localType, hx]
  · rcases R with _ | ⟨u, R'⟩
    · simp [fastR, toF, localType, hx, finishCheckR, prefixSub]
    · cases hu : C.toTypeCtx.checkVal u t <;>
        simp [fastR, toF, localType, hx, finishCheckR, prefixSub, localsOkL, resOk, hu]

theorem fast_localTee (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (x : LocalIdx) :
    fastR la C R R.length (.localTee x) = toF la C R (directStepR fa rs la C R (.localTee x)) := by
  show _ = toF la C R (match (localType la (.localTee x)).bind (finishCheckR C R) with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none)
  rcases hx : la[x.toNat]? with _ | ⟨_, t⟩
  · simp [fastR, toF, localType, hx]
  · rcases R with _ | ⟨u, R'⟩
    · simp [fastR, toF, localType, hx, finishCheckR, prefixSub]
    · cases hu : C.toTypeCtx.checkVal u t <;> cases ht : tyOkC C.toTypeCtx t <;>
        simp [fastR, toF, localType, hx, finishCheckR, prefixSub, localsOkL, resOk, tyOkV_eq, hu, ht]

theorem fast_intUnOp (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (t : IntType) (op : IntUnOp) :
    fastR la C R R.length (.intUnOp t op) = .slow ∨
      fastR la C R R.length (.intUnOp t op) = toF la C R (directStepR fa rs la C R (.intUnOp t op)) := by
  cases hv : op.valid t
  · exact .inl (by simp [fastR, hv])
  · have h : NumAt fa rs la C (.intUnOp t op) (.plain [.num (.int t)] [.num (.int t)]) :=
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, by simp [numericType?, hv], rfl, rfl, fun _ => rfl⟩
    refine .inr (fast_un (.int t) (.int t) h (fun R => ?_) R)
    rcases R with _ | ⟨_, _⟩ <;> simp [fastR, hv]

theorem fastR_cases (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (R : List CValType) (i : Instr) :
    fastR la C R R.length i = .slow ∨
      fastR la C R R.length i = toF la C R (checkInstrR fa rs la C R i) := by
  cases i
  case localGet x => exact .inr (fast_localGet fa rs la C R x)
  case localSet x => exact .inr (fast_localSet fa rs la C R x)
  case localTee x => exact .inr (fast_localTee fa rs la C R x)
  case intConst t c => exact .inr (fast_const (.int t)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩ (fun _ => rfl) R)
  case floatConst t c => exact .inr (fast_const (.float t)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩ (fun _ => rfl) R)
  case intUnOp t op => exact fast_intUnOp fa rs la C R t op
  case intBinOp t op => exact .inr (fast_bin (.int t) (.int t)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl) R)
  case intRelOp t op => exact .inr (fast_bin (.int t) (.int .i32)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl) R)
  case floatBinOp t op => exact .inr (fast_bin (.float t) (.float t)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl) R)
  case floatRelOp t op => exact .inr (fast_bin (.float t) (.int .i32)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl) R)
  case intTestOp t op => exact .inr (fast_un (.int t) (.int .i32)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _⟩ <;> rfl) R)
  case floatUnOp t op => exact .inr (fast_un (.float t) (.float t)
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _⟩ <;> rfl) R)
  case convert op => exact .inr (fast_un op.source op.target
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩
    (fun R => by rcases R with _ | ⟨_, _⟩ <;> rfl) R)
  all_goals exact .inl rfl

/-! ## Sequences -/

/-- `checkSeqR`'s general step (the code after `.slow`), as a function. -/
def slowSeq (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType) (C : Context)
    (r : List CValType) (len : Nat) (poly : Bool) (goal : Option (List CValType))
    (acc : List Nat) (i : Instr) (is : List Instr) : Option (List CValType × List Nat) :=
  match checkInstrR fa rs la C (if poly then r ++ List.replicate (padForF fa C true i) .botv else r) i with
  | some (.normal n xs out) =>
    if localsOkL la xs && resOk tyOkC C.toTypeCtx out then
      checkSeqR fa rs (initLocalsL la xs) C (out.reverse ++ r.drop n) (len - n + out.length)
        poly goal (xs.reverse ++ acc) is
    else none
  | some (.poly _) => checkSeqR fa rs la C [] 0 true goal acc is
  | none => none

/-- The direct paths change nothing: `checkSeqR` is its general step. -/
theorem checkSeqR_slow (fa : Array DefType) (rs : Std.HashSet Nat) (la : Array LocalType)
    (C : Context) (r : List CValType) (poly : Bool) (goal : Option (List CValType))
    (acc : List Nat) (i : Instr) (is : List Instr) :
    checkSeqR fa rs la C r r.length poly goal acc (i :: is) =
      slowSeq fa rs la C r r.length poly goal acc i is := by
  cases poly
  · rcases fastR_cases fa rs la C r i with h | h
    · simp only [checkSeqR, slowSeq, h, Bool.false_eq_true, ite_false]
      rfl
    · simp only [checkSeqR, slowSeq, h, Bool.false_eq_true, ite_false]
      rcases checkInstrR fa rs la C r i with _ | ⟨n, xs, out⟩ | t₁
      · rfl
      · by_cases hc : (localsOkL la xs && resOk tyOkC C.toTypeCtx out) = true
        · simp only [toF, hc, ite_true]
        · simp only [toF, hc, Bool.false_eq_true, ite_false]
      · rfl
  · rfl

theorem localsOkL_rev (la : Array LocalType) (xs : List Nat) :
    localsOkL la (xs.reverse ++ []) = localsOkL la xs := by
  simp only [localsOkL, List.append_nil, List.all_reverse]

theorem body_eq (la : Array LocalType) (X : Option StepRes)
    (o : Option (List CValType × List Nat × Nat)) :
    (match o.map (fun p => (p.1, p.2.1.reverse ++ [])) with
     | some (_, xsb) => if localsOkL la xsb then X else none
     | none => none) =
    (match o with
     | some (_, xsb, _) => if localsOkL la xsb then X else none
     | none => none) := by
  rcases o with _ | ⟨_, xs, _⟩
  · rfl
  · simp only [Option.map_some, localsOkL_rev]

theorem body2_eq (la : Array LocalType) (X : Option StepRes)
    (o₁ o₂ : Option (List CValType × List Nat × Nat)) :
    (match o₁.map (fun p => (p.1, p.2.1.reverse ++ [])),
        o₂.map (fun p => (p.1, p.2.1.reverse ++ [])) with
     | some (_, xs₁), some (_, xs₂) => if localsOkL la xs₁ && localsOkL la xs₂ then X else none
     | _, _ => none) =
    (match o₁, o₂ with
     | some (_, xs₁, _), some (_, xs₂, _) =>
       if localsOkL la xs₁ && localsOkL la xs₂ then X else none
     | _, _ => none) := by
  rcases o₁ with _ | ⟨_, xs₁, _⟩ <;> rcases o₂ with _ | ⟨_, xs₂, _⟩
  all_goals first | rfl | simp only [Option.map_some, localsOkL_rev]

theorem map_seq (xs : List Nat) (acc : List Nat) (k : Nat)
    (X : Option (List CValType × List Nat × Nat)) :
    X.map (fun (p : List CValType × List Nat × Nat) => (p.1, p.2.1.reverse ++ (xs.reverse ++ acc))) =
      (match X with
       | some (out', xs', k') => some (out', xs ++ xs', k' + k)
       | none => none).map (fun (p : List CValType × List Nat × Nat) => (p.1, p.2.1.reverse ++ acc)) := by
  rcases X with _ | ⟨o, xs', k'⟩
  · rfl
  · simp only [Option.map_some, List.reverse_append, List.append_assoc]

theorem map_poly (acc : List Nat) (k : Nat) (X : Option (List CValType × List Nat × Nat)) :
    X.map (fun (p : List CValType × List Nat × Nat) => (p.1, p.2.1.reverse ++ acc)) =
      (match X with
       | some (out', xs', _) => some (out', xs', k)
       | none => none).map (fun (p : List CValType × List Nat × Nat) => (p.1, p.2.1.reverse ++ acc)) := by
  rcases X with _ | ⟨o, xs', k'⟩ <;> rfl

theorem pad_rev (r : List CValType) (p : Nat) :
    (r ++ List.replicate p (.botv : CValType)).reverse = padStack p r.reverse := by
  simp only [List.reverse_append, List.reverse_replicate, padStack]

theorem stack_rev (r out : List CValType) (n : Nat) :
    (out.reverse ++ r.drop n).reverse = r.reverse.take (r.reverse.length - n) ++ out := by
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_drop, List.length_reverse]

theorem stack_len (r out : List CValType) (n : Nat) :
    r.length - n + out.length = (out.reverse ++ r.drop n).length := by
  simp only [List.length_append, List.length_reverse, List.length_drop]
  omega

mutual

theorem checkInstrR_eq (fa : Array DefType) (rs : Std.HashSet Nat) (i : Instr) :
    ∀ (la : Array LocalType) (C : Context) (R : List CValType),
      checkInstrR fa rs la C R i = checkInstrF fa rs la C R.reverse i := by
  intro la C R
  have ihb : ∀ body, sizeOf body < sizeOf i → ∀ (C' : Context) (t₁ : List CValType) g,
      checkSeqR fa rs la C' t₁.reverse t₁.length false g [] body =
        (checkSeqF fa rs la C' t₁ false g body).map (fun p => (p.1, p.2.1.reverse ++ [])) :=
    fun body hlt C' t₁ g => by
      rw [← List.length_reverse (as := t₁), checkSeqR_eq fa rs body la C' t₁.reverse false g [],
        List.reverse_reverse]
  cases i
  case block bt body =>
    show checkInstrR fa rs la C R (.block bt body) = checkInstrF fa rs la C R.reverse (.block bt body)
    simp only [checkInstrR, checkInstrF, ihb body (by simp), stepAR_eq]
    rcases CheckInstrs.blockType? tyOkC C bt with _ | ⟨t₁, t₂⟩
    · rfl
    · by_cases hc : (resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂) = true
      · simp only [hc, ite_true]
        exact body_eq la _ _
      · simp only [hc, Bool.false_eq_true, ite_false]
  case loop bt body =>
    show checkInstrR fa rs la C R (.loop bt body) = checkInstrF fa rs la C R.reverse (.loop bt body)
    simp only [checkInstrR, checkInstrF, ihb body (by simp), stepAR_eq]
    rcases CheckInstrs.blockType? tyOkC C bt with _ | ⟨t₁, t₂⟩
    · rfl
    · by_cases hc : (resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂) = true
      · simp only [hc, ite_true]
        exact body_eq la _ _
      · simp only [hc, Bool.false_eq_true, ite_false]
  case if_ bt b₁ b₂ =>
    show checkInstrR fa rs la C R (.if_ bt b₁ b₂) = checkInstrF fa rs la C R.reverse (.if_ bt b₁ b₂)
    simp only [checkInstrR, checkInstrF, ihb b₁ (by rw [Instr.if_.sizeOf_spec]; omega),
      ihb b₂ (by rw [Instr.if_.sizeOf_spec]; omega),
      stepAR_eq]
    rcases CheckInstrs.blockType? tyOkC C bt with _ | ⟨t₁, t₂⟩
    · rfl
    · by_cases hc : (resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂) = true
      · simp only [hc, ite_true]
        exact body2_eq la _ _ _
      · simp only [hc, Bool.false_eq_true, ite_false]
  case tryTable bt cs body =>
    show checkInstrR fa rs la C R (.tryTable bt cs body) = checkInstrF fa rs la C R.reverse (.tryTable bt cs body)
    simp only [checkInstrR, checkInstrF, ihb body (by simp), stepAR_eq]
    rcases CheckInstrs.blockType? tyOkC C bt with _ | ⟨t₁, t₂⟩
    · rfl
    · by_cases hc : (resOk tyOkC C.toTypeCtx t₁ && resOk tyOkC C.toTypeCtx t₂ &&
          cs.all (catchOk? C)) = true
      · simp only [hc, ite_true]
        exact body_eq la _ _
      · simp only [hc, Bool.false_eq_true, ite_false]
  case select ts =>
    cases ts with
    | none =>
      simp only [checkInstrR, checkInstrF, stepAR_eq, directStepGR_eq]
      rfl
    | some ts => exact directStepR_eq fa rs la C R _
  all_goals exact directStepR_eq fa rs la C R _
termination_by sizeOf i
decreasing_by all_goals assumption

/-- **The reversed-stack sequence checker is `checkSeqF`**, with the dead-code count dropped
and the initialised locals reversed onto `acc`. -/
theorem checkSeqR_eq (fa : Array DefType) (rs : Std.HashSet Nat) (l : List Instr) :
    ∀ (la : Array LocalType) (C : Context) (r : List CValType) (poly : Bool)
      (goal : Option (List CValType)) (acc : List Nat),
      checkSeqR fa rs la C r r.length poly goal acc l =
        (checkSeqF fa rs la C r.reverse poly goal l).map (fun p => (p.1, p.2.1.reverse ++ acc)) := by
  intro la C r poly goal acc
  match l with
  | [] =>
    cases goal with
    | none => simp only [checkSeqR, checkSeqF, Option.map_some, List.reverse_nil, List.nil_append]
    | some g =>
      simp only [checkSeqR, checkSeqF, endPad, List.length_reverse]
      split <;> (split <;> rfl)
  | i :: is =>
    show checkSeqR fa rs la C r r.length poly goal acc (i :: is) =
      (checkSeqF fa rs la C r.reverse poly goal (i :: is)).map (fun p => (p.1, p.2.1.reverse ++ acc))
    have ihi : ∀ R, checkInstrR fa rs la C R i = checkInstrF fa rs la C R.reverse i :=
      checkInstrR_eq fa rs i la C
    have ihs : ∀ la' r' acc', checkSeqR fa rs la' C r' r'.length poly goal acc' is =
        (checkSeqF fa rs la' C r'.reverse poly goal is).map (fun p => (p.1, p.2.1.reverse ++ acc')) :=
      fun la' r' acc' => checkSeqR_eq fa rs is la' C r' poly goal acc'
    have ihp : ∀ acc', checkSeqR fa rs la C [] 0 true goal acc' is =
        (checkSeqF fa rs la C [] true goal is).map (fun p => (p.1, p.2.1.reverse ++ acc')) :=
      fun acc' => checkSeqR_eq fa rs is la C [] true goal acc'
    rw [checkSeqR_slow]
    show slowSeq fa rs la C r r.length poly goal acc i is = (checkSeqF fa rs la C r.reverse poly goal (i :: is)).map _
    simp only [slowSeq, checkSeqF]
    have hpad : (if poly then r ++ List.replicate (padForF fa C true i) .botv else r).reverse =
        padStack (padForF fa C poly i) r.reverse := by
      cases poly
      · simp only [Bool.false_eq_true, ite_false, padForF, padStack, List.replicate_zero, List.nil_append]
      · simp only [ite_true, pad_rev]
    rw [ihi, hpad]
    rcases checkInstrF fa rs la C (padStack (padForF fa C poly i) r.reverse) i with _ | ⟨n, xs, out⟩ | t₁
    · rfl
    · by_cases hc : (localsOkL la xs && resOk tyOkC C.toTypeCtx out) = true
      · simp only [hc, ite_true]
        rw [stack_len r out n, ihs, stack_rev]
        exact map_seq xs acc _ _
      · simp only [hc, Bool.false_eq_true, ite_false, Option.map_none]
    · rw [ihp]
      exact map_poly acc _ _
termination_by sizeOf l
decreasing_by all_goals first | (simp_wf; omega) | simp_wf

end

/-! ## Modules -/

theorem checkExprR_eq : checkExprR = checkExprF := by
  funext fa rs C e ts
  have h : checkSeqR fa rs C.locals.toArray { C with locals := [] } [] 0 false (some ts) [] e =
      (checkSeqF fa rs C.locals.toArray { C with locals := [] } [] false (some ts) e).map
        (fun p => (p.1, p.2.1.reverse ++ [])) :=
    checkSeqR_eq fa rs e _ _ [] false (some ts) []
  unfold checkExprR checkExprF
  rw [h]
  cases checkSeqF fa rs C.locals.toArray { C with locals := [] } [] false (some ts) e <;> rfl

theorem checkModuleR_eq : checkModuleR = checkModuleF := by
  funext m
  unfold checkModuleR checkModuleF
  rw [checkExprR_eq]

/-- **The reversed-stack validator is silmaril's `validate?`.** -/
theorem validateR_eq : validateR = validate? := by
  funext m
  show checkModuleR m = validate? m
  rw [checkModuleR_eq, ← validateF_eq]
  rfl

end Silmaril.Proofs.Wasm.Perf.ValidateR
