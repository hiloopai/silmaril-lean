module

public import Silmaril.Wasm.Validation.Instructions
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Stack-directed checkers: parametric, numeric, variable and vector instructions

Each `familyCheck? C stk i` inspects the (bottom-first) operand stack `stk` and returns
`(n, xs, out)`: `n` operands consumed from the top, locals `xs` initialised, and the
pushed types `out`. Soundness: the consumed operands are pointwise subtypes of the
parameters of a valid instruction type `⟨t₁, xs, out⟩`.

`unreachable` returns `none` (stack polymorphism is the sequence checker's job).
Completeness is not claimed.
-/

namespace Silmaril.Wasm.Validation

/-! ## Generic operand matching -/

/-- Pointwise `Sub.check` on two lists of equal length. -/
def checkResultSub (Δ : TypeCtx) : List CValType → List CValType → Bool
  | [], [] => true
  | a :: as, b :: bs => Sub.check Δ a b && checkResultSub Δ as bs
  | _, _ => false

theorem checkResultSub_sound {Δ : TypeCtx} :
    {as bs : List CValType} → checkResultSub Δ as bs = true → ResultSub Δ as bs
  | [], [], _ => .nil
  | a :: as, b :: bs, h => by
    simp only [checkResultSub, Bool.and_eq_true] at h
    exact .cons (Sub.check_sound h.1) (checkResultSub_sound h.2)
  | [], _ :: _, h => by simp [checkResultSub] at h
  | _ :: _, [], h => by simp [checkResultSub] at h

/-- The top `t₁.length` operands of `stk` match `t₁`. -/
def popOk (Δ : TypeCtx) (stk t₁ : List CValType) : Bool :=
  decide (t₁.length ≤ stk.length) && checkResultSub Δ (stk.drop (stk.length - t₁.length)) t₁

/-- Accept instruction type `it` against the stack. -/
def finishCheck (C : Context) (stk : List CValType) (it : InstrType) :
    Option (Nat × List Nat × List CValType) :=
  if popOk C.toTypeCtx stk it.params then some (it.params.length, it.inits, it.results)
  else none

theorem finishCheck_sound {C : Context} {stk : List CValType} {it : InstrType}
    {P : InstrType → Prop} (hP : P it) {n : Nat} {xs : List Nat} {out : List CValType}
    (h : finishCheck C stk it = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁ : List CValType, t₁.length = n ∧ P ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  unfold finishCheck at h
  split at h
  · rename_i hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [popOk, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨hp.1, it.params, rfl, hP, checkResultSub_sound hp.2⟩
  · cases h

/-- Bind a type-producing function into a checker, with the generic soundness. -/
theorem bind_finishCheck_sound {C : Context} {stk : List CValType} {o : Option InstrType}
    {P : InstrType → Prop} (hP : ∀ it, o = some it → P it) {n : Nat} {xs : List Nat}
    {out : List CValType} (h : (o.bind (finishCheck C stk)) = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁ : List CValType, t₁.length = n ∧ P ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  cases ho : o with
  | none => rw [ho] at h; cases h
  | some it =>
    rw [ho] at h
    exact finishCheck_sound (hP it ho) h

theorem tyOk_of_isNumOrVec {Δ : TypeCtx} {t : CValType} (h : t.IsNumOrVec) : TyOk Δ t := by
  cases t <;> simp [Ty.IsNumOrVec] at h
  · exact .num _
  · exact .vec _

/-! ## Parametric -/

/-- Implicit `select`: pick the numeric/vector type among the two value operands. -/
def selectImplType? (stk : List CValType) : Option CValType :=
  match stk.reverse with
  | _ :: b :: a :: _ =>
    if a.IsNumOrVec then some a else if b.IsNumOrVec then some b else none
  | _ => none

theorem selectImplType?_isNumOrVec {stk : List CValType} {t : CValType}
    (h : selectImplType? stk = some t) : t.IsNumOrVec := by
  unfold selectImplType? at h
  split at h
  · split at h
    · cases h; assumption
    · split at h
      · cases h; assumption
      · cases h
  · cases h

def parametricType? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (stk : List CValType) :
    Instr → Option InstrType
  | .nop => some (.plain [] [])
  | .drop =>
    match stk.getLast? with
    | some t => if tyOk t then some (.plain [t] []) else none
    | none => none
  | .select (some [t]) =>
    if tyOk (C.closeVal t) then
      some (.plain [C.closeVal t, C.closeVal t, .i32] [C.closeVal t])
    else none
  | .select none =>
    match selectImplType? stk with
    | some t => some (.plain [t, t, .i32] [t])
    | none => none
  | _ => none

theorem parametricType?_sound {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (htyOk : ∀ {k} {t : Ty k}, tyOk t = true → TyOk C.toTypeCtx t)
    {stk : List CValType} {i : Instr} {it : InstrType}
    (h : parametricType? tyOk C stk i = some it) : ParametricInstrOk C i it := by
  unfold parametricType? at h
  split at h
  · cases h; exact .nop
  · split at h
    · split at h
      · cases h; exact .drop (htyOk (by assumption))
      · cases h
    · cases h
  · split at h
    · cases h; exact .selectExpl (htyOk (by assumption))
    · cases h
  · split at h
    · rename_i t ht
      cases h
      have hnv := selectImplType?_isNumOrVec ht
      exact .selectImpl (tyOk_of_isNumOrVec hnv) (Sub.refl _ (k := .val) trivial t) hnv
    · cases h
  · cases h

def parametricCheck? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (stk : List CValType)
    (i : Instr) : Option (Nat × List Nat × List CValType) :=
  (parametricType? tyOk C stk i).bind (finishCheck C stk)

theorem parametricCheck?_sound {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (htyOk : ∀ {k} {t : Ty k}, tyOk t = true → TyOk C.toTypeCtx t)
    {stk : List CValType} {i : Instr} {n : Nat} {xs : List Nat} {out : List CValType}
    (h : parametricCheck? tyOk C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ ParametricInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ :=
  bind_finishCheck_sound (fun _ hit => parametricType?_sound htyOk hit) h

/-! ## Numeric -/

def numericType? : Instr → Option InstrType
  | .intConst t _ => some (.plain [] [.num (.int t)])
  | .floatConst t _ => some (.plain [] [.num (.float t)])
  | .intUnOp t op => if op.valid t then some (.plain [.num (.int t)] [.num (.int t)]) else none
  | .floatUnOp t _ => some (.plain [.num (.float t)] [.num (.float t)])
  | .intBinOp t _ => some (.plain [.num (.int t), .num (.int t)] [.num (.int t)])
  | .floatBinOp t _ => some (.plain [.num (.float t), .num (.float t)] [.num (.float t)])
  | .intTestOp t _ => some (.plain [.num (.int t)] [.i32])
  | .intRelOp t _ => some (.plain [.num (.int t), .num (.int t)] [.i32])
  | .floatRelOp t _ => some (.plain [.num (.float t), .num (.float t)] [.i32])
  | .convert op => some (.plain [.num op.source] [.num op.target])
  | _ => none

theorem numericType?_sound {C : Context} {i : Instr} {it : InstrType}
    (h : numericType? i = some it) : NumericInstrOk C i it := by
  unfold numericType? at h
  split at h <;> (try split at h) <;> cases h
  all_goals (constructor <;> assumption)

def numericCheck? (C : Context) (stk : List CValType) (i : Instr) :
    Option (Nat × List Nat × List CValType) :=
  (numericType? i).bind (finishCheck C stk)

theorem numericCheck?_sound {C : Context} {stk : List CValType} {i : Instr} {n : Nat}
    {xs : List Nat} {out : List CValType} (h : numericCheck? C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ NumericInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ :=
  bind_finishCheck_sound (fun _ hit => numericType?_sound hit) h

/-! ## Variable -/

def variableType? (C : Context) : Instr → Option InstrType
  | .localGet x =>
    match C.locals[x.toNat]? with
    | some ⟨.set, t⟩ => some (.plain [] [t])
    | _ => none
  | .localSet x =>
    match C.locals[x.toNat]? with
    | some ⟨_, t⟩ => some ⟨[t], [x.toNat], []⟩
    | none => none
  | .localTee x =>
    match C.locals[x.toNat]? with
    | some ⟨_, t⟩ => some ⟨[t], [x.toNat], [t]⟩
    | none => none
  | .globalGet x =>
    match C.globals[x.toNat]? with
    | some ⟨_, t⟩ => some (.plain [] [t])
    | none => none
  | .globalSet x =>
    match C.globals[x.toNat]? with
    | some ⟨.var, t⟩ => some (.plain [t] [])
    | _ => none
  | _ => none

theorem variableType?_sound {C : Context} {i : Instr} {it : InstrType}
    (h : variableType? C i = some it) : VariableInstrOk C i it := by
  unfold variableType? at h
  split at h
  · split at h
    · cases h; exact .localGet (by assumption)
    · cases h
  · split at h
    · cases h; exact .localSet (by assumption)
    · cases h
  · split at h
    · cases h; exact .localTee (by assumption)
    · cases h
  · split at h
    · cases h; exact .globalGet (by assumption)
    · cases h
  · split at h
    · cases h; exact .globalSet (by assumption)
    · cases h
  · cases h

def variableCheck? (C : Context) (stk : List CValType) (i : Instr) :
    Option (Nat × List Nat × List CValType) :=
  (variableType? C i).bind (finishCheck C stk)

theorem variableCheck?_sound {C : Context} {stk : List CValType} {i : Instr} {n : Nat}
    {xs : List Nat} {out : List CValType} (h : variableCheck? C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ VariableInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ :=
  bind_finishCheck_sound (fun _ hit => variableType?_sound hit) h

/-! ## Vector -/

def vectorType? : Instr → Option InstrType
  | .vecConst _ => some (.plain [] [.v128])
  | .vecUnOp _ => some (.plain [.v128] [.v128])
  | .vecBinOp _ => some (.plain [.v128, .v128] [.v128])
  | .vecTernOp _ => some (.plain [.v128, .v128, .v128] [.v128])
  | .vecTestOp _ => some (.plain [.v128] [.i32])
  | .vecIntUnOp sh op => if op.valid sh then some (.plain [.v128] [.v128]) else none
  | .vecFloatUnOp _ _ => some (.plain [.v128] [.v128])
  | .vecIntBinOp sh op => if op.valid sh then some (.plain [.v128, .v128] [.v128]) else none
  | .vecFloatBinOp _ _ => some (.plain [.v128, .v128] [.v128])
  | .vecIntTernOp _ _ => some (.plain [.v128, .v128, .v128] [.v128])
  | .vecFloatTernOp _ _ => some (.plain [.v128, .v128, .v128] [.v128])
  | .vecAllTrue _ => some (.plain [.v128] [.i32])
  | .vecIntRelOp sh op =>
    if op.validShape sh then some (.plain [.v128, .v128] [.v128]) else none
  | .vecFloatRelOp _ _ => some (.plain [.v128, .v128] [.v128])
  | .vecShiftOp _ _ => some (.plain [.v128, .i32] [.v128])
  | .vecBitmask _ => some (.plain [.v128] [.i32])
  | .vecSwizzle _ => some (.plain [.v128, .v128] [.v128])
  | .vecShuffle lanes =>
    if lanes.length = 16 ∧ ∀ i ∈ lanes, i.val < 32 then some (.plain [.v128, .v128] [.v128])
    else none
  | .vecSplat sh => some (.plain [.num sh.unpacked] [.v128])
  | .vecExtractLane sh sx i =>
    if i.val < sh.lanes ∧ sx.isSome = decide (sh.laneWidth < 32) then
      some (.plain [.v128] [.num sh.unpacked])
    else none
  | .vecReplaceLane sh i =>
    if i.val < sh.lanes then some (.plain [.v128, .num sh.unpacked] [.v128]) else none
  | .vecExtUnOp sh₁ sh₂ op =>
    if op.valid sh₁ sh₂ then some (.plain [.v128] [.v128]) else none
  | .vecExtBinOp sh₁ sh₂ op =>
    if op.valid sh₁ sh₂ then some (.plain [.v128, .v128] [.v128]) else none
  | .vecExtTernOp sh₁ sh₂ op =>
    if op.valid sh₁ sh₂ then some (.plain [.v128, .v128, .v128] [.v128]) else none
  | .vecNarrow sh₁ sh₂ _ =>
    if sh₁.laneWidth = 2 * sh₂.laneWidth ∧ sh₁.laneWidth ≤ 32 then
      some (.plain [.v128, .v128] [.v128])
    else none
  | .vecConvert sh₁ sh₂ op =>
    if op.valid sh₁ sh₂ then some (.plain [.v128] [.v128]) else none
  | _ => none

theorem vectorType?_sound {C : Context} {i : Instr} {it : InstrType}
    (h : vectorType? i = some it) : VectorInstrOk C i it := by
  unfold vectorType? at h
  split at h <;> (try split at h) <;> cases h
  all_goals (constructor <;> first | assumption | simp_all)

def vectorCheck? (C : Context) (stk : List CValType) (i : Instr) :
    Option (Nat × List Nat × List CValType) :=
  (vectorType? i).bind (finishCheck C stk)

theorem vectorCheck?_sound {C : Context} {stk : List CValType} {i : Instr} {n : Nat}
    {xs : List Nat} {out : List CValType} (h : vectorCheck? C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ VectorInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ :=
  bind_finishCheck_sound (fun _ hit => vectorType?_sound hit) h

/-! ## Dispatch -/

def atomicA? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (stk : List CValType)
    (i : Instr) : Option (Nat × List Nat × List CValType) :=
  match parametricCheck? tyOk C stk i with
  | some r => some r
  | none =>
    match numericCheck? C stk i with
    | some r => some r
    | none =>
      match variableCheck? C stk i with
      | some r => some r
      | none => vectorCheck? C stk i

theorem atomicA?_sound {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (htyOk : ∀ {k} {t : Ty k}, tyOk t = true → TyOk C.toTypeCtx t)
    {stk : List CValType} {i : Instr} {n : Nat} {xs : List Nat} {out : List CValType}
    (h : atomicA? tyOk C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ InstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  unfold atomicA? at h
  split at h
  · rename_i r hr
    cases h
    obtain ⟨hn, t₁, hl, hi, hs⟩ := parametricCheck?_sound htyOk hr
    exact ⟨hn, t₁, hl, .parametric hi, hs⟩
  · split at h
    · rename_i r hr
      cases h
      obtain ⟨hn, t₁, hl, hi, hs⟩ := numericCheck?_sound hr
      exact ⟨hn, t₁, hl, .numeric hi, hs⟩
    · split at h
      · rename_i r hr
        cases h
        obtain ⟨hn, t₁, hl, hi, hs⟩ := variableCheck?_sound hr
        exact ⟨hn, t₁, hl, .variable hi, hs⟩
      · obtain ⟨hn, t₁, hl, hi, hs⟩ := vectorCheck?_sound h
        exact ⟨hn, t₁, hl, .vector hi, hs⟩

end Silmaril.Wasm.Validation
