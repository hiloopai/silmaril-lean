module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.CoreEval

/-!
# Core 3.0 constant evaluation of a Lime1 constant expression is Lime1 evaluation

`Lime1Inst.evalConst?_toCore` runs Lime1 constant evaluation forward into Core 3.0. Here the
converse: when Core 3.0's executable evaluator `evalConst?` succeeds on the image of a Lime1
constant expression (`Validation.ConstantInstr`: constants, `global.get`, integer
`add`/`sub`/`mul`), and the two global reads agree on the `global.get`s of the expression, Lime1's
evaluator `constExpr?` succeeds with the same value and Core's store is unchanged
(`evalConst_back`).

Lime1 initializer typing is extended to module instances with globals (`constExpr?_typeG`):
`Lime1Inst.constExpr?_type` assumes a module instance without globals, while segment offsets read
the module's globals.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Eng

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst)
open Silmaril.Proofs.Wasm.Component.Lime1Inst (coreStack StackTy)

variable {H H' : Type}

/-- The value of the `x`-th global of a Lime1 module instance. -/
def lread (s : Silmaril.Wasm.Lime1.Execution.Store H) (mod : ModuleInst) (x : GlobalIdx) :
    Option Value :=
  (mod.globals[x.toNat]?).bind fun a => (s.globals[a.value]?).map (·.value)

/-- Core 3.0 and Lime1 read the same value for global `x`. -/
def GAgreeAt (S : Silmaril.Wasm.Execution.Core.Store H') (F : Silmaril.Wasm.Execution.Core.Frame)
    (s : Silmaril.Wasm.Lime1.Execution.Store H) (mod : ModuleInst) (x : GlobalIdx) : Prop :=
  (S.global? F x).map (fun p => p.2.value) = (lread s mod x).map Value.toCore

theorem coreStack_cons (v : Value) (st : List Value) :
    coreStack (v :: st) = coreStack st ++ [v.toCore] := by
  simp [coreStack]

theorem toCore_int? {w : Value} {t : IntType} {x : BitVec t.width}
    (h : (Value.toCore w).int? t = some x) : w = ⟨.int t, x⟩ := by
  rcases w with ⟨⟨t' | t'⟩, b⟩ <;>
    simp [Value.toCore, Silmaril.Wasm.Execution.Core.Val.int?] at h
  all_goals (obtain ⟨rfl, rfl⟩ := h; rfl)

theorem constStep_globalGet (s : Silmaril.Wasm.Lime1.Execution.Store H) (mod : ModuleInst)
    (x : GlobalIdx) (st : List Value) :
    Silmaril.Wasm.Lime1.Execution.constStep? s mod (.globalGet x) st =
      (lread s mod x).map (· :: st) := by
  simp only [Silmaril.Wasm.Lime1.Execution.constStep?, Silmaril.Wasm.Lime1.Execution.constInstr?,
    lread]
  rcases hm : mod.globals[x.toNat]? with _ | a
  · simp
  · rcases hg : s.globals[a.value]? with _ | g <;> simp [hg]

/-- A Core stack of two more values is the image of a Lime1 stack of two more values. -/
theorem coreStack_two {st : List Value} {pre : List Silmaril.Wasm.Execution.Core.Val}
    {v₁ v₂ : Silmaril.Wasm.Execution.Core.Val} (h : coreStack st = pre ++ [v₁, v₂]) :
    ∃ w₂ w₁ rest, st = w₂ :: w₁ :: rest ∧ w₁.toCore = v₁ ∧ w₂.toCore = v₂ ∧
      coreStack rest = pre := by
  have h' : st.map Value.toCore = v₂ :: v₁ :: pre.reverse := by
    have := congrArg List.reverse h
    simpa [coreStack] using this
  match st, h' with
  | w₂ :: w₁ :: rest, h' =>
    simp only [List.map_cons, List.cons.injEq] at h'
    obtain ⟨h2, h1, hr⟩ := h'
    refine ⟨w₂, w₁, rest, rfl, h1, h2, ?_⟩
    simp [coreStack, hr]

/-- The Core image of a constant integer operation succeeds only where Lime1's does. -/
theorem step_back_bin {s : Silmaril.Wasm.Lime1.Execution.Store H}
    {mod : ModuleInst} {t : IntType} {op : IntBinOp}
    (hop : op = .add ∨ op = .sub ∨ op = .mul)
    {S S' : Silmaril.Wasm.Execution.Core.Store H'} {F : Silmaril.Wasm.Execution.Core.Frame}
    {st : List Value} {vs' : List Silmaril.Wasm.Execution.Core.Val}
    (h : Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st)
      (Lime1.Instr.intBinOp t op).toCore = some (S', vs')) :
    S' = S ∧ ∃ st', Silmaril.Wasm.Lime1.Execution.constStep? s mod (.intBinOp t op) st =
      some st' ∧ vs' = coreStack st' := by
  have hc : Silmaril.Wasm.Execution.Core.constBinOp op = true := by
    rcases hop with rfl | rfl | rfl <;> rfl
  simp only [Lime1.Instr.toCore, Silmaril.Wasm.Execution.Core.constInstr?, hc, ite_true,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at h
  obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, h⟩ := h
  obtain ⟨w₂, w₁, rest, rfl, rfl, rfl, hrest⟩ :=
    coreStack_two (Silmaril.Wasm.Execution.Core.pop2?_eq hp)
  obtain rfl := toCore_int? hx
  obtain rfl := toCore_int? hy
  split at h
  · rename_i z hz
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, Value.int t z :: rest, ?_, ?_⟩
    · rcases hop with rfl | rfl | rfl <;> cases t <;>
        simp [Silmaril.Wasm.Lime1.Execution.constStep?,
          Silmaril.Wasm.Lime1.Execution.constBinary?, hz, Except.toOption, Value.int]
    · rw [coreStack_cons, hrest]; rfl
  · cases h

/-- A pushed constant, backwards. -/
theorem step_back_push {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {i : Lime1.Instr} {v : Value}
    (hL : ∀ st, Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some (v :: st))
    {S S' : Silmaril.Wasm.Execution.Core.Store H'} {F : Silmaril.Wasm.Execution.Core.Frame}
    (hC : ∀ vs, Silmaril.Wasm.Execution.Core.constInstr? S F vs i.toCore =
      some (S, vs ++ [v.toCore]))
    {st : List Value} {vs' : List Silmaril.Wasm.Execution.Core.Val}
    (h : Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st) i.toCore = some (S', vs')) :
    S' = S ∧ ∃ st', Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some st' ∧
      vs' = coreStack st' := by
  have he : (S, coreStack st ++ [v.toCore]) = (S', vs') := Option.some.inj ((hC _).symm.trans h)
  have hS : S' = S := (congrArg Prod.fst he).symm
  have hv : vs' = coreStack (v :: st) := by rw [coreStack_cons]; exact (congrArg Prod.snd he).symm
  exact ⟨hS, v :: st, hL st, hv⟩

/-- `global.get`, backwards. -/
theorem step_back_global {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {x : GlobalIdx} {S S' : Silmaril.Wasm.Execution.Core.Store H'}
    {F : Silmaril.Wasm.Execution.Core.Frame} (hx : GAgreeAt S F s mod x)
    {st : List Value} {vs' : List Silmaril.Wasm.Execution.Core.Val}
    (h : Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st)
      (Lime1.Instr.globalGet x).toCore = some (S', vs')) :
    S' = S ∧ ∃ st', Silmaril.Wasm.Lime1.Execution.constStep? s mod (.globalGet x) st =
      some st' ∧ vs' = coreStack st' := by
  have h' : ∃ a g, S.global? F x = some (a, g) ∧ S = S' ∧ coreStack st ++ [g.value] = vs' := by
    simpa only [Lime1.Instr.toCore, Silmaril.Wasm.Execution.Core.constInstr?,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq,
      Prod.exists] using h
  obtain ⟨a, g, hg, hS, hvs⟩ := h'
  have hr : (lread s mod x).map Value.toCore = some g.value := by
    have hx' : (S.global? F x).map (fun p => p.2.value) = (lread s mod x).map Value.toCore := hx
    rw [← hx', hg]; rfl
  obtain ⟨v, hv, hvc⟩ := Option.map_eq_some_iff.mp hr
  have hL : Silmaril.Wasm.Lime1.Execution.constStep? s mod (.globalGet x) st = some (v :: st) := by
    rw [constStep_globalGet, hv]; rfl
  exact ⟨hS.symm, v :: st, hL, by rw [coreStack_cons, hvc, hvs]⟩

/-- **One constant step, backwards.** -/
theorem step_back {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
    {i : Lime1.Instr} (hc : ConstantInstr C i)
    {S S' : Silmaril.Wasm.Execution.Core.Store H'} {F : Silmaril.Wasm.Execution.Core.Frame}
    (hG : ∀ x, i = .globalGet x → GAgreeAt S F s mod x)
    {st : List Value} {vs' : List Silmaril.Wasm.Execution.Core.Val}
    (h : Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st) i.toCore = some (S', vs')) :
    S' = S ∧ ∃ st', Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some st' ∧
      vs' = coreStack st' := by
  cases hc with
  | intConst t x => exact step_back_push (v := Value.int t x) (fun _ => rfl) (fun _ => rfl) h
  | floatConst t x => exact step_back_push (v := Value.float t x) (fun _ => rfl) (fun _ => rfl) h
  | globalGet x => exact step_back_global (hG x rfl) h
  | add t => exact step_back_bin (.inl rfl) h
  | sub t => exact step_back_bin (.inr (.inl rfl)) h
  | mul t => exact step_back_bin (.inr (.inr rfl)) h

/-- **A run of constant steps, backwards.** -/
theorem fold_back {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
    {S : Silmaril.Wasm.Execution.Core.Store H'} {F : Silmaril.Wasm.Execution.Core.Frame} :
    ∀ {es : Lime1.Expr} {st : List Value} {S' : Silmaril.Wasm.Execution.Core.Store H'}
      {vs' : List Silmaril.Wasm.Execution.Core.Val},
      (∀ i ∈ es, ConstantInstr C i) → (∀ x, Lime1.Instr.globalGet x ∈ es → GAgreeAt S F s mod x) →
      (es.map Lime1.Instr.toCore).foldlM
        (fun (p : Silmaril.Wasm.Execution.Core.Store H' × List Silmaril.Wasm.Execution.Core.Val) i =>
          Silmaril.Wasm.Execution.Core.constInstr? p.1 F p.2 i) (S, coreStack st) = some (S', vs') →
      S' = S ∧ ∃ st', es.foldlM (fun stack i => Silmaril.Wasm.Lime1.Execution.constStep? s mod i
        stack) st = some st' ∧ vs' = coreStack st'
  | [], st, _, _, _, _, h => by
    simp only [List.map_nil, List.foldlM_nil, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, st, rfl, rfl⟩
  | i :: es, st, _, _, hc, hG, h => by
    simp only [List.map_cons, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨⟨S₁, vs₁⟩, h₁, h₂⟩ := h
    obtain ⟨rfl, st₁, hs₁, rfl⟩ := step_back (hc i (by simp))
      (fun x hx => hG x (by simp [hx])) h₁
    obtain ⟨rfl, st', hs', rfl⟩ := fold_back (fun j hj => hc j (by simp [hj]))
      (fun x hx => hG x (by simp [hx])) h₂
    refine ⟨rfl, st', ?_, rfl⟩
    simp only [List.foldlM_cons, hs₁, Option.bind_eq_bind, Option.bind_some]
    exact hs'

/-- **Core 3.0 evaluation of the image of a Lime1 constant expression is Lime1 evaluation.** -/
theorem evalConst_back {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {C : Context} {es : Lime1.Expr} (hc : ∀ i ∈ es, ConstantInstr C i)
    {S S' : Silmaril.Wasm.Execution.Core.Store H'} {F : Silmaril.Wasm.Execution.Core.Frame}
    (hG : ∀ x, Lime1.Instr.globalGet x ∈ es → GAgreeAt S F s mod x)
    {v : Silmaril.Wasm.Execution.Core.Val}
    (h : Silmaril.Wasm.Execution.Core.evalConst? S F (Lime1.Expr.toCore es) = some (S', v)) :
    S' = S ∧ ∃ v', Silmaril.Wasm.Lime1.Execution.constExpr? s mod es = some v' ∧
      v = v'.toCore := by
  simp only [Silmaril.Wasm.Execution.Core.evalConst?, Silmaril.Wasm.Execution.Core.constExpr?,
    Lime1.Expr.toCore_eq_map] at h
  split at h
  · rename_i S₁ w hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show ((S, []) : Silmaril.Wasm.Execution.Core.Store H' × _) = (S, coreStack []) from rfl]
      at hw
    obtain ⟨rfl, st', hst', hw'⟩ := fold_back hc hG hw
    have hm : st'.map Value.toCore = [w] := by
      have := congrArg List.reverse hw'
      simpa [coreStack] using this.symm
    match st', hm with
    | [w'], hm =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
      refine ⟨rfl, w', ?_, hm.symm⟩
      simp only [Silmaril.Wasm.Lime1.Execution.constExpr?, Option.bind_eq_bind, hst',
        Option.bind_some]
  · cases h

/-! ## Typing with globals -/

theorem instrType_globalGet {C : Context} {x : GlobalIdx} :
    ∀ {i : Lime1.Instr} {a b : V1.ResultType}, InstrType C i a b → i = .globalGet x →
      ∃ gt, C.globals[x.toNat]? = some gt ∧ b = a ++ [gt.value]
  | _, _, _, .frame pre h, hi => by
    obtain ⟨gt, hgt, hb⟩ := instrType_globalGet h hi
    exact ⟨gt, hgt, by rw [hb, List.append_assoc]⟩
  | _, _, _, .globalGet _ hgt, hi => by cases hi; exact ⟨_, hgt, rfl⟩
  | _, _, _, .nop .., hi | _, _, _, .unreachable .., hi | _, _, _, .drop .., hi
  | _, _, _, .select .., hi | _, _, _, .block .., hi | _, _, _, .loop .., hi
  | _, _, _, .if_ .., hi | _, _, _, .br .., hi | _, _, _, .brIf .., hi
  | _, _, _, .brTable .., hi | _, _, _, .return_ .., hi | _, _, _, .call .., hi
  | _, _, _, .callIndirect .., hi | _, _, _, .localGet .., hi | _, _, _, .localSet .., hi
  | _, _, _, .localTee .., hi | _, _, _, .intConst .., hi | _, _, _, .globalSet .., hi
  | _, _, _, .intLoad .., hi | _, _, _, .floatLoad .., hi | _, _, _, .intStore .., hi
  | _, _, _, .floatStore .., hi | _, _, _, .memorySize .., hi | _, _, _, .memoryGrow .., hi
  | _, _, _, .memoryFill .., hi | _, _, _, .memoryCopy .., hi | _, _, _, .floatConst .., hi
  | _, _, _, .intUnOp .., hi | _, _, _, .intBinOp .., hi | _, _, _, .intTestOp .., hi
  | _, _, _, .intRelOp .., hi | _, _, _, .floatUnOp .., hi | _, _, _, .floatBinOp .., hi
  | _, _, _, .floatRelOp .., hi | _, _, _, .convert .., hi => nomatch hi

/-- A constant step other than `global.get` does not read the module instance. -/
theorem constStep_nonGlobal {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {i : Lime1.Instr} (hi : ∀ x, i ≠ .globalGet x) (st : List Value) :
    Silmaril.Wasm.Lime1.Execution.constStep? s mod i st =
      Silmaril.Wasm.Lime1.Execution.constStep? s ({} : ModuleInst) i st := by
  cases i <;> try rfl
  exact absurd rfl (hi _)

/-- The global reads of a module instance have the types of a context. -/
def GTyped (s : Silmaril.Wasm.Lime1.Execution.Store H) (mod : ModuleInst) (C : Context) : Prop :=
  ∀ x v, lread s mod x = some v → ∀ gt, C.globals[x.toNat]? = some gt → v.type = gt.value

theorem step_tyG {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
    (hGT : GTyped s mod C) {i : Lime1.Instr} {a b : V1.ResultType} (hi : InstrType C i a b)
    {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some st') (hst : StackTy st a) :
    StackTy st' b := by
  by_cases hg : ∃ x, i = .globalGet x
  · obtain ⟨x, rfl⟩ := hg
    obtain ⟨gt, hgt, rfl⟩ := instrType_globalGet hi rfl
    rw [constStep_globalGet] at h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    have := Silmaril.Proofs.Wasm.Component.Lime1Inst.stackTy_cons (v := v) hst
    rwa [hGT x v hv gt hgt] at this
  · have hne : ∀ x, i ≠ .globalGet x := fun x hx => hg ⟨x, hx⟩
    rw [constStep_nonGlobal hne] at h
    exact Silmaril.Proofs.Wasm.Component.Lime1Inst.step_ty rfl hi h hst

theorem fold_tyG {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
    (hGT : GTyped s mod C) :
    ∀ {es : Lime1.Expr} {a c : V1.ResultType} {st st' : List Value}, ExprType C es a c →
      StackTy st a →
      es.foldlM (fun stack i => Silmaril.Wasm.Lime1.Execution.constStep? s mod i stack) st =
        some st' → StackTy st' c
  | [], _, _, _, _, he, hst, h => by
    cases he
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ hst
  | _ :: _, _, _, _, _, .cons hi his, hst, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    exact fold_tyG hGT his (step_tyG hGT hi h₁ hst) h₂

/-- **A typed Lime1 constant expression evaluates to a value of its type**, in a module instance
whose global reads have the context's types. -/
theorem constExpr?_typeG {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {C : Context} (hGT : GTyped s mod C) {es : Lime1.Expr} {t : V1.ValType}
    (he : ExprType C es [] [t]) {v : Value}
    (h : Silmaril.Wasm.Lime1.Execution.constExpr? s mod es = some v) : v.type = t := by
  simp only [Silmaril.Wasm.Lime1.Execution.constExpr?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  have hty := fold_tyG hGT he (st := []) rfl hvs
  rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at hv
  subst hv
  simpa [StackTy] using hty

end Silmaril.Proofs.Wasm.Component.Lime1Eng
