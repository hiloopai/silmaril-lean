module

public import Silmaril.Wasm.Component.Lime1Bridge.Thms

/-!
# Lime1 initializer values have their declared types

A Lime1 global initializer that the validator types `[] → [t]` and that the executable evaluator
`Lime1.Execution.constExpr?` evaluates, in a module instance without globals, to `v` has
`v.type = t` (`constExpr?_type`). The evaluator's stack has its top at the head, the typing's
result type its top at the end (`StackTy`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst)

/-- The value stack `st` (top at the head) has the result type `ts` (top at the end). -/
def StackTy (st : List Value) (ts : V1.ResultType) : Prop := (st.map (·.type)).reverse = ts

theorem instrType_intConst {C : Context} {t : IntType} {x : BitVec t.width} :
    ∀ {i : Lime1.Instr} {a b : V1.ResultType}, InstrType C i a b → i = .intConst t x →
      b = a ++ [.int t]
  | _, _, _, .frame pre h, hi => by rw [instrType_intConst h hi, List.append_assoc]
  | _, _, _, .intConst .., hi => by cases hi; rfl
  | _, _, _, .nop .., hi | _, _, _, .unreachable .., hi | _, _, _, .drop .., hi
  | _, _, _, .select .., hi | _, _, _, .block .., hi | _, _, _, .loop .., hi
  | _, _, _, .if_ .., hi | _, _, _, .br .., hi | _, _, _, .brIf .., hi
  | _, _, _, .brTable .., hi | _, _, _, .return_ .., hi | _, _, _, .call .., hi
  | _, _, _, .callIndirect .., hi | _, _, _, .localGet .., hi | _, _, _, .localSet .., hi
  | _, _, _, .localTee .., hi | _, _, _, .globalGet .., hi | _, _, _, .globalSet .., hi
  | _, _, _, .intLoad .., hi | _, _, _, .floatLoad .., hi | _, _, _, .intStore .., hi
  | _, _, _, .floatStore .., hi | _, _, _, .memorySize .., hi | _, _, _, .memoryGrow .., hi
  | _, _, _, .memoryFill .., hi | _, _, _, .memoryCopy .., hi | _, _, _, .floatConst .., hi
  | _, _, _, .intUnOp .., hi | _, _, _, .intBinOp .., hi | _, _, _, .intTestOp .., hi
  | _, _, _, .intRelOp .., hi | _, _, _, .floatUnOp .., hi | _, _, _, .floatBinOp .., hi
  | _, _, _, .floatRelOp .., hi | _, _, _, .convert .., hi=> nomatch hi

theorem instrType_floatConst {C : Context} {t : FloatType} {x : BitVec t.width} :
    ∀ {i : Lime1.Instr} {a b : V1.ResultType}, InstrType C i a b → i = .floatConst t x →
      b = a ++ [.float t]
  | _, _, _, .frame pre h, hi => by rw [instrType_floatConst h hi, List.append_assoc]
  | _, _, _, .floatConst .., hi => by cases hi; rfl
  | _, _, _, .nop .., hi | _, _, _, .unreachable .., hi | _, _, _, .drop .., hi
  | _, _, _, .select .., hi | _, _, _, .block .., hi | _, _, _, .loop .., hi
  | _, _, _, .if_ .., hi | _, _, _, .br .., hi | _, _, _, .brIf .., hi
  | _, _, _, .brTable .., hi | _, _, _, .return_ .., hi | _, _, _, .call .., hi
  | _, _, _, .callIndirect .., hi | _, _, _, .localGet .., hi | _, _, _, .localSet .., hi
  | _, _, _, .localTee .., hi | _, _, _, .globalGet .., hi | _, _, _, .globalSet .., hi
  | _, _, _, .intLoad .., hi | _, _, _, .floatLoad .., hi | _, _, _, .intStore .., hi
  | _, _, _, .floatStore .., hi | _, _, _, .memorySize .., hi | _, _, _, .memoryGrow .., hi
  | _, _, _, .memoryFill .., hi | _, _, _, .memoryCopy .., hi | _, _, _, .intConst .., hi
  | _, _, _, .intUnOp .., hi | _, _, _, .intBinOp .., hi | _, _, _, .intTestOp .., hi
  | _, _, _, .intRelOp .., hi | _, _, _, .floatUnOp .., hi | _, _, _, .floatBinOp .., hi
  | _, _, _, .floatRelOp .., hi | _, _, _, .convert .., hi=> nomatch hi

theorem instrType_intBinOp {C : Context} {t : IntType} {op : IntBinOp} :
    ∀ {i : Lime1.Instr} {a b : V1.ResultType}, InstrType C i a b → i = .intBinOp t op →
      ∃ pre, a = pre ++ [.int t, .int t] ∧ b = pre ++ [.int t]
  | _, _, _, .frame pre h, hi => by
    obtain ⟨p, ha, hb⟩ := instrType_intBinOp h hi
    exact ⟨pre ++ p, by rw [ha, List.append_assoc], by rw [hb, List.append_assoc]⟩
  | _, _, _, .intBinOp .., hi => by cases hi; exact ⟨[], rfl, rfl⟩
  | _, _, _, .nop .., hi | _, _, _, .unreachable .., hi | _, _, _, .drop .., hi
  | _, _, _, .select .., hi | _, _, _, .block .., hi | _, _, _, .loop .., hi
  | _, _, _, .if_ .., hi | _, _, _, .br .., hi | _, _, _, .brIf .., hi
  | _, _, _, .brTable .., hi | _, _, _, .return_ .., hi | _, _, _, .call .., hi
  | _, _, _, .callIndirect .., hi | _, _, _, .localGet .., hi | _, _, _, .localSet .., hi
  | _, _, _, .localTee .., hi | _, _, _, .globalGet .., hi | _, _, _, .globalSet .., hi
  | _, _, _, .intLoad .., hi | _, _, _, .floatLoad .., hi | _, _, _, .intStore .., hi
  | _, _, _, .floatStore .., hi | _, _, _, .memorySize .., hi | _, _, _, .memoryGrow .., hi
  | _, _, _, .memoryFill .., hi | _, _, _, .memoryCopy .., hi | _, _, _, .intConst .., hi
  | _, _, _, .floatConst .., hi | _, _, _, .intUnOp .., hi | _, _, _, .intTestOp .., hi
  | _, _, _, .intRelOp .., hi | _, _, _, .floatUnOp .., hi | _, _, _, .floatBinOp .., hi
  | _, _, _, .floatRelOp .., hi | _, _, _, .convert .., hi=> nomatch hi

theorem constBinary_shape {t : IntType} {op : IntBinOp} {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constBinary? t op st = some st') :
    ∃ y x rest z, st = y :: x :: rest ∧ y.type = .int t ∧ x.type = .int t ∧ st' = z :: rest ∧
      z.type = .int t := by
  cases t <;> simp only [Silmaril.Wasm.Lime1.Execution.constBinary?] at h <;> split at h <;>
    simp only [Option.map_eq_some_iff, reduceCtorEq] at h
  all_goals obtain ⟨z, -, rfl⟩ := h
  all_goals exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩

theorem constStep_bin {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {t : IntType} {op : IntBinOp} {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constStep? s mod (.intBinOp t op) st = some st') :
    ∃ t' op' y x rest z, Lime1.Instr.intBinOp t op = .intBinOp t' op' ∧ st = y :: x :: rest ∧
      y.type = .int t' ∧ x.type = .int t' ∧ st' = z :: rest ∧ z.type = .int t' := by
  cases op <;> simp only [Silmaril.Wasm.Lime1.Execution.constStep?,
    Silmaril.Wasm.Lime1.Execution.constInstr?, Option.map_none, reduceCtorEq] at h
  all_goals obtain ⟨y, x, rest, z, h1, h2, h3, h4, h5⟩ := constBinary_shape h
  all_goals exact ⟨_, _, y, x, rest, z, rfl, h1, h2, h3, h4, h5⟩

/-- The shapes of a successful constant step in a module instance without globals. -/
theorem constStep_shape {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (hg : mod.globals = []) {i : Lime1.Instr} {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some st') :
    (∃ t x, i = .intConst t x ∧ st' = ⟨.int t, x⟩ :: st) ∨
      (∃ t x, i = .floatConst t x ∧ st' = ⟨.float t, x⟩ :: st) ∨
      (∃ t op y x rest z, i = .intBinOp t op ∧ st = y :: x :: rest ∧ y.type = .int t ∧
        x.type = .int t ∧ st' = z :: rest ∧ z.type = .int t) := by
  cases i with
  | intConst t x =>
    have h' : some (Value.int t x :: st) = some st' := by simpa only [
      Silmaril.Wasm.Lime1.Execution.constStep?, Silmaril.Wasm.Lime1.Execution.constInstr?,
      Option.map_some] using h
    exact .inl ⟨t, x, rfl, (Option.some.inj h').symm⟩
  | floatConst t x =>
    have h' : some (Value.float t x :: st) = some st' := by simpa only [
      Silmaril.Wasm.Lime1.Execution.constStep?, Silmaril.Wasm.Lime1.Execution.constInstr?,
      Option.map_some] using h
    exact .inr (.inl ⟨t, x, rfl, (Option.some.inj h').symm⟩)
  | intBinOp t op => exact .inr (.inr (constStep_bin h))
  | globalGet x => simp [Silmaril.Wasm.Lime1.Execution.constStep?,
      Silmaril.Wasm.Lime1.Execution.constInstr?, hg] at h
  | _ => simp [Silmaril.Wasm.Lime1.Execution.constStep?,
      Silmaril.Wasm.Lime1.Execution.constInstr?] at h

theorem stackTy_cons {v : Value} {st : List Value} {a : V1.ResultType} (h : StackTy st a) :
    StackTy (v :: st) (a ++ [v.type]) := by
  simp only [StackTy, List.map_cons, List.reverse_cons] at h ⊢
  rw [h]

/-- One successful constant step keeps the stack typed. -/
theorem step_ty {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (hg : mod.globals = []) {C : Context} {i : Lime1.Instr} {a b : V1.ResultType}
    (hi : InstrType C i a b) {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some st') (hst : StackTy st a) :
    StackTy st' b := by
  rcases constStep_shape hg h with ⟨t, x, rfl, rfl⟩ | ⟨t, x, rfl, rfl⟩ |
    ⟨t, op, y, x, rest, z, rfl, rfl, hy, hx, rfl, hz⟩
  · rw [instrType_intConst hi rfl]; exact stackTy_cons hst
  · rw [instrType_floatConst hi rfl]; exact stackTy_cons hst
  · obtain ⟨pre, rfl, rfl⟩ := instrType_intBinOp hi rfl
    have hr : (rest.map (·.type)).reverse ++ [NumType.int t, .int t] =
        pre ++ [.int t, .int t] := by
      simpa only [StackTy, List.map_cons, List.reverse_cons, hx, hy, List.append_assoc,
        List.cons_append, List.nil_append] using hst
    have hpre : (rest.map (·.type)).reverse = pre := List.append_inj_left' hr rfl
    have hz' : StackTy (z :: rest) (pre ++ [z.type]) := stackTy_cons hpre
    rwa [hz] at hz'

/-- A typed sequence of successful constant steps ends in a stack of the result type. -/
theorem fold_ty {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (hg : mod.globals = []) {C : Context} :
    ∀ {es : Lime1.Expr} {a c : V1.ResultType} {st st' : List Value}, ExprType C es a c →
      StackTy st a →
      es.foldlM (fun stack i => Silmaril.Wasm.Lime1.Execution.constStep? s mod i stack) st =
        some st' → StackTy st' c
  | [], _, _, _, _, he, hst, h => by
    cases he
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ hst
  | i :: es, _, _, _, _, .cons hi his, hst, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    exact fold_ty hg his (step_ty hg hi h₁ hst) h₂

/-- **A typed Lime1 initializer evaluates to a value of its type**, in a module instance
without globals. -/
theorem constExpr?_type {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (hg : mod.globals = []) {C : Context} {es : Lime1.Expr} {t : V1.ValType}
    (he : ExprType C es [] [t]) {v : Value}
    (h : Silmaril.Wasm.Lime1.Execution.constExpr? s mod es = some v) : v.type = t := by
  simp only [Silmaril.Wasm.Lime1.Execution.constExpr?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  have hty := fold_ty hg he (st := []) rfl hvs
  rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at hv
  subst hv
  simpa [StackTy] using hty

end Silmaril.Proofs.Wasm.Component.Lime1Inst
