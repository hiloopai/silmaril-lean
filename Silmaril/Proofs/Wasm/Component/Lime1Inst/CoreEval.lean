module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.InitType
public import Silmaril.Wasm.Execution.Core.Exec.ConstEvalComplete

/-!
# Lime1 initializer evaluation is Core 3.0 constant evaluation

The executable evaluators of Lime1 (`Lime1.Execution.constExpr?`, stack top at the head) and of
Core (`Execution.Core.evalConst?`, stack top at the end) agree on the Core image of a Lime1
initializer that Lime1 evaluates in a module instance without globals:

* `step_core`: one constant step;
* **`evalConst?_toCore`**: `evalConst? S F (Expr.toCore e) = some (S, v.toCore)`, for every Core
  store `S` and frame `F`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm Silmaril.Wasm.Lime1
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst)

/-- The Core stack of a Lime1 stack. -/
def coreStack (st : List Value) : List Silmaril.Wasm.Execution.Core.Val :=
  (st.map Value.toCore).reverse

theorem except_ok_of_toOption {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e <;> simp_all [Except.toOption]

theorem int?_toCore (t : IntType) (x : BitVec t.width) :
    Silmaril.Wasm.Execution.Core.Val.int? t (Value.toCore ⟨.int t, x⟩) = some x :=
  Silmaril.Wasm.Execution.Core.Val.int?_self t x

theorem step_core_bin {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {t : IntType} {op : IntBinOp} {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constStep? s mod (.intBinOp t op) st = some st')
    {H' : Type} (S : Silmaril.Wasm.Execution.Core.Store H') (F : Silmaril.Wasm.Execution.Core.Frame) :
    Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st) (Lime1.Instr.intBinOp t op).toCore =
      some (S, coreStack st') := by
  cases t <;> cases op <;> simp only [Silmaril.Wasm.Lime1.Execution.constStep?,
    Silmaril.Wasm.Lime1.Execution.constInstr?, Option.map_none, reduceCtorEq,
    Silmaril.Wasm.Lime1.Execution.constBinary?] at h
  all_goals split at h
  all_goals simp only [Option.map_eq_some_iff, reduceCtorEq] at h
  all_goals obtain ⟨z, hz, rfl⟩ := h
  all_goals
    have hz' := except_ok_of_toOption hz
    simp only [coreStack, List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Lime1.Instr.toCore, Silmaril.Wasm.Execution.Core.constInstr?,
      Silmaril.Wasm.Execution.Core.constBinOp, ite_true,
      Silmaril.Wasm.Execution.Core.pop2?_append, Option.bind_eq_bind, Option.bind_some]
    erw [int?_toCore, Option.bind_some, int?_toCore, Option.bind_some, hz']
    rfl

theorem step_core_push {H' : Type} (S : Silmaril.Wasm.Execution.Core.Store H')
    (F : Silmaril.Wasm.Execution.Core.Frame) (st : List Value) {i : Lime1.Instr} {v : Value}
    (hi : Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st) i.toCore =
      some (S, coreStack st ++ [v.toCore])) :
    Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st) i.toCore =
      some (S, coreStack (v :: st)) := by
  simpa [coreStack] using hi

theorem step_core {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (hg : mod.globals = []) {i : Lime1.Instr} {st st' : List Value}
    (h : Silmaril.Wasm.Lime1.Execution.constStep? s mod i st = some st') {H' : Type}
    (S : Silmaril.Wasm.Execution.Core.Store H') (F : Silmaril.Wasm.Execution.Core.Frame) :
    Silmaril.Wasm.Execution.Core.constInstr? S F (coreStack st) i.toCore =
      some (S, coreStack st') := by
  rcases constStep_shape hg h with ⟨t, x, rfl, rfl⟩ | ⟨t, x, rfl, rfl⟩ | ⟨t, op, -, -, -, -, rfl, -⟩
  · exact step_core_push S F st rfl
  · exact step_core_push S F st rfl
  · exact step_core_bin h S F

theorem fold_core {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (hg : mod.globals = []) {H' : Type} (S : Silmaril.Wasm.Execution.Core.Store H')
    (F : Silmaril.Wasm.Execution.Core.Frame) :
    ∀ {es : Lime1.Expr} {st st' : List Value},
      es.foldlM (fun stack i => Silmaril.Wasm.Lime1.Execution.constStep? s mod i stack) st =
        some st' →
      (es.map Lime1.Instr.toCore).foldlM
        (fun (p : Silmaril.Wasm.Execution.Core.Store H' × List Silmaril.Wasm.Execution.Core.Val) i =>
          Silmaril.Wasm.Execution.Core.constInstr? p.1 F p.2 i) (S, coreStack st) =
        some (S, coreStack st')
  | [], _, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | i :: es, _, _, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    simp only [List.map_cons, List.foldlM_cons, step_core hg h₁ S F, Option.bind_eq_bind,
      Option.bind_some]
    exact fold_core hg S F h₂

/-- **Lime1 initializer evaluation is Core constant evaluation** of the image, in every Core
store and frame, when the Lime1 module instance has no globals. -/
theorem evalConst?_toCore {H : Type} {s : Silmaril.Wasm.Lime1.Execution.Store H}
    {mod : ModuleInst} (hg : mod.globals = []) {es : Lime1.Expr} {v : Value}
    (h : Silmaril.Wasm.Lime1.Execution.constExpr? s mod es = some v) {H' : Type}
    (S : Silmaril.Wasm.Execution.Core.Store H') (F : Silmaril.Wasm.Execution.Core.Frame) :
    Silmaril.Wasm.Execution.Core.evalConst? S F (Lime1.Expr.toCore es) = some (S, v.toCore) := by
  simp only [Silmaril.Wasm.Lime1.Execution.constExpr?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at hv
  subst hv
  have hf := fold_core hg S F (st := []) hvs
  simp only [Silmaril.Wasm.Execution.Core.evalConst?, Silmaril.Wasm.Execution.Core.constExpr?,
    Lime1.Expr.toCore_eq_map]
  rw [show ((S, []) : Silmaril.Wasm.Execution.Core.Store H' × _) = (S, coreStack []) from rfl, hf]
  rfl

end Silmaril.Proofs.Wasm.Component.Lime1Inst
