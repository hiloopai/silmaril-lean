module

public import Silmaril.Wasm.Lime1.Execution.Instantiation
public import Silmaril.Raw.Wasm.Versions.Lime1.Execution.Properties

/-! # Constant evaluation agrees with the independent Lime1 machine

The executable initializer evaluator uses a stack with its top at the head;
the machine's instruction stack is bottom-to-top. The soundness theorem relates
these presentations for every successful evaluation, including extended integer
constant expressions.
-/

@[expose] public section
namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution.Runtime

theorem constInstr?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {i : Instr} {v : Value} (h : constInstr? s f.module i = some v) :
    Steps host ⟨s, f, [.source i]⟩ ⟨s, f, [value v]⟩ := by
  cases i <;> simp only [constInstr?] at h
  all_goals try contradiction
  case intConst t bits => cases h; exact .refl
  case floatConst t bits => cases h; exact .refl
  case globalGet i =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a, ha, g, hg, rfl⟩ := h
    exact (Step.globalGet s f i a g ha hg).steps

private theorem except_toOption_some {E A : Type*} {e : Except E A} {a : A}
    (h : e.toOption = some a) : e = .ok a := by
  cases e <;> simp_all [Except.toOption]

/-- A successful binary constant operation consumed two values of the selected type. -/
theorem constBinary?_success (t : IntType) (op : IntBinOp)
    {stack result : List Value} (h : constBinary? t op stack = some result) :
    ∃ (x y z : BitVec t.width) (rest : List Value),
      stack = .int t y :: .int t x :: rest ∧ result = .int t z :: rest ∧
      Numerics.intBinOp t op x y = .ok z := by
  cases t <;> simp only [constBinary?] at h
  all_goals split at h
  all_goals try contradiction
  all_goals rename_i y x rest
  all_goals
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨x, y, z, rest, rfl, rfl, except_toOption_some hz⟩

theorem constBinary?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    (t : IntType) (op : IntBinOp) {stack result : List Value}
    (h : constBinary? t op stack = some result) :
    Steps host ⟨s, f, values stack.reverse ++ [.source (.intBinOp t op)]⟩
      ⟨s, f, values result.reverse⟩ := by
  obtain ⟨x, y, z, rest, rfl, rfl, evaluated⟩ := constBinary?_success t op h
  have step : Step host
      ⟨s, f, [value (.int t x), value (.int t y), .source (.intBinOp t op)]⟩
      ⟨s, f, [value (.int t z)]⟩ := .pure _ _ (.intBinary t op x y z evaluated)
  simpa [List.reverse_cons, values, List.append_assoc] using
    (step.context rest.reverse []).steps

/-- One evaluator instruction agrees with machine execution beneath an arbitrary stack. -/
theorem constStep?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {i : Instr} {stack result : List Value} (h : constStep? s f.module i stack = some result) :
    Steps host ⟨s, f, values stack.reverse ++ [.source i]⟩
      ⟨s, f, values result.reverse⟩ := by
  cases i with
  | intBinOp t op =>
    cases op <;> simp only [constStep?, constInstr?] at h
    all_goals try contradiction
    all_goals exact constBinary?_sound host s f t _ h
  | _ =>
    simp only [constStep?] at h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa [List.reverse_cons, values, List.append_assoc] using
      (constInstr?_sound host s f hv).context stack.reverse []

/-- The evaluator's top-first stack is reversed at the machine boundary. -/
theorem constFold?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {es : Expr} {stack result : List Value}
    (h : es.foldlM (fun stack i => constStep? s f.module i stack) stack = some result) :
    Steps host ⟨s, f, values stack.reverse ++ expression es⟩
      ⟨s, f, values result.reverse⟩ := by
  induction es generalizing stack with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst result
    simp only [expression, List.map_nil, List.append_nil]
    exact .refl
  | cons i es ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, first, rest⟩ := h
    have begin := (constStep?_sound host s f first).context [] (expression es)
    have finish := ih rest
    simpa [values, expression, List.append_assoc] using begin.trans finish

/-- Every successful initializer value is produced by an actual finite machine run. -/
theorem constExpr?_sound {H : Type} (host : HostSemantics H) (s : Store H) (f : Frame)
    {es : Expr} {v : Value} (h : constExpr? s f.module es = some v) :
    Steps host ⟨s, f, expression es⟩ ⟨s, f, [value v]⟩ := by
  simp only [constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vs, hv, result⟩ := h
  split at result <;> simp_all
  simpa [values] using constFold?_sound host s f hv

end Silmaril.Wasm.Lime1.Execution
