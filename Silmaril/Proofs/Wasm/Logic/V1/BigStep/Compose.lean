module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.HeightCompose

/-!
# Decomposition of concatenated code

The semantic content of Wasm Logic's `[seq]` rule: a run of `es ++ es'` either
runs `es` to a normal result and continues with `es'`, or `es` ends abruptly and
`es'` is unreachable.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- Sequential composition when the first part terminates normally. -/
theorem BigStep.append {s s₂ : Store H} {f f₂ : Frame} {vs ws : List Value}
    {es es' : List Admin} {o : Outcome H} (first : BigStep host s f vs es ⟨s₂, f₂, .normal ws⟩)
    (second : BigStep host s₂ f₂ ws es' o) : BigStep host s f vs (es ++ es') o := by
  obtain ⟨n, h₁⟩ := first.toHeight
  obtain ⟨m, h₂⟩ := second.toHeight
  exact (h₁.append h₂).toBigStep

/-- An abrupt first part abandons everything after it. -/
theorem BigStep.append_abrupt {s : Store H} {f : Frame} {vs : List Value}
    {es es' : List Admin} {o : Outcome H} (first : BigStep host s f vs es o)
    (abrupt : o.result.Abrupt) : BigStep host s f vs (es ++ es') o := by
  obtain ⟨n, h⟩ := first.toHeight
  exact (h.append_abrupt abrupt).toBigStep

/-- Decomposition of a run of concatenated code: the `[seq]` rule, semantically. -/
theorem BigStep.append_inv {s : Store H} {f : Frame} {vs : List Value}
    {es es' : List Admin} {o : Outcome H} (h : BigStep host s f vs (es ++ es') o) :
    (∃ s₂ f₂ ws, BigStep host s f vs es ⟨s₂, f₂, .normal ws⟩ ∧ BigStep host s₂ f₂ ws es' o) ∨
      (BigStep host s f vs es o ∧ o.result.Abrupt) := by
  obtain ⟨n, hn⟩ := h.toHeight
  rcases hn.append_inv with ⟨s₂, f₂, ws, h₁, h₂⟩ | ⟨h₁, hab⟩
  · exact .inl ⟨s₂, f₂, ws, h₁.toBigStep, h₂.toBigStep⟩
  · exact .inr ⟨h₁.toBigStep, hab⟩

/-- Operand-stack weakening: the `[extension]` rule, semantically. -/
theorem BigStep.weaken {s : Store H} {f : Frame} {vs us : List Value} {es : List Admin}
    {o : Outcome H} (h : BigStep host s f vs es o) :
    BigStep host s f (us ++ vs) es ⟨o.store, o.frame, o.result.extend us⟩ := by
  obtain ⟨n, hn⟩ := h.toHeight
  exact hn.weaken.toBigStep

end Silmaril.Wasm.Logic.V1
