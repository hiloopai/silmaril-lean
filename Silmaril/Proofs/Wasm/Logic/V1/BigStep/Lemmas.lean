module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Plain

/-!
# Structural laws of the big-step semantics

Operand-stack weakening (`BigStep.weaken`, in `…/Compose.lean`) is the semantic content of Wasm
Logic's `[extension]` rule, and the decomposition laws (`BigStep.append`,
`BigStep.append_inv`) are the semantic content of its `[seq]` rule.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

@[simp] theorem BigResult.extend_nil (r : BigResult) : r.extend [] = r := by
  cases r <;> simp [BigResult.extend]

theorem BigResult.extend_append (us vs : List Value) (r : BigResult) :
    (r.extend vs).extend us = r.extend (us ++ vs) := by
  cases r <;> simp [BigResult.extend]

variable {H : Type*} {host : HostSemantics H}

/-- Exhausted code returns the operand stack unchanged. -/
theorem BigStep.nil_inv {s : Store H} {f : Frame} {vs : List Value} {o : Outcome H}
    (h : BigStep host s f vs [] o) : o = ⟨s, f, .normal vs⟩ := by
  cases h
  rfl

/-- A leading integer constant is the same as pushing it on the operand stack. -/
private theorem BigStep.intConst_cons_iff {s : Store H} {f : Frame} {vs : List Value}
    {t : IntType} {bits : BitVec t.width} {es : List Admin} {o : Outcome H} :
    BigStep host s f vs (.source (.intConst t bits) :: es) o ↔
      BigStep host s f (vs ++ [⟨.int t, bits⟩]) es o := by
  constructor
  · intro h
    cases h with
    | plain =>
      rename_i step rest
      cases step
      simpa [Value.int] using rest
    | plainTrap =>
      rename_i step
      cases step
  · intro h
    have h' : BigStep host s f (vs ++ []) (.source (.intConst t bits) :: es) o :=
      BigStep.plain (Plain.intConst s f t bits) (by simpa [Value.int] using h)
    simpa using h'

/-- A leading floating-point constant is the same as pushing it on the operand stack. -/
private theorem BigStep.floatConst_cons_iff {s : Store H} {f : Frame} {vs : List Value}
    {t : FloatType} {bits : BitVec t.width} {es : List Admin} {o : Outcome H} :
    BigStep host s f vs (.source (.floatConst t bits) :: es) o ↔
      BigStep host s f (vs ++ [⟨.float t, bits⟩]) es o := by
  constructor
  · intro h
    cases h with
    | plain =>
      rename_i step rest
      cases step
      simpa [Value.float] using rest
    | plainTrap =>
      rename_i step
      cases step
  · intro h
    have h' : BigStep host s f (vs ++ []) (.source (.floatConst t bits) :: es) o :=
      BigStep.plain (Plain.floatConst s f t bits) (by simpa [Value.float] using h)
    simpa using h'

/-- A single leading constant is the same as pushing it on the operand stack. -/
private theorem BigStep.value_cons_iff {s : Store H} {f : Frame} {vs : List Value}
    {w : Value} {es : List Admin} {o : Outcome H} :
    BigStep host s f vs (value w :: es) o ↔ BigStep host s f (vs ++ [w]) es o := by
  obtain ⟨t, bits⟩ := w
  cases t with
  | int t => exact BigStep.intConst_cons_iff
  | float t => exact BigStep.floatConst_cons_iff

/-- Leading constants in the code are the same as operands on the stack. -/
theorem BigStep.values_append_iff {s : Store H} {f : Frame} {vs ws : List Value}
    {es : List Admin} {o : Outcome H} :
    BigStep host s f vs (values ws ++ es) o ↔ BigStep host s f (vs ++ ws) es o := by
  induction ws generalizing vs with
  | nil => simp [values]
  | cons w ws ih =>
    rw [show values (w :: ws) = value w :: values ws from rfl, List.cons_append,
      BigStep.value_cons_iff, ih]
    simp

theorem BigStep.of_values_append {s : Store H} {f : Frame} {vs ws : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStep host s f (vs ++ ws) es o) :
    BigStep host s f vs (values ws ++ es) o := values_append_iff.mpr h

end Silmaril.Wasm.Logic.V1
