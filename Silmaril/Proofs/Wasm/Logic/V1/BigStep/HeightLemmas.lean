module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Height

/-!
# Structural laws of the height-indexed big-step semantics

The counterparts of `Silmaril/Wasm/V1/BigStep/Lemmas.lean`, keeping track of
the derivation height so that the soundness proof of Wasm Logic can recurse on
it.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- Pushing a leading constant onto the code costs exactly one derivation step. -/
private theorem BigStepN.value_cons {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {w : Value} {es : List Admin} {o : Outcome H}
    (h : BigStepN host n s f (vs ++ [w]) es o) :
    BigStepN host (n + 1) s f vs (value w :: es) o := by
  obtain ⟨t, bits⟩ := w
  cases t with
  | int t =>
    have h' : BigStepN host (n + 1) s f (vs ++ []) (.source (.intConst t bits) :: es) o :=
      BigStepN.plain (Plain.intConst s f t bits) (by simpa [Value.int] using h)
    simpa [value] using h'
  | float t =>
    have h' : BigStepN host (n + 1) s f (vs ++ []) (.source (.floatConst t bits) :: es) o :=
      BigStepN.plain (Plain.floatConst s f t bits) (by simpa [Value.float] using h)
    simpa [value] using h'

/-- Stripping a leading constant off the code only shrinks the derivation. -/
private theorem BigStepN.value_cons_inv {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {w : Value} {es : List Admin} {o : Outcome H}
    (h : BigStepN host n s f vs (value w :: es) o) :
    BigStepN host n s f (vs ++ [w]) es o := by
  obtain ⟨t, bits⟩ := w
  cases t with
  | int t =>
    have hi : BigStepN host n s f vs (.source (.intConst t bits) :: es) o := h
    cases hi with
    | plain step rest =>
      cases step
      exact BigStepN.mono (Nat.le_succ _) (by simpa [Value.int] using rest)
    | plainTrap step => cases step
  | float t =>
    have hf : BigStepN host n s f vs (.source (.floatConst t bits) :: es) o := h
    cases hf with
    | plain step rest =>
      cases step
      exact BigStepN.mono (Nat.le_succ _) (by simpa [Value.float] using rest)
    | plainTrap step => cases step

/-- Leading constants in the code are the same as operands on the stack. -/
theorem BigStepN.values_append {n : Nat} {s : Store H} {f : Frame} {vs ws : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStepN host n s f (vs ++ ws) es o) :
    BigStepN host (n + ws.length) s f vs (values ws ++ es) o := by
  induction ws generalizing n vs with
  | nil => simpa [values] using h
  | cons w ws ih =>
    have h' : BigStepN host n s f ((vs ++ [w]) ++ ws) es o := by simpa using h
    rw [show values (w :: ws) = value w :: values ws from rfl, List.cons_append,
      List.length_cons, ← Nat.add_assoc]
    exact BigStepN.value_cons (ih h')

theorem BigStepN.values_append_inv {n : Nat} {s : Store H} {f : Frame} {vs ws : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStepN host n s f vs (values ws ++ es) o) :
    BigStepN host n s f (vs ++ ws) es o := by
  induction ws generalizing n vs with
  | nil => simpa [values] using h
  | cons w ws ih =>
    rw [show values (w :: ws) = value w :: values ws from rfl, List.cons_append] at h
    have h2 := ih (BigStepN.value_cons_inv h)
    simpa using h2

/-- Operand-stack weakening: the `[extension]` rule, semantically. -/
theorem BigStepN.weaken {n : Nat} {s : Store H} {f : Frame} {vs us : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStepN host n s f vs es o) :
    BigStepN host n s f (us ++ vs) es ⟨o.store, o.frame, o.result.extend us⟩ := by
  induction h with
  | nil => exact BigStepN.nil _ _ _
  | plain step _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.plain step (by simpa only [← List.append_assoc] using ih)
  | plainTrap step =>
    simp only [← List.append_assoc]
    exact BigStepN.plainTrap step
  | trap => exact BigStepN.trap _ _ _ _
  | block _ ih => exact BigStepN.block ih
  | loop _ ih => exact BigStepN.loop ih
  | ifZero _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.ifZero ih
  | ifNonzero nonzero _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.ifNonzero nonzero ih
  | br => exact BigStepN.br _ _ _ _ _
  | brIfZero _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.brIfZero ih
  | brIfNonzero nonzero _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.brIfNonzero nonzero ih
  | brTable _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.brTable ih
  | return_ => exact BigStepN.return_ _ _ _ _
  | call found _ ih => exact BigStepN.call found ih
  | callIndirect tableFound typeFound element found typeMatch _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.callIndirect tableFound typeFound element found typeMatch ih
  | callIndirectBounds tableFound outOfBounds =>
    simp only [← List.append_assoc]
    exact BigStepN.callIndirectBounds tableFound outOfBounds
  | callIndirectNull tableFound null =>
    simp only [← List.append_assoc]
    exact BigStepN.callIndirectNull tableFound null
  | callIndirectType tableFound typeFound element found typeMismatch =>
    simp only [← List.append_assoc]
    exact BigStepN.callIndirectType tableFound typeFound element found typeMismatch
  | invokeWasm found arity resultArity _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.invokeWasm found arity resultArity ih
  | invokeHost found arity behavior _ ih =>
    simp only [← List.append_assoc]
    exact BigStepN.invokeHost found arity behavior ih
  | labelNormal inner _ _ ih =>
    exact BigStepN.labelNormal inner (by simpa only [← List.append_assoc] using ih)
  | labelBrZero inner target arity _ _ ih =>
    exact BigStepN.labelBrZero inner target arity (by simpa only [← List.append_assoc] using ih)
  | labelBrSucc inner outer _ =>
    simp only [BigResult.extend, ← List.append_assoc]
    exact BigStepN.labelBrSucc inner outer
  | labelRet inner _ =>
    simp only [BigResult.extend, ← List.append_assoc]
    exact BigStepN.labelRet inner
  | labelTrap inner _ =>
    exact BigStepN.labelTrap inner
  | frameNormal inner arity _ _ ih =>
    exact BigStepN.frameNormal inner arity (by simpa only [← List.append_assoc] using ih)
  | frameRet inner arity _ _ ih =>
    exact BigStepN.frameRet inner arity (by simpa only [← List.append_assoc] using ih)
  | frameTrap inner _ =>
    exact BigStepN.frameTrap inner

end Silmaril.Wasm.Logic.V1
