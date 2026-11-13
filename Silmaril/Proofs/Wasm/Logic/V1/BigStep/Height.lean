module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Lemmas

/-!
# A height-indexed big-step semantics: properties

`BigStepN host n` is `BigStep host` restricted to derivations of height at most
`n`. The index is what makes the soundness proof of Wasm Logic go through: both
the `[loop]` rule and the `[module]` rule for mutually recursive functions are
sound only by well-founded recursion on the execution, and a `Prop`-valued
inductive relation carries no such measure.

It is also the natural interface for an executing interpreter, where `n` is
fuel: `BigStepN host n` is decidable-in-principle progress bounded by `n`.

Everything else about the relation is identical to `BigStep`, and
`bigStep_iff_exists_height` says so.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

set_option linter.unusedTactic false in
/-- A derivation of height `n` is a derivation of height `n + 1`: every rule
is stated for an arbitrary height of its premises. -/
private theorem BigStepN.succ {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStepN host n s f vs es o) :
    BigStepN host (n + 1) s f vs es o := by
  induction h with
  | nil => exact .nil ..
  | plain => apply BigStepN.plain; all_goals assumption
  | plainTrap => apply BigStepN.plainTrap; all_goals assumption
  | trap => exact .trap ..
  | block => apply BigStepN.block; all_goals assumption
  | loop => apply BigStepN.loop; all_goals assumption
  | ifZero => apply BigStepN.ifZero; all_goals assumption
  | ifNonzero => apply BigStepN.ifNonzero; all_goals assumption
  | br => exact .br ..
  | brIfZero => apply BigStepN.brIfZero; all_goals assumption
  | brIfNonzero => apply BigStepN.brIfNonzero; all_goals assumption
  | brTable => apply BigStepN.brTable; all_goals assumption
  | return_ => exact .return_ ..
  | call => apply BigStepN.call; all_goals assumption
  | callIndirect => apply BigStepN.callIndirect; all_goals assumption
  | callIndirectBounds => apply BigStepN.callIndirectBounds; all_goals assumption
  | callIndirectNull => apply BigStepN.callIndirectNull; all_goals assumption
  | callIndirectType => apply BigStepN.callIndirectType; all_goals assumption
  | invokeWasm => apply BigStepN.invokeWasm; all_goals assumption
  | invokeHost => apply BigStepN.invokeHost; all_goals assumption
  | labelNormal => apply BigStepN.labelNormal; all_goals assumption
  | labelBrZero => apply BigStepN.labelBrZero; all_goals assumption
  | labelBrSucc => apply BigStepN.labelBrSucc; all_goals assumption
  | labelRet => apply BigStepN.labelRet; all_goals assumption
  | labelTrap => apply BigStepN.labelTrap; all_goals assumption
  | frameNormal => apply BigStepN.frameNormal; all_goals assumption
  | frameRet => apply BigStepN.frameRet; all_goals assumption
  | frameTrap => apply BigStepN.frameTrap; all_goals assumption

/-- A derivation of height `n` is a derivation of any greater height. -/
theorem BigStepN.mono {n m : Nat} (le : n ≤ m) {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStepN host n s f vs es o) :
    BigStepN host m s f vs es o := by
  induction m, le using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih.succ

set_option linter.unusedTactic false in
/-- Forgetting the height recovers the unindexed semantics. -/
theorem BigStepN.toBigStep {n : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o : Outcome H} (h : BigStepN host n s f vs es o) :
    BigStep host s f vs es o := by
  induction h with
  | nil => exact .nil ..
  | plain => apply BigStep.plain; all_goals assumption
  | plainTrap => apply BigStep.plainTrap; all_goals assumption
  | trap => exact .trap ..
  | block => apply BigStep.block; all_goals assumption
  | loop => apply BigStep.loop; all_goals assumption
  | ifZero => apply BigStep.ifZero; all_goals assumption
  | ifNonzero => apply BigStep.ifNonzero; all_goals assumption
  | br => exact .br ..
  | brIfZero => apply BigStep.brIfZero; all_goals assumption
  | brIfNonzero => apply BigStep.brIfNonzero; all_goals assumption
  | brTable => apply BigStep.brTable; all_goals assumption
  | return_ => exact .return_ ..
  | call => apply BigStep.call; all_goals assumption
  | callIndirect => apply BigStep.callIndirect; all_goals assumption
  | callIndirectBounds => apply BigStep.callIndirectBounds; all_goals assumption
  | callIndirectNull => apply BigStep.callIndirectNull; all_goals assumption
  | callIndirectType => apply BigStep.callIndirectType; all_goals assumption
  | invokeWasm => apply BigStep.invokeWasm; all_goals assumption
  | invokeHost => apply BigStep.invokeHost; all_goals assumption
  | labelNormal => apply BigStep.labelNormal; all_goals assumption
  | labelBrZero => apply BigStep.labelBrZero; all_goals assumption
  | labelBrSucc => apply BigStep.labelBrSucc; all_goals assumption
  | labelRet => apply BigStep.labelRet; all_goals assumption
  | labelTrap => apply BigStep.labelTrap; all_goals assumption
  | frameNormal => apply BigStep.frameNormal; all_goals assumption
  | frameRet => apply BigStep.frameRet; all_goals assumption
  | frameTrap => apply BigStep.frameTrap; all_goals assumption

/-- Every derivation has a height: the premises of a two-premise rule are
lifted to their common maximum by `BigStepN.mono`. -/
theorem BigStep.toHeight {s : Store H} {f : Frame} {vs : List Value} {es : List Admin}
    {o : Outcome H} (h : BigStep host s f vs es o) :
    ∃ n, BigStepN host n s f vs es o := by
  induction h with
  | nil => exact ⟨1, .nil ..⟩
  | plain step _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.plain step hn⟩
  | plainTrap step => exact ⟨1, BigStepN.plainTrap step⟩
  | trap => exact ⟨1, .trap ..⟩
  | block _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.block hn⟩
  | loop _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.loop hn⟩
  | ifZero _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.ifZero hn⟩
  | ifNonzero nonzero _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.ifNonzero nonzero hn⟩
  | br => exact ⟨1, .br ..⟩
  | brIfZero _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.brIfZero hn⟩
  | brIfNonzero nonzero _ ih =>
    exact ih.elim fun n hn => ⟨n + 1, BigStepN.brIfNonzero nonzero hn⟩
  | brTable _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.brTable hn⟩
  | return_ => exact ⟨1, .return_ ..⟩
  | call found _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.call found hn⟩
  | callIndirect tableFound typeFound element found typeMatch _ ih =>
    exact ih.elim fun n hn =>
      ⟨n + 1, BigStepN.callIndirect tableFound typeFound element found typeMatch hn⟩
  | callIndirectBounds tableFound outOfBounds =>
    exact ⟨1, BigStepN.callIndirectBounds tableFound outOfBounds⟩
  | callIndirectNull tableFound null => exact ⟨1, BigStepN.callIndirectNull tableFound null⟩
  | callIndirectType tableFound typeFound element found typeMismatch =>
    exact ⟨1, BigStepN.callIndirectType tableFound typeFound element found typeMismatch⟩
  | invokeWasm found arity resultArity _ ih =>
    exact ih.elim fun n hn => ⟨n + 1, BigStepN.invokeWasm found arity resultArity hn⟩
  | invokeHost found arity behavior _ ih =>
    exact ih.elim fun n hn => ⟨n + 1, BigStepN.invokeHost found arity behavior hn⟩
  | labelNormal _ _ ih₁ ih₂ =>
    exact ih₁.elim fun n₁ h₁ => ih₂.elim fun n₂ h₂ => ⟨max n₁ n₂ + 1,
      BigStepN.labelNormal (h₁.mono (Nat.le_max_left _ _)) (h₂.mono (Nat.le_max_right _ _))⟩
  | labelBrZero _ target arity _ ih₁ ih₂ =>
    exact ih₁.elim fun n₁ h₁ => ih₂.elim fun n₂ h₂ => ⟨max n₁ n₂ + 1,
      BigStepN.labelBrZero (h₁.mono (Nat.le_max_left _ _)) target arity
        (h₂.mono (Nat.le_max_right _ _))⟩
  | labelBrSucc _ outer ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.labelBrSucc hn outer⟩
  | labelRet _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.labelRet hn⟩
  | labelTrap _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.labelTrap hn⟩
  | frameNormal _ arity _ ih₁ ih₂ =>
    exact ih₁.elim fun n₁ h₁ => ih₂.elim fun n₂ h₂ => ⟨max n₁ n₂ + 1,
      BigStepN.frameNormal (h₁.mono (Nat.le_max_left _ _)) arity (h₂.mono (Nat.le_max_right _ _))⟩
  | frameRet _ arity _ ih₁ ih₂ =>
    exact ih₁.elim fun n₁ h₁ => ih₂.elim fun n₂ h₂ => ⟨max n₁ n₂ + 1,
      BigStepN.frameRet (h₁.mono (Nat.le_max_left _ _)) arity (h₂.mono (Nat.le_max_right _ _))⟩
  | frameTrap _ ih => exact ih.elim fun n hn => ⟨n + 1, BigStepN.frameTrap hn⟩

theorem bigStep_iff_exists_height {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o : Outcome H} :
    BigStep host s f vs es o ↔ ∃ n, BigStepN host n s f vs es o :=
  ⟨BigStep.toHeight, fun ⟨_, h⟩ => h.toBigStep⟩

/-- Exhausted code returns the operand stack unchanged. -/
theorem BigStepN.nil_inv {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {o : Outcome H}
    (h : BigStepN host n s f vs [] o) : o = ⟨s, f, .normal vs⟩ := by
  cases h
  rfl

end Silmaril.Wasm.Logic.V1
