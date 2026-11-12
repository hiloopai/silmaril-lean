module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission.Defs
/-! An accepted actual native lambda-SSA view has the arithmetic instruction
syntax required by the separate folding theorem. This does not establish
operand scope, shape, SSA well-formedness or actual semantic refinement. -/
@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.RTL (Opcode)
open Silmaril.Machine.RTL.SSA (Scope)
open Folding

theorem proj_pure (index : Nat) {term : Old.Tm} (pure : term.ForallInstr ArithmeticOpcode) :
    (Silmaril.Machine.RTL.SSA.proj index term).ForallInstr ArithmeticOpcode := by
  induction index generalizing term with
  | zero => exact ⟨pure, trivial⟩
  | succ index ih => exact ⟨pure, ih trivial⟩

theorem ref_pure (scope : Scope Nat) (register : Nat) :
    (scope.ref (Φ := Old.Opcode) register).ForallInstr ArithmeticOpcode := by
  unfold Scope.ref
  split
  · exact proj_pure _ trivial
  · trivial

theorem pack_pure (scope : Scope Nat) (registers : List Nat) :
    (scope.pack (Φ := Old.Opcode) registers).ForallInstr ArithmeticOpcode := by
  induction registers with
  | nil => trivial
  | cons register rest ih => exact ⟨ref_pure scope register, ih⟩

theorem op_toTm_pure (scope : Scope Nat) {instruction : Old.Op} (admitted : ArithmeticOp instruction) :
    (instruction.toTm [] scope).ForallInstr ArithmeticOpcode := by
  cases instruction with
  | const => exact ⟨trivial, trivial⟩
  | move | unary => exact ⟨trivial, pack_pure scope _⟩
  | binary => exact ⟨admitted, pack_pure scope _⟩
  | load | store | call => cases admitted

theorem term_toRegion_pure (function : Old.Func) (scope : Scope Nat)
    {terminator : Silmaril.Machine.RTL.SSA.Term Nat} (admitted : NoTestTerm terminator) :
    (terminator.toRegion [] function scope).ForallInstr ArithmeticOpcode := by
  cases terminator with
  | jump | ret => exact pack_pure scope _
  | trap => trivial
  | cond => cases admitted

theorem opsRegion_pure (scope : Scope Nat) (instructions : List Old.Op)
    (admitted : ∀ instruction ∈ instructions, ArithmeticOp instruction)
    {continuation : Old.Region} (pure : continuation.ForallInstr ArithmeticOpcode) :
    (Silmaril.Machine.RTL.SSA.opsRegion [] scope instructions continuation).ForallInstr ArithmeticOpcode := by
  induction instructions generalizing scope with
  | nil => exact pure
  | cons instruction rest ih =>
    exact ⟨op_toTm_pure scope (admitted instruction (List.mem_cons_self)),
      ih _ (fun instruction member => admitted instruction (List.mem_cons_of_mem _ member))⟩

theorem blockRegion_pure (function : Old.Func)
    (admitted : ∀ block ∈ function.blocks,
      (∀ instruction ∈ block.ops, ArithmeticOp instruction) ∧ NoTestTerm block.term)
    (fuel : Nat) (scope : Scope Nat) (label : Nat) :
    (Silmaril.Machine.RTL.SSA.blockRegion [] fuel function scope label).ForallInstr ArithmeticOpcode := by
  induction fuel generalizing scope label with
  | zero => trivial
  | succ fuel ih =>
    unfold Silmaril.Machine.RTL.SSA.blockRegion
    split
    · trivial
    · rename_i block found
      have member : block ∈ function.blocks := List.mem_of_getElem? found
      apply opsRegion_pure _ _ (admitted block member).1
      exact ⟨term_toRegion_pure function _ (admitted block member).2, fun _ => ih _ _⟩

theorem toLambdaSSA_pure (function : Old.Func)
    (admitted : ∀ block ∈ function.blocks,
      (∀ instruction ∈ block.ops, ArithmeticOp instruction) ∧ NoTestTerm block.term) :
    (Silmaril.Machine.RTL.SSA.toLambdaSSA [] function).ForallInstr ArithmeticOpcode :=
  ⟨trivial, fun _ => blockRegion_pure function admitted _ _ _⟩

theorem oldOp_admitted {instruction : Silmaril.Compile.Mir.Instr} {converted : Old.Op}
    (accepted : oldOp instruction = some converted) : ArithmeticOp converted := by
  cases instruction with
  | op operation =>
    cases operation with
    | const | move | unary => cases accepted; trivial
    | binary opcode destination left right =>
      cases opcode <;> simp only [oldOp, oldBinary, Option.map_none, Option.map_some,
        Option.some.injEq, reduceCtorEq] at accepted
      all_goals cases accepted; rfl
    | load | store | slotGet | slotSet => cases accepted
  | fop | addr | call | callIndirect => cases accepted

theorem oldOps_admitted {instructions : List Silmaril.Compile.Mir.Instr} {converted : List Old.Op}
    (accepted : instructions.mapM oldOp = some converted) :
    ∀ instruction ∈ converted, ArithmeticOp instruction := by
  induction instructions generalizing converted with
  | nil =>
    cases accepted
    intro instruction member
    cases member
  | cons instruction rest ih =>
    cases head : oldOp instruction with
    | none => simp [List.mapM_cons, head] at accepted
    | some convertedHead =>
      cases tail : rest.mapM oldOp with
      | none => simp [List.mapM_cons, head, tail] at accepted
      | some convertedTail =>
        have same : convertedHead :: convertedTail = converted := by
          simpa [List.mapM_cons, head, tail] using accepted
        rw [← same]
        intro candidate member
        obtain rfl | member := List.mem_cons.mp member
        · exact oldOp_admitted head
        · exact ih tail candidate member

/-- An accepted actual view always uses the admitted pure total arithmetic
syntax, independently of SSA operand-scope or shape admission. -/
theorem view_pure {base : Nat} {source : Silmaril.Compile.Mir.Block} {result : View}
    (accepted : view base source = some result) : result.region.ForallInstr ArithmeticOpcode := by
  unfold view at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · cases converted : (enter base source).body.instrs.toList.mapM oldOp with
    | none => simp [converted] at accepted
    | some instructions =>
      simp only [converted, bind, pure] at accepted
      obtain rfl := Option.some.inj accepted
      apply toLambdaSSA_pure
      intro block member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨oldOps_admitted converted, trivial⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.Admission
