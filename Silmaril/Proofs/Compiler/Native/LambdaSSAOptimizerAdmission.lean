module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.OptimizerAdmission.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission.Thms
/-! Successful actual selection derives source and candidate validator
admission through real stateful renaming, adapter conversions and restore. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.OptimizerAdmission
open Silmaril.Compile Silmaril.Machine

theorem oldOp_admitted {instruction : Mir.Instr} {operation : Old.Op}
    (accepted : oldOp instruction = some operation) : Validation.Lists.AdmittedInstr instruction := by
  cases instruction with
  | op primitive =>
    cases primitive with
    | const | move | unary => trivial
    | binary opcode destination left right =>
      cases opcode <;> simp only [oldOp, oldBinary, Option.map_none, Option.map_some,
        Option.some.injEq, reduceCtorEq] at accepted
      all_goals rfl
    | load | store | slotGet | slotSet => cases accepted
  | fop | addr | call | callIndirect => cases accepted

theorem newOp_admitted (register : Nat → Nat) {operation : Old.Op} {instruction : Mir.Instr}
    (accepted : newOp register operation = some instruction) : Validation.Lists.AdmittedInstr instruction := by
  cases operation with
  | const | move | unary => cases accepted; trivial
  | binary opcode destination left right =>
    cases opcode <;> simp only [newOp, newBinary, Option.map_none, Option.map_some,
      Option.some.injEq, reduceCtorEq] at accepted
    all_goals cases accepted; rfl
  | load | store | call => cases accepted

theorem admitted_cons (head : Mir.Instr) (tail : List Mir.Instr) :
    Validation.Lists.Admitted (head :: tail) ↔
      Validation.Lists.AdmittedInstr head ∧ Validation.Lists.Admitted tail := by
  simp [Validation.Lists.Admitted]

theorem oldOps_admitted {instructions : List Mir.Instr} {operations : List Old.Op}
    (accepted : instructions.mapM oldOp = some operations) : Validation.Lists.Admitted instructions := by
  induction instructions generalizing operations with
  | nil => intro instruction member; cases member
  | cons instruction rest ih =>
    show Validation.Lists.Admitted (instruction :: rest)
    rw [List.mapM_cons] at accepted
    obtain ⟨operation, head, tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨converted, convertedRest, _⟩ := Option.bind_eq_some_iff.mp tail
    exact (admitted_cons instruction rest).mpr ⟨oldOp_admitted head, ih convertedRest⟩

theorem newOps_admitted (register : Nat → Nat) {operations : List Old.Op} {instructions : List Mir.Instr}
    (accepted : operations.mapM (newOp register) = some instructions) : Validation.Lists.Admitted instructions := by
  induction operations generalizing instructions with
  | nil => cases accepted; intro instruction member; cases member
  | cons operation rest ih =>
    show Validation.Lists.Admitted instructions
    rw [List.mapM_cons] at accepted
    obtain ⟨instruction, head, tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨converted, convertedRest, same⟩ := Option.bind_eq_some_iff.mp tail
    have shape : instruction :: converted = instructions := Option.some.inj same
    rw [← shape, admitted_cons]
    exact ⟨newOp_admitted register head, ih convertedRest⟩

theorem renameOp_admitted_iff (state : Rename) (operation : Lir.Op Nat) :
    Validation.Roots.Admitted ((renameOp operation).run state).1 ↔ Validation.Roots.Admitted operation := by
  cases operation <;> rfl

theorem renameInstr_admitted_iff (state : Rename) (instruction : Mir.Instr) :
    Validation.Lists.AdmittedInstr ((renameInstr instruction).run state).1 ↔
      Validation.Lists.AdmittedInstr instruction := by
  cases instruction with
  | op operation => exact renameOp_admitted_iff state operation
  | fop | addr | call | callIndirect => rfl

theorem renameList_admitted_iff (state : Rename) (instructions : List Mir.Instr) :
    Validation.Lists.Admitted ((instructions.mapM renameInstr).run state).1 ↔
      Validation.Lists.Admitted instructions := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [renameInstrs_cons]
    change Validation.Lists.Admitted (((renameInstr instruction).run state).1 ::
      ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).1) ↔
        Validation.Lists.Admitted (instruction :: rest)
    rw [admitted_cons, admitted_cons, renameInstr_admitted_iff, ih]

theorem enter_admitted_iff (base : Nat) (source : Mir.Block) :
    Validation.Lists.Admitted (enter base source).body.instrs.toList ↔
      Validation.Lists.Admitted source.instrs.toList := by
  simpa only [enter, renameArray_run, List.toList_toArray] using
    renameList_admitted_iff ({next := base} : Rename) source.instrs.toList

theorem view_source_admitted {base : Nat} {source : Mir.Block} {result : View}
    (accepted : view base source = some result) : Validation.Lists.Admitted source.instrs.toList := by
  unfold view at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨operations, converted, _⟩ := Option.bind_eq_some_iff.mp accepted
    exact (enter_admitted_iff base source).mp (oldOps_admitted converted)

theorem commits_admitted (versions : List (Nat × Nat)) : Validation.Lists.Admitted (commitInstrs versions) := by
  intro instruction member
  obtain ⟨pair, _, same⟩ := List.mem_map.mp member
  subst instruction
  trivial

theorem restore_candidate_admitted {base : Nat} {source candidate : Mir.Block} {result : View} {region : Old.Region}
    (accepted : restore base source result region = some candidate) : Validation.Lists.Admitted candidate.instrs.toList := by
  obtain ⟨function, body, values, instructions, _, _, _, _, _, _, converted, shape⟩ := RestoreAdmission.restore_witness accepted
  rw [shape, List.toList_toArray]
  intro instruction member
  rcases List.mem_append.mp member with native | commit
  · exact newOps_admitted (RestoreAdmission.register base result.inputs) converted instruction native
  · obtain ⟨pair, _, same⟩ := List.mem_map.mp commit
    subst instruction
    trivial

/-- Actual optimizer selection supplies both admission predicates from actual
view renaming and successful old/new adapters, without semantic premises. -/
theorem optimize_admitted {base : Nat} {source candidate : Mir.Block} {count : Nat}
    (accepted : optimize? base source = some (candidate, count)) :
    Validation.Lists.Admitted source.instrs.toList ∧ Validation.Lists.Admitted candidate.instrs.toList ∧
      Validation.check base source candidate = true := by
  obtain ⟨result, viewed, restored, _, _, checked, _⟩ := RestoreAdmission.optimize_witness accepted
  exact ⟨view_source_admitted viewed, restore_candidate_admitted restored, checked⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.OptimizerAdmission
