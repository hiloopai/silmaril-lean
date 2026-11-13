module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.BlockSemantics.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion
open Silmaril.Machine.RTL (Frame CallOracle)
open Silmaril.Machine.RTL.SSA (Scope)
open Silmaril.Machine.Lir (Word Memory)
open ViewTyping Admission
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem writeAll_completeFrom (source initial : Frame Nat) (inputs : List Nat) :
    initial.writeAll inputs (arguments source inputs) = some (completeFrom source initial inputs) := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons register rest ih => exact ih _

theorem completeFrom_get (source initial : Frame Nat) (inputs : List Nat) (register : Nat) :
    (completeFrom source initial inputs).get register =
      if register ∈ inputs then some ((source.get register).getD 0) else initial.get register := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons first rest ih =>
    simp only [completeFrom, ih, Frame.get_set, List.mem_cons]
    by_cases member : register ∈ rest <;> by_cases same : register = first <;> simp [member, same]

theorem complete_defined (source : Frame Nat) (inputs : List Nat) :
    DefinedAgreement (entryScope inputs) source (complete source inputs) := by
  intro register available word defined
  have member : register ∈ inputs := by
    obtain ⟨group, groupMember, member⟩ := available
    obtain rfl := List.mem_singleton.mp groupMember
    exact member
  simp [complete, completeFrom_get, member, defined]

theorem set_defined {scope : Scope Nat} {source target : Frame Nat}
    (agreed : DefinedAgreement scope source target) (destination : Nat) (word : Word) :
    DefinedAgreement (scope.push [destination]) (source.set destination word) (target.set destination word) := by
  intro register available value defined
  by_cases same : register = destination
  · simpa [Frame.get_set, same] using defined
  · have old : scope.HasReg register := by
      obtain fresh | old := Scope.hasReg_push.mp available
      · exact False.elim (same (List.mem_singleton.mp fresh))
      · exact old
    have before : source.get register = some value := by simpa [Frame.get_set, same] using defined
    simpa [Frame.get_set, same] using agreed register old value before

/-- Forward simulation uses only successful source reads; it does not reflect
failure after missing source inputs are completed. -/
theorem operation_defined {scope : Scope Nat} {source target final : Frame Nat}
    {memory after : Memory} {operation : Old.Op}
    (admitted : ArithmeticOp operation) (covered : scope.Covers operation.uses)
    (agreed : DefinedAgreement scope source target)
    (executed : operation.exec source memory = some (final, after)) :
    after = memory ∧ ∃ result, operation.exec target memory = some (result, memory) ∧
      DefinedAgreement (scope.push operation.defs) final result := by
  cases operation with
  | const destination word =>
    cases executed
    exact ⟨rfl, _, rfl, set_defined agreed destination word⟩
  | move destination operand =>
    show after = memory ∧ ∃ result,
      (Silmaril.Machine.RTL.SSA.Op.move destination operand).exec target memory = some (result, memory) ∧
      DefinedAgreement (scope.push [destination]) final result
    obtain ⟨word, read, output⟩ : ∃ word, source.get operand = some word ∧
        (source.set destination word = final ∧ memory = after) := by
      simpa only [Silmaril.Machine.RTL.SSA.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    have copied : target.get operand = some word :=
      agreed operand (covered operand (by simp [Silmaril.Machine.RTL.SSA.Op.uses])) word read
    refine ⟨output.2.symm, target.set destination word, ?_, ?_⟩
    · simp [Silmaril.Machine.RTL.SSA.Op.exec, copied]
    · rw [← output.1]
      exact set_defined agreed destination word
  | unary opcode destination operand =>
    show after = memory ∧ ∃ result,
      (Silmaril.Machine.RTL.SSA.Op.unary opcode destination operand).exec target memory = some (result, memory) ∧
      DefinedAgreement (scope.push [destination]) final result
    obtain ⟨word, read, output⟩ : ∃ word, source.get operand = some word ∧
        (source.set destination (opcode.eval word) = final ∧ memory = after) := by
      simpa only [Silmaril.Machine.RTL.SSA.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    have copied : target.get operand = some word :=
      agreed operand (covered operand (by simp [Silmaril.Machine.RTL.SSA.Op.uses])) word read
    refine ⟨output.2.symm, target.set destination (opcode.eval word), ?_, ?_⟩
    · simp [Silmaril.Machine.RTL.SSA.Op.exec, copied]
    · rw [← output.1]
      exact set_defined agreed destination (opcode.eval word)
  | binary opcode destination left right =>
    show after = memory ∧ ∃ result,
      (Silmaril.Machine.RTL.SSA.Op.binary opcode destination left right).exec target memory = some (result, memory) ∧
      DefinedAgreement (scope.push [destination]) final result
    obtain ⟨x, leftRead, y, rightRead, word, computed, output⟩ :
        ∃ x, source.get left = some x ∧ ∃ y, source.get right = some y ∧
          ∃ word, opcode.eval x y = some word ∧ (source.set destination word = final ∧ memory = after) := by
      simpa only [Silmaril.Machine.RTL.SSA.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq] using executed
    have copiedLeft : target.get left = some x :=
      agreed left (covered left (by simp [Silmaril.Machine.RTL.SSA.Op.uses])) x leftRead
    have copiedRight : target.get right = some y :=
      agreed right (covered right (by simp [Silmaril.Machine.RTL.SSA.Op.uses])) y rightRead
    refine ⟨output.2.symm, target.set destination word, ?_, ?_⟩
    · simp [Silmaril.Machine.RTL.SSA.Op.exec, copiedLeft, copiedRight, computed]
    · rw [← output.1]
      exact set_defined agreed destination word
  | load | store | call => cases admitted

/-- Actual call-free old operation lists preserve defined reads while the
actual translation scope grows through their real destination groups. -/
theorem operations_defined (oracle : CallOracle) (operations : List Old.Op)
    (admitted : ∀ operation ∈ operations, ArithmeticOp operation)
    {scope : Scope Nat} (covered : PrefixCovers scope operations)
    {source target final : Frame Nat} {memory after : Memory}
    (agreed : DefinedAgreement scope source target)
    (executed : Silmaril.Machine.RTL.SSA.Ops.Exec oracle operations source memory final after) :
    after = memory ∧ ∃ result,
      Silmaril.Machine.RTL.SSA.Ops.Exec oracle operations target memory result memory ∧
      DefinedAgreement (scope.afterOps operations) final result := by
  induction operations generalizing scope source target final memory after with
  | nil =>
    cases executed
    exact ⟨rfl, target, .nil, agreed⟩
  | cons operation rest ih =>
    obtain ⟨middle, middleMemory, first, tail⟩ :=
      BlockSemantics.ops_cons_inv oracle (admitted operation (by simp)) executed
    obtain ⟨firstMemory, targetMiddle, targetFirst, middleAgreed⟩ :=
      operation_defined (admitted operation (by simp)) covered.1 agreed first
    subst middleMemory
    obtain ⟨lastMemory, result, targetTail, lastAgreed⟩ :=
      ih (fun operation member => admitted operation (by simp [member])) covered.2 middleAgreed tail
    exact ⟨lastMemory, result, .op targetFirst targetTail, lastAgreed⟩

theorem readAll_defined {scope : Scope Nat} {source target : Frame Nat}
    (agreed : DefinedAgreement scope source target) (registers : List Nat)
    (covered : scope.Covers registers) (values : List Word)
    (read : source.readAll registers = some values) : target.readAll registers = some values := by
  induction registers generalizing values with
  | nil => exact read
  | cons register rest ih =>
    cases first : source.get register with
    | none => simp [Frame.readAll, List.mapM_cons, first] at read
    | some word =>
      have copied := agreed register (covered register (by simp)) word first
      cases tail : source.readAll rest with
      | none =>
        change rest.mapM source.get = none at tail
        simp [Frame.readAll, List.mapM_cons, first, tail] at read
      | some words =>
        have tailEquation : rest.mapM source.get = some words := tail
        have actual : values = word :: words := by
          simpa [Frame.readAll, List.mapM_cons, first, tailEquation] using read.symm
        subst values
        have restCopied := ih (fun register member => covered register (by simp [member])) words tail
        change rest.mapM target.get = some words at restCopied
        simp [Frame.readAll, List.mapM_cons, copied, restCopied]

theorem native_instructions_preserve (instructions : List Silmaril.Compile.Mir.Instr)
    (converted : List Old.Op) (accepted : instructions.mapM oldOp = some converted)
    (calls : OpenCalls) {source final : Silmaril.Machine.Lir.Frame Nat}
    {memory after : Silmaril.Machine.Lir.Memory}
    (executed : InstructionsExec calls instructions source memory final after) :
    final.slots = source.slots ∧ after = memory := by
  induction instructions generalizing converted source final memory after with
  | nil => cases executed; exact ⟨rfl, rfl⟩
  | cons instruction rest ih =>
    obtain ⟨head, tail, headAccepted, tailAccepted, same⟩ := oldOps_cons accepted
    cases executed with
    | cons first remaining =>
      have primitive := (InstructionSemantics.instructionExec_iff headAccepted calls _ _ _ _).mp first
      have preserved := InstructionSemantics.execute_preserves headAccepted _ _ _ _ primitive
      have later := ih tail tailAccepted remaining
      exact ⟨later.1.trans preserved.1, later.2.trans preserved.2⟩

/-- An actual successful entered native view can be evaluated using an actual
empty.writeAll input frame, without requiring its arbitrary incoming frame to
have exactly that shape. Missing inputs are concretely completed with zero;
only successful defined reads and final output reads are preserved. -/
theorem view_completed_eval {base : Nat} {block : Silmaril.Compile.Mir.Block} {result : View}
    (accepted : view base block = some result)
    (calls : OpenCalls) (oracle : CallOracle)
    (signatures : Silmaril.Machine.RTL.SSA.CallOracle.MatchesSigs oracle [])
    (source final : Silmaril.Machine.Lir.Frame Nat) (memory : Silmaril.Machine.Lir.Memory)
    (executed : InstructionsExec calls (enter base block).body.instrs.toList source memory final memory)
    (values : List Word)
    (read : final.readAll (((enter base block).outputs.map Prod.snd).map Silmaril.Machine.Lir.Loc.reg) = some values)
    (environment : Silmaril.Isotope.LambdaSSA.Semantics.Env Word)
    (input : environment 0 = Silmaril.Machine.RTL.packValues
      (arguments (InstructionSemantics.frame source) result.inputs))
    (before : Memory) :
    Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval (Silmaril.Machine.RTL.Opcode.step oracle)
      environment result.region before 0 (Silmaril.Machine.RTL.packValues values) before := by
  obtain ⟨converted, unique, conversion, inputs, _, region⟩ := BlockSemantics.view_function accepted
  have unchanged := native_instructions_preserve _ converted conversion calls executed
  have original := (BlockSemantics.instructions_iff _ converted conversion calls oracle source memory
    before before (InstructionSemantics.frame final)).mpr ⟨final, executed, rfl, unchanged.1, rfl⟩
  obtain ⟨prefixes, returned⟩ := enter_scoped base block converted conversion
  obtain ⟨_, completedFinal, completedExecution, agreed⟩ := operations_defined oracle converted
    (oldOps_admitted conversion) prefixes
    (complete_defined (InstructionSemantics.frame source) (enter base block).inputs) original
  have originalRead : (InstructionSemantics.frame final).readAll ((enter base block).outputs.map Prod.snd) =
      some values := (BlockSemantics.frame_readAll _ _).trans read
  have completedRead := readAll_defined agreed _ returned values originalRead
  have initial : Frame.empty.writeAll (enter base block).inputs
      (arguments (InstructionSemantics.frame source) (enter base block).inputs) =
      some (complete (InstructionSemantics.frame source) (enter base block).inputs) :=
    writeAll_completeFrom _ _ _
  have actualInput : environment 0 = Silmaril.Machine.RTL.packValues
      (arguments (InstructionSemantics.frame source) (enter base block).inputs) := by
    rw [← inputs]
    exact input
  rw [region]
  apply (BlockSemantics.singleFunction_eval_iff _ _ _
    (BlockSemantics.enter_function_wellFormed base block converted unique conversion)
    (oldOps_admitted conversion) oracle signatures _ _ initial environment actualInput before before
      0 (Silmaril.Machine.RTL.packValues values)).mpr
  exact ⟨rfl, values, rfl, .ret rfl completedExecution rfl completedRead⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.EntryCompletion
