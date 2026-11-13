module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.BlockSemantics.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ViewTyping.Thms
/-! Actual admitted native instruction lists and the exact old singleton function
agree in both directions. Accepted view construction discharges existing old
well-formedness and call-arity conditions. The existing toLambdaSSA oracle and
entry-frame hypotheses stay explicit at the final view boundary. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.BlockSemantics
open Silmaril.Compile Silmaril.Machine
open Silmaril.Machine.RTL (CallOracle)
open InstructionSemantics ViewTyping Admission
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.RTL (Opcode packValues)
open Silmaril.Machine.Lir (Word)

theorem instruction_iff {instruction : Mir.Instr} {old : Old.Op}
    (admitted : oldOp instruction = some old) (calls : OpenCalls)
    (source : Lir.Frame Nat) (memory : Lir.Memory)
    (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat) :
    old.exec (frame source) oldMemory = some (oldFinal, oldAfter) ↔
      ∃ final, InstructionExec calls instruction source memory final memory ∧
        frame final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory := by
  constructor
  · intro executed
    have mapped : (execute instruction source memory).map
        (fun result => (frame result.1, oldMemory)) = some (oldFinal, oldAfter) :=
      (oldOp_execute instruction old admitted source memory oldMemory).symm.trans executed
    obtain ⟨⟨final, finalMemory⟩, native, projected⟩ := Option.map_eq_some_iff.mp mapped
    have preserved : final.slots = source.slots ∧ finalMemory = memory :=
      execute_preserves admitted source final memory finalMemory native
    have projectedFrame : frame final = oldFinal := congrArg Prod.fst projected
    have unchanged : oldAfter = oldMemory := (congrArg Prod.snd projected).symm
    refine ⟨final, ?_, projectedFrame, preserved.1, unchanged⟩
    exact (instructionExec_iff admitted calls source final memory memory).mpr (preserved.2 ▸ native)
  · rintro ⟨final, native, projectedFrame, _, unchanged⟩
    have executed : execute instruction source memory = some (final, memory) :=
      (instructionExec_iff admitted calls source final memory memory).mp native
    rw [oldOp_execute instruction old admitted source memory oldMemory, executed, unchanged]
    exact congrArg some (congrArg (fun target => (target, oldMemory)) projectedFrame)

theorem ops_cons_inv (oracle : CallOracle) {instruction : Old.Op} {rest : List Old.Op}
    {source final : Silmaril.Machine.RTL.Frame Nat} {memory after : Silmaril.Machine.Lir.Memory}
    (admitted : ArithmeticOp instruction)
    (executed : Silmaril.Machine.RTL.SSA.Ops.Exec oracle (instruction :: rest) source memory final after) :
    ∃ middle middleMemory, instruction.exec source memory = some (middle, middleMemory) ∧
      Silmaril.Machine.RTL.SSA.Ops.Exec oracle rest middle middleMemory final after := by
  cases executed with
  | op primitive tail => exact ⟨_, _, primitive, tail⟩
  | call => cases admitted

/-- Actual admitted instruction lists and actual older operation lists agree
for arbitrary call oracles, native slots/memory and independent old memory. -/
theorem instructions_iff (instructions : List Mir.Instr) (converted : List Old.Op)
    (accepted : instructions.mapM oldOp = some converted) (calls : OpenCalls) (oracle : CallOracle)
    (source : Lir.Frame Nat) (memory : Lir.Memory)
    (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat) :
    Silmaril.Machine.RTL.SSA.Ops.Exec oracle converted (frame source) oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls instructions source memory final memory ∧
        frame final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory := by
  induction instructions generalizing converted source memory oldMemory oldAfter oldFinal with
  | nil =>
    show Silmaril.Machine.RTL.SSA.Ops.Exec oracle converted (frame source) oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls [] source memory final memory ∧
        frame final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory
    have same : converted = [] := Option.some.inj accepted.symm
    subst converted
    constructor
    · intro executed
      cases executed
      exact ⟨source, .nil, rfl, rfl, rfl⟩
    · rintro ⟨final, native, projected, _, unchanged⟩
      cases native
      rw [← projected, unchanged]
      exact .nil
  | cons instruction rest ih =>
    show Silmaril.Machine.RTL.SSA.Ops.Exec oracle converted (frame source) oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls (instruction :: rest) source memory final memory ∧
        frame final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory
    obtain ⟨head, tail, headAccepted, tailAccepted, same⟩ := oldOps_cons accepted
    subst converted
    constructor
    · show Silmaril.Machine.RTL.SSA.Ops.Exec oracle (head :: tail) (frame source) oldMemory oldFinal oldAfter →
        ∃ final, InstructionsExec calls (instruction :: rest) source memory final memory ∧
          frame final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory
      intro executed
      obtain ⟨oldMiddle, oldMiddleMemory, oldStep, oldTail⟩ :=
        ops_cons_inv oracle (oldOp_admitted headAccepted) executed
      obtain ⟨middle, nativeStep, projectedMiddle, middleSlots, oldUnchanged⟩ :=
        (instruction_iff headAccepted calls source memory oldMemory oldMiddleMemory oldMiddle).mp oldStep
      have projectedTail : Silmaril.Machine.RTL.SSA.Ops.Exec oracle tail (frame middle)
          oldMiddleMemory oldFinal oldAfter := by rw [projectedMiddle]; exact oldTail
      obtain ⟨final, nativeTail, projectedFinal, finalSlots, unchanged⟩ :=
        (ih tail tailAccepted middle memory oldMiddleMemory oldAfter oldFinal).mp projectedTail
      exact ⟨final, .cons nativeStep nativeTail, projectedFinal,
        finalSlots.trans middleSlots, unchanged.trans oldUnchanged⟩
    · show (∃ final, InstructionsExec calls (instruction :: rest) source memory final memory ∧
        frame final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory) →
        Silmaril.Machine.RTL.SSA.Ops.Exec oracle (head :: tail) (frame source) oldMemory oldFinal oldAfter
      rintro ⟨final, native, projectedFinal, finalSlots, unchanged⟩
      cases native with
      | @cons _ _ _ _ middle middleMemory _ _ nativeStep nativeTail =>
        show Silmaril.Machine.RTL.SSA.Ops.Exec oracle (head :: tail) (frame source) oldMemory oldFinal oldAfter
        have primitive : execute instruction source memory = some (middle, middleMemory) :=
          (instructionExec_iff headAccepted calls source middle memory middleMemory).mp nativeStep
        have preserved : middle.slots = source.slots ∧ middleMemory = memory :=
          execute_preserves headAccepted source middle memory middleMemory primitive
        have step : head.exec (frame source) oldMemory = some (frame middle, oldMemory) :=
          (instruction_iff headAccepted calls source memory oldMemory oldMemory (frame middle)).mpr
            ⟨middle, preserved.2 ▸ nativeStep, rfl, preserved.1, rfl⟩
        have rest : Silmaril.Machine.RTL.SSA.Ops.Exec oracle tail (frame middle) oldMemory oldFinal oldAfter :=
          (ih tail tailAccepted middle memory oldMemory oldAfter oldFinal).mpr
            ⟨final, preserved.2 ▸ nativeTail, projectedFinal, finalSlots.trans preserved.1.symm, unchanged⟩
        exact .op step rest

theorem frame_readAll (source : Lir.Frame Nat) (registers : List Nat) :
    (frame source).readAll registers = source.readAll (registers.map Lir.Loc.reg) := by
  simp only [Silmaril.Machine.RTL.Frame.readAll, Lir.Frame.readAll, List.mapM_map]
  rfl

theorem singleFunction_exec_iff (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat)
    (oracle : CallOracle) (source : Silmaril.Machine.RTL.Frame Nat) (memory : Silmaril.Machine.Lir.Memory)
    (out : Silmaril.Machine.RTL.SSA.Exit) :
    Silmaril.Machine.RTL.SSA.Func.Exec oracle (singleFunction inputs instructions outputs) 0 source memory out ↔
      ∃ final after values, Silmaril.Machine.RTL.SSA.Ops.Exec oracle instructions source memory final after ∧
        final.readAll outputs = some values ∧ out = .returned values after := by
  constructor
  · intro executed
    cases executed with
    | jump found _ term => cases found; cases term
    | cond found _ term => cases found; cases term
    | ret found operations term returned =>
      cases found
      cases term
      exact ⟨_, _, _, operations, returned, rfl⟩
    | trap found _ term => cases found; cases term
  · rintro ⟨final, after, values, operations, returned, rfl⟩
    exact .ret rfl operations rfl returned

/-- The actual singleton function returns precisely the actual native boundary
registers after its admitted instruction list, preserving native slots/memory. -/
theorem function_native_iff (inputs outputs : List Nat) (instructions : List Mir.Instr)
    (converted : List Old.Op) (accepted : instructions.mapM oldOp = some converted)
    (calls : OpenCalls) (oracle : CallOracle) (source : Lir.Frame Nat) (memory : Lir.Memory)
    (oldMemory : Silmaril.Machine.Lir.Memory) (out : Silmaril.Machine.RTL.SSA.Exit) :
    Silmaril.Machine.RTL.SSA.Func.Exec oracle (singleFunction inputs converted outputs) 0
      (frame source) oldMemory out ↔
      ∃ final values, InstructionsExec calls instructions source memory final memory ∧
        final.slots = source.slots ∧ final.readAll (outputs.map Lir.Loc.reg) = some values ∧
        out = .returned values oldMemory := by
  constructor
  · intro executed
    obtain ⟨oldFinal, oldAfter, values, operations, read, output⟩ :=
      (singleFunction_exec_iff inputs converted outputs oracle (frame source) oldMemory out).mp executed
    obtain ⟨final, native, projected, slots, unchanged⟩ :=
      (instructions_iff instructions converted accepted calls oracle source memory oldMemory oldAfter oldFinal).mp operations
    have readNative : final.readAll (outputs.map Lir.Loc.reg) = some values := by
      rw [← frame_readAll, projected]
      exact read
    exact ⟨final, values, native, slots, readNative, output.trans (congrArg (Silmaril.Machine.RTL.SSA.Exit.returned values) unchanged)⟩
  · rintro ⟨final, values, native, slots, read, rfl⟩
    have operations : Silmaril.Machine.RTL.SSA.Ops.Exec oracle converted (frame source) oldMemory (frame final) oldMemory :=
      (instructions_iff instructions converted accepted calls oracle source memory oldMemory oldMemory (frame final)).mpr
        ⟨final, native, rfl, slots, rfl⟩
    exact .ret rfl operations rfl ((frame_readAll final outputs).trans read)

theorem singleFunction_okUse (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat)
    (index register : Nat)
    (available : ((entryScope inputs).afterOps (instructions.take index)).HasReg register) :
    (singleFunction inputs instructions outputs).okUse 0 index register = true := by
  obtain original | ⟨instruction, member, defined⟩ := Silmaril.Machine.RTL.SSA.Scope.hasReg_afterOps.mp available
  · have member : register ∈ inputs := by
      obtain ⟨tuple, tupleMember, member⟩ := original
      obtain rfl := List.mem_singleton.mp tupleMember
      exact member
    simp [Silmaril.Machine.RTL.SSA.Func.okUse, singleFunction, Silmaril.Machine.RTL.SSA.Func.block?, member]
  · have emitted : (instructions.take index).any (fun instruction => decide (register ∈ instruction.defs)) = true :=
      List.any_eq_true.mpr ⟨instruction, member, by simpa using defined⟩
    simp [Silmaril.Machine.RTL.SSA.Func.okUse, singleFunction, Silmaril.Machine.RTL.SSA.Func.block?, emitted]

theorem singleFunction_instructionDominated (inputs : List Nat) (instructions : List Old.Op)
    (outputs : List Nat) (prefixes : PrefixCovers (entryScope inputs) instructions)
    {index : Nat} {instruction : Old.Op} (found : instructions[index]? = some instruction) :
    instruction.uses.all ((singleFunction inputs instructions outputs).okUse 0 index) = true := by
  apply List.all_eq_true.mpr
  intro register used
  have split : instructions = instructions.take index ++ instruction :: instructions.drop (index + 1) := by
    obtain ⟨bounded, same⟩ : ∃ bounded : index < instructions.length,
        instructions[index]'bounded = instruction := List.getElem?_eq_some_iff.mp found
    rw [← same, ← List.drop_eq_getElem_cons bounded]
    exact (List.take_append_drop index instructions).symm
  exact singleFunction_okUse inputs instructions outputs index register
    (prefixCovers_at prefixes _ instruction _ split register used)

theorem singleFunction_usesDominated (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat)
    (prefixes : PrefixCovers (entryScope inputs) instructions)
    (returned : ((entryScope inputs).afterOps instructions).Covers outputs) :
    (singleFunction inputs instructions outputs).UsesDominated := by
  simp only [Silmaril.Machine.RTL.SSA.Func.UsesDominated, Silmaril.Machine.RTL.SSA.Func.usesDominated,
    singleFunction, List.length_cons, List.length_nil, Nat.zero_add, List.range_one, List.all_cons, List.all_nil,
    Bool.and_true, Silmaril.Machine.RTL.SSA.Func.block?, List.getElem?_cons_zero, Silmaril.Machine.RTL.SSA.Term.uses]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro index member
    cases found : instructions[index]? with
    | none => rfl
    | some instruction =>
      simpa only [singleFunction] using singleFunction_instructionDominated inputs instructions outputs prefixes found
  · apply List.all_eq_true.mpr
    intro register member
    apply singleFunction_okUse
    simpa only [List.take_length] using returned register member

theorem singleFunction_wellFormed (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat)
    (unique : (inputs ++ instructions.flatMap Silmaril.Machine.RTL.SSA.Op.defs).Nodup)
    (prefixes : PrefixCovers (entryScope inputs) instructions)
    (returned : ((entryScope inputs).afterOps instructions).Covers outputs) :
    (singleFunction inputs instructions outputs).WellFormed := by
  refine ⟨?_, ?_, singleFunction_usesDominated inputs instructions outputs prefixes returned, ?_⟩
  · simp [Silmaril.Machine.RTL.SSA.Func.WellFormedSig, singleFunction,
      Silmaril.Machine.RTL.SSA.Func.block?, Silmaril.Machine.RTL.SSA.Term.okIn, Silmaril.Machine.RTL.SSA.Term.successors]
  · simpa only [Silmaril.Machine.RTL.SSA.Func.SingleAssignment, Silmaril.Machine.RTL.SSA.Func.allDefs,
      singleFunction, List.flatMap_cons, List.flatMap_nil, List.append_nil, Silmaril.Machine.RTL.SSA.Block.defs]
      using unique
  · rfl

theorem oldOps_defs (instructions : List Mir.Instr) (converted : List Old.Op)
    (accepted : instructions.mapM oldOp = some converted) :
    converted.flatMap Silmaril.Machine.RTL.SSA.Op.defs = instructions.flatMap defs := by
  induction instructions generalizing converted with
  | nil => cases accepted; rfl
  | cons instruction rest ih =>
    obtain ⟨head, tail, headAccepted, tailAccepted, same⟩ := oldOps_cons accepted
    rw [same, List.flatMap_cons, List.flatMap_cons, oldOp_defs headAccepted, ih tail tailAccepted]

theorem singleFunction_callsMatch (inputs : List Nat) (instructions : List Old.Op) (outputs : List Nat)
    (admitted : ∀ instruction ∈ instructions, ArithmeticOp instruction) :
    (singleFunction inputs instructions outputs).CallsMatch [] := by
  simp only [Silmaril.Machine.RTL.SSA.Func.CallsMatch, Silmaril.Machine.RTL.SSA.Func.callsMatch,
    singleFunction, List.all_cons, List.all_nil, Bool.and_true]
  apply List.all_eq_true.mpr
  intro instruction member
  cases instruction <;> first | rfl | exact False.elim (admitted _ member)

/-- Actual enter/name admission discharges the actual old function's existing
well-formedness, including use dominance rather than only destination uniqueness. -/
theorem enter_function_wellFormed (base : Nat) (source : Mir.Block) (converted : List Old.Op)
    (unique : (enter base source).isSSA = true)
    (accepted : (enter base source).body.instrs.toList.mapM oldOp = some converted) :
    (singleFunction (enter base source).inputs converted ((enter base source).outputs.map Prod.snd)).WellFormed := by
  have actualUnique : ((enter base source).inputs ++
      (enter base source).body.instrs.toList.flatMap defs).Nodup := of_decide_eq_true unique
  have convertedUnique : ((enter base source).inputs ++
      converted.flatMap Silmaril.Machine.RTL.SSA.Op.defs).Nodup := by
    rw [oldOps_defs _ _ accepted]
    exact actualUnique
  obtain ⟨prefixes, returned⟩ := enter_scoped base source converted accepted
  exact singleFunction_wellFormed _ _ _ convertedUnique prefixes returned

/-- Successful actual view construction exposes its exact converted instruction
list, checked SSA names and existing singleton function. -/
theorem view_function {base : Nat} {block : Mir.Block} {result : View}
    (accepted : view base block = some result) :
    ∃ converted, (enter base block).isSSA = true ∧
      (enter base block).body.instrs.toList.mapM oldOp = some converted ∧
      result.inputs = (enter base block).inputs ∧
      result.outputs = (enter base block).outputs.map Prod.fst ∧
      result.region = Silmaril.Machine.RTL.SSA.toLambdaSSA []
        (singleFunction (enter base block).inputs converted ((enter base block).outputs.map Prod.snd)) := by
  unfold view at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i unique
    cases converted : (enter base block).body.instrs.toList.mapM oldOp with
    | none => simp [converted] at accepted
    | some instructions =>
      simp only [converted, bind, pure] at accepted
      obtain rfl := Option.some.inj accepted
      refine ⟨instructions, ?_, rfl, rfl, rfl, rfl⟩
      simpa using unique

/-- Existing toLambdaSSA finite evaluation, specialized to the actual
call-free singleton, cannot produce a trapped exit. The global signature
condition is retained exactly as required by the existing translation theorem. -/
theorem singleFunction_eval_iff (inputs outputs : List Nat) (instructions : List Old.Op)
    (wellFormed : (singleFunction inputs instructions outputs).WellFormed)
    (admitted : ∀ instruction ∈ instructions, ArithmeticOp instruction)
    (oracle : CallOracle) (signatures : Silmaril.Machine.RTL.SSA.CallOracle.MatchesSigs oracle [])
    (args : List Word) (source : Silmaril.Machine.RTL.Frame Nat)
    (initial : Silmaril.Machine.RTL.Frame.empty.writeAll inputs args = some source)
    (env : Semantics.Env Word) (input : env 0 = packValues args)
    (before after : Silmaril.Machine.Lir.Memory) (label : Nat) (value : Value Word) :
    Semantics.Region.Eval (Opcode.step oracle) env
      (Silmaril.Machine.RTL.SSA.toLambdaSSA [] (singleFunction inputs instructions outputs))
      before label value after ↔
      label = 0 ∧ ∃ values, value = packValues values ∧
        Silmaril.Machine.RTL.SSA.Func.Exec oracle (singleFunction inputs instructions outputs)
          0 source before (.returned values after) := by
  have translated : Semantics.Region.Eval (Opcode.step oracle) env
      (Silmaril.Machine.RTL.SSA.toLambdaSSA [] (singleFunction inputs instructions outputs))
        before label value after ↔
      (label = 0 ∧ ∃ values, value = packValues values ∧
        Silmaril.Machine.RTL.SSA.Func.Exec oracle (singleFunction inputs instructions outputs)
          0 source before (.returned values after)) ∨
      (label = 1 ∧ value = .unit ∧
        Silmaril.Machine.RTL.SSA.Func.Exec oracle (singleFunction inputs instructions outputs)
          0 source before (.trapped after)) :=
    Silmaril.Machine.RTL.SSA.toLambdaSSA_eval_iff wellFormed signatures
    (singleFunction_callsMatch inputs instructions outputs admitted) (by rfl) initial input
      (m := before) (m' := after) (label := label) (value := value)
  constructor
  · intro evaluated
    obtain returned | trapped := translated.mp evaluated
    · exact returned
    · obtain ⟨_, _, executed⟩ := trapped
      obtain ⟨_, _, _, _, _, impossible⟩ :=
        (singleFunction_exec_iff inputs instructions outputs oracle source before (.trapped after)).mp executed
      cases impossible
  · intro returned
    exact translated.mpr (.inl returned)

/-- The actual accepted native arithmetic view agrees with actual execution of
its entered instruction list and boundary register reads. Native memory and
slots and the independent older RTL memory are preserved. This theorem retains
an explicit actual empty.writeAll entry frame and the existing global oracle
signature side condition; it does not assume successful source execution. -/
theorem view_native_eval_iff {base : Nat} {block : Mir.Block} {result : View}
    (accepted : view base block = some result)
    (calls : OpenCalls) (oracle : CallOracle)
    (signatures : Silmaril.Machine.RTL.SSA.CallOracle.MatchesSigs oracle [])
    (source : Lir.Frame Nat) (memory : Lir.Memory) (args : List Word)
    (initial : Silmaril.Machine.RTL.Frame.empty.writeAll result.inputs args = some (frame source))
    (env : Semantics.Env Word) (input : env 0 = packValues args)
    (before after : Silmaril.Machine.Lir.Memory) (label : Nat) (value : Value Word) :
    Semantics.Region.Eval (Opcode.step oracle) env result.region before label value after ↔
      label = 0 ∧ ∃ final values,
        InstructionsExec calls (enter base block).body.instrs.toList source memory final memory ∧
        final.slots = source.slots ∧
        final.readAll (((enter base block).outputs.map Prod.snd).map Lir.Loc.reg) = some values ∧
        value = packValues values ∧ after = before := by
  obtain ⟨converted, unique, convertedActual, inputs, _, region⟩ := view_function accepted
  rw [region]
  have enteredInitial : Silmaril.Machine.RTL.Frame.empty.writeAll (enter base block).inputs args =
      some (frame source) := by rw [← inputs]; exact initial
  rw [singleFunction_eval_iff _ _ _ (enter_function_wellFormed base block converted unique convertedActual)
    (oldOps_admitted convertedActual) oracle signatures args (frame source) enteredInitial env input]
  constructor
  · rintro ⟨returned, values, packed, executed⟩
    obtain ⟨final, actualValues, native, slots, read, same⟩ :=
      (function_native_iff _ _ _ converted convertedActual calls oracle source memory before
        (.returned values after)).mp executed
    obtain ⟨rfl, unchanged⟩ := Silmaril.Machine.RTL.SSA.Exit.returned.inj same
    exact ⟨returned, final, values, native, slots, read, packed, unchanged⟩
  · rintro ⟨returned, final, values, native, slots, read, packed, unchanged⟩
    refine ⟨returned, values, packed, ?_⟩
    apply (function_native_iff _ _ _ converted convertedActual calls oracle source memory before
      (.returned values after)).mpr
    exact ⟨final, values, native, slots, read,
      congrArg (Silmaril.Machine.RTL.SSA.Exit.returned values) unchanged⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.BlockSemantics
