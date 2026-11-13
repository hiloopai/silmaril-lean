module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.InstructionSemantics.Thms
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.RestoreAdmission.Thms
/-! Actual reverse-adapter primitive and list execution, retaining partial
reads under arbitrary injective register maps. Actual restore supplies a
concrete emitted body witness; output commits remain a separate obligation. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics
open Silmaril.Compile Silmaril.Machine
open InstructionSemantics

theorem pullback_get (register : Nat → Nat) (source : Lir.Frame Nat) (index : Nat) :
    (pullback register source).get index = source.get (register index) := rfl

theorem pullback_set (register : Nat → Nat) (injective : Function.Injective register)
    (source : Lir.Frame Nat) (index : Nat) (value : Lir.Word) :
    pullback register (source.set (register index) value) = (pullback register source).set index value := by
  simp only [pullback, Silmaril.Machine.RTL.Frame.set, Lir.Frame.get, Lir.Frame.set]
  congr 1
  funext other
  simp only [injective.eq_iff]

theorem newUnary_eval (operation : Old.Unop) (word : Lir.Word) :
    (newUnary operation).eval word = operation.eval word := by
  cases operation <;> rfl

theorem newBinary_oldBinary (operation : Old.Binop) (native : Lir.Binop)
    (accepted : newBinary operation = some native) : oldBinary native = some operation := by
  cases operation <;> cases accepted <;> rfl

/-- The actual reverse adapter under an arbitrary injective map preserves the
complete partial primitive result under a concrete register pullback frame. -/
theorem newOp_execute (register : Nat → Nat) (injective : Function.Injective register)
    (old : Old.Op) (instruction : Mir.Instr) (accepted : newOp register old = some instruction)
    (source : Lir.Frame Nat) (memory : Lir.Memory) (oldMemory : Silmaril.Machine.Lir.Memory) :
    old.exec (pullback register source) oldMemory =
      (execute instruction source memory).map (fun result => (pullback register result.1, oldMemory)) := by
  cases old with
  | const destination value =>
    cases accepted
    simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, Option.map_some,
      pullback_set register injective]
  | move destination operand =>
    cases accepted
    simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, pullback_get]
    cases source.get (register operand) <;>
      simp only [Option.map_none, Option.map_some, pullback_set register injective]
  | unary operation destination operand =>
    cases accepted
    simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, pullback_get, newUnary_eval]
    cases source.get (register operand) <;>
      simp only [Option.map_none, Option.map_some, pullback_set register injective]
  | binary operation destination left right =>
    show (Silmaril.Machine.RTL.SSA.Op.binary operation destination left right).exec
        (pullback register source) oldMemory =
      (execute instruction source memory).map (fun result => (pullback register result.1, oldMemory))
    have selected : (newBinary operation).map
        (fun native => Mir.Instr.op (.binary native (register destination) (register left) (register right))) =
        some instruction := accepted
    obtain ⟨native, converted, same⟩ := Option.map_eq_some_iff.mp selected
    cases same
    simp only [execute, Lir.Op.exec, Silmaril.Machine.RTL.SSA.Op.exec, pullback_get,
      oldBinary_eval native operation (newBinary_oldBinary operation native converted), Option.map_bind,
      Option.map_map, Function.comp_def, pullback_set register injective]
  | _ => cases accepted

theorem newOp_native_admitted {register : Nat → Nat} {old : Old.Op} {instruction : Mir.Instr}
    (accepted : newOp register old = some instruction) : ∃ converted, oldOp instruction = some converted := by
  cases old with
  | const destination value => cases accepted; exact ⟨_, rfl⟩
  | move destination operand => cases accepted; exact ⟨_, rfl⟩
  | unary operation destination operand => cases accepted; exact ⟨_, rfl⟩
  | binary operation destination left right =>
    obtain ⟨native, converted, same⟩ := Option.map_eq_some_iff.mp accepted
    cases same
    exact ⟨.binary operation (register destination) (register left) (register right),
      by simp only [oldOp, newBinary_oldBinary operation native converted, Option.map_some]⟩
  | _ => cases accepted

theorem newOp_arithmetic {register : Nat → Nat} {old : Old.Op} {instruction : Mir.Instr}
    (accepted : newOp register old = some instruction) : Admission.ArithmeticOp old := by
  cases old with
  | const | move | unary => trivial
  | binary operation destination left right =>
    obtain ⟨native, converted, _⟩ := Option.map_eq_some_iff.mp accepted
    simp only [Admission.ArithmeticOp, converted, Option.isSome_some]
  | _ => cases accepted

theorem instruction_iff {register : Nat → Nat} (injective : Function.Injective register)
    {old : Old.Op} {instruction : Mir.Instr} (accepted : newOp register old = some instruction)
    (calls : OpenCalls) (source : Lir.Frame Nat) (memory : Lir.Memory)
    (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat) :
    old.exec (pullback register source) oldMemory = some (oldFinal, oldAfter) ↔
      ∃ final, InstructionExec calls instruction source memory final memory ∧
        pullback register final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory := by
  obtain ⟨nativeOld, admitted⟩ := newOp_native_admitted accepted
  constructor
  · intro executed
    have mapped : (execute instruction source memory).map
        (fun result => (pullback register result.1, oldMemory)) = some (oldFinal, oldAfter) :=
      (newOp_execute register injective old instruction accepted source memory oldMemory).symm.trans executed
    obtain ⟨⟨final, finalMemory⟩, native, projected⟩ := Option.map_eq_some_iff.mp mapped
    have preserved : final.slots = source.slots ∧ finalMemory = memory :=
      execute_preserves admitted source final memory finalMemory native
    have projectedFrame : pullback register final = oldFinal := congrArg Prod.fst projected
    have unchanged : oldAfter = oldMemory := (congrArg Prod.snd projected).symm
    exact ⟨final, (instructionExec_iff admitted calls source final memory memory).mpr (preserved.2 ▸ native),
      projectedFrame, preserved.1, unchanged⟩
  · rintro ⟨final, native, projectedFrame, _, unchanged⟩
    have executed : execute instruction source memory = some (final, memory) :=
      (instructionExec_iff admitted calls source final memory memory).mp native
    rw [newOp_execute register injective old instruction accepted source memory oldMemory, executed, unchanged]
    exact congrArg some (congrArg (fun target => (target, oldMemory)) projectedFrame)

theorem newOps_cons {register : Nat → Nat} {old : Old.Op} {rest : List Old.Op} {instructions : List Mir.Instr}
    (accepted : (old :: rest).mapM (newOp register) = some instructions) :
    ∃ first tail, newOp register old = some first ∧ rest.mapM (newOp register) = some tail ∧
      instructions = first :: tail := by
  have sequenced : (newOp register old).bind (fun first => (rest.mapM (newOp register)).bind
      (fun tail => some (first :: tail))) = some instructions := by
    simpa [List.mapM_cons] using accepted
  obtain ⟨first, firstAccepted, restAccepted⟩ := Option.bind_eq_some_iff.mp sequenced
  obtain ⟨tail, tailAccepted, same⟩ := Option.bind_eq_some_iff.mp restAccepted
  exact ⟨first, tail, firstAccepted, tailAccepted, (Option.some.inj same).symm⟩

/-- Actual whole reverse-adapted lists agree with actual old operation-list
execution under an injective register pullback, with partial reads retained. -/
theorem instructions_iff (register : Nat → Nat) (injective : Function.Injective register)
    (operations : List Old.Op) (instructions : List Mir.Instr)
    (accepted : operations.mapM (newOp register) = some instructions)
    (calls : OpenCalls) (oracle : Silmaril.Machine.RTL.CallOracle)
    (source : Lir.Frame Nat) (memory : Lir.Memory)
    (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat) :
    Silmaril.Machine.RTL.SSA.Ops.Exec oracle operations (pullback register source) oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls instructions source memory final memory ∧
        pullback register final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory := by
  induction operations generalizing instructions source memory oldMemory oldAfter oldFinal with
  | nil =>
    show Silmaril.Machine.RTL.SSA.Ops.Exec oracle [] (pullback register source) oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls instructions source memory final memory ∧
        pullback register final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory
    have same : instructions = [] := Option.some.inj accepted.symm
    rw [same]
    constructor
    · intro executed
      cases executed
      exact ⟨source, .nil, rfl, rfl, rfl⟩
    · rintro ⟨final, native, projected, _, unchanged⟩
      cases native
      rw [← projected, unchanged]
      exact .nil
  | cons old rest ih =>
    show Silmaril.Machine.RTL.SSA.Ops.Exec oracle (old :: rest) (pullback register source) oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls instructions source memory final memory ∧
        pullback register final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory
    obtain ⟨first, tail, firstAccepted, tailAccepted, same⟩ := newOps_cons accepted
    rw [same]
    constructor
    · show Silmaril.Machine.RTL.SSA.Ops.Exec oracle (old :: rest) (pullback register source) oldMemory oldFinal oldAfter →
        ∃ final, InstructionsExec calls (first :: tail) source memory final memory ∧
          pullback register final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory
      intro executed
      obtain ⟨oldMiddle, oldMiddleMemory, oldStep, oldTail⟩ :=
        BlockSemantics.ops_cons_inv oracle (newOp_arithmetic firstAccepted) executed
      obtain ⟨middle, nativeStep, projectedMiddle, middleSlots, oldUnchanged⟩ :=
        (instruction_iff injective firstAccepted calls source memory oldMemory oldMiddleMemory oldMiddle).mp oldStep
      have projectedTail : Silmaril.Machine.RTL.SSA.Ops.Exec oracle rest (pullback register middle)
          oldMiddleMemory oldFinal oldAfter := by rw [projectedMiddle]; exact oldTail
      obtain ⟨final, nativeTail, projectedFinal, finalSlots, unchanged⟩ :=
        (ih tail tailAccepted middle memory oldMiddleMemory oldAfter oldFinal).mp projectedTail
      exact ⟨final, .cons nativeStep nativeTail, projectedFinal,
        finalSlots.trans middleSlots, unchanged.trans oldUnchanged⟩
    · show (∃ final, InstructionsExec calls (first :: tail) source memory final memory ∧
        pullback register final = oldFinal ∧ final.slots = source.slots ∧ oldAfter = oldMemory) →
        Silmaril.Machine.RTL.SSA.Ops.Exec oracle (old :: rest) (pullback register source) oldMemory oldFinal oldAfter
      rintro ⟨final, native, projectedFinal, finalSlots, unchanged⟩
      cases native with
      | @cons _ _ _ _ middle middleMemory _ _ nativeStep nativeTail =>
        show Silmaril.Machine.RTL.SSA.Ops.Exec oracle (old :: rest) (pullback register source) oldMemory oldFinal oldAfter
        obtain ⟨nativeOld, admitted⟩ := newOp_native_admitted firstAccepted
        have primitive : execute first source memory = some (middle, middleMemory) :=
          (instructionExec_iff admitted calls source middle memory middleMemory).mp nativeStep
        have preserved : middle.slots = source.slots ∧ middleMemory = memory :=
          execute_preserves admitted source middle memory middleMemory primitive
        have step : old.exec (pullback register source) oldMemory = some (pullback register middle, oldMemory) :=
          (instruction_iff injective firstAccepted calls source memory oldMemory oldMemory (pullback register middle)).mpr
            ⟨middle, preserved.2 ▸ nativeStep, rfl, preserved.1, rfl⟩
        have rest : Silmaril.Machine.RTL.SSA.Ops.Exec oracle rest (pullback register middle) oldMemory oldFinal oldAfter :=
          (ih tail tailAccepted middle memory oldMemory oldAfter oldFinal).mpr
            ⟨final, preserved.2 ▸ nativeTail, projectedFinal, finalSlots.trans preserved.1.symm, unchanged⟩
        exact .op step rest

/-- The concrete map selected by a real function/block view satisfies the
injectivity needed by actual reverse-adapted instruction-list execution. -/
theorem view_instructions_iff {function : Mir.Func} {block : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (viewAccepted : view (freshBase function) block = some result)
    (operations : List Old.Op) (instructions : List Mir.Instr)
    (accepted : operations.mapM (newOp (RestoreAdmission.register (freshBase function) result.inputs)) =
      some instructions)
    (calls : OpenCalls) (oracle : Silmaril.Machine.RTL.CallOracle)
    (source : Lir.Frame Nat) (memory : Lir.Memory)
    (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat) :
    Silmaril.Machine.RTL.SSA.Ops.Exec oracle operations
        (pullback (RestoreAdmission.register (freshBase function) result.inputs) source)
        oldMemory oldFinal oldAfter ↔
      ∃ final, InstructionsExec calls instructions source memory final memory ∧
        pullback (RestoreAdmission.register (freshBase function) result.inputs) final = oldFinal ∧
        final.slots = source.slots ∧ oldAfter = oldMemory :=
  instructions_iff _ (RestoreAdmission.view_register_injective member viewAccepted)
    operations instructions accepted calls oracle source memory oldMemory oldAfter oldFinal

/-- Successful actual restore supplies the actual flattened body to which the
reverse-adapter execution theorem applies. Boundary commits are exposed as the
real emitted list; their execution is a separate obligation. -/
theorem restored_body_execution {function : Mir.Func} {block candidate : Mir.Block}
    (member : block ∈ function.blocks.toList) {result : View}
    (viewAccepted : view (freshBase function) block = some result) {region : Old.Region}
    (restored : restore (freshBase function) block result region = some candidate) :
    ∃ flattened body values instructions,
      Silmaril.Machine.RTL.SSA.ofLambdaSSA? [] region result.annotation
        result.inputs.length result.outputs.length = some flattened ∧
      flattened.entry = 0 ∧ flattened.blocks = [body] ∧
      body.params = List.range result.inputs.length ∧ body.term = .ret values ∧
      values.length = result.outputs.length ∧
      body.ops.mapM (newOp (RestoreAdmission.register (freshBase function) result.inputs)) = some instructions ∧
      candidate = ⟨(instructions ++ (result.outputs.zip values).map (fun (original, value) =>
        Mir.Instr.op (.move original (RestoreAdmission.register (freshBase function) result.inputs value)))).toArray,
        block.term⟩ ∧
      ∀ (calls : OpenCalls) (oracle : Silmaril.Machine.RTL.CallOracle)
        (source : Lir.Frame Nat) (memory : Lir.Memory)
        (oldMemory oldAfter : Silmaril.Machine.Lir.Memory) (oldFinal : Silmaril.Machine.RTL.Frame Nat),
        Silmaril.Machine.RTL.SSA.Ops.Exec oracle body.ops
            (pullback (RestoreAdmission.register (freshBase function) result.inputs) source)
            oldMemory oldFinal oldAfter ↔
          ∃ final, InstructionsExec calls instructions source memory final memory ∧
            pullback (RestoreAdmission.register (freshBase function) result.inputs) final = oldFinal ∧
            final.slots = source.slots ∧ oldAfter = oldMemory := by
  obtain ⟨flattened, body, values, instructions, compiled, entry, singleton, parameters,
    terminator, width, converted, emitted⟩ := RestoreAdmission.restore_witness restored
  refine ⟨flattened, body, values, instructions, compiled, entry, singleton, parameters,
    terminator, width, converted, emitted, ?_⟩
  intro calls oracle source memory oldMemory oldAfter oldFinal
  exact view_instructions_iff member viewAccepted body.ops instructions converted
    calls oracle source memory oldMemory oldAfter oldFinal

end Silmaril.Compiler.Native.Optimize.LambdaSSA.RenamingSemantics
