module

public import Silmaril.Compiler.Native.Emit.Scalar.Defs
public import Silmaril.Compiler.Native.Emit.Prologue.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.Scalar
open Silmaril Silmaril.X86
open Silmaril.Process (Memory)
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

theorem render_equivalent (operation : Operation) : Asm.operation operation.lir = .ok operation.render := by
  cases operation <;> rfl

private theorem load_length (register : Register) (target : Reg) (choice : target = .rax ∨ target = .r10) :
    (Ext.Instr.load .q target (Prologue.slot register.index)).length = 4 := by
  have all : ∀ register : Register,
      (Ext.Instr.load .q .rax (Prologue.slot register.index)).length = 4 ∧
      (Ext.Instr.load .q .r10 (Prologue.slot register.index)).length = 4 := by decide +kernel
  rcases choice with rfl | rfl
  · exact (all register).1
  · exact (all register).2

private theorem store_length (register : Register) :
    (Ext.Instr.mov .q (.mem (Prologue.slot register.index)) .rax).length = 4 := by
  have all : ∀ register : Register,
      (Ext.Instr.mov .q (.mem (Prologue.slot register.index)) .rax).length = 4 := by decide +kernel
  exact all register

private theorem slot_address (stack : Word) (state : X86.State) (register : Register) (next : Word)
    (base : state.read .rbp = stack - 8) :
    (Prologue.slot register.index).addr state next = address stack register := by
  have all : ∀ register : Register,
      (-(BitVec.ofNat 32 (8 * (register.index + 1)))).signExtend 64 =
        -(BitVec.ofNat 64 (8 * (register.index + 1))) := by decide +kernel
  simp only [Prologue.slot, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Base.value_reg,
    base, Option.map_none, Option.getD_none, all register]
  change stack - 8 + (0 : Word) + -(BitVec.ofNat 64 (8 * (register.index + 1))) = _
  rw [add_zero, ← sub_eq_add_neg, sub_sub]
  unfold address
  congr 1
  change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * (register.index + 1)) = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

private theorem address_nat (stack : Word) (lower : 96 ≤ stack.toNat) (register : Register) :
    (address stack register).toNat = stack.toNat - 8 * (register.index + 2) := by
  apply Ext.toNat_sub_ofNat
  · have bound := register.isLt
    unfold Register.index
    omega
  · have bound := register.isLt
    unfold Register.index
    omega

private theorem Entry.permitted {stack : Word} {before : X86.MState} (entry : Entry stack before)
    (register : Register) (access : Process.Access) (choice : access = .read ∨ access = .write) :
    before.memory.Permitted access (address stack register).toNat 8 := by
  rw [address_nat stack entry.lower]
  have bound := register.isLt
  unfold Register.index
  rcases choice with rfl | rfl
  · exact Ext.Memory.Permitted.sub entry.readable (by decide) (by omega) (by omega)
  · exact Ext.Memory.Permitted.sub entry.writable (by decide) (by omega) (by omega)

private theorem Entry.store_frame {stack : Word} {before : X86.MState} (entry : Entry stack before)
    {after : Memory} (destination : Register) (value : Word)
    (stored : Ext.Stored before.memory after (address stack destination).toNat (Ext.leBytes value 8)) :
    before.memory.WritesWithin after (footprint stack) := by
  apply stored.writesWithin
  intro offset bound
  rw [Ext.length_leBytes] at bound
  rw [address_nat stack entry.lower]
  have minimum := entry.lower
  have registerBound := destination.isLt
  unfold footprint Register.index
  omega

private theorem slots_disjoint (stack : Word) (lower : 96 ≤ stack.toNat)
    (first last : Register) (different : first ≠ last) :
    (address stack first).toNat + 8 ≤ (address stack last).toNat ∨
      (address stack last).toNat + 8 ≤ (address stack first).toNat := by
  have distinct : first.val ≠ last.val := fun same => different (Fin.ext same)
  have firstBound := first.isLt
  have lastBound := last.isLt
  rw [address_nat stack lower, address_nat stack lower]
  unfold Register.index
  omega

private theorem represented_store {stack : Word} {before : X86.MState} (entry : Entry stack before)
    {frame : Silmaril.Machine.Lir.Frame Nat} (represented : Represents stack before.memory frame)
    (destination : Register) (value : Word) {after : Memory}
    (stored : Ext.Stored before.memory after (address stack destination).toNat (Ext.leBytes value 8)) :
    Represents stack after (frame.set destination.index value) := by
  intro register oldValue found
  by_cases same : register = destination
  · show Ext.HoldsLE after (address stack register).toNat 8 oldValue
    subst register
    have equal : value = oldValue := by
      simpa only [Silmaril.Machine.Lir.Frame.get_set, ↓reduceIte, Option.some.injEq] using found
    subst oldValue
    exact Ext.HoldsLE.of_stored_self stored (entry.permitted destination .read (.inl rfl))
  · show Ext.HoldsLE after (address stack register).toNat 8 oldValue
    have different : register.index ≠ destination.index := by
      intro equal
      apply same
      apply Fin.ext
      unfold Register.index at equal
      omega
    have original : frame.get register.index = some oldValue := by
      simpa only [Silmaril.Machine.Lir.Frame.get_set, different, ↓reduceIte] using found
    apply Ext.HoldsLE.of_stored_disjoint stored (represented register oldValue original)
    rw [Ext.length_leBytes]
    exact slots_disjoint stack entry.lower register destination same

private theorem store_represents {stack : Word} {before : X86.MState} (entry : Entry stack before)
    {frame : Silmaril.Machine.Lir.Frame Nat} (represented : Represents stack before.memory frame)
    (destination : Register) (value : Word) :
    ∃ after, Ext.storeN before.memory (address stack destination) 8 value = some after ∧
      before.memory.WritesWithin after (footprint stack) ∧
      Represents stack after (frame.set destination.index value) := by
  obtain ⟨after, written, stored⟩ := Ext.storeN_isSome (v := value) (entry.permitted destination .write (.inr rfl))
  exact ⟨after, written, entry.store_frame destination value stored, represented_store entry represented destination value stored⟩

private theorem exec_load_generic (target : Ext.Mem) (register : Reg) (state : X86.State)
    (memory : Memory) (value : Word) (length : (Ext.Instr.load .q register target).length = 4)
    (held : Ext.HoldsLE memory (target.addr state (state.rip + 4)).toNat 8 value) :
    Ext.exec (.load .q register target) state memory =
      .ok {state.write register value with rip := state.rip + 4} memory := by
  have loaded := Ext.loadN_of_holdsLE_eight held
  simp only [Ext.exec, length, Ext.readRM, Ext.retire]
  change (match ((Ext.loadN memory (target.addr state (state.rip + 4)) 8).map (fun v => v)).map
      (fun v => (state.write register v, memory)) with
    | some (next, mem) => Ext.Result.ok {next with rip := state.rip + 4} mem
    | none => Ext.Result.dataFault) = _
  rw [loaded]
  rfl

private theorem exec_load (stack : Word) (state : X86.State) (memory : Memory)
    (source : Register) (target : Reg) (value : Word) (choice : target = .rax ∨ target = .r10)
    (base : state.read .rbp = stack - 8) (held : Ext.HoldsLE memory (address stack source).toNat 8 value) :
    Ext.exec (.load .q target (Prologue.slot source.index)) state memory =
      .ok {state.write target value with rip := state.rip + 4} memory :=
  exec_load_generic _ _ _ _ _ (load_length source target choice) (by rw [slot_address stack state source _ base]; exact held)

private theorem exec_store_generic (target : Ext.Mem) (state : X86.State) {memory after : Memory}
    (length : (Ext.Instr.mov .q (.mem target) .rax).length = 4)
    (written : Ext.storeN memory (target.addr state (state.rip + 4)) 8 (state.read .rax) = some after) :
    Ext.exec (.mov .q (.mem target) .rax) state memory = .ok {state with rip := state.rip + 4} after := by
  simp only [Ext.exec, length, Ext.writeRM, Ext.Sz.read_q, Ext.retire]
  change (match (Ext.storeN memory (target.addr state (state.rip + 4)) 8 (state.read .rax)).map
    (fun after => (state, after)) with
    | some (next, mem) => Ext.Result.ok {next with rip := state.rip + 4} mem
    | none => Ext.Result.dataFault) = _
  rw [written]
  rfl

private theorem exec_constant (state : X86.State) (memory : Memory) (value : Word) :
    Ext.exec (.movabs .rax value) state memory =
      .ok {state.write .rax value with rip := state.rip + 10} memory := by
  simp only [Ext.exec, Ext.retire]
  rfl

private theorem exec_sext32 (state : X86.State) (memory : Memory) :
    Ext.exec (.movsxd .rax (.reg .rax)) state memory =
      .ok {state.write .rax (Silmaril.Machine.Lir.Unop.sext32.eval (state.read .rax)) with rip := state.rip + 3} memory := by
  simp only [Ext.exec, Ext.readRM, Ext.Sz.read, Ext.retire]
  rfl

private theorem exec_add (state : X86.State) (memory : Memory) :
    Ext.exec (.alu .q .add (.reg .rax) .r10) state memory =
      .ok {state.write .rax (state.read .rax + state.read .r10) with
        flags := Ext.AluOp.flagsN .add (state.read .rax) (state.read .r10), rip := state.rip + 3} memory := by
  simp only [Ext.exec, Ext.aluStep, Ext.readRM, Ext.writeRM, Ext.Sz.read_q,
    Ext.AluOp.resultN, Ext.retire]
  rfl

private theorem write_result (stack : Word) (before : X86.MState)
    (frame : Silmaril.Machine.Lir.Frame Nat) (entry : Entry stack before)
    (represented : Represents stack before.memory frame) (destination : Register) (value : Word)
    (earlier : List Ext.Instr) (bytes : Nat) (prepared : X86.State)
    (executed : Prologue.Executes earlier before ⟨prepared, before.memory⟩)
    (pc : prepared.rip = before.core.rip + BitVec.ofNat 64 bytes)
    (registers : ∀ register, register ≠ .rax → register ≠ .r10 → prepared.read register = before.core.read register)
    (fsBase : prepared.fsBase = before.core.fsBase) (accumulator : prepared.read .rax = value) :
    ∃ after, Prologue.Executes (earlier ++ [.mov .q (.mem (Prologue.slot destination.index)) .rax]) before after ∧
      Result stack before after (frame.set destination.index value) (bytes + 4) ∧ after.core.read .rax = value := by
  obtain ⟨memory, written, framed, representedAfter⟩ := store_represents entry represented destination value
  have base : prepared.read .rbp = stack - 8 := (registers .rbp (by decide) (by decide)).trans entry.base
  have store : Ext.exec (.mov .q (.mem (Prologue.slot destination.index)) .rax) prepared before.memory =
      .ok {prepared with rip := prepared.rip + 4} memory :=
    exec_store_generic _ prepared (store_length destination) (by
      rw [slot_address stack prepared destination _ base, accumulator]
      exact written)
  let after : X86.MState := ⟨{prepared with rip := prepared.rip + 4}, memory⟩
  refine ⟨after, executed.append (.cons _ [] ⟨prepared, before.memory⟩ after after store (.nil _)), ?_, accumulator⟩
  refine ⟨?_, registers, fsBase, framed, representedAfter⟩
  change prepared.rip + 4 = before.core.rip + BitVec.ofNat 64 (bytes + 4)
  rw [pc, BitVec.ofNat_add, add_assoc]
  rfl

/-- Pure scalar input reads and independent stack permissions derive actual
instruction execution and an updated physical-slot representation. -/
theorem operation (stack : Word) (before : X86.MState) (frame : Silmaril.Machine.Lir.Frame Nat)
    (selected : Operation) (value : Word) (entry : Entry stack before)
    (represented : Represents stack before.memory frame) (evaluated : selected.value frame = some value) :
    ∃ after, Prologue.Executes selected.instructions before after ∧
      Result stack before after (frame.set selected.destination.index value) selected.bytes ∧
      after.core.read .rax = value := by
  cases selected with
  | constant destination literal =>
    show ∃ after, Prologue.Executes (Operation.constant destination literal).instructions before after ∧
      Result stack before after (frame.set destination.index value) (Operation.constant destination literal).bytes ∧
      after.core.read .rax = value
    have same : literal = value := Option.some.inj evaluated
    subst value
    let prepared := {before.core.write .rax literal with rip := before.core.rip + 10}
    have executed : Prologue.Executes [.movabs .rax literal] before ⟨prepared, before.memory⟩ :=
      .cons _ [] before ⟨prepared, before.memory⟩ _ (exec_constant _ _ _) (.nil _)
    exact write_result stack before frame entry represented destination literal _ 10 prepared executed rfl
      (by intro register notAx notTen; simp [prepared, State.read, State.write, Silmaril.Machine.RegisterFile.write, notAx])
      rfl (by simp [prepared, State.read, State.write, Silmaril.Machine.RegisterFile.write])
  | sext32 destination source =>
    show ∃ after, Prologue.Executes (Operation.sext32 destination source).instructions before after ∧
      Result stack before after (frame.set destination.index value) (Operation.sext32 destination source).bytes ∧
      after.core.read .rax = value
    obtain ⟨input, found, same⟩ := Option.map_eq_some_iff.mp evaluated
    subst value
    let one := {before.core.write .rax input with rip := before.core.rip + 4}
    let prepared := {one.write .rax (Silmaril.Machine.Lir.Unop.sext32.eval input) with rip := one.rip + 3}
    have first : Ext.exec (.load .q .rax (Prologue.slot source.index)) before.core before.memory =
        .ok one before.memory :=
      exec_load stack before.core before.memory source .rax input (.inl rfl) entry.base (represented source input found)
    have second : Ext.exec (.movsxd .rax (.reg .rax)) one before.memory = .ok prepared before.memory := by
      have actual := exec_sext32 one before.memory
      simpa [one, prepared, State.read, State.write, Silmaril.Machine.RegisterFile.write] using actual
    have executed : Prologue.Executes [.load .q .rax (Prologue.slot source.index), .movsxd .rax (.reg .rax)]
        before ⟨prepared, before.memory⟩ :=
      .cons _ _ before ⟨one, before.memory⟩ _ first (.cons _ [] ⟨one, before.memory⟩ _ _ second (.nil _))
    exact write_result stack before frame entry represented destination _ _ 7 prepared executed
      (by change before.core.rip + 4 + 3 = before.core.rip + 7; rw [add_assoc]; rfl)
      (by intro register notAx notTen; simp [prepared, one, State.read, State.write, Silmaril.Machine.RegisterFile.write, notAx])
      rfl (by simp [prepared, State.read, State.write, Silmaril.Machine.RegisterFile.write])
  | add destination left right =>
    show ∃ after, Prologue.Executes (Operation.add destination left right).instructions before after ∧
      Result stack before after (frame.set destination.index value) (Operation.add destination left right).bytes ∧
      after.core.read .rax = value
    obtain ⟨x, readLeft, rest⟩ := Option.bind_eq_some_iff.mp evaluated
    obtain ⟨y, readRight, same⟩ := Option.bind_eq_some_iff.mp rest
    have sameValue : x + y = value := Option.some.inj same
    subst value
    let one := {before.core.write .rax x with rip := before.core.rip + 4}
    let two := {one.write .r10 y with rip := one.rip + 4}
    let prepared := {two.write .rax (x + y) with flags := Ext.AluOp.flagsN .add x y, rip := two.rip + 3}
    have first : Ext.exec (.load .q .rax (Prologue.slot left.index)) before.core before.memory =
        .ok one before.memory :=
      exec_load stack before.core before.memory left .rax x (.inl rfl) entry.base (represented left x readLeft)
    have base : one.read .rbp = stack - 8 := by
      simpa [one, State.read, State.write, Silmaril.Machine.RegisterFile.write] using entry.base
    have second : Ext.exec (.load .q .r10 (Prologue.slot right.index)) one before.memory =
        .ok two before.memory :=
      exec_load stack one before.memory right .r10 y (.inr rfl) base (represented right y readRight)
    have third : Ext.exec (.alu .q .add (.reg .rax) .r10) two before.memory = .ok prepared before.memory := by
      have actual := exec_add two before.memory
      simpa [one, two, prepared, State.read, State.write, Silmaril.Machine.RegisterFile.write] using actual
    have executed : Prologue.Executes [.load .q .rax (Prologue.slot left.index),
        .load .q .r10 (Prologue.slot right.index), .alu .q .add (.reg .rax) .r10] before ⟨prepared, before.memory⟩ :=
      .cons _ _ before ⟨one, before.memory⟩ _ first (.cons _ _ ⟨one, before.memory⟩ ⟨two, before.memory⟩ _ second
        (.cons _ [] ⟨two, before.memory⟩ _ _ third (.nil _)))
    exact write_result stack before frame entry represented destination _ _ 11 prepared executed
      (by change before.core.rip + 4 + 4 + 3 = before.core.rip + 11; simp only [add_assoc]; rfl)
      (by intro register notAx notTen; simp [prepared, two, one, State.read, State.write, Silmaril.Machine.RegisterFile.write, notAx, notTen])
      rfl (by simp [prepared, State.read, State.write, Silmaril.Machine.RegisterFile.write])

theorem Represents.empty (stack : Word) (memory : Memory) :
    Represents stack memory Silmaril.Machine.Lir.Frame.empty := by
  intro register value impossible
  cases impossible

/-- Every completed operation preserves the independent entry metadata and
permissions for the next operation. No temporary-slot backing is assumed. -/
theorem Entry.after {stack : Word} {before after : X86.MState} {frame : Silmaril.Machine.Lir.Frame Nat} {bytes : Nat}
    (entry : Entry stack before) (result : Result stack before after frame bytes) : Entry stack after :=
  ⟨entry.lower, (result.registers .rbp (by decide) (by decide)).trans entry.base,
    (result.memory.permitted_iff _ _ _).mpr entry.readable,
    (result.memory.permitted_iff _ _ _).mpr entry.writable⟩

theorem Result.trans {stack : Word} {before middle after : X86.MState}
    {firstFrame lastFrame : Silmaril.Machine.Lir.Frame Nat} {firstBytes lastBytes : Nat}
    (earlier : Result stack before middle firstFrame firstBytes)
    (later : Result stack middle after lastFrame lastBytes) :
    Result stack before after lastFrame (firstBytes + lastBytes) := by
  refine ⟨?_, fun register notAx notTen => (later.registers register notAx notTen).trans
    (earlier.registers register notAx notTen), later.fsBase.trans earlier.fsBase,
    earlier.memory.trans later.memory, later.represented⟩
  rw [later.pc, earlier.pc, BitVec.ofNat_add, add_assoc]

/-- Evaluation here supplies only pure virtual-register values. Actual machine
execution and physical backing are derived operation by operation. -/
theorem sequence (stack : Word) (before : X86.MState) (frame : Silmaril.Machine.Lir.Frame Nat)
    (operations : List Operation) (finalFrame : Silmaril.Machine.Lir.Frame Nat)
    (entry : Entry stack before) (represented : Represents stack before.memory frame)
    (evaluated : evaluate operations frame = some finalFrame) :
    ∃ after, Prologue.Executes (operations.flatMap Operation.instructions) before after ∧
      Result stack before after finalFrame (operations.map Operation.bytes).sum := by
  induction operations generalizing before frame with
  | nil =>
    have same : frame = finalFrame := Option.some.inj evaluated
    subst finalFrame
    exact ⟨before, .nil _, ⟨by simp, fun _ _ _ => rfl, rfl, .refl _ _, represented⟩⟩
  | cons selected rest ih =>
    obtain ⟨value, selectedValue, remaining⟩ := Option.bind_eq_some_iff.mp evaluated
    obtain ⟨middle, firstSteps, firstResult, _⟩ := operation stack before frame selected value entry represented selectedValue
    obtain ⟨after, laterSteps, laterResult⟩ :=
      ih middle (frame.set selected.destination.index value) (entry.after firstResult) firstResult.represented remaining
    exact ⟨after, firstSteps.append laterSteps, firstResult.trans laterResult⟩

private theorem operation_code_length (operation : Operation) :
    (operation.instructions.flatMap Ext.encode).length = operation.bytes := by
  cases operation with
  | constant destination value =>
    simp only [Operation.instructions, Operation.bytes, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    change 10 + ((Ext.Instr.mov .q (.mem (Prologue.slot destination.index)) .rax).length + 0) = 14
    rw [store_length]
  | sext32 destination source =>
    simp only [Operation.instructions, Operation.bytes, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    change (Ext.Instr.load .q .rax (Prologue.slot source.index)).length +
      (3 + ((Ext.Instr.mov .q (.mem (Prologue.slot destination.index)) .rax).length + 0)) = 11
    rw [load_length source .rax (.inl rfl), store_length]
  | add destination left right =>
    simp only [Operation.instructions, Operation.bytes, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    change (Ext.Instr.load .q .rax (Prologue.slot left.index)).length +
      ((Ext.Instr.load .q .r10 (Prologue.slot right.index)).length +
      (3 + ((Ext.Instr.mov .q (.mem (Prologue.slot destination.index)) .rax).length + 0))) = 15
    rw [load_length left .rax (.inl rfl), load_length right .r10 (.inr rfl), store_length]

theorem code_length (operations : List Operation) :
    ((operations.flatMap Operation.instructions).flatMap Ext.encode).length = (operations.map Operation.bytes).sum := by
  induction operations with
  | nil => rfl
  | cons selected rest ih =>
    simp only [List.flatMap_cons, List.flatMap_append, List.length_append,
      operation_code_length, ih, List.map_cons, List.sum_cons]

end Silmaril.Compiler.Native.Emit.Scalar
