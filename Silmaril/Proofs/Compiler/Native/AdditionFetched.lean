module

public import Silmaril.Compiler.Native.Emit.AdditionFetched.Defs
public import Silmaril.Compiler.Native.Emit.AdditionFunction.Thms
public import Silmaril.X86.FetchTrace.Thms
public import Silmaril.X86.Ext.Lemmas
public import Silmaril.X86.Ext.Behaviour
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionFetched
open Silmaril Silmaril.X86
open Silmaril.X86
open Silmaril.X86.FetchTrace
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

/-- Structural instructions between frame activation and LEAVE. This predicate
inspects syntax only, independently of decoding or successful execution. -/
private inductive Safe : Ext.Instr → Prop
  | move (destination source : Reg) (notBp : destination ≠ .rbp) : Safe (.mov .q (.reg destination) source)
  | constant (destination : Reg) (value : Word) (notBp : destination ≠ .rbp) : Safe (.movabs destination value)
  | load (destination : Reg) (source : Ext.Mem) (notBp : destination ≠ .rbp) : Safe (.load .q destination source)
  | sext (destination source : Reg) (notBp : destination ≠ .rbp) : Safe (.movsxd destination (.reg source))
  | arithmetic (operation : AluOp) (destination source : Reg) (notCmp : operation ≠ .cmp)
      (notBp : destination ≠ .rbp) : Safe (.alu .q operation (.reg destination) source)
  | immediate (operation : AluOp) (destination : Reg) (value : BitVec 8) (notCmp : operation ≠ .cmp)
      (notBp : destination ≠ .rbp) : Safe (.aluI8 .q operation (.reg destination) value)
  | store (slot : Fin 11) (allowed : slot.val = 0 ∨ 2 ≤ slot.val) (source : Reg) :
      Safe (.mov .q (.mem (Prologue.slot slot.val)) source)
  | jump : Safe (.jmp8 0)

private theorem Safe.not_ret {instruction : Ext.Instr} (safe : Safe instruction) : instruction ≠ .ret := by
  cases safe <;> simp

private theorem slot_address (stack : Word) (state : X86.State) (slot : Fin 11) (next : Word)
    (base : state.read .rbp = stack - 8) :
    (Prologue.slot slot.val).addr state next = stack - BitVec.ofNat 64 (8 * (slot.val + 2)) := by
  have signed : ∀ slot : Fin 11,
      (-(BitVec.ofNat 32 (8 * (slot.val + 1)))).signExtend 64 =
        -(BitVec.ofNat 64 (8 * (slot.val + 1))) := by decide +kernel
  simp only [Prologue.slot, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Base.value_reg,
    base, Option.map_none, Option.getD_none, signed slot]
  change stack - 8 + (0 : Word) + -(BitVec.ofNat 64 (8 * (slot.val + 1))) = _
  rw [add_zero, ← sub_eq_add_neg, sub_sub]
  congr 1
  change BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * (slot.val + 1)) = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

private theorem slot_frame (stack : Word) (lower : 96 ≤ stack.toNat) (slot : Fin 11)
    (allowed : slot.val = 0 ∨ 2 ≤ slot.val) (value : Word) {before after : Process.Memory}
    (written : Ext.storeN before (stack - BitVec.ofNat 64 (8 * (slot.val + 2))) 8 value = some after) :
    before.WritesWithin after (AdditionFunction.footprint stack) := by
  apply (Ext.Stored.of_storeN written).writesWithin
  intro offset bound
  rw [Ext.length_leBytes] at bound
  have slotBound := slot.isLt
  have address : (stack - BitVec.ofNat 64 (8 * (slot.val + 2))).toNat =
      stack.toNat - 8 * (slot.val + 2) := Ext.toNat_sub_ofNat (by omega) (by omega)
  rw [address]
  rcases allowed with zero | regular
  · apply Or.inl
    unfold Prologue.footprint
    rw [zero]
    omega
  · apply Or.inr
    unfold Scalar.footprint
    omega

private theorem move_effect (destination source : Reg) (notBp : destination ≠ .rbp) (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.mov .q (.reg destination) source) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.mov .q (.reg destination) source).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_mov_reg] at executed
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      refine ⟨rfl, ?_, .refl _ _⟩
      simp [Ext.Sz.write, State.read, State.write, Silmaril.Machine.RegisterFile.write, Ne.symm notBp]

private theorem constant_effect (destination : Reg) (value : Word) (notBp : destination ≠ .rbp) (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.movabs destination value) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.movabs destination value).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_movabs] at executed
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      refine ⟨rfl, ?_, .refl _ _⟩
      simp [State.read, State.write, Silmaril.Machine.RegisterFile.write, Ne.symm notBp]

private theorem load_effect (destination : Reg) (source : Ext.Mem) (notBp : destination ≠ .rbp) (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.load .q destination source) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.load .q destination source).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_load] at executed
      split at executed
      next value =>
        obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
        refine ⟨rfl, ?_, .refl _ _⟩
        simp [Ext.Sz.write, State.read, State.write, Silmaril.Machine.RegisterFile.write, Ne.symm notBp]
      next => contradiction

private theorem sext_effect (destination source : Reg) (notBp : destination ≠ .rbp) (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.movsxd destination (.reg source)) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.movsxd destination (.reg source)).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_movsxd_reg] at executed
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      refine ⟨rfl, ?_, .refl _ _⟩
      simp [State.read, State.write, Silmaril.Machine.RegisterFile.write, Ne.symm notBp]

private theorem arithmetic_effect (operation : AluOp) (destination source : Reg) (notCmp : operation ≠ .cmp) (notBp : destination ≠ .rbp) (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.alu .q operation (.reg destination) source) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.alu .q operation (.reg destination) source).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_alu_reg _ _ _ _ _ _ notCmp] at executed
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      refine ⟨rfl, ?_, .refl _ _⟩
      simp [Ext.Sz.write, State.read, State.write, Silmaril.Machine.RegisterFile.write, Ne.symm notBp]

private theorem immediate_effect (operation : AluOp) (destination : Reg) (value : BitVec 8) (notCmp : operation ≠ .cmp) (notBp : destination ≠ .rbp) (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.aluI8 .q operation (.reg destination) value) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.aluI8 .q operation (.reg destination) value).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_aluI8_reg _ _ _ _ _ _ notCmp] at executed
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      refine ⟨rfl, ?_, .refl _ _⟩
      simp [Ext.Sz.write, State.read, State.write, Silmaril.Machine.RegisterFile.write, Ne.symm notBp]

private theorem store_effect (slot : Fin 11) (allowed : slot.val = 0 ∨ 2 ≤ slot.val) (source : Reg) (stack : Word)
    (lower : 96 ≤ stack.toNat) (before after : X86.MState)
    (base : before.core.read .rbp = stack - 8)
    (executed : Ext.exec (.mov .q (.mem (Prologue.slot slot.val)) source) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.mov .q (.mem (Prologue.slot slot.val)) source).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_store] at executed
      split at executed
      next afterMemory written =>
        obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
        refine ⟨rfl, rfl, ?_⟩
        rw [slot_address stack before.core slot _ base] at written
        exact slot_frame stack lower slot allowed _ written
      next => contradiction

private theorem jump_effect  (stack : Word) (before after : X86.MState)
    (executed : Ext.exec (.jmp8 0) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 (Ext.Instr.jmp8 0).length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases after with
  | mk core memory =>
      rw [Ext.exec_jmp8] at executed
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      refine ⟨?_, rfl, .refl _ _⟩
      have zero : (0 : BitVec 8).signExtend 64 = 0 := rfl
      rw [zero, add_zero]

/-- Real execution of each independently admitted instruction derives its
PC movement, unchanged frame base and exact stack-store footprint. -/
private theorem Safe.effect {instruction : Ext.Instr} (safe : Safe instruction) (stack : Word)
    (lower : 96 ≤ stack.toNat) (before after : X86.MState)
    (base : before.core.read .rbp = stack - 8)
    (executed : Ext.exec instruction before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + BitVec.ofNat 64 instruction.length ∧
      after.core.read .rbp = before.core.read .rbp ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint stack) := by
  cases safe with
  | move destination source notBp =>
    exact move_effect destination source notBp stack before after executed
  | constant destination value notBp =>
    exact constant_effect destination value notBp stack before after executed
  | load destination source notBp =>
    exact load_effect destination source notBp stack before after executed
  | sext destination source notBp =>
    exact sext_effect destination source notBp stack before after executed
  | arithmetic operation destination source notCmp notBp =>
    exact arithmetic_effect operation destination source notCmp notBp stack before after executed
  | immediate operation destination value notCmp notBp =>
    exact immediate_effect operation destination value notCmp notBp stack before after executed
  | store slot allowed source =>
    exact store_effect slot allowed source stack lower before after base executed
  | jump =>
    exact jump_effect stack before after executed

private theorem executes_split (first second : List Ext.Instr) (before after : X86.MState)
    (trace : Prologue.Executes (first ++ second) before after) :
    ∃ middle, Prologue.Executes first before middle ∧ Prologue.Executes second middle after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, trace⟩
  | cons instruction rest ih =>
    cases trace with
    | cons _ _ _ middle _ executed later =>
      obtain ⟨split, initial, final⟩ := ih middle later
      exact ⟨split, .cons _ _ _ _ _ executed initial, final⟩

private theorem scalar_safe (operation : Scalar.Operation) :
    ∀ instruction ∈ operation.instructions, Safe instruction := by
  have store (register : Scalar.Register) : Safe (.mov .q (.mem (Prologue.slot register.index)) .rax) := by
    exact .store ⟨register.index, by have := register.isLt; unfold Scalar.Register.index; omega⟩
      (by right; change 2 ≤ register.val + 2; omega) .rax
  cases operation with
  | constant destination value =>
    show ∀ instruction ∈ (Scalar.Operation.constant destination value).instructions, Safe instruction
    intro instruction member
    have selected : instruction = .movabs .rax value ∨ instruction = .mov .q (.mem (Prologue.slot destination.index)) .rax := by
      simpa only [Scalar.Operation.instructions, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases selected with constant | written
    · exact constant.symm ▸ Safe.constant _ _ (by decide)
    · exact written.symm ▸ store destination
  | sext32 destination source =>
    show ∀ instruction ∈ (Scalar.Operation.sext32 destination source).instructions, Safe instruction
    intro instruction member
    have selected : instruction = .load .q .rax (Prologue.slot source.index) ∨
      instruction = .movsxd .rax (.reg .rax) ∨ instruction = .mov .q (.mem (Prologue.slot destination.index)) .rax := by
      simpa only [Scalar.Operation.instructions, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases selected with loaded | extended | written
    · exact loaded.symm ▸ Safe.load _ _ (by decide)
    · exact extended.symm ▸ Safe.sext _ _ (by decide)
    · exact written.symm ▸ store destination
  | add destination left right =>
    show ∀ instruction ∈ (Scalar.Operation.add destination left right).instructions, Safe instruction
    intro instruction member
    have selected : instruction = .load .q .rax (Prologue.slot left.index) ∨
      instruction = .load .q .r10 (Prologue.slot right.index) ∨
      instruction = .alu .q .add (.reg .rax) .r10 ∨ instruction = .mov .q (.mem (Prologue.slot destination.index)) .rax := by
      simpa only [Scalar.Operation.instructions, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases selected with leftLoad | rightLoad | added | written
    · exact leftLoad.symm ▸ Safe.load _ _ (by decide)
    · exact rightLoad.symm ▸ Safe.load _ _ (by decide)
    · exact added.symm ▸ Safe.arithmetic _ _ _ (by decide) (by decide)
    · exact written.symm ▸ store destination

private def middle (left right : Word) : List Ext.Instr :=
  [.aluI8 .q .sub (.reg .rsp) 96, .aluI8 .q .and (.reg .rsp) (BitVec.ofInt 8 (-64)),
    .mov .q (.reg .rax) .rsp, .mov .q (.mem (Prologue.slot 0)) .rax, .jmp8 0] ++
    AdditionBody.instructions left right ++ [.load .q .rax (Prologue.slot 10)]

private theorem middle_safe (left right : Word) :
    ∀ instruction ∈ middle left right, Safe instruction := by
  intro instruction member
  simp only [middle, List.mem_append] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl | rfl | rfl) | body) | rfl
  · exact .immediate _ _ _ (by decide) (by decide)
  · exact .immediate _ _ _ (by decide) (by decide)
  · exact .move _ _ (by decide)
  · exact .store ⟨0, by decide⟩ (Or.inl rfl) .rax
  · exact .jump
  · obtain ⟨operation, _, selected⟩ := List.mem_flatMap.mp body
    exact scalar_safe operation instruction selected
  · exact .load _ _ (by decide)

private theorem safe_trace (stack : Word) (lower : 96 ≤ stack.toNat)
    {instructions : List Ext.Instr} {before after : X86.MState}
    (trace : Prologue.Executes instructions before after)
    (safe : ∀ instruction ∈ instructions, Safe instruction)
    (base : before.core.read .rbp = stack - 8) :
    Trace (AdditionFunction.footprint stack) instructions before after ∧
      after.core.read .rbp = stack - 8 := by
  induction trace with
  | nil state => exact ⟨.nil _, base⟩
  | cons instruction rest before middle after executed later ih =>
    have admitted := safe instruction (by simp)
    obtain ⟨pc, bp, frame⟩ := admitted.effect stack lower before middle base executed
    obtain ⟨remaining, finalBase⟩ := ih (fun instruction member => safe instruction (by simp [member])) (bp.trans base)
    exact ⟨.cons _ _ _ _ _ admitted.not_ret executed pc frame remaining, finalBase⟩

private theorem push_frame (before : X86.MState) (after : Process.Memory)
    (lower : 96 ≤ (before.core.read .rsp).toNat)
    (store : before.memory.writeBytes (before.core.read .rsp - 8#64).toNat
      (Silmaril.Machine.LittleEndian.encodeWords [before.core.read .rbp]) = some after) :
    before.memory.WritesWithin after (AdditionFunction.footprint (before.core.read .rsp)) := by
  apply (Ext.Stored.of_writeBytes store).writesWithin
  intro offset bound
  have bytes : (Silmaril.Machine.LittleEndian.encodeWords [before.core.read .rbp]).length = 8 := rfl
  have offsetBound : offset < 8 := by simpa only [bytes] using bound
  have address : (before.core.read .rsp - 8).toNat = (before.core.read .rsp).toNat - 8 :=
    Ext.toNat_sub_ofNat (k := 8) (by omega) (by decide)
  apply Or.inl
  unfold Prologue.footprint
  have eight : (8#64) = (8 : Word) := by decide +kernel
  rw [eight, address]
  omega

private theorem push_effect (before after : X86.MState)
    (lower : 96 ≤ (before.core.read .rsp).toNat)
    (executed : Ext.exec (.push .rbp) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + 1 ∧
      after.core.read .rsp = before.core.read .rsp - 8 ∧
      before.memory.WritesWithin after.memory (AdditionFunction.footprint (before.core.read .rsp)) := by
  cases after with
  | mk core memory =>
    simp only [Ext.exec, X86.pushWord, Ext.retire] at executed
    split at executed
    next value written =>
      cases value with
      | mk state afterMemory =>
        simp only [Option.map_eq_some_iff] at written
        obtain ⟨stored, store, same⟩ := written
        cases same
        obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
        refine ⟨rfl, ?_, ?_⟩
        · simp [State.read, State.write, Silmaril.Machine.RegisterFile.write]
        · exact push_frame before _ lower store
    next => contradiction

private theorem activate_base (before after : X86.MState)
    (executed : Ext.exec (.mov .q (.reg .rbp) .rsp) before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + 3 ∧ after.core.read .rbp = before.core.read .rsp ∧
      after.memory = before.memory := by
  cases after with
  | mk core memory =>
    rw [Ext.exec_mov_reg] at executed
    obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
    refine ⟨rfl, ?_, rfl⟩
    simp [Ext.Sz.write, State.read, State.write, Silmaril.Machine.RegisterFile.write]

private theorem leave_effect (before after : X86.MState)
    (executed : Ext.exec .leave before.core before.memory = .ok after.core after.memory) :
    after.core.rip = before.core.rip + 1 ∧ after.memory = before.memory := by
  cases after with
  | mk core memory =>
    rw [Ext.exec_leave] at executed
    split at executed
    next value =>
      obtain ⟨rfl, rfl⟩ := Ext.Result.ok.inj executed
      exact ⟨rfl, rfl⟩
    next => contradiction


private theorem retiring_shape (left right : Word) :
    retiringInstructions left right =
      [.push .rbp, .mov .q (.reg .rbp) .rsp] ++ middle left right ++ [.leave] := by rfl

private theorem function_shape (left right : Word) :
    AdditionFunction.instructions left right =
      [.push .rbp, .mov .q (.reg .rbp) .rsp] ++ middle left right ++ [.leave, .ret] := by rfl

/-- Annotate the independently derived actual decoded execution. The stack
base and every per-instruction memory frame are consequences of execution. -/
theorem decoded_trace (caller : X86.MState) (left right exit : Word)
    (entry : AdditionFunction.Entry caller exit) :
    ∃ beforeRet final,
      Trace (AdditionFunction.footprint (caller.core.read .rsp)) (retiringInstructions left right) caller beforeRet ∧
      Ext.exec .ret beforeRet.core beforeRet.memory = .ok final.core final.memory ∧
      AdditionFunction.Ready caller final left right exit := by
  obtain ⟨final, trace, ready⟩ := AdditionFunction.execute caller left right exit entry
  rw [function_shape] at trace
  obtain ⟨beforeLeave, initial, last⟩ := executes_split
    ([.push .rbp, .mov .q (.reg .rbp) .rsp] ++ middle left right) [.leave, .ret] caller final trace
  obtain ⟨activated, first, body⟩ := executes_split
    [.push .rbp, .mov .q (.reg .rbp) .rsp] (middle left right) caller beforeLeave initial
  cases first with
  | cons _ _ _ pushed _ push rest =>
    show ∃ beforeRet final, Trace (AdditionFunction.footprint (caller.core.read .rsp)) (retiringInstructions left right) caller beforeRet ∧
      Ext.exec .ret beforeRet.core beforeRet.memory = .ok final.core final.memory ∧ AdditionFunction.Ready caller final left right exit
    cases rest with
    | cons _ _ _ active _ move rest =>
      show ∃ beforeRet final, Trace (AdditionFunction.footprint (caller.core.read .rsp)) (retiringInstructions left right) caller beforeRet ∧
        Ext.exec .ret beforeRet.core beforeRet.memory = .ok final.core final.memory ∧ AdditionFunction.Ready caller final left right exit
      cases rest
      obtain ⟨pushPc, pushSp, pushFrame⟩ := push_effect caller pushed (by have := entry.lower; omega) push
      obtain ⟨movePc, moveBase, moveMemory⟩ := activate_base pushed activated move
      have base : activated.core.read .rbp = caller.core.read .rsp - 8 := moveBase.trans pushSp
      obtain ⟨bodyTrace, bodyBase⟩ := safe_trace (caller.core.read .rsp) (by have := entry.lower; omega)
        body (middle_safe left right) base
      cases last with
      | cons _ _ _ beforeRet _ leave rest =>
        show ∃ beforeRet final, Trace (AdditionFunction.footprint (caller.core.read .rsp)) (retiringInstructions left right) caller beforeRet ∧
          Ext.exec .ret beforeRet.core beforeRet.memory = .ok final.core final.memory ∧ AdditionFunction.Ready caller final left right exit
        cases rest with
        | cons _ _ _ afterRet _ ret rest =>
          show ∃ beforeRet final, Trace (AdditionFunction.footprint (caller.core.read .rsp)) (retiringInstructions left right) caller beforeRet ∧
            Ext.exec .ret beforeRet.core beforeRet.memory = .ok final.core final.memory ∧ AdditionFunction.Ready caller final left right exit
          cases rest
          obtain ⟨leavePc, leaveMemory⟩ := leave_effect beforeLeave beforeRet leave
          have leaveFrame : beforeLeave.memory.WritesWithin beforeRet.memory
              (AdditionFunction.footprint (caller.core.read .rsp)) := by
            rw [leaveMemory]
            exact .refl _ _
          have moveFrame : pushed.memory.WritesWithin activated.memory
              (AdditionFunction.footprint (caller.core.read .rsp)) := by
            rw [moveMemory]
            exact .refl _ _
          refine ⟨beforeRet, final, ?_, ret, ready⟩
          rw [retiring_shape, List.append_assoc]
          apply Trace.append
          · exact .cons _ _ _ _ _ (by simp) push pushPc pushFrame
              (.cons _ _ _ _ _ (by simp) move movePc moveFrame (.nil _))
          · exact bodyTrace.append (.cons _ _ _ _ _ (by simp) leave leavePc leaveFrame (.nil _))


theorem retiring_count (left right : Word) : (retiringInstructions left right).length = 35 := rfl

theorem code_split (left right : Word) :
    AdditionFunction.code left right = FetchTrace.code (retiringInstructions left right) ++ Ext.encode .ret := by
  have shape : AdditionFunction.instructions left right = retiringInstructions left right ++ [.ret] := rfl
  simp only [AdditionFunction.code, shape, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, FetchTrace.code]

theorem retiring_bytes (left right : Word) : (FetchTrace.code (retiringInstructions left right)).length = 135 := by
  have length := AdditionFunction.code_length left right
  rw [code_split, List.length_append] at length
  have retLength : (Ext.encode .ret).length = 1 := rfl
  rw [retLength] at length
  omega

/-- The actual loaded 136-byte image performs 35 fetched retirements and a
real returning RET. Every intermediate decoder equation and surviving code
image follows from execution, exact store frames and entry disjointness. -/
theorem execute (caller : X86.MState) (left right exit : Word) (entry : Entry caller left right exit) :
    ∃ beforeRet final, Ext.Runs exit 35 caller beforeRet ∧ Ext.step exit beforeRet = .returned final ∧
      AdditionFunction.Ready caller final left right exit ∧
      Ext.Loaded final.memory caller.core.rip (AdditionFunction.code left right) := by
  obtain ⟨beforeRet, final, trace, ret, ready⟩ := decoded_trace caller left right exit entry.function
  have loaded : Ext.Loaded caller.memory caller.core.rip
      ([] ++ FetchTrace.code (retiringInstructions left right) ++ Ext.encode .ret) := by
    simpa only [List.nil_append, ← code_split] using entry.loaded
  have disjoint : Disjoint caller.core.rip
      ([] ++ FetchTrace.code (retiringInstructions left right) ++ Ext.encode .ret)
      (AdditionFunction.footprint (caller.core.read .rsp)) := by
    simpa only [List.nil_append, ← code_split] using entry.disjoint
  obtain ⟨runs, beforeLoaded⟩ := trace.fetched exit caller.core.rip [] (Ext.encode .ret) loaded (by simp) disjoint
  have pc : beforeRet.core.rip = caller.core.rip + BitVec.ofNat 64 135 := by
    simpa only [retiring_bytes] using trace.pc
  have image : Ext.Loaded beforeRet.memory caller.core.rip (AdditionFunction.code left right) := by
    simpa only [List.nil_append, ← code_split] using beforeLoaded
  have fits : 135 + 1 ≤ (AdditionFunction.code left right).length := by rw [AdditionFunction.code_length]
  have decoded : Ext.decode (((AdditionFunction.code left right).drop 135).take 1) = some (.ret, 1) := by
    have retLength : (Ext.encode .ret).length = 1 := rfl
    have exactSlice := FetchTrace.decode_at (FetchTrace.code (retiringInstructions left right)) [] .ret
    simpa only [List.append_nil, ← code_split, retiring_bytes, retLength] using exactSlice
  have returned := Ext.step_returned_of_loaded image pc fits decoded ret ready.returned.pc
  refine ⟨beforeRet, final, ?_, returned, ready, ?_⟩
  · simpa only [retiring_count] using runs
  · exact FetchTrace.loaded_after entry.loaded ready.frame entry.disjoint

/-- Actual bounded source lowering and fetched execution compose at the
limited INTEGER-state SysV result boundary. GNU-as text remains separate. -/
theorem compile_execute (left right : Int) (bounded : Correctness.AdditionSource.Bounds left right)
    (tag : String) (caller : X86.MState) (exit : Word)
    (entry : Entry caller (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit) :
    Lower.compile tag (Correctness.AdditionSource.program left right) =
      .ok (Correctness.AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) ∧
    ∃ beforeRet final, Ext.Runs exit 35 caller beforeRet ∧ Ext.step exit beforeRet = .returned final ∧
      AdditionFunction.Ready caller final (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit ∧
      C.Api.SysV.ResultAt final (some .int32) ((BitVec.ofInt 64 (left + right)).setWidth 32) := by
  obtain ⟨beforeRet, final, runs, returned, ready, _⟩ := execute caller _ _ exit entry
  exact ⟨Correctness.AdditionLower.compile left right bounded tag, beforeRet, final, runs, returned,
    ready, ready.addition_int32 left right bounded⟩

private theorem runs_reach {exit : Word} {count : Nat} {before after : X86.MState}
    (runs : Ext.Runs exit count before after) :
    Relation.ReflTransGen (fun first second => Ext.step exit first = .retired second) before after := by
  induction count generalizing before with
  | zero =>
    have same : before = after := Option.some.inj runs
    subst same
    exact .refl
  | succ count ih =>
    change (Ext.stepOpt exit before).bind (Silmaril.Machine.Execution.run (Ext.stepOpt exit) count) = some after at runs
    cases first : Ext.stepOpt exit before with
    | none => rw [first, Option.bind_none] at runs; contradiction
    | some middle =>
      rw [first, Option.bind_some] at runs
      exact (ih runs).head (Ext.stepOpt_eq_some_iff.mp first)

/-- Complete standard fetched-machine behavior is exactly one returned final
state. This quantifies over all observations, including faults, traps,
exhaustion, undefined behavior and divergence, without restricting the target
semantics or supplying a successful run as a premise. -/
theorem behavior (caller : X86.MState) (left right exit : Word) (entry : Entry caller left right exit)
    (Exhausted : X86.MState → Prop) :
    ∃ final, AdditionFunction.Ready caller final left right exit ∧
      ∀ observation, (Ext.sem Exhausted).Beh (exit, caller) observation ↔ observation = .returned final := by
  obtain ⟨beforeRet, final, runs, returned, ready, _⟩ := execute caller left right exit entry
  have actual : (Ext.sem Exhausted).Beh (exit, caller) (.returned final) := Ext.beh_returned (runs_reach runs) returned
  refine ⟨final, ready, ?_⟩
  intro observation
  constructor
  · intro seen
    exact Silmaril.Machine.Behaviour.Semantics.Beh.unique Ext.sem_deterministic seen actual
  · intro same
    simpa only [same] using actual

end Silmaril.Compiler.Native.Emit.AdditionFetched
