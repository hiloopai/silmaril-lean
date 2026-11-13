module

public import Silmaril.Compiler.Native.Correctness.LiteralInteger.Defs
import Silmaril.Compiler.Native.Correctness.Execution.Thms
import Silmaril.Compiler.Native.Correctness.LiteralEmission.Thms
import Silmaril.X86.Ext.Store

/-! Actual fetched-byte symbolic execution of the integer template. Generic
Ext.encode decoding replaces the one fixed immediate; the caller/frame proof
uses permission-derived stores and the actual Features retire/RET path. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralInteger
open Silmaril Silmaril.X86
open Silmaril.X86.Ext
open Silmaril.Process (Memory)
open Silmaril.Compiler.Native.Correctness
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem movabs_length (value : Word) : (Ext.encode (.movabs .rax value)).length = 10 := by rfl

theorem code_length (value : Word) : (code value).length = 83 := by
  simp [code, LiteralImage.code, movabs_length]

private def slot (k : Nat) : Ext.Mem := Ext.Mem.ofReg .rbp none (BitVec.ofInt 32 (-Int.ofNat k))

private theorem decode0 (value : Word) :
    Ext.decode (((code value).drop 0).take 1) = some (.push .rbp, 1) := by
  simp [code, LiteralImage.code]
  decide +kernel

private theorem decode1 (value : Word) :
    Ext.decode (((code value).drop 1).take 3) = some (.mov .q (.reg .rbp) .rsp, 3) := by
  simp [code, LiteralImage.code]
  decide +kernel

private theorem decode2 (value : Word) :
    Ext.decode (((code value).drop 4).take 4) = some (.aluI8 .q .sub (.reg .rsp) 48, 4) := by
  simp [code, LiteralImage.code]
  decide +kernel

private theorem decode3 (value : Word) :
    Ext.decode (((code value).drop 8).take 4) = some (.aluI8 .q .and (.reg .rsp) 0xc0, 4) := by
  simp [code, LiteralImage.code]
  decide +kernel

private theorem decode4 (value : Word) :
    Ext.decode (((code value).drop 12).take 3) = some (.mov .q (.reg .rax) .rsp, 3) := by
  simp [code, LiteralImage.code]
  decide +kernel

private theorem decode5 (value : Word) :
    Ext.decode (((code value).drop 15).take 4) = some (.mov .q (.mem (slot 8)) .rax, 4) := by
  simp [code, LiteralImage.code]
  decide +kernel

private theorem decode6 (value : Word) :
    Ext.decode (((code value).drop 19).take 2) = some (.jmp8 0, 2) := by
  simp [code, LiteralImage.code, List.take_append, movabs_length]
  decide +kernel

private theorem decode7 (value : Word) :
    Ext.decode (((code value).drop 21).take 10) = some (.movabs .rax value, 10) := by
  simp [code, LiteralImage.code, List.drop_append, movabs_length]

private theorem decode8 (value : Word) :
    Ext.decode (((code value).drop 31).take 4) = some (.mov .q (.mem (slot 24)) .rax, 4) := by
  simp [code, LiteralImage.code, movabs_length]
  decide +kernel

private theorem decode9 (value : Word) :
    Ext.decode (((code value).drop 35).take 4) = some (.load .q .rax (slot 24), 4) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode10 (value : Word) :
    Ext.decode (((code value).drop 39).take 3) = some (.movsxd .rax (.reg .rax), 3) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode11 (value : Word) :
    Ext.decode (((code value).drop 42).take 4) = some (.mov .q (.mem (slot 32)) .rax, 4) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode12 (value : Word) :
    Ext.decode (((code value).drop 46).take 4) = some (.load .q .rax (slot 32), 4) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode13 (value : Word) :
    Ext.decode (((code value).drop 50).take 3) = some (.movsxd .rax (.reg .rax), 3) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode14 (value : Word) :
    Ext.decode (((code value).drop 53).take 4) = some (.mov .q (.mem (slot 40)) .rax, 4) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode15 (value : Word) :
    Ext.decode (((code value).drop 57).take 4) = some (.load .q .rax (slot 40), 4) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode16 (value : Word) :
    Ext.decode (((code value).drop 61).take 1) = some (.leave, 1) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel

private theorem decode17 (value : Word) :
    Ext.decode (((code value).drop 62).take 1) = some (.ret, 1) := by
  simp [code, LiteralImage.code, List.drop_append, List.take_append, movabs_length]
  rw [List.drop_eq_nil_of_le (by rw [movabs_length]; decide)]
  decide +kernel


private abbrev lift (original : Features.State) (state : X86.MState) : NativeState :=
  ⟨original.setCore state.core, state.memory⟩

private theorem safe_lift_step {base exit : Word} {bytes : List Byte}
    {before after : X86.MState} {offset len : Nat} {i : Ext.Instr}
    (original : Features.State)
    (loaded : Ext.Loaded before.memory base bytes)
    (pc : before.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : Ext.decode ((bytes.drop offset).take len) = some (i, len))
    (safe : Features.baseRequirement i = none)
    (executed : Ext.stepOpt exit before = some after) :
    Retires exit (lift original before) (lift original after) := by
  have fetched : Ext.fetch before.memory before.core.rip.toNat = .decoded i len := by
    apply Ext.fetch_eq_decoded_iff.mpr
    refine ⟨(bytes.drop offset).take len, ?_, decoded⟩
    rw [pc, loaded.toNat_add (by have := (Ext.decode_length decoded).2.1; omega)]
    exact loaded.fetchBytes_sub (Ext.decode_length decoded).2.1 fits
  have stepBase := Features.step_of_base
    (m := lift original before) (F := Features.FeatureSet.baseline64)
    (exts := [Features.floatExt, Features.Fpu.ext]) (exit := exit) fetched
  change step exit (lift original before) = .retired (lift original after)
  rw [Silmaril.Compiler.Native.Correctness.step, stepBase]
  have h := Ext.stepOpt_eq_some_iff.mp executed
  simp only [Features.baseCheck, safe]
  change Features.Outcome.ofBase (original.setCore before.core)
    (Ext.step exit before) = .retired (lift original after)
  rw [h]
  rfl

private theorem safe_lift_return {base exit : Word} {bytes : List Byte}
    {before final : X86.MState} {offset len : Nat}
    (original : Features.State)
    (loaded : Ext.Loaded before.memory base bytes)
    (pc : before.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : Ext.decode ((bytes.drop offset).take len) = some (.ret, len))
    (returned : Ext.step exit before = .returned final) :
    step exit (lift original before) = .returned (lift original final) := by
  have fetched : Ext.fetch before.memory before.core.rip.toNat = .decoded .ret len := by
    apply Ext.fetch_eq_decoded_iff.mpr
    refine ⟨(bytes.drop offset).take len, ?_, decoded⟩
    rw [pc, loaded.toNat_add (by have := (Ext.decode_length decoded).2.1; omega)]
    exact loaded.fetchBytes_sub (Ext.decode_length decoded).2.1 fits
  have stepBase := Features.step_of_base
    (m := lift original before) (F := Features.FeatureSet.baseline64)
    (exts := [Features.floatExt, Features.Fpu.ext]) (exit := exit) fetched
  rw [Silmaril.Compiler.Native.Correctness.step, stepBase]
  change Features.Outcome.ofBase (original.setCore before.core)
    (Ext.step exit before) = .returned (lift original final)
  rw [returned]
  rfl


private def coreWith (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) : X86.State :=
  { regs := fun r => if r = .rsp then sp else if r = .rbp then bp else if r = .rax then ax else initial.read r,
    rip := pc, flags, fsBase := initial.fsBase }

private theorem coreWith_read_rsp (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).read .rsp = sp := by simp [coreWith, State.read]
private theorem coreWith_read_rbp (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).read .rbp = bp := by simp [coreWith, State.read]
private theorem coreWith_read_rax (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).read .rax = ax := by simp [coreWith, State.read]

private theorem coreWith_initial (initial : X86.State) :
    coreWith initial initial.rip (initial.read .rsp) (initial.read .rbp) (initial.read .rax)
      initial.flags = initial := by
  cases initial with
  | mk regs rip flags fsBase =>
    simp only [coreWith, State.read, State.mk.injEq, and_true]
    funext r
    cases r <;> rfl

private theorem coreWith_regs (initial : X86.State) (pc sp bp ax : Word) (flags : Flags)
    (r : Reg) (hrsp : r ≠ .rsp) (hrbp : r ≠ .rbp) (hrax : r ≠ .rax) :
    (coreWith initial pc sp bp ax flags).read r = initial.read r := by
  simp [coreWith, State.read, hrsp, hrbp, hrax]

private theorem coreWith_write (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags)
    (r : Reg) :
    (coreWith initial pc sp bp ax flags).write r value =
      { coreWith initial pc sp bp ax flags with
        regs := fun q => if q = r then value else (coreWith initial pc sp bp ax flags).read q } := rfl

private theorem coreWith_write_rsp (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).write .rsp value = coreWith initial pc value bp ax flags := by
  simp only [coreWith, State.write, State.mk.injEq, and_true]
  funext r
  cases r <;> simp [Machine.RegisterFile.write, State.read]
private theorem coreWith_write_rbp (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).write .rbp value = coreWith initial pc sp value ax flags := by
  simp only [coreWith, State.write, State.mk.injEq, and_true]
  funext r
  cases r <;> simp [Machine.RegisterFile.write, State.read]
private theorem coreWith_write_rax (initial : X86.State) (pc sp bp ax value : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).write .rax value = coreWith initial pc sp bp value flags := by
  simp only [coreWith, State.write, State.mk.injEq, and_true]
  funext r
  cases r <;> simp [Machine.RegisterFile.write, State.read]

private theorem coreWith_rip (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) :
    (coreWith initial pc sp bp ax flags).rip = pc := rfl
private theorem coreWith_set_rip (initial : X86.State) (pc sp bp ax next : Word) (flags : Flags) :
    { coreWith initial pc sp bp ax flags with rip := next } =
      coreWith initial next sp bp ax flags := rfl
private theorem coreWith_set_flags (initial : X86.State) (pc sp bp ax : Word) (flags next : Flags) :
    { coreWith initial pc sp bp ax flags with flags := next } =
      coreWith initial pc sp bp ax next := rfl

private theorem exec_move_bp (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) (memory : Memory) :
    Ext.exec (.mov .q (.reg .rbp) .rsp) (coreWith initial pc sp bp ax flags) memory =
      .ok (coreWith initial (pc + 3) sp sp ax flags) memory := by
  simp only [Ext.exec, Ext.writeRM, Ext.Sz.read_q, Ext.Sz.write_q,
    coreWith_read_rsp, coreWith_write_rbp, Ext.retire, coreWith_rip, coreWith_set_rip]
  rfl

private theorem exec_move_ax (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) (memory : Memory) :
    Ext.exec (.mov .q (.reg .rax) .rsp) (coreWith initial pc sp bp ax flags) memory =
      .ok (coreWith initial (pc + 3) sp bp sp flags) memory := by
  simp only [Ext.exec, Ext.writeRM, Ext.Sz.read_q, Ext.Sz.write_q,
    coreWith_read_rsp, coreWith_write_rax, Ext.retire, coreWith_rip, coreWith_set_rip]
  rfl



private theorem slot_addr (initial : X86.State) (pc currentSp sp ax next : Word) (flags : Flags)
    (k : Nat) (hk : k = 8 ∨ k = 24 ∨ k = 32 ∨ k = 40) :
    (slot k).addr (coreWith initial pc currentSp (sp - 8) ax flags) next =
      sp - BitVec.ofNat 64 (8 + k) := by
  have disp : (BitVec.ofInt 32 (-Int.ofNat k)).signExtend 64 = -BitVec.ofNat 64 k := by
    rcases hk with rfl | rfl | rfl | rfl <;> decide +kernel
  simp only [slot, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Base.value_reg,
    coreWith_read_rbp, Option.map_none, Option.getD_none]
  rw [disp, ← sub_eq_add_neg]
  change sp - 8 + (0 : Word) - BitVec.ofNat 64 k = _
  rw [add_zero, sub_sub]
  congr 1
  exact Ext.ofNat_add_ofNat 8 k

private def subFlags (sp : Word) : Flags := Ext.AluOp.flagsN .sub (sp - 8) (48 : Word)
private def aligned (sp : Word) : Word := (sp - 56) &&& 0xffffffffffffffc0
private theorem coreWith_set_flags_rip (initial : X86.State) (pc sp bp ax next : Word)
    (flags nextFlags : Flags) :
    { coreWith initial pc sp bp ax flags with flags := nextFlags, rip := next } =
      coreWith initial next sp bp ax nextFlags := rfl

private theorem exec_sub (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) (memory : Memory) :
    Ext.exec (.aluI8 .q .sub (.reg .rsp) 48) (coreWith initial pc (sp - 8) bp ax flags) memory =
      .ok (coreWith initial (pc + 4) (sp - 56) bp ax (subFlags sp)) memory := by
  have hl : (Ext.Instr.aluI8 .q .sub (.reg .rsp) 48).length = 4 := by decide +kernel
  simp only [Ext.exec, hl, Ext.aluStep, Ext.readRM, Ext.writeRM, Ext.Sz.read_q,
    coreWith_read_rsp, Ext.retire, coreWith_rip, Option.map_some]
  change Ext.Result.ok { (coreWith initial pc (sp - 8) bp ax flags).write .rsp
    (sp - 8 - 48) with flags := subFlags sp, rip := pc + 4 } memory = _
  have value : sp - 8 - 48 = sp - 56 := by rw [sub_sub]; rfl
  rw [coreWith_write_rsp, value]
  rfl

private theorem exec_and (initial : X86.State) (pc sp bp ax : Word) (flags : Flags) (memory : Memory) :
    Ext.exec (.aluI8 .q .and (.reg .rsp) 0xc0) (coreWith initial pc (sp - 56) bp ax flags) memory =
      .ok (coreWith initial (pc + 4) (aligned sp) bp ax (alignedFlags sp)) memory := by
  have hl : (Ext.Instr.aluI8 .q .and (.reg .rsp) 0xc0).length = 4 := by decide +kernel
  simp only [Ext.exec, hl, Ext.aluStep, Ext.readRM, Ext.writeRM, Ext.Sz.read_q,
    coreWith_read_rsp, Ext.retire, coreWith_rip, Option.map_some]
  change Ext.Result.ok { (coreWith initial pc (sp - 56) bp ax flags).write .rsp
    (aligned sp) with flags := alignedFlags sp, rip := pc + 4 } memory = _
  rw [coreWith_write_rsp]
  rfl


private theorem Entry.sub_address {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) (k : Nat) (fits : k ≤ 128) :
    (initial.core.read .rsp - BitVec.ofNat 64 k).toNat = (initial.core.read .rsp).toNat - k :=
  Ext.toNat_sub_ofNat (by have := entry.stackLower; omega) (by omega)

private theorem Entry.permitted_stack {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) {memory : Memory}
    (frame : initial.memory.WritesWithin memory (footprint (initial.core.read .rsp)))
    (access : Process.Access) (choice : access = .read ∨ access = .write)
    (k : Nat) (lower : 8 ≤ k) (upper : k ≤ 48) :
    memory.Permitted access (initial.core.read .rsp - BitVec.ofNat 64 k).toNat 8 := by
  rw [frame.permitted_iff, entry.sub_address k (by omega)]
  rcases choice with rfl | rfl
  · exact Ext.Memory.Permitted.sub entry.stackRead (by decide) (by omega) (by have := entry.stackLower; omega)
  · exact Ext.Memory.Permitted.sub entry.stackWrite (by decide) (by omega) (by have := entry.stackLower; omega)

private theorem Entry.loaded_frame {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) {memory : Memory}
    (frame : initial.memory.WritesWithin memory (footprint (initial.core.read .rsp))) :
    Ext.Loaded memory base (code literalValue) := by
  change memory.fetchBytes base.toNat (code literalValue).length = some (code literalValue)
  rw [frame.fetchBytes]
  · exact entry.image
  · intro offset bound
    have separate := entry.separate
    unfold footprint
    omega

private theorem Entry.return_frame {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) {memory : Memory}
    (frame : initial.memory.WritesWithin memory (footprint (initial.core.read .rsp))) :
    memory.readBytes (initial.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) := by
  rw [frame.readBytes]
  · exact entry.returnAddress
  · intro offset bound
    unfold footprint
    omega

private theorem Entry.stored_frame {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) {before after : Memory}
    (frame : initial.memory.WritesWithin before (footprint (initial.core.read .rsp)))
    {k : Nat} (lower : 8 ≤ k) (upper : k ≤ 48) {value : Word}
    (stored : Ext.Stored before after (initial.core.read .rsp - BitVec.ofNat 64 k).toNat
      (Ext.leBytes value 8)) :
    initial.memory.WritesWithin after (footprint (initial.core.read .rsp)) := by
  apply frame.step stored
  intro offset bound
  rw [Ext.length_leBytes] at bound
  rw [entry.sub_address k (by omega)]
  unfold footprint
  have := entry.stackLower
  omega


private theorem exec_push (initial : X86.State) (pc sp bp ax : Word) (flags : Flags)
    {memory after : Memory}
    (written : Ext.storeN memory (sp - 8) 8 bp = some after) :
    Ext.exec (.push .rbp) (coreWith initial pc sp bp ax flags) memory =
      .ok (coreWith initial (pc + 1) (sp - 8) bp ax flags) after := by
  have written' : memory.writeBytes (sp - 8).toNat (Silmaril.Machine.LittleEndian.encodeWords [bp]) =
      some after := by simpa only [Ext.storeN, Ext.leBytes_eight] using written
  simp only [Ext.exec, X86.pushWord, coreWith_read_rsp, coreWith_read_rbp,
    Ext.retire, coreWith_rip, coreWith_write_rsp]
  change (match (memory.writeBytes (sp - 8).toNat (Silmaril.Machine.LittleEndian.encodeWords [bp])).map
    (fun after => (coreWith initial pc (sp - 8) bp ax flags, after)) with
    | some (t, m) => Ext.Result.ok { t with rip := pc + 1 } m
    | none => Ext.Result.dataFault) = _
  rw [written']
  rfl

private theorem exec_store (initial : X86.State) (pc currentSp sp ax : Word) (flags : Flags)
    {memory after : Memory} (k : Nat) (hk : k = 8 ∨ k = 24 ∨ k = 32 ∨ k = 40)
    (written : Ext.storeN memory (sp - BitVec.ofNat 64 (8 + k)) 8 ax = some after) :
    Ext.exec (.mov .q (.mem (slot k)) .rax)
      (coreWith initial pc currentSp (sp - 8) ax flags) memory =
      .ok (coreWith initial (pc + 4) currentSp (sp - 8) ax flags) after := by
  have hl : (Ext.Instr.mov .q (.mem (slot k)) .rax).length = 4 := by
    rcases hk with rfl | rfl | rfl | rfl <;> decide +kernel
  simp only [Ext.exec, hl, Ext.writeRM, Ext.Sz.read_q, coreWith_read_rax,
    slot_addr initial pc currentSp sp ax _ flags k hk, Ext.retire, coreWith_rip]
  change (match (Ext.storeN memory (sp - BitVec.ofNat 64 (8 + k)) 8 ax).map
    (fun after => (coreWith initial pc currentSp (sp - 8) ax flags, after)) with
    | some (t, m) => Ext.Result.ok { t with rip := pc + 4 } m
    | none => Ext.Result.dataFault) = _
  rw [written]
  rfl

private theorem exec_load (initial : X86.State) (pc currentSp sp ax value : Word) (flags : Flags)
    (memory : Memory) (k : Nat) (hk : k = 8 ∨ k = 24 ∨ k = 32 ∨ k = 40)
    (held : Ext.HoldsLE memory (sp - BitVec.ofNat 64 (8 + k)).toNat 8 value) :
    Ext.exec (.load .q .rax (slot k))
      (coreWith initial pc currentSp (sp - 8) ax flags) memory =
      .ok (coreWith initial (pc + 4) currentSp (sp - 8) value flags) memory := by
  have hl : (Ext.Instr.load .q .rax (slot k)).length = 4 := by
    rcases hk with rfl | rfl | rfl | rfl <;> decide +kernel
  have loaded := Ext.loadN_of_holdsLE_eight held
  simp only [Ext.exec, hl, Ext.readRM,
    slot_addr initial pc currentSp sp ax _ flags k hk, Ext.retire, coreWith_rip]
  change (match ((Ext.loadN memory (sp - BitVec.ofNat 64 (8 + k)) 8).map
    (fun v => v)).map (fun v => ((coreWith initial pc currentSp (sp - 8) ax flags).write .rax v, memory)) with
    | some (t, m) => Ext.Result.ok { t with rip := pc + 4 } m
    | none => Ext.Result.dataFault) = _
  rw [loaded]
  simp only [Option.map_some, coreWith_write_rax]
  rfl

private theorem exec_literal (literalValue : Word) (initial : X86.State) (pc currentSp bp ax : Word) (flags : Flags)
    (memory : Memory) :
    Ext.exec (.movabs .rax literalValue) (coreWith initial pc currentSp bp ax flags) memory =
      .ok (coreWith initial (pc + 10) currentSp bp literalValue flags) memory := by
  simp only [Ext.exec, coreWith_write_rax, Ext.retire, coreWith_rip, coreWith_set_rip]
  rfl

private theorem exec_signext (literalValue : Word) (initial : X86.State) (pc currentSp bp : Word) (flags : Flags)
    (memory : Memory)
    (normalized : (literalValue.setWidth 32).signExtend 64 = literalValue) :
    Ext.exec (.movsxd .rax (.reg .rax)) (coreWith initial pc currentSp bp literalValue flags) memory =
      .ok (coreWith initial (pc + 3) currentSp bp literalValue flags) memory := by
  simp only [Ext.exec, Ext.readRM, Ext.Sz.read, coreWith_read_rax,
    Option.map_some, Ext.retire, coreWith_rip]
  change Ext.Result.ok { (coreWith initial pc currentSp bp literalValue flags).write .rax ((literalValue.setWidth 32).signExtend 64) with
    rip := pc + 3 } memory = _
  rw [normalized, coreWith_write_rax]
  rfl

private theorem exec_jump (initial : X86.State) (pc currentSp bp ax : Word) (flags : Flags)
    (memory : Memory) :
    Ext.exec (.jmp8 0) (coreWith initial pc currentSp bp ax flags) memory =
      .ok (coreWith initial (pc + 2) currentSp bp ax flags) memory := by
  simp only [Ext.exec, coreWith_rip]
  change Ext.Result.ok { coreWith initial pc currentSp bp ax flags with rip := pc + 2 + 0 } memory = _
  rw [add_zero]
  rfl

private theorem exec_leave (initial : X86.State) (pc currentSp sp ax savedBp : Word) (flags : Flags)
    (memory : Memory)
    (saved : memory.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [savedBp])) :
    Ext.exec .leave (coreWith initial pc currentSp (sp - 8) ax flags) memory =
      .ok (coreWith initial (pc + 1) sp savedBp ax flags) memory := by
  have popped := X86.popWord_of_readBytes (s :=
    coreWith initial pc (sp - 8) (sp - 8) ax flags) (by simpa only [coreWith_read_rsp] using saved)
  simp only [Ext.exec, coreWith_read_rbp, coreWith_write_rsp, popped,
    Option.map_some, Ext.retire, coreWith_rip, coreWith_read_rsp,
    coreWith_write_rsp, coreWith_write_rbp, coreWith_set_rip]
  change Ext.Result.ok (coreWith initial (pc + 1) (sp - 8 + 8) savedBp ax flags) memory = _
  rw [sub_add_cancel]


private theorem retired_from_loaded {base exit : Word} {bytes : List Byte}
    {before after : X86.MState} {offset len : Nat} {i : Ext.Instr}
    (original : Features.State)
    (loaded : Ext.Loaded before.memory base bytes)
    (pc : before.core.rip = base + BitVec.ofNat 64 offset)
    (fits : offset + len ≤ bytes.length)
    (decoded : Ext.decode ((bytes.drop offset).take len) = some (i, len))
    (safe : Features.baseRequirement i = none) (notRet : i ≠ .ret)
    (executed : Ext.exec i before.core before.memory = .ok after.core after.memory) :
    Retires exit (lift original before) (lift original after) :=
  safe_lift_step original loaded pc fits decoded safe
    (Ext.stepOpt_of_loaded loaded pc fits decoded notRet executed)

private def stageCore (initial : X86.State) (base literalValue : Word) (stage : Nat) : X86.State :=
  let sp := initial.read .rsp
  let bp := initial.read .rbp
  let ax := initial.read .rax
  let flags := initial.flags
  match stage with
  | 0 => coreWith initial base sp bp ax flags
  | 1 => coreWith initial (base + 1) (sp - 8) bp ax flags
  | 2 => coreWith initial (base + 4) (sp - 8) (sp - 8) ax flags
  | 3 => coreWith initial (base + 8) (sp - 56) (sp - 8) ax (subFlags sp)
  | 4 => coreWith initial (base + 12) (aligned sp) (sp - 8) ax (alignedFlags sp)
  | 5 => coreWith initial (base + 15) (aligned sp) (sp - 8) (aligned sp) (alignedFlags sp)
  | 6 => coreWith initial (base + 19) (aligned sp) (sp - 8) (aligned sp) (alignedFlags sp)
  | 7 => coreWith initial (base + 21) (aligned sp) (sp - 8) (aligned sp) (alignedFlags sp)
  | 8 => coreWith initial (base + 31) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 9 => coreWith initial (base + 35) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 10 => coreWith initial (base + 39) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 11 => coreWith initial (base + 42) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 12 => coreWith initial (base + 46) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 13 => coreWith initial (base + 50) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 14 => coreWith initial (base + 53) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 15 => coreWith initial (base + 57) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | 16 => coreWith initial (base + 61) (aligned sp) (sp - 8) literalValue (alignedFlags sp)
  | _ => coreWith initial (base + 62) sp bp literalValue (alignedFlags sp)

private theorem Entry.saved_disjoint {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) {before after : Memory}
    {k : Nat} (lower : 16 ≤ k) (upper : k ≤ 48) {value savedBp : Word}
    (stored : Ext.Stored before after (initial.core.read .rsp - BitVec.ofNat 64 k).toNat
      (Ext.leBytes value 8))
    (saved : before.readBytes (initial.core.read .rsp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [savedBp])) :
    after.readBytes (initial.core.read .rsp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [savedBp]) := by
  rw [show after.readBytes (initial.core.read .rsp - 8).toNat 8 =
    before.readBytes (initial.core.read .rsp - 8).toNat 8 from
      stored.readWith_disjoint .read _ _ ?_]
  · exact saved
  · have addr : (initial.core.read .rsp - 8).toNat = (initial.core.read .rsp).toNat - 8 :=
      entry.sub_address 8 (by decide)
    rw [Ext.length_leBytes, entry.sub_address k (by omega), addr]
    right
    have := entry.stackLower
    omega


private theorem Entry.stored_exact_frame {literalValue base exit : Word} {initial : X86.MState}
    (entry : Entry literalValue base exit initial) {before after : Memory}
    (frame : initial.memory.WritesWithin before (writeFootprint (initial.core.read .rsp)))
    {k : Nat} (choice : k = 8 ∨ k = 16 ∨ k = 32 ∨ k = 40 ∨ k = 48) {value : Word}
    (stored : Ext.Stored before after (initial.core.read .rsp - BitVec.ofNat 64 k).toNat
      (Ext.leBytes value 8)) :
    initial.memory.WritesWithin after (writeFootprint (initial.core.read .rsp)) := by
  apply frame.step stored
  intro offset bound
  rw [Ext.length_leBytes] at bound
  have fits : k ≤ 128 := by rcases choice with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [entry.sub_address k fits]
  unfold writeFootprint
  have := entry.stackLower
  rcases choice with rfl | rfl | rfl | rfl | rfl <;> omega

/-- Completion of the actual 83-byte emitted integer function for arbitrary
caller state and arbitrary memory satisfying byte/permission/separation inputs.
No successful run, returned state, or result is assumed. -/
theorem execute_word {literalValue base exit : Word} (initial : NativeState)
    (normalized : (literalValue.setWidth 32).signExtend 64 = literalValue)
    (entry : Entry literalValue base exit initial.toBase) :
    ∃ before final, Relation.ReflTransGen (Retires exit) initial before ∧
      Silmaril.Compiler.Native.Correctness.step exit before = .returned final ∧
      Result literalValue exit initial final := by
  let sp : Word := initial.state.core.read .rsp
  let bp : Word := initial.state.core.read .rbp
  let ax : Word := initial.state.core.read .rax
  have frame0 : initial.memory.WritesWithin initial.memory (footprint sp) := .refl _ _
  obtain ⟨m1, w1, stored1⟩ := Ext.storeN_isSome (v := bp)
    (entry.permitted_stack frame0 .write (Or.inr rfl) 8 (by decide) (by decide))
  have frame1 : initial.memory.WritesWithin m1 (footprint sp) := entry.stored_frame frame0 (by decide : 8 ≤ 8) (by decide : 8 ≤ 48) stored1
  have image1 : Ext.Loaded m1 base (code literalValue) := entry.loaded_frame frame1
  have saved1 : m1.readBytes (sp - 8).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := by
    have held : Ext.HoldsLE m1 (sp - 8).toNat 8 bp := Ext.HoldsLE.of_stored_self stored1
      (entry.permitted_stack frame0 .read (Or.inl rfl) 8 (by decide) (by decide))
    change m1.readBytes (sp - 8).toNat 8 = some (Ext.leBytes bp 8) at held
    rw [Ext.leBytes_eight] at held
    exact held
  obtain ⟨m2, w2, stored2⟩ := Ext.storeN_isSome (v := aligned sp)
    (entry.permitted_stack frame1 .write (Or.inr rfl) 16 (by decide) (by decide))
  have frame2 : initial.memory.WritesWithin m2 (footprint sp) := entry.stored_frame frame1 (by decide : 8 ≤ 16) (by decide : 16 ≤ 48) stored2
  have image2 : Ext.Loaded m2 base (code literalValue) := entry.loaded_frame frame2
  have saved2 : m2.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := entry.saved_disjoint (by decide : 16 ≤ 16) (by decide : 16 ≤ 48) stored2 saved1
  obtain ⟨m3, w3, stored3⟩ := Ext.storeN_isSome (v := literalValue)
    (entry.permitted_stack frame2 .write (Or.inr rfl) 32 (by decide) (by decide))
  have frame3 : initial.memory.WritesWithin m3 (footprint sp) := entry.stored_frame frame2 (by decide : 8 ≤ 32) (by decide : 32 ≤ 48) stored3
  have image3 : Ext.Loaded m3 base (code literalValue) := entry.loaded_frame frame3
  have saved3 : m3.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := entry.saved_disjoint (by decide : 16 ≤ 32) (by decide : 32 ≤ 48) stored3 saved2
  have held3 : Ext.HoldsLE m3 (sp - 32).toNat 8 literalValue := Ext.HoldsLE.of_stored_self stored3
    (entry.permitted_stack frame2 .read (Or.inl rfl) 32 (by decide) (by decide))
  obtain ⟨m4, w4, stored4⟩ := Ext.storeN_isSome (v := literalValue)
    (entry.permitted_stack frame3 .write (Or.inr rfl) 40 (by decide) (by decide))
  have frame4 : initial.memory.WritesWithin m4 (footprint sp) := entry.stored_frame frame3 (by decide : 8 ≤ 40) (by decide : 40 ≤ 48) stored4
  have image4 : Ext.Loaded m4 base (code literalValue) := entry.loaded_frame frame4
  have saved4 : m4.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := entry.saved_disjoint (by decide : 16 ≤ 40) (by decide : 40 ≤ 48) stored4 saved3
  have held4 : Ext.HoldsLE m4 (sp - 40).toNat 8 literalValue := Ext.HoldsLE.of_stored_self stored4
    (entry.permitted_stack frame3 .read (Or.inl rfl) 40 (by decide) (by decide))
  obtain ⟨m5, w5, stored5⟩ := Ext.storeN_isSome (v := literalValue)
    (entry.permitted_stack frame4 .write (Or.inr rfl) 48 (by decide) (by decide))
  have frame5 : initial.memory.WritesWithin m5 (footprint sp) := entry.stored_frame frame4 (by decide : 8 ≤ 48) (by decide : 48 ≤ 48) stored5
  have image5 : Ext.Loaded m5 base (code literalValue) := entry.loaded_frame frame5
  have saved5 : m5.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := entry.saved_disjoint (by decide : 16 ≤ 48) (by decide : 48 ≤ 48) stored5 saved4
  have held5 : Ext.HoldsLE m5 (sp - 48).toNat 8 literalValue := Ext.HoldsLE.of_stored_self stored5
    (entry.permitted_stack frame4 .read (Or.inl rfl) 48 (by decide) (by decide))
  let s0 : X86.MState := ⟨stageCore initial.state.core base literalValue 0, initial.memory⟩
  let s1 : X86.MState := ⟨stageCore initial.state.core base literalValue 1, m1⟩
  have initial_eq : lift initial.state s0 = initial := by
    have core_eq : stageCore initial.state.core base literalValue 0 = initial.state.core := by
      change coreWith initial.state.core base sp bp ax initial.state.core.flags = initial.state.core
      rw [← entry.pc]
      exact coreWith_initial _
    change Features.MState.mk (initial.state.setCore (stageCore initial.state.core base literalValue 0)) initial.memory = initial
    rw [core_eq]
    cases initial
    rfl
  have t0 : Retires exit (lift initial.state s0) (lift initial.state s1) := by
    apply retired_from_loaded (before := s0) (after := s1) (offset := 0) (len := 1) (i := .push .rbp)
      initial.state entry.image (by change base = base + 0; rw [add_zero]) (by rw [code_length]; decide) (decode0 literalValue) rfl (by decide)
    simp only [s0, s1, stageCore]
    exact exec_push initial.state.core base sp bp ax initial.state.core.flags w1
  let s2 : X86.MState := ⟨stageCore initial.state.core base literalValue 2, m1⟩
  have t1 : Retires exit (lift initial.state s1) (lift initial.state s2) := by
    apply retired_from_loaded (before := s1) (after := s2) (offset := 1) (len := 3) (i := .mov .q (.reg .rbp) .rsp)
      initial.state image1 (by rfl) (by rw [code_length]; decide) (decode1 literalValue) rfl (by decide)
    have computed := exec_move_bp initial.state.core (base + 1) (sp - 8) bp ax initial.state.core.flags m1
    simp only [add_assoc] at computed
    simp only [s1, s2, stageCore]
    exact computed
  let s3 : X86.MState := ⟨stageCore initial.state.core base literalValue 3, m1⟩
  have t2 : Retires exit (lift initial.state s2) (lift initial.state s3) := by
    apply retired_from_loaded (before := s2) (after := s3) (offset := 4) (len := 4) (i := .aluI8 .q .sub (.reg .rsp) 48)
      initial.state image1 (by rfl) (by rw [code_length]; decide) (decode2 literalValue) rfl (by decide)
    have computed := exec_sub initial.state.core (base + 4) sp (sp - 8) ax initial.state.core.flags m1
    simp only [add_assoc] at computed
    simp only [s2, s3, stageCore]
    exact computed
  let s4 : X86.MState := ⟨stageCore initial.state.core base literalValue 4, m1⟩
  have t3 : Retires exit (lift initial.state s3) (lift initial.state s4) := by
    apply retired_from_loaded (before := s3) (after := s4) (offset := 8) (len := 4) (i := .aluI8 .q .and (.reg .rsp) 0xc0)
      initial.state image1 (by rfl) (by rw [code_length]; decide) (decode3 literalValue) rfl (by decide)
    have computed := exec_and initial.state.core (base + 8) sp (sp - 8) ax (subFlags sp) m1
    simp only [add_assoc] at computed
    simp only [s3, s4, stageCore]
    exact computed
  let s5 : X86.MState := ⟨stageCore initial.state.core base literalValue 5, m1⟩
  have t4 : Retires exit (lift initial.state s4) (lift initial.state s5) := by
    apply retired_from_loaded (before := s4) (after := s5) (offset := 12) (len := 3) (i := .mov .q (.reg .rax) .rsp)
      initial.state image1 (by rfl) (by rw [code_length]; decide) (decode4 literalValue) rfl (by decide)
    have computed := exec_move_ax initial.state.core (base + 12) (aligned sp) (sp - 8) ax (alignedFlags sp) m1
    simp only [add_assoc] at computed
    simp only [s4, s5, stageCore]
    exact computed
  let s6 : X86.MState := ⟨stageCore initial.state.core base literalValue 6, m2⟩
  have t5 : Retires exit (lift initial.state s5) (lift initial.state s6) := by
    apply retired_from_loaded (before := s5) (after := s6) (offset := 15) (len := 4) (i := .mov .q (.mem (slot 8)) .rax)
      initial.state image1 (by rfl) (by rw [code_length]; decide) (decode5 literalValue) rfl (by decide)
    have computed := exec_store initial.state.core (base + 15) (aligned sp) sp (aligned sp) (alignedFlags sp) 8 (Or.inl rfl) w2
    simp only [add_assoc] at computed
    simp only [s5, s6, stageCore]
    exact computed
  let s7 : X86.MState := ⟨stageCore initial.state.core base literalValue 7, m2⟩
  have t6 : Retires exit (lift initial.state s6) (lift initial.state s7) := by
    apply retired_from_loaded (before := s6) (after := s7) (offset := 19) (len := 2) (i := .jmp8 0)
      initial.state image2 (by rfl) (by rw [code_length]; decide) (decode6 literalValue) rfl (by decide)
    have computed := exec_jump initial.state.core (base + 19) (aligned sp) (sp - 8) (aligned sp) (alignedFlags sp) m2
    simp only [add_assoc] at computed
    simp only [s6, s7, stageCore]
    exact computed
  let s8 : X86.MState := ⟨stageCore initial.state.core base literalValue 8, m2⟩
  have t7 : Retires exit (lift initial.state s7) (lift initial.state s8) := by
    apply retired_from_loaded (before := s7) (after := s8) (offset := 21) (len := 10) (i := .movabs .rax literalValue)
      initial.state image2 (by rfl) (by rw [code_length]; decide) (decode7 literalValue) rfl (by intro impossible; cases impossible)
    have computed := exec_literal literalValue initial.state.core (base + 21) (aligned sp) (sp - 8) (aligned sp) (alignedFlags sp) m2
    simp only [add_assoc] at computed
    simp only [s7, s8, stageCore]
    exact computed
  let s9 : X86.MState := ⟨stageCore initial.state.core base literalValue 9, m3⟩
  have t8 : Retires exit (lift initial.state s8) (lift initial.state s9) := by
    apply retired_from_loaded (before := s8) (after := s9) (offset := 31) (len := 4) (i := .mov .q (.mem (slot 24)) .rax)
      initial.state image2 (by rfl) (by rw [code_length]; decide) (decode8 literalValue) rfl (by decide)
    have computed := exec_store initial.state.core (base + 31) (aligned sp) sp literalValue (alignedFlags sp) 24 (Or.inr (Or.inl rfl)) w3
    simp only [add_assoc] at computed
    simp only [s8, s9, stageCore]
    exact computed
  let s10 : X86.MState := ⟨stageCore initial.state.core base literalValue 10, m3⟩
  have t9 : Retires exit (lift initial.state s9) (lift initial.state s10) := by
    apply retired_from_loaded (before := s9) (after := s10) (offset := 35) (len := 4) (i := .load .q .rax (slot 24))
      initial.state image3 (by rfl) (by rw [code_length]; decide) (decode9 literalValue) rfl (by decide)
    have computed := exec_load initial.state.core (base + 35) (aligned sp) sp literalValue literalValue (alignedFlags sp) m3 24 (Or.inr (Or.inl rfl)) held3
    simp only [add_assoc] at computed
    simp only [s9, s10, stageCore]
    exact computed
  let s11 : X86.MState := ⟨stageCore initial.state.core base literalValue 11, m3⟩
  have t10 : Retires exit (lift initial.state s10) (lift initial.state s11) := by
    apply retired_from_loaded (before := s10) (after := s11) (offset := 39) (len := 3) (i := .movsxd .rax (.reg .rax))
      initial.state image3 (by rfl) (by rw [code_length]; decide) (decode10 literalValue) rfl (by decide)
    have computed := exec_signext literalValue initial.state.core (base + 39) (aligned sp) (sp - 8) (alignedFlags sp) m3 normalized
    simp only [add_assoc] at computed
    simp only [s10, s11, stageCore]
    exact computed
  let s12 : X86.MState := ⟨stageCore initial.state.core base literalValue 12, m4⟩
  have t11 : Retires exit (lift initial.state s11) (lift initial.state s12) := by
    apply retired_from_loaded (before := s11) (after := s12) (offset := 42) (len := 4) (i := .mov .q (.mem (slot 32)) .rax)
      initial.state image3 (by rfl) (by rw [code_length]; decide) (decode11 literalValue) rfl (by decide)
    have computed := exec_store initial.state.core (base + 42) (aligned sp) sp literalValue (alignedFlags sp) 32 (Or.inr (Or.inr (Or.inl rfl))) w4
    simp only [add_assoc] at computed
    simp only [s11, s12, stageCore]
    exact computed
  let s13 : X86.MState := ⟨stageCore initial.state.core base literalValue 13, m4⟩
  have t12 : Retires exit (lift initial.state s12) (lift initial.state s13) := by
    apply retired_from_loaded (before := s12) (after := s13) (offset := 46) (len := 4) (i := .load .q .rax (slot 32))
      initial.state image4 (by rfl) (by rw [code_length]; decide) (decode12 literalValue) rfl (by decide)
    have computed := exec_load initial.state.core (base + 46) (aligned sp) sp literalValue literalValue (alignedFlags sp) m4 32 (Or.inr (Or.inr (Or.inl rfl))) held4
    simp only [add_assoc] at computed
    simp only [s12, s13, stageCore]
    exact computed
  let s14 : X86.MState := ⟨stageCore initial.state.core base literalValue 14, m4⟩
  have t13 : Retires exit (lift initial.state s13) (lift initial.state s14) := by
    apply retired_from_loaded (before := s13) (after := s14) (offset := 50) (len := 3) (i := .movsxd .rax (.reg .rax))
      initial.state image4 (by rfl) (by rw [code_length]; decide) (decode13 literalValue) rfl (by decide)
    have computed := exec_signext literalValue initial.state.core (base + 50) (aligned sp) (sp - 8) (alignedFlags sp) m4 normalized
    simp only [add_assoc] at computed
    simp only [s13, s14, stageCore]
    exact computed
  let s15 : X86.MState := ⟨stageCore initial.state.core base literalValue 15, m5⟩
  have t14 : Retires exit (lift initial.state s14) (lift initial.state s15) := by
    apply retired_from_loaded (before := s14) (after := s15) (offset := 53) (len := 4) (i := .mov .q (.mem (slot 40)) .rax)
      initial.state image4 (by rfl) (by rw [code_length]; decide) (decode14 literalValue) rfl (by decide)
    have computed := exec_store initial.state.core (base + 53) (aligned sp) sp literalValue (alignedFlags sp) 40 (Or.inr (Or.inr (Or.inr rfl))) w5
    simp only [add_assoc] at computed
    simp only [s14, s15, stageCore]
    exact computed
  let s16 : X86.MState := ⟨stageCore initial.state.core base literalValue 16, m5⟩
  have t15 : Retires exit (lift initial.state s15) (lift initial.state s16) := by
    apply retired_from_loaded (before := s15) (after := s16) (offset := 57) (len := 4) (i := .load .q .rax (slot 40))
      initial.state image5 (by rfl) (by rw [code_length]; decide) (decode15 literalValue) rfl (by decide)
    have computed := exec_load initial.state.core (base + 57) (aligned sp) sp literalValue literalValue (alignedFlags sp) m5 40 (Or.inr (Or.inr (Or.inr rfl))) held5
    simp only [add_assoc] at computed
    simp only [s15, s16, stageCore]
    exact computed
  let s17 : X86.MState := ⟨stageCore initial.state.core base literalValue 17, m5⟩
  have t16 : Retires exit (lift initial.state s16) (lift initial.state s17) := by
    apply retired_from_loaded (before := s16) (after := s17) (offset := 61) (len := 1) (i := .leave)
      initial.state image5 (by rfl) (by rw [code_length]; decide) (decode16 literalValue) rfl (by decide)
    have computed := exec_leave initial.state.core (base + 61) (aligned sp) sp literalValue bp (alignedFlags sp) m5 saved5
    simp only [add_assoc] at computed
    simp only [s16, s17, stageCore]
    exact computed
  let finalBase : X86.MState :=
    ⟨coreWith initial.state.core exit (sp + 8) bp literalValue (alignedFlags sp), m5⟩
  have returnBase : Ext.step exit s17 = .returned finalBase := by
    have ret := Ext.step_returned_ret_mk (exit := exit) (m := s17)
      image5 (by rfl) (by rw [code_length]; decide : 62 + 1 ≤ (code literalValue).length)
      (decode17 literalValue)
      (by simpa only [s17, stageCore, coreWith_read_rsp, Ext.HoldsLE, Ext.leBytes_eight, Features.MState.toBase] using entry.return_frame frame5)
    simp only [s17, finalBase, stageCore, coreWith_read_rsp, coreWith_write_rsp, coreWith_set_rip] at ret ⊢
    exact ret
  have returned := safe_lift_return (before := s17) (offset := 62) (len := 1)
    initial.state image5 (by rfl) (by rw [code_length]; decide)
    (decode17 literalValue) returnBase
  have exact0 : initial.memory.WritesWithin initial.memory (writeFootprint sp) := .refl _ _
  have exact1 : initial.memory.WritesWithin m1 (writeFootprint sp) := entry.stored_exact_frame exact0 (Or.inl rfl) stored1
  have exact2 : initial.memory.WritesWithin m2 (writeFootprint sp) := entry.stored_exact_frame exact1 (Or.inr (Or.inl rfl)) stored2
  have exact3 : initial.memory.WritesWithin m3 (writeFootprint sp) := entry.stored_exact_frame exact2 (Or.inr (Or.inr (Or.inl rfl))) stored3
  have exact4 : initial.memory.WritesWithin m4 (writeFootprint sp) := entry.stored_exact_frame exact3 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) stored4
  have exact5 : initial.memory.WritesWithin m5 (writeFootprint sp) := entry.stored_exact_frame exact4 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) stored5
  have reaches : Relation.ReflTransGen (Retires exit) (lift initial.state s0) (lift initial.state s17) :=
    (((((((((((((((((Relation.ReflTransGen.single t0).trans (Relation.ReflTransGen.single t1)).trans (Relation.ReflTransGen.single t2)).trans (Relation.ReflTransGen.single t3)).trans (Relation.ReflTransGen.single t4)).trans (Relation.ReflTransGen.single t5)).trans (Relation.ReflTransGen.single t6)).trans (Relation.ReflTransGen.single t7)).trans (Relation.ReflTransGen.single t8)).trans (Relation.ReflTransGen.single t9)).trans (Relation.ReflTransGen.single t10)).trans (Relation.ReflTransGen.single t11)).trans (Relation.ReflTransGen.single t12)).trans (Relation.ReflTransGen.single t13)).trans (Relation.ReflTransGen.single t14)).trans (Relation.ReflTransGen.single t15)).trans (Relation.ReflTransGen.single t16))
  refine ⟨lift initial.state s17, lift initial.state finalBase, initial_eq ▸ reaches, returned, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, exact5⟩
  · exact coreWith_read_rsp _ _ _ _ _ _
  · exact coreWith_read_rax _ _ _ _ _ _
  · intro r hrsp hrax
    by_cases hrbp : r = .rbp
    · subst r
      exact coreWith_read_rbp _ _ _ _ _ _
    · exact coreWith_regs _ _ _ _ _ _ r hrsp hrbp hrax


/-- The actual integer-state System V return discipline. DF and x87-mode
architecture are absent from this machine, so this is not a full Ffi.Return. -/
theorem Result.sysv_return {literalValue base exit : Word} {initial final : NativeState}
    (result : Result literalValue exit initial final) :
    Silmaril.C.Api.SysV.Return ⟨base, exit, initial.toBase⟩ final.toBase := by
  refine ⟨result.pc, result.stack, ?_⟩
  intro r member
  exact result.registers r
    (by cases r <;> simp_all [Silmaril.X86.sysv64])
    (by cases r <;> simp_all [Silmaril.X86.sysv64])

theorem Result.sysv_int32 {literalValue exit : Word} {initial final : NativeState}
    (result : Result literalValue exit initial final) :
    Silmaril.C.Api.SysV.ResultAt final.toBase (some .int32) (literalValue.setWidth 32) := by
  change (final.state.core.read .rax).setWidth 32 = literalValue.setWidth 32
  rw [result.value]

theorem Result.readBytes {literalValue exit : Word} {initial final : NativeState}
    (result : Result literalValue exit initial final) {address count : Nat}
    (disjoint : ∀ offset < count, ¬ writeFootprint (initial.state.core.read .rsp) (address + offset)) :
    final.memory.readBytes address count = initial.memory.readBytes address count :=
  result.frame.readBytes disjoint

/-- Finite actual completion also excludes every stopped and infinite execution,
and determines a unique complete native state for the admitted caller. -/
theorem total_word {literalValue base exit : Word} (initial : NativeState)
    (normalized : (literalValue.setWidth 32).signExtend 64 = literalValue)
    (entry : Entry literalValue base exit initial.toBase) :
    ∃ final, Result literalValue exit initial final ∧
      ∀ observation, Realises exit initial observation ↔ observation = .returned final := by
  obtain ⟨before, final, reaches, returned, result⟩ := execute_word initial normalized entry
  exact ⟨final, result, Execution.realises_completed_iff reaches returned⟩

theorem observes_word {literalValue base exit : Word} (initial : NativeState)
    (normalized : (literalValue.setWidth 32).signExtend 64 = literalValue)
    (entry : Entry literalValue base exit initial.toBase) (observation : Observation)
    (realised : Realises exit initial observation) :
    observe observation = .exit (literalValue.toNat % 256) [] := by
  obtain ⟨final, result, all⟩ := total_word initial normalized entry
  rw [(all observation).mp realised]
  simp only [observe, result.value]


/-- The generic byte template agrees exactly with the existing literal42 image. -/
theorem code42 : code 42 = LiteralImage.code := by cbv

/-- Actual completion for any independently bounded signed32 input integer. -/
theorem execute {base exit : Word} (number : Int) (bounded : LiteralEmission.IsInt32 number)
    (initial : NativeState) (entry : Entry (BitVec.ofInt 64 number) base exit initial.toBase) :
    ∃ before final, Relation.ReflTransGen (Retires exit) initial before ∧
      step exit before = .returned final ∧ Result (BitVec.ofInt 64 number) exit initial final :=
  execute_word initial (LiteralEmission.word_normalized number bounded) entry

/-- All observations have one actual returned state on the signed32 input domain. -/
theorem total {base exit : Word} (number : Int) (bounded : LiteralEmission.IsInt32 number)
    (initial : NativeState) (entry : Entry (BitVec.ofInt 64 number) base exit initial.toBase) :
    ∃ final, Result (BitVec.ofInt 64 number) exit initial final ∧
      ∀ observation, Realises exit initial observation ↔ observation = .returned final :=
  total_word initial (LiteralEmission.word_normalized number bounded) entry

/-- The actual native process projection is the integer's modulo256 exit status. -/
theorem observes {base exit : Word} (number : Int) (bounded : LiteralEmission.IsInt32 number)
    (initial : NativeState) (entry : Entry (BitVec.ofInt 64 number) base exit initial.toBase)
    (observation : Observation) (realised : Realises exit initial observation) :
    observe observation = .exit (number % 256).toNat [] := by
  simpa only [LiteralEmission.word_status] using
    observes_word initial (LiteralEmission.word_normalized number bounded) entry observation realised

end Silmaril.Compiler.Native.Correctness.LiteralInteger
