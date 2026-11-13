module

public import Silmaril.Compiler.Native.Emit.Prologue.Defs
public import Silmaril.Compiler.Native.Emit.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Thms
public import Silmaril.X86.Ext.SymExec
public import Silmaril.X86.Ext.Store
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.Prologue
open Silmaril Silmaril.X86
open Silmaril.Process (Memory)
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

theorem render_equivalent (bytes alignment : Nat) :
    (Plan.mk bytes alignment).render = "  push rbp\n  mov rbp, rsp\n" ++
      s!"  sub rsp, {bytes}\n  and rsp, {- (alignment : Int)}\n" := rfl

theorem render_frame_equivalent (register : Nat) :
    renderFrame register = "  mov rax, rsp\n" ++ Asm.write register := rfl

theorem short_adjust (operation : Silmaril.X86.AluOp) (value : Int)
    (lower : -128 ≤ value) (upper : value ≤ 127) :
    adjust operation value = .aluI8 .q operation (.reg .rsp) (BitVec.ofInt 8 value) := by
  simp only [adjust, lower, upper, and_self, ↓reduceIte]

theorem immediate_signExtend (bits : Nat) (value : Int) (positive : 0 < bits)
    (lower : -(2 ^ (bits - 1)) ≤ value) (upper : value < 2 ^ (bits - 1)) :
    (BitVec.ofInt bits value).signExtend 64 = BitVec.ofInt 64 value := by
  simp only [BitVec.signExtend, BitVec.toInt_ofInt_eq_self positive lower upper]

theorem Executes.append {first last : List Ext.Instr} {before middle after : X86.MState}
    (earlier : Executes first before middle) (later : Executes last middle after) :
    Executes (first ++ last) before after := by
  induction earlier with
  | nil => exact later
  | cons instruction rest before next middle executed tail ih =>
    exact .cons instruction (rest ++ last) before next after executed (ih later)

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

private theorem coreWith_set_flags_rip (initial : X86.State) (pc sp bp ax next : Word)
    (flags updated : Flags) :
    { coreWith initial pc sp bp ax flags with flags := updated, rip := next } =
      coreWith initial next sp bp ax updated := rfl

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



/-- A well-formed selected plan's mask really clears all low alignment bits. -/
theorem frameAddress_aligned (plan : Plan) (valid : Valid plan) (stack : Word) :
    (frameAddress plan stack).toNat % plan.alignment = 0 := by
  obtain ⟨exponent, bounded, alignment⟩ := valid.alignment
  have positive : 0 < 2 ^ exponent := Nat.two_pow_pos exponent
  have below : 2 ^ exponent < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have natValue : (BitVec.ofNat 64 (2 ^ exponent)).toNat = 2 ^ exponent := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt below]
  have bitPositive : (0 : Word) < BitVec.ofNat 64 (2 ^ exponent) := by
    change 0 < (BitVec.ofNat 64 (2 ^ exponent)).toNat
    rw [natValue]
    exact positive
  have mask : (BitVec.ofInt 64 (-(plan.alignment : Int))).toNat = 2 ^ 64 - 2 ^ exponent := by
    rw [alignment, BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.toNat_neg_of_pos bitPositive, natValue]
  have residue : (BitVec.ofInt 64 (-(plan.alignment : Int))).toNat % 2 ^ exponent = 0 := by
    rw [mask]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub (Nat.pow_dvd_pow 2 (by omega)) (dvd_refl _))
  rw [alignment] at residue
  simp only [frameAddress, alignment, BitVec.toNat_and, Nat.and_mod_two_pow, residue, Nat.and_zero]

theorem Valid.alignment_range {plan : Plan} (valid : Valid plan) :
    1 ≤ plan.alignment ∧ plan.alignment ≤ 2147483648 := by
  obtain ⟨exponent, bounded, alignment⟩ := valid.alignment
  rw [alignment]
  exact ⟨Nat.one_le_pow _ _ (by decide), by
    have : 2 ^ exponent ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
    exact this⟩

private theorem adjust_exec (operation : Silmaril.X86.AluOp) (notCmp : operation ≠ .cmp)
    (value : Int) (lower : -2147483648 ≤ value) (upper : value < 2147483648)
    (state : X86.State) (memory : Process.Memory) :
    Ext.exec (adjust operation value) state memory =
      .ok { state.write .rsp (Ext.AluOp.resultN operation (state.read .rsp) (BitVec.ofInt 64 value)) with
        flags := Ext.AluOp.flagsN operation (state.read .rsp) (BitVec.ofInt 64 value),
        rip := state.rip + BitVec.ofNat 64 (adjust operation value).length } memory := by
  by_cases short : -128 ≤ value ∧ value ≤ 127
  · rw [short_adjust operation value short.1 short.2]
    have sign : (BitVec.ofInt 8 value).signExtend 64 = BitVec.ofInt 64 value :=
      immediate_signExtend 8 value (by decide) short.1 (by have := short.2; omega)
    simp only [Ext.exec, Ext.aluStep, Ext.readRM, Ext.writeRM, Ext.Sz.read_q, Ext.Sz.bits,
      Ext.Sz.write_q, sign, notCmp, ↓reduceIte, Option.map_some, Ext.retire]
  · have chosen : adjust operation value = .aluI .q operation (.reg .rsp) (BitVec.ofInt 32 value) := by
      unfold adjust
      exact ite_eq_right short
    rw [chosen]
    have sign : (BitVec.ofInt 32 value).signExtend 64 = BitVec.ofInt 64 value :=
      immediate_signExtend 32 value (by decide) lower upper
    simp only [Ext.exec, Ext.aluStep, Ext.readRM, Ext.writeRM, Ext.Sz.read_q, Ext.Sz.bits,
      Ext.Sz.write_q, sign, notCmp, ↓reduceIte, Option.map_some, Ext.retire]

private def subFlags (plan : Plan) (stack : Word) : Flags :=
  Ext.AluOp.flagsN .sub (stack - 8) (BitVec.ofNat 64 plan.bytes)

private def alignFlags (plan : Plan) (stack : Word) : Flags :=
  Ext.AluOp.flagsN .and (stack - 8 - BitVec.ofNat 64 plan.bytes) (BitVec.ofInt 64 (-(plan.alignment : Int)))

private theorem exec_sub (plan : Plan) (valid : Valid plan) (initial : X86.State)
    (pc stack base ax : Word) (flags : Flags) (memory : Process.Memory) :
    Ext.exec (adjust .sub plan.bytes) (coreWith initial pc (stack - 8) base ax flags) memory =
      .ok (coreWith initial (pc + BitVec.ofNat 64 (adjust .sub plan.bytes).length)
        (stack - 8 - BitVec.ofNat 64 plan.bytes) base ax (subFlags plan stack)) memory := by
  have lower : -2147483648 ≤ (plan.bytes : Int) := by omega
  have upper : (plan.bytes : Int) < 2147483648 := by exact_mod_cast valid.bytes
  have actual := adjust_exec .sub (by decide) plan.bytes lower upper
    (coreWith initial pc (stack - 8) base ax flags) memory
  simpa only [BitVec.ofInt_natCast, Ext.AluOp.resultN,
    coreWith_read_rsp, coreWith_write_rsp, coreWith_rip, coreWith_set_flags_rip, subFlags] using actual

private theorem exec_and (plan : Plan) (valid : Valid plan) (initial : X86.State)
    (pc stack base ax : Word) (flags : Flags) (memory : Process.Memory) :
    Ext.exec (adjust .and (-(plan.alignment : Int)))
        (coreWith initial pc (stack - 8 - BitVec.ofNat 64 plan.bytes) base ax flags) memory =
      .ok (coreWith initial (pc + BitVec.ofNat 64 (adjust .and (-(plan.alignment : Int))).length)
        (frameAddress plan stack) base ax (alignFlags plan stack)) memory := by
  have lower : -2147483648 ≤ -(plan.alignment : Int) := by
    have bound := valid.alignment_range.2
    omega
  have upper : -(plan.alignment : Int) < 2147483648 := by omega
  have actual := adjust_exec .and (by decide) (-(plan.alignment : Int)) lower upper
    (coreWith initial pc (stack - 8 - BitVec.ofNat 64 plan.bytes) base ax flags) memory
  simpa only [Ext.AluOp.resultN, coreWith_read_rsp,
    coreWith_write_rsp, coreWith_rip, coreWith_set_flags_rip, frameAddress, alignFlags] using actual

private theorem exec_push (initial : X86.State) (pc stack base ax : Word) (flags : Flags)
    {memory after : Process.Memory}
    (written : Ext.storeN memory (stack - 8) 8 base = some after) :
    Ext.exec (.push .rbp) (coreWith initial pc stack base ax flags) memory =
      .ok (coreWith initial (pc + 1) (stack - 8) base ax flags) after := by
  have written' : memory.writeBytes (stack - 8).toNat (Silmaril.Machine.LittleEndian.encodeWords [base]) =
      some after := by simpa only [Ext.storeN, Ext.leBytes_eight] using written
  simp only [Ext.exec, X86.pushWord, coreWith_read_rsp, coreWith_read_rbp,
    Ext.retire, coreWith_rip, coreWith_write_rsp]
  change (match (memory.writeBytes (stack - 8).toNat (Silmaril.Machine.LittleEndian.encodeWords [base])).map
    (fun after => (coreWith initial pc (stack - 8) base ax flags, after)) with
    | some (state, mem) => Ext.Result.ok { state with rip := pc + 1 } mem
    | none => Ext.Result.dataFault) = _
  rw [written']
  rfl

private theorem slot_address (initial : X86.State) (pc stack currentSp ax next : Word) (flags : Flags) :
    (slot 0).addr (coreWith initial pc currentSp (stack - 8) ax flags) next = stack - 16 := by
  simp only [slot, Ext.Mem.ofReg, Ext.Mem.addr, Ext.Base.value_reg, coreWith_read_rbp,
    Option.map_none, Option.getD_none]
  change stack - 8 + 0 + (0xfffffffffffffff8 : Word) = stack - 16
  rw [add_zero]
  have negative : (0xfffffffffffffff8 : Word) = -(8 : Word) := by decide +kernel
  rw [negative, ← sub_eq_add_neg, sub_sub]
  rfl

private theorem slot_zero : slot 0 = Ext.Mem.ofReg .rbp none (0xfffffff8 : BitVec 32) := rfl

private theorem exec_store_generic (target : Ext.Mem) (state : X86.State) {memory after : Memory}
    (length : (Ext.Instr.mov .q (.mem target) .rax).length = 4)
    (written : Ext.storeN memory (target.addr state (state.rip + 4)) 8 (state.read .rax) = some after) :
    Ext.exec (.mov .q (.mem target) .rax) state memory = .ok { state with rip := state.rip + 4 } after := by
  simp only [Ext.exec, length, Ext.writeRM, Ext.Sz.read_q, Ext.retire]
  change (match (Ext.storeN memory (target.addr state (state.rip + 4)) 8 (state.read .rax)).map
    (fun after => (state, after)) with
    | some (next, mem) => Ext.Result.ok { next with rip := state.rip + 4 } mem
    | none => Ext.Result.dataFault) = _
  rw [written]
  rfl

private theorem exec_store_frame (initial : X86.State) (pc stack currentSp ax : Word) (flags : Flags)
    {memory after : Process.Memory} (written : Ext.storeN memory (stack - 16) 8 ax = some after) :
    Ext.exec (.mov .q (.mem (slot 0)) .rax)
        (coreWith initial pc currentSp (stack - 8) ax flags) memory =
      .ok (coreWith initial (pc + 4) currentSp (stack - 8) ax flags) after := by
  have length : (Ext.Instr.mov .q (.mem (slot 0)) .rax).length = 4 := by
    rw [slot_zero]
    decide +kernel
  have actual := exec_store_generic (slot 0) (coreWith initial pc currentSp (stack - 8) ax flags)
    length (by simpa only [slot_address, coreWith_rip, coreWith_read_rax] using written)
  simpa only [coreWith_rip, coreWith_set_rip] using actual


private theorem Entry.sub_address {plan : Plan} {initial : X86.MState}
    (entry : Entry plan initial) (k : Nat) (fits : k ≤ 16) :
    (initial.core.read .rsp - BitVec.ofNat 64 k).toNat = (initial.core.read .rsp).toNat - k :=
  Ext.toNat_sub_ofNat (by have := entry.stackLower; omega) (by omega)

private theorem Entry.permitted_stack {plan : Plan} {initial : X86.MState}
    (entry : Entry plan initial) {memory : Memory}
    (frame : initial.memory.WritesWithin memory (footprint (initial.core.read .rsp)))
    (access : Process.Access) (choice : access = .read ∨ access = .write)
    (k : Nat) (lower : 8 ≤ k) (upper : k ≤ 16) :
    memory.Permitted access (initial.core.read .rsp - BitVec.ofNat 64 k).toNat 8 := by
  rw [frame.permitted_iff, entry.sub_address k upper]
  rcases choice with rfl | rfl
  · exact Ext.Memory.Permitted.sub entry.readable (by decide) (by omega)
      (by have := entry.stackLower; omega)
  · exact Ext.Memory.Permitted.sub entry.writable (by decide) (by omega)
      (by have := entry.stackLower; omega)

private theorem Entry.stored_frame {plan : Plan} {initial : X86.MState}
    (entry : Entry plan initial) {before after : Memory}
    (frame : initial.memory.WritesWithin before (footprint (initial.core.read .rsp)))
    {k : Nat} (lower : 8 ≤ k) (upper : k ≤ 16) {value : Word}
    (stored : Ext.Stored before after (initial.core.read .rsp - BitVec.ofNat 64 k).toNat
      (Ext.leBytes value 8)) :
    initial.memory.WritesWithin after (footprint (initial.core.read .rsp)) := by
  apply frame.step stored
  intro offset bound
  rw [Ext.length_leBytes] at bound
  rw [entry.sub_address k upper]
  unfold footprint
  have := entry.stackLower
  omega

private theorem Entry.saved_disjoint {plan : Plan} {initial : X86.MState}
    (entry : Entry plan initial) {before after : Memory} {value savedBp : Word}
    (stored : Ext.Stored before after (initial.core.read .rsp - 16).toNat
      (Ext.leBytes value 8))
    (saved : before.readBytes (initial.core.read .rsp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [savedBp])) :
    after.readBytes (initial.core.read .rsp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [savedBp]) := by
  rw [show after.readBytes (initial.core.read .rsp - 8).toNat 8 =
    before.readBytes (initial.core.read .rsp - 8).toNat 8 from
      stored.readWith_disjoint .read _ _ ?_]
  · exact saved
  · change (initial.core.read .rsp - BitVec.ofNat 64 8).toNat + 8 ≤
        (initial.core.read .rsp - BitVec.ofNat 64 16).toNat ∨
        (initial.core.read .rsp - BitVec.ofNat 64 16).toNat + 8 ≤
        (initial.core.read .rsp - BitVec.ofNat 64 8).toNat
    rw [entry.sub_address 16 (by decide), entry.sub_address 8 (by decide)]
    right
    have := entry.stackLower
    omega


theorem code_length (plan : Plan) :
    (plan.code 0).length =
      1 + 3 + (adjust .sub plan.bytes).length + (adjust .and (-(plan.alignment : Int))).length + 3 + 4 := by
  simp only [Plan.code, Plan.activate, Plan.instructions, frameInstructions,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
  change 1 + (3 + ((adjust .sub plan.bytes).length +
      ((adjust .and (-(plan.alignment : Int))).length + 0))) + (3 + (4 + 0)) = _
  omega

/-- Actual execution of the emitted frame prefix and reserved-frame store.
The entry supplies only metadata and stack permissions; success is derived. -/
theorem execute (plan : Plan) (initial : X86.MState) (entry : Entry plan initial) :
    ∃ final, Executes (plan.activate 0) initial final ∧ Ready plan initial final := by
  let sp := initial.core.read .rsp
  let bp := initial.core.read .rbp
  let ax := initial.core.read .rax
  let ip := initial.core.rip
  let flags := initial.core.flags
  let address := frameAddress plan sp
  have aligned : address.toNat % plan.alignment = 0 := frameAddress_aligned plan entry.valid sp
  let p1 := ip + 1
  let p2 := p1 + 3
  let p3 := p2 + BitVec.ofNat 64 (adjust .sub plan.bytes).length
  let p4 := p3 + BitVec.ofNat 64 (adjust .and (-(plan.alignment : Int))).length
  let p5 := p4 + 3
  let p6 := p5 + 4
  have advance : p6 = ip + BitVec.ofNat 64 (plan.code 0).length := by
    rw [code_length]
    simp only [p6, p5, p4, p3, p2, p1, BitVec.ofNat_add]
    ac_rfl
  have frame0 : initial.memory.WritesWithin initial.memory (footprint sp) := .refl _ _
  let c1 := coreWith initial.core p1 (sp - 8) bp ax flags
  let c2 := coreWith initial.core p2 (sp - 8) (sp - 8) ax flags
  let c3 := coreWith initial.core p3 (sp - 8 - BitVec.ofNat 64 plan.bytes) (sp - 8) ax (subFlags plan sp)
  let c4 := coreWith initial.core p4 address (sp - 8) ax (alignFlags plan sp)
  let c5 := coreWith initial.core p5 address (sp - 8) address (alignFlags plan sp)
  let c6 := coreWith initial.core p6 address (sp - 8) address (alignFlags plan sp)
  obtain ⟨m1, w1, stored1⟩ := Ext.storeN_isSome (v := bp)
    (entry.permitted_stack frame0 .write (Or.inr rfl) 8 (by decide) (by decide))
  have frame1 : initial.memory.WritesWithin m1 (footprint sp) :=
    entry.stored_frame frame0 (by decide : 8 ≤ 8) (by decide : 8 ≤ 16) stored1
  have saved1 : m1.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := by
    have held : Ext.HoldsLE m1 (sp - 8).toNat 8 bp := Ext.HoldsLE.of_stored_self stored1
      (entry.permitted_stack frame0 .read (Or.inl rfl) 8 (by decide) (by decide))
    change m1.readBytes (sp - 8).toNat 8 = some (Ext.leBytes bp 8) at held
    simpa only [Ext.leBytes_eight] using held
  obtain ⟨m2, w2, stored2⟩ := Ext.storeN_isSome (v := address)
    (entry.permitted_stack frame1 .write (Or.inr rfl) 16 (by decide) (by decide))
  have frame2 : initial.memory.WritesWithin m2 (footprint sp) :=
    entry.stored_frame frame1 (by decide : 8 ≤ 16) (by decide : 16 ≤ 16) stored2
  have saved2 : m2.readBytes (sp - 8).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [bp]) := entry.saved_disjoint stored2 saved1
  have reserved2 : m2.readBytes (sp - 16).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [address]) := by
    have held : Ext.HoldsLE m2 (sp - 16).toNat 8 address := Ext.HoldsLE.of_stored_self stored2
      (entry.permitted_stack frame1 .read (Or.inl rfl) 16 (by decide) (by decide))
    change m2.readBytes (sp - 16).toNat 8 = some (Ext.leBytes address 8) at held
    simpa only [Ext.leBytes_eight] using held
  have e1 : Ext.exec (.push .rbp) initial.core initial.memory = .ok c1 m1 := by
    have actual : Ext.exec (.push .rbp) (coreWith initial.core ip sp bp ax flags) initial.memory =
        .ok c1 m1 := exec_push initial.core ip sp bp ax flags w1
    simpa only [ip, sp, bp, ax, flags, coreWith_initial] using actual
  have e2 : Ext.exec (.mov .q (.reg .rbp) .rsp) c1 m1 = .ok c2 m1 :=
    exec_move_bp initial.core p1 (sp - 8) bp ax flags m1
  have e3 : Ext.exec (adjust .sub plan.bytes) c2 m1 = .ok c3 m1 :=
    exec_sub plan entry.valid initial.core p2 sp (sp - 8) ax flags m1
  have e4 : Ext.exec (adjust .and (-(plan.alignment : Int))) c3 m1 = .ok c4 m1 :=
    exec_and plan entry.valid initial.core p3 sp (sp - 8) ax (subFlags plan sp) m1
  have e5 : Ext.exec (.mov .q (.reg .rax) .rsp) c4 m1 = .ok c5 m1 :=
    exec_move_ax initial.core p4 address (sp - 8) ax (alignFlags plan sp) m1
  have e6 : Ext.exec (.mov .q (.mem (slot 0)) .rax) c5 m1 = .ok c6 m2 :=
    exec_store_frame initial.core p5 sp address address (alignFlags plan sp) w2
  refine ⟨⟨c6, m2⟩, ?_, ?_⟩
  · exact .cons _ _ initial ⟨c1, m1⟩ _ e1
      (.cons _ _ ⟨c1, m1⟩ ⟨c2, m1⟩ _ e2
      (.cons _ _ ⟨c2, m1⟩ ⟨c3, m1⟩ _ e3
      (.cons _ _ ⟨c3, m1⟩ ⟨c4, m1⟩ _ e4
      (.cons _ _ ⟨c4, m1⟩ ⟨c5, m1⟩ _ e5
      (.cons _ _ ⟨c5, m1⟩ ⟨c6, m2⟩ _ e6 (.nil _))))))
  · show Ready plan initial ⟨c6, m2⟩
    refine ⟨advance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, frame2⟩
    · exact aligned
    · exact coreWith_read_rsp _ _ _ _ _ _
    · exact coreWith_read_rbp _ _ _ _ _ _
    · exact coreWith_read_rax _ _ _ _ _ _
    · rw [← entry.sub_address 8 (by decide)]
      exact saved2
    · rw [← entry.sub_address 16 (by decide)]
      exact reserved2
    · exact coreWith_regs _ _ _ _ _ _


/-- The actual physical slot contains exactly the word supplied to the open
reserved-address instruction. Other memory/call interpretations stay explicit. -/
theorem Ready.reserved_realized {plan : Plan} {initial final : X86.MState}
    (ready : Ready plan initial final) (artifact : Silmaril.Compiler.Native.Artifact)
    (environment : Silmaril.Compiler.Native.Semantics.OpenFrame.Environment)
    (frame : Silmaril.Machine.Lir.Frame Nat) (memory : Silmaril.Machine.Lir.Memory) :
    Silmaril.Compiler.Native.Optimize.InstructionExec
      (Silmaril.Compiler.Native.Semantics.OpenFrame.calls artifact
        { environment with frameAddress := final.core.read .rsp })
      (.addr 0 "__ccomp_frame" 0) frame memory
      (frame.set 0 (final.core.read .rsp)) memory ∧
    final.memory.readBytes ((initial.core.read .rsp).toNat - 16) 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [final.core.read .rsp]) := by
  refine ⟨.addr (Silmaril.Compiler.Native.Semantics.OpenFrame.reserved_address _ _ _), ?_⟩
  simpa only [ready.stack] using ready.reserved

private def additionCallPlan : Silmaril.Machine.SystemV.Abi.CallPlan :=
  { arguments := [], result := .direct [⟨0, 4, .gp .rax⟩],
    stackSize := 0, stackAlign := 16, gpUsed := 0, vectorUsed := 0, variadicAL := none }

/-- Independently computed validity of the real unoptimized addition frame. -/
theorem addition_valid : Valid ⟨96, 64⟩ :=
  ⟨by decide +kernel, ⟨6, by decide +kernel, by decide +kernel⟩⟩

/-- Actual Artifact function metadata, shared ABI plan, Emit.frame and all-call
alignment fold select this plan. No compiler success is an input. -/
theorem addition_selected (left right : Silmaril.Machine.Lir.Word) :
    let artifact := Silmaril.Compiler.Native.Correctness.AdditionLower.artifact left right
    let function := Silmaril.Compiler.Native.Correctness.AdditionLower.function left right
    ∃ info abi,
      artifact.functions.find? (·.name == function.name) = some info ∧
      Emit.functionPlan info = .ok abi ∧
      (do
        let fr := Emit.frame function info abi
        let alignment ← artifact.calls.foldlM (fun alignment call => do
          return max alignment (← Emit.callPlan call).stackAlign) fr.alignment
        pure (Plan.mk fr.bytes alignment)) = Except.ok ⟨96, 64⟩ := by
  let info := (Silmaril.Compiler.Native.Correctness.AdditionLower.artifact left right).functions[0]'(by
    change 0 < 1
    decide)
  refine ⟨info, additionCallPlan, rfl, rfl, ?_⟩
  have framed : Emit.frame (Silmaril.Compiler.Native.Correctness.AdditionLower.function left right)
      info additionCallPlan = ⟨96, 64, [], 0⟩ := by
    simp [Emit.frame, info, additionCallPlan,
      Silmaril.Compiler.Native.Correctness.AdditionLower.function,
      Silmaril.Compiler.Native.Correctness.AdditionLower.artifact,
      Silmaril.Compiler.Native.Optimize.freshBase,
      Silmaril.Compiler.Native.Optimize.uses, Silmaril.Compiler.Native.Optimize.defs,
      Silmaril.Compiler.Native.Correctness.AdditionLower.prologue,
      Silmaril.Compiler.Native.Correctness.AdditionLower.body,
      Silmaril.Compiler.Native.Correctness.AdditionLower.fallback,
      Silmaril.Compile.Mir.DeadCode.termUses, Silmaril.Compile.Mir.DeadCode.opUses,
      Silmaril.Compile.Mir.DeadCode.opDef, Emit.aggregate, Silmaril.Machine.SystemV.Abi.alignUp]
  dsimp only
  rw [framed]
  rfl

end Silmaril.Compiler.Native.Emit.Prologue
