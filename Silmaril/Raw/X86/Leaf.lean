module

public import Silmaril.X86.Machine

/-!
# An addition leaf and its caller on the memory-backed x86-64 machine

The leaf is the seven bytes `48 89 F8 48 01 F0 C3`, that is
`mov rax, rdi; add rax, rsi; ret`, placed at an arbitrary address. For every
state whose memory can fetch exactly these bytes at RIP and read an
eight-byte return address at RSP, `leaf_returns` proves that the machine
reaches that return address with `rax = rdi + rsi` (modulo `2^64`), RSP
increased by eight, the flags of the addition, every register other than RAX and
RSP unchanged (in particular the System V callee-saved RBX, RBP and R12–R15),
and memory unchanged.

`caller_returns` adds a caller `call rel32; ret` that reaches the leaf through a
real eight-byte stack write, returns into the caller and returns again. Memory
changes only in the eight bytes of the pushed return address.

`initial` builds concrete states for arbitrary inputs, over a well-formed
memory with the code in a readable, executable, non-writable page and the stack
in a readable, writable, non-executable region. `initial_leafEntry` and
`initial_callerEntry` prove that they satisfy the premises, and
`exists_leaf_run` and `exists_caller_run` combine this with the two theorems.

The premises do not require the stack to be aligned as the System V ABI demands;
the model has no alignment checks. The code bytes are placed in memory by hand:
they are not taken from assembled objects or a linked ELF, and no relocation is
involved. All results are about the local handwritten model of `Machine.lean`
and `Stack.lean`, not about the Sail, ACL2 or any hardware description.
-/

@[expose] public section

namespace Silmaril.X86.Leaf

open Silmaril.Process (Memory Region)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine.Execution (run run_succ run_zero)

/-- `mov rax, rdi; add rax, rsi; ret`. -/
def code : List Insn := [.base (.movRR .rax .rdi), .base (.alu .add .rax .rsi), .ret]

/-- The exact bytes of the leaf. -/
def bytes : List Byte := [0x48, 0x89, 0xF8, 0x48, 0x01, 0xF0, 0xC3]

theorem bytes_eq_encode : bytes = code.flatMap Insn.encode := by decide

/-- The System V AMD64 callee-saved general-purpose registers other than RSP. -/
def calleeSaved : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Premises for entering the leaf at `entry` with return address `ret`: RIP is
at the leaf, its seven bytes can be fetched there, and the eight bytes at RSP
can be read and hold `ret`. -/
structure Entry (m : MState) (entry ret : Word) : Prop where
  rip : m.core.rip = entry
  code : m.memory.fetchBytes entry.toNat 7 = some bytes
  stack : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [ret])

/-! ## Arithmetic helpers -/

private theorem toNat_add_ofNat {x : Word} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

private theorem fetch_bound {memory : Memory} {address length : Nat} {bytes : List Byte}
    (h : memory.fetchBytes address length = some bytes) : address + length ≤ 2 ^ 64 := by
  have := Memory.readWith_permitted h
  rw [Memory.Permitted, Memory.checkSpan_iff] at this
  exact this.2.1

private theorem fetchBytes_slice {memory : Memory} {address length : Nat} {bytes : List Byte}
    (h : memory.fetchBytes address length = some bytes)
    (offset count : Nat) (positive : 0 < count) (bound : offset + count ≤ length) :
    memory.fetchBytes (address + offset) count = some ((bytes.drop offset).take count) :=
  Memory.readWith_slice h offset count positive bound

/-! ## The leaf -/

/-- The core state after the two arithmetic instructions. -/
def body (s : State) : State := X86.step (.alu .add .rax .rsi) (X86.step (.movRR .rax .rdi) s)

/-- The state after the leaf's RET, given the incoming state and the popped address. -/
def after (m : MState) (ret : Word) : MState :=
  ⟨{ (body m.core).write .rsp (m.core.read .rsp + 8#64) with rip := ret }, m.memory⟩

theorem body_read_rax (s : State) : (body s).read .rax = s.read .rdi + s.read .rsi := by
  unfold body
  rw [step_alu_read_dst _ _ _ _ (by decide), step_movRR_read_dst,
    step_read_other _ _ _ (by simp [Instr.dest?])]
  rfl

theorem body_read_other (s : State) (r : Reg) (h : r ≠ .rax) : (body s).read r = s.read r := by
  unfold body
  rw [step_read_other _ _ _ (by simp [Instr.dest?, Ne.symm h]),
    step_read_other _ _ _ (by simp [Instr.dest?, Ne.symm h])]

theorem body_rip (s : State) : (body s).rip = s.rip + 6#64 := by
  simp only [body, step_rip, Instr.length, BitVec.add_assoc]
  rfl

theorem body_flags (s : State) : (body s).flags = addFlags (s.read .rdi) (s.read .rsi) := by
  simp only [body, step_alu_flags, step_movRR_read_dst]
  rw [step_read_other _ _ _ (by simp [Instr.dest?])]
  rfl

theorem after_read_rax (m : MState) (ret : Word) :
    (after m ret).core.read .rax = m.core.read .rdi + m.core.read .rsi := by
  simp only [after]
  rw [show ({ (body m.core).write .rsp (m.core.read .rsp + 8#64) with rip := ret } : State).read
      .rax = ((body m.core).write .rsp (m.core.read .rsp + 8#64)).read .rax from rfl,
    State.read_write_other _ _ _ _ (by decide), body_read_rax]

theorem after_read_rsp (m : MState) (ret : Word) :
    (after m ret).core.read .rsp = m.core.read .rsp + 8#64 := by
  simp [after, State.read, State.write]

theorem after_read_other (m : MState) (ret : Word) (r : Reg) (hax : r ≠ .rax) (hsp : r ≠ .rsp) :
    (after m ret).core.read r = m.core.read r := by
  simp only [after]
  rw [show ({ (body m.core).write .rsp (m.core.read .rsp + 8#64) with rip := ret } : State).read
      r = ((body m.core).write .rsp (m.core.read .rsp + 8#64)).read r from rfl,
    State.read_write_other _ _ _ _ hsp, body_read_other _ _ hax]

theorem after_flags (m : MState) (ret : Word) :
    (after m ret).core.flags = addFlags (m.core.read .rdi) (m.core.read .rsi) := by
  simp only [after]
  exact body_flags m.core

/-- The leaf's three instructions for any designated exit: two retirements, then
a RET to `ret`, which reports `returned` exactly when `ret = exit`. -/
theorem leaf_steps (exit : Word) {m : MState} {entry ret : Word} (h : Entry m entry ret) :
    ∃ mid, run (MState.stepOpt exit) 2 m = some mid ∧
      MState.step exit mid =
        if ret = exit then .returned (after m ret) else .retired (after m ret) := by
  have bound := fetch_bound h.code
  -- mov rax, rdi
  have f1 : m.memory.fetchBytes m.core.rip.toNat 3 = some [0x48, 0x89, 0xF8] := by
    have := fetchBytes_slice h.code 0 3 (by omega) (by omega)
    rw [h.rip]
    simpa [bytes] using this
  have s1 := MState.stepOpt_of_exec (exit := exit) (instr := .base (.movRR .rax .rdi)) f1
    (by decide) (Insn.exec_base _ _ _)
    (by simp)
  -- add rax, rsi
  set m1 : MState := ⟨X86.step (.movRR .rax .rdi) m.core, m.memory⟩ with hm1
  have rip1 : m1.core.rip.toNat = entry.toNat + 3 := by
    simp only [hm1, step_rip, h.rip, Instr.length]
    exact toNat_add_ofNat (by omega)
  have f2 : m1.memory.fetchBytes m1.core.rip.toNat 3 = some [0x48, 0x01, 0xF0] := by
    have := fetchBytes_slice h.code 3 3 (by omega) (by omega)
    rw [rip1]
    simpa [bytes] using this
  have s2 := MState.stepOpt_of_exec (exit := exit) (instr := .base (.alu .add .rax .rsi)) f2
    (by decide) (Insn.exec_base _ _ _)
    (by simp)
  -- ret
  set m2 : MState := ⟨body m.core, m.memory⟩ with hm2
  have rip2 : m2.core.rip.toNat = entry.toNat + 6 := by
    simp only [hm2, body_rip, h.rip]
    exact toNat_add_ofNat (by omega)
  have f3 : m2.memory.fetchBytes m2.core.rip.toNat 1 = some [0xC3] := by
    have := fetchBytes_slice h.code 6 1 (by omega) (by omega)
    rw [rip2]
    simpa [bytes] using this
  have sp2 : m2.core.read .rsp = m.core.read .rsp := body_read_other _ _ (by decide)
  have pop : popWord m2.core m2.memory = some (ret, m2.core.write .rsp (m.core.read .rsp + 8#64)) := by
    rw [popWord_of_readBytes (by rw [sp2]; exact h.stack), sp2]
  have e3 : Insn.ret.exec m2.core m2.memory = some ((after m ret).core, (after m ret).memory) := by
    simp only [Insn.exec, pop, Option.map_some]
    rfl
  refine ⟨m2, ?_, ?_⟩
  · simp only [run_succ, s1, Option.bind_some]
    rw [s2]
    rfl
  · rw [MState.step_of_exec (instr := .ret) f3 (by decide) e3]
    by_cases hret : ret = exit
    · simp [hret, after]
    · simp [hret, after]


/-- **The leaf returns.** From any state that can fetch the leaf's bytes at RIP
and read the return address `ret` at RSP, the machine retires two instructions
and then returns to `ret`, with `rax = rdi + rsi` modulo `2^64`, RSP increased by
eight, the flags of the addition, every other register unchanged and memory
unchanged. -/
theorem leaf_returns {m : MState} {entry ret : Word} (h : Entry m entry ret) :
    ∃ final, MState.Returns ret m final ∧
      final.core.rip = ret ∧
      final.core.read .rax = m.core.read .rdi + m.core.read .rsi ∧
      (final.core.read .rax).toNat =
        ((m.core.read .rdi).toNat + (m.core.read .rsi).toNat) % 2 ^ 64 ∧
      final.core.read .rsp = m.core.read .rsp + 8#64 ∧
      final.core.flags = addFlags (m.core.read .rdi) (m.core.read .rsi) ∧
      (∀ r, r ≠ .rax → r ≠ .rsp → final.core.read r = m.core.read r) ∧
      final.memory = m.memory := by
  obtain ⟨mid, hrun, hstep⟩ := leaf_steps ret h
  refine ⟨after m ret, ⟨2, mid, hrun, by simpa using hstep⟩, rfl, after_read_rax m ret, ?_,
    after_read_rsp m ret, after_flags m ret, after_read_other m ret, rfl⟩
  rw [after_read_rax, BitVec.toNat_add]

/-- The leaf preserves the callee-saved registers. -/
theorem leaf_preserves_calleeSaved {m : MState} {entry ret : Word} (h : Entry m entry ret) :
    ∃ final, MState.Returns ret m final ∧
      ∀ r ∈ calleeSaved, final.core.read r = m.core.read r := by
  obtain ⟨final, hret, -, -, -, -, -, hother, -⟩ := leaf_returns h
  refine ⟨final, hret, fun r hr => hother r ?_ ?_⟩ <;>
    (simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## A caller: `call rel32; ret` -/

/-- The bytes of `call rel; ret`. -/
def callerBytes (rel : BitVec 32) : List Byte := Insn.encode (.call rel) ++ Insn.encode .ret

/-- Premises for entering the caller at `caller`, which calls the leaf at `leaf`
and whose own return address is `exit`. The pushed return-address slot, eight
bytes below RSP, must be readable and writable and must not overlap either code
sequence; the caller's return address must differ from `exit`. -/
structure CallerEntry (m : MState) (caller leaf exit : Word) (rel : BitVec 32) : Prop where
  rip : m.core.rip = caller
  callerCode : m.memory.fetchBytes caller.toNat 6 = some (callerBytes rel)
  target : caller + 5#64 + rel.signExtend 64 = leaf
  leafCode : m.memory.fetchBytes leaf.toNat 7 = some bytes
  stack : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [exit])
  slotWritable : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8
  slotReadable : m.memory.Permitted .read (m.core.read .rsp - 8#64).toNat 8
  callerApart : caller.toNat + 6 ≤ (m.core.read .rsp - 8#64).toNat ∨
    (m.core.read .rsp - 8#64).toNat + 8 ≤ caller.toNat
  leafApart : leaf.toNat + 7 ≤ (m.core.read .rsp - 8#64).toNat ∨
    (m.core.read .rsp - 8#64).toNat + 8 ≤ leaf.toNat
  exit_ne : exit ≠ caller + 5#64

/-- The slot below RSP and the eight bytes at RSP never overlap. -/
private theorem slot_apart (sp : Word) :
    (sp - 8#64).toNat + 8 ≤ sp.toNat ∨ sp.toNat + 8 ≤ (sp - 8#64).toNat := by
  have hsp := sp.isLt
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- A RET at RIP with `v` at RSP. -/
private theorem ret_exec {m : MState} {v : Word}
    (stack : m.memory.readBytes (m.core.read .rsp).toNat 8 = some (encodeWords [v])) :
    Insn.ret.exec m.core m.memory =
      some ({ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := v }, m.memory) := by
  simp only [Insn.exec, popWord_of_readBytes stack, Option.map_some]

/-- **Caller, leaf and return.** From any state satisfying `CallerEntry`, the
machine executes CALL (a real eight-byte stack write), the leaf's MOV, ADD and
RET (returning into the caller), and the caller's RET, which returns to `exit`
with `rax = rdi + rsi`, RSP increased by eight, the flags of the addition and
every other register unchanged. Memory changes only in the eight-byte slot
below the incoming RSP, which holds the caller's return address. -/
theorem caller_returns {m : MState} {caller leaf exit : Word} {rel : BitVec 32}
    (h : CallerEntry m caller leaf exit rel) :
    ∃ final, (∃ mid, run (MState.stepOpt exit) 4 m = some mid ∧
        MState.step exit mid = .returned final) ∧
      final.core.rip = exit ∧
      final.core.read .rax = m.core.read .rdi + m.core.read .rsi ∧
      final.core.read .rsp = m.core.read .rsp + 8#64 ∧
      final.core.flags = addFlags (m.core.read .rdi) (m.core.read .rsi) ∧
      (∀ r, r ≠ .rax → r ≠ .rsp → final.core.read r = m.core.read r) ∧
      Memory.WritesOnly m.memory final.memory (m.core.read .rsp - 8#64).toNat 8 ∧
      final.memory.readBytes (m.core.read .rsp - 8#64).toNat 8 =
        some (encodeWords [caller + 5#64]) := by
  set sp := m.core.read .rsp with hsp
  have callerBound := fetch_bound h.callerCode
  -- call rel
  have f0 : m.memory.fetchBytes m.core.rip.toNat 5 = some (Insn.encode (.call rel)) := by
    have := fetchBytes_slice h.callerCode 0 5 (by omega) (by omega)
    rw [h.rip]
    simpa [callerBytes, Insn.encode, imm32Bytes] using this
  obtain ⟨core1, mem1, hpush⟩ : ∃ core1 mem1,
      pushWord m.core m.memory (m.core.rip + BitVec.ofNat 64 (Insn.call rel).length) =
        some (core1, mem1) := ⟨_, _, pushWord_eq_some h.slotWritable⟩
  have hcore1 := pushWord_state hpush
  have frame1 := pushWord_writesOnly hpush
  have slot1 := pushWord_readBytes hpush h.slotReadable
  set m1 : MState := ⟨{ core1 with
    rip := (m.core.rip + BitVec.ofNat 64 (Insn.call rel).length + rel.signExtend 64) }, mem1⟩
    with hm1
  have e0 : (Insn.call rel).exec m.core m.memory = some (m1.core, m1.memory) := by
    simp only [Insn.exec, hpush, Option.map_some, hm1]
  have s0 := MState.stepOpt_of_exec (exit := exit) f0 (Insn.decode_encode _) e0 (by simp)
  -- the leaf, returning into the caller
  have next : m.core.rip + BitVec.ofNat 64 (Insn.call rel).length = caller + 5#64 := by
    rw [h.rip]; rfl
  have entry1 : Entry m1 leaf (caller + 5#64) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hm1, next, h.target]
    · rw [show m1.memory = mem1 from rfl, ← h.leafCode]
      exact Memory.readWith_writesOnly frame1 _ _ _ h.leafApart
    · have : m1.core.read .rsp = sp - 8#64 := by
        simp [hm1, hcore1, State.read, State.write, hsp]
      rw [this, ← next]
      simpa [hsp] using slot1
  obtain ⟨mid, hrun, hstep⟩ := leaf_steps exit entry1
  have hne : ¬ (caller + 5#64 = exit) := fun e => h.exit_ne e.symm
  simp only [hne, ite_false] at hstep
  have s3 : MState.stepOpt exit mid = some (after m1 (caller + 5#64)) :=
    MState.stepOpt_eq_some_iff.mpr hstep
  -- the caller's ret
  set m3 := after m1 (caller + 5#64) with hm3
  have codeKept : mem1.fetchBytes caller.toNat 6 = some (callerBytes rel) := by
    rw [← h.callerCode]
    exact Memory.readWith_writesOnly frame1 _ _ _ h.callerApart
  have f4 : m3.memory.fetchBytes m3.core.rip.toNat 1 = some [0xC3] := by
    have := fetchBytes_slice codeKept 5 1 (by omega) (by omega)
    have rip3 : m3.core.rip.toNat = caller.toNat + 5 := toNat_add_ofNat (by omega)
    rw [rip3]
    show mem1.fetchBytes _ 1 = _
    simpa [callerBytes, Insn.encode, imm32Bytes] using this
  have sp3 : m3.core.read .rsp = sp := by
    rw [hm3, after_read_rsp]
    simp [hm1, hcore1, State.read, State.write, hsp]
  have stack3 : m3.memory.readBytes (m3.core.read .rsp).toNat 8 = some (encodeWords [exit]) := by
    rw [sp3, show m3.memory = mem1 from rfl, ← h.stack]
    exact Memory.readWith_writesOnly frame1 _ _ _ (slot_apart sp).symm
  have e4 := ret_exec stack3
  set final : MState := ⟨{ m3.core.write .rsp (m3.core.read .rsp + 8#64) with rip := exit },
    m3.memory⟩ with hfinal
  have s4 : MState.step exit m3 = .returned final :=
    MState.step_returned_of_exec f4 (by decide) e4 rfl
  have hrun4 : run (MState.stepOpt exit) 4 m = some m3 := by
    have first : run (MState.stepOpt exit) 4 m = run (MState.stepOpt exit) (2 + 1) m1 := by
      rw [run_succ, s0]
      rfl
    rw [first, Machine.Execution.run_add, hrun]
    simp only [Option.bind_some, run_succ, s3, run_zero]
  -- register facts
  have m1_other : ∀ r, r ≠ .rsp → m1.core.read r = m.core.read r := by
    intro r hr
    simp [hm1, hcore1, State.read, State.write, Machine.RegisterFile.write, hr]
  have final_other : ∀ r, r ≠ .rsp → final.core.read r = m3.core.read r := by
    intro r hr
    simp [hfinal, State.read, State.write, Machine.RegisterFile.write, hr]
  refine ⟨final, ⟨m3, hrun4, s4⟩, rfl, ?_, ?_, ?_, ?_, frame1, ?_⟩
  · rw [final_other _ (by decide), hm3, after_read_rax, m1_other _ (by decide),
      m1_other _ (by decide)]
  · rw [← sp3]
    simp [hfinal, State.read, State.write]
  · rw [show final.core.flags = m3.core.flags from rfl, hm3, after_flags,
      m1_other _ (by decide), m1_other _ (by decide)]
  · intro r hax hsp'
    rw [final_other _ hsp', hm3, after_read_other _ _ _ hax hsp', m1_other _ hsp']
  · rw [next] at slot1
    exact slot1


/-! ## Concrete entry states -/

/-- A 4 KiB readable, executable, non-writable code page at `0x401000`. -/
def codeRegion : Region := ⟨0x401000, 0x1000, ⟨true, false, true⟩⟩

/-- A 64 KiB readable, writable, non-executable stack at `0x7fff0000`. -/
def stackRegion : Region := ⟨0x7fff0000, 0x10000, ⟨true, true, false⟩⟩

def callerAddress : Word := 0x401000
def leafAddress : Word := 0x401010
/-- The CALL displacement from the end of the CALL (`0x401005`) to the leaf. -/
def callRel : BitVec 32 := 0x0B
/-- The return address stored at RSP on entry; only its value is used. -/
def exitAddress : Word := 0x401800
def stackPointer : Word := 0x7fffffe8

/-- Both regions, with every mapped byte backed by zero. -/
def zeroMemory : Memory where
  regions := [codeRegion, stackRegion]
  bytes := Memory.install (Memory.install ∅ 0x401000 (List.replicate 0x1000 0))
    0x7fff0000 (List.replicate 0x10000 0)

/-- The caller at `0x401000` and the leaf at `0x401010`. -/
def codeMemory : Memory :=
  { zeroMemory with
    bytes := Memory.install (Memory.install zeroMemory.bytes 0x401000 (callerBytes callRel))
      0x401010 bytes }

/-- The code, and `exitAddress` stored at `stackPointer`. -/
def initialMemory : Memory :=
  { codeMemory with
    bytes := Memory.install codeMemory.bytes stackPointer.toNat (encodeWords [exitAddress]) }

/-- An entry state at `entry` with arguments `a` in RDI and `b` in RSI and RSP at
`stackPointer`; every other register and the flags are taken from `core`. -/
def initial (core : State) (a b entry : Word) : MState :=
  ⟨{ ((core.write .rdi a).write .rsi b).write .rsp stackPointer with rip := entry },
    initialMemory⟩

theorem zeroMemory_regions : zeroMemory.regions = [codeRegion, stackRegion] := rfl
theorem codeMemory_regions : codeMemory.regions = [codeRegion, stackRegion] := rfl
theorem initialMemory_regions : initialMemory.regions = [codeRegion, stackRegion] := rfl

theorem zeroMemory_bytes : zeroMemory.bytes =
    Memory.install (Memory.install ∅ 0x401000 (List.replicate 0x1000 0))
      0x7fff0000 (List.replicate 0x10000 0) := rfl
theorem codeMemory_bytes : codeMemory.bytes =
    Memory.install (Memory.install zeroMemory.bytes 0x401000 (callerBytes callRel))
      0x401010 bytes := rfl
theorem initialMemory_bytes : initialMemory.bytes =
    Memory.install codeMemory.bytes stackPointer.toNat (encodeWords [exitAddress]) := rfl

theorem zeroMemory_wellFormed : zeroMemory.WellFormed 4096 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro region member
    rw [zeroMemory_regions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [codeRegion, stackRegion, Process.addressLimit]
  · rw [zeroMemory_regions]
    simp [codeRegion, stackRegion, Region.Disjoint]
  · intro region member address inside
    rw [zeroMemory_regions] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [zeroMemory_bytes]
    rcases member with rfl | rfl
    · simp only [codeRegion, Region.Contains] at inside
      rw [Memory.install_outside _ _ _ _ (by rw [List.length_replicate]; omega)]
      have := Memory.install_get (∅ : Process.ByteMemory) 0x401000 (List.replicate 0x1000 0)
        (address - 0x401000) (by rw [List.length_replicate]; omega)
      rw [show 0x401000 + (address - 0x401000) = address by omega] at this
      rw [this]
      rfl
    · simp only [stackRegion, Region.Contains] at inside
      have := Memory.install_get (Memory.install ∅ 0x401000 (List.replicate 0x1000 0))
        0x7fff0000 (List.replicate 0x10000 0) (address - 0x7fff0000)
        (by rw [List.length_replicate]; omega)
      rw [show 0x7fff0000 + (address - 0x7fff0000) = address by omega] at this
      rw [this]
      rfl

/-- The concrete memory is well formed for 4 KiB pages. -/
theorem initialMemory_wellFormed : initialMemory.WellFormed 4096 := by
  have h1 := Memory.install_wellFormed zeroMemory_wellFormed 0x401000 (callerBytes callRel)
  have h2 := Memory.install_wellFormed h1 0x401010 bytes
  exact Memory.install_wellFormed h2 stackPointer.toNat (encodeWords [exitAddress])

/-- The code page is not writable and the stack is not executable. -/
theorem initialMemory_permissions (address : Nat) :
    (0x401000 ≤ address → address < 0x402000 → initialMemory.permits .write address = false) ∧
      (0x7fff0000 ≤ address → address < 0x80000000 →
        initialMemory.permits .execute address = false) := by
  constructor
  · intro lo hi
    have outside : ¬ stackRegion.Contains address := by
      simp only [stackRegion, Region.Contains]; omega
    simp [Memory.permits, initialMemory_regions, outside, codeRegion,
      Process.Permissions.allows]
  · intro lo hi
    have outside : ¬ codeRegion.Contains address := by
      simp only [codeRegion, Region.Contains]; omega
    simp [Memory.permits, initialMemory_regions, outside, stackRegion,
      Process.Permissions.allows]

private theorem initialMemory_leaf (index : Nat) (bound : index < 7) :
    initialMemory.bytes.get? (leafAddress.toNat + index) = some (bytes[index]'bound) := by
  rw [initialMemory_bytes, Memory.install_outside _ _ _ _ (by simp [leafAddress, stackPointer]; omega),
    codeMemory_bytes]
  exact Memory.install_get _ _ bytes index bound

private theorem initialMemory_caller (index : Nat) (bound : index < 6) :
    initialMemory.bytes.get? (callerAddress.toNat + index) =
      some ((callerBytes callRel)[index]'(by simpa [callerBytes, Insn.encode] using bound)) := by
  rw [initialMemory_bytes,
    Memory.install_outside _ _ _ _ (by simp [callerAddress, stackPointer]; omega),
    codeMemory_bytes, Memory.install_outside _ _ _ _ (by simp [callerAddress, bytes]; omega)]
  exact Memory.install_get _ _ _ index _

private theorem initialMemory_stack (index : Nat) (bound : index < 8) :
    initialMemory.bytes.get? (stackPointer.toNat + index) =
      some ((encodeWords [exitAddress])[index]'(by simpa using bound)) := by
  rw [initialMemory_bytes]
  exact Memory.install_get _ _ _ index _

private theorem code_fetch : initialMemory.fetchBytes leafAddress.toNat 7 = some bytes :=
  Memory.readWith_eq_some_iff.mpr ⟨rfl,
    Memory.permitted_of_region _ _ _ _ codeRegion (by rw [initialMemory_regions]; simp)
      rfl (by decide) (by decide) (by decide) (by decide),
    fun index bound => initialMemory_leaf index bound⟩

private theorem caller_fetch :
    initialMemory.fetchBytes callerAddress.toNat 6 = some (callerBytes callRel) :=
  Memory.readWith_eq_some_iff.mpr ⟨by simp [callerBytes, Insn.encode],
    Memory.permitted_of_region _ _ _ _ codeRegion (by rw [initialMemory_regions]; simp)
      rfl (by decide) (by decide) (by decide) (by decide),
    fun index bound => initialMemory_caller index (by simpa [callerBytes, Insn.encode] using bound)⟩

private theorem stack_read :
    initialMemory.readBytes stackPointer.toNat 8 = some (encodeWords [exitAddress]) :=
  Memory.readWith_eq_some_iff.mpr ⟨by simp,
    Memory.permitted_of_region _ _ _ _ stackRegion (by rw [initialMemory_regions]; simp)
      rfl (by decide) (by decide) (by decide) (by decide),
    fun index bound => initialMemory_stack index (by simpa using bound)⟩

@[simp] private theorem initial_rdi (core : State) (a b entry : Word) :
    (initial core a b entry).core.read .rdi = a := by
  simp [initial, State.read, State.write]

@[simp] private theorem initial_rsi (core : State) (a b entry : Word) :
    (initial core a b entry).core.read .rsi = b := by
  simp [initial, State.read, State.write]

@[simp] private theorem initial_rsp (core : State) (a b entry : Word) :
    (initial core a b entry).core.read .rsp = stackPointer := by
  simp [initial, State.read, State.write]

/-- The concrete states satisfy the leaf premises. -/
theorem initial_leafEntry (core : State) (a b : Word) :
    Entry (initial core a b leafAddress) leafAddress exitAddress :=
  ⟨rfl, code_fetch, by rw [initial_rsp]; exact stack_read⟩

/-- The concrete states satisfy the caller premises. -/
theorem initial_callerEntry (core : State) (a b : Word) :
    CallerEntry (initial core a b callerAddress) callerAddress leafAddress exitAddress callRel := by
  refine ⟨rfl, caller_fetch, by decide, code_fetch, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [initial_rsp]; exact stack_read
  · rw [initial_rsp]
    exact Memory.permitted_of_region _ _ _ _ stackRegion
      (by rw [show (initial _ _ _ _).memory = initialMemory from rfl, initialMemory_regions]; simp) rfl
      (by decide) (by decide) (by decide) (by decide)
  · rw [initial_rsp]
    exact Memory.permitted_of_region _ _ _ _ stackRegion
      (by rw [show (initial _ _ _ _).memory = initialMemory from rfl, initialMemory_regions]; simp) rfl
      (by decide) (by decide) (by decide) (by decide)
  · rw [initial_rsp]; left; decide
  · rw [initial_rsp]; left; decide

/-- A register state for the examples; its values are never read. -/
def zeroCore : State :=
  { regs := fun _ => 0, rip := 0, flags := ⟨none, none, none, none, none, none⟩ }

/-- **Arbitrary inputs, concrete entry.** For all `a` and `b` there is a
well-formed state, with the leaf's bytes in a non-writable executable page and
the return address on a non-executable stack, from which the leaf returns to
`exitAddress` with `a + b` in RAX and the callee-saved registers and memory
unchanged. -/
theorem exists_leaf_run (a b : Word) :
    ∃ m final, Entry m leafAddress exitAddress ∧ m.memory.WellFormed 4096 ∧
      m.core.read .rdi = a ∧ m.core.read .rsi = b ∧
      MState.Returns exitAddress m final ∧ final.core.read .rax = a + b ∧
      final.core.rip = exitAddress ∧ final.core.read .rsp = stackPointer + 8#64 ∧
      (∀ r ∈ calleeSaved, final.core.read r = m.core.read r) ∧ final.memory = m.memory := by
  have h := initial_leafEntry zeroCore a b
  obtain ⟨final, hret, hrip, hrax, -, hrsp, -, hother, hmem⟩ := leaf_returns h
  refine ⟨_, final, h, initialMemory_wellFormed, by simp, by simp, hret, by simpa using hrax,
    hrip, by simpa using hrsp, fun r hr => hother r ?_ ?_, hmem⟩ <;>
    (simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- **Arbitrary inputs, concrete caller.** For all `a` and `b`, the caller at
`callerAddress` calls the leaf, which returns into the caller, which returns to
`exitAddress` with `a + b` in RAX; memory changes only in the eight-byte slot
below the entry RSP. -/
theorem exists_caller_run (a b : Word) :
    ∃ m final, CallerEntry m callerAddress leafAddress exitAddress callRel ∧
      m.memory.WellFormed 4096 ∧ m.core.read .rdi = a ∧ m.core.read .rsi = b ∧
      MState.Returns exitAddress m final ∧ final.core.read .rax = a + b ∧
      final.core.rip = exitAddress ∧ final.core.read .rsp = stackPointer + 8#64 ∧
      (∀ r ∈ calleeSaved, final.core.read r = m.core.read r) ∧
      Memory.WritesOnly m.memory final.memory (stackPointer - 8#64).toNat 8 := by
  have h := initial_callerEntry zeroCore a b
  obtain ⟨final, ⟨mid, hrun, hstep⟩, hrip, hrax, hrsp, -, hother, hframe, -⟩ :=
    caller_returns h
  refine ⟨_, final, h, initialMemory_wellFormed, by simp, by simp, ⟨4, mid, hrun, hstep⟩,
    by simpa using hrax, hrip, by simpa using hrsp, fun r hr => hother r ?_ ?_,
    by simpa using hframe⟩ <;>
    (simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
     rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

end Silmaril.X86.Leaf
