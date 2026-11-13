module

public import Silmaril.Machine.RiscV.Ext.Decoder.Defs
public import Silmaril.Machine.RiscV.Ext.Memory.Defs
public import Silmaril.Machine.Execution

/-!
# A PC-driven machine for the extended RV64 model

`MState` pairs the local RV64 register state (`RiscV.State`, with `x0`
hardwired to zero) with a `Process.Memory`. `MState.step` fetches four
executable bytes at an aligned PC, decodes them with `Ext.decode`, and executes
the instruction. It is a handwritten local model of one user-mode hart without
the C extension; it is not proved to correspond to the generated Sail model
except for the instruction clauses in the Sail correspondence module (not in this repository: it needs the `riscv-zkvm` package).

## Outcomes

* `retired next`: the instruction completed with successor state `next`.
* `stopped`: the instruction was `EBREAK`. The state is left unchanged; the
  breakpoint trap and its handler are outside the model.
* `fetchFault`: the PC is not four-byte aligned, or some byte of the four at
  PC is unmapped, not executable, above `2^64`, or has no backing.
* `undecodable word`: the fetched word is outside `Instr`.
* `targetMisaligned instr target`: a taken branch, `JAL` or `JALR` would jump
  to an address that is not four-byte aligned. As the specification requires
  without the C extension, the exception is raised on the jump itself, which
  has no effect (in particular `rd` is not written).
* `dataMisaligned instr address`: a load or store whose effective address is
  not a multiple of its width. The specification lets an execution environment
  either perform such accesses or trap; this model always traps, so code proved
  against it uses naturally aligned accesses.
* `dataFault instr address`: a naturally aligned load or store whose span is
  not readable (respectively writable) or not backed in `Process.Memory`.

Faults carry no successor state, and a faulting instruction has no partial
effect. Loads to `x0` still perform (and may fault on) the access.

Fetch reads the current memory, so a store to executable memory is visible to
the next fetch; `FENCE.I`, instruction-fetch ordering, privilege, virtual
memory, PMP, interrupts and concurrency are not modeled.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

open Silmaril.Process (Memory)

/-- The register state and memory of one hart. -/
structure MState where
  core : State
  memory : Memory

/-! ## Fetch -/

/-- Four executable, backed bytes at a four-byte-aligned PC, as a 32-bit word. -/
def fetch (memory : Memory) (pc : Word) : Option (BitVec 32) :=
  if pc.toNat % 4 = 0 then (memory.fetchBytes pc.toNat 4).bind wordOfBytes else none

theorem fetch_of_fetchBytes {memory : Memory} {pc : Word} {word : BitVec 32}
    (aligned : pc.toNat % 4 = 0) (bytes : memory.fetchBytes pc.toNat 4 = some (wordBytes word)) :
    fetch memory pc = some word := by
  simp [fetch, aligned, bytes]

theorem fetch_eq_some_iff {memory : Memory} {pc : Word} {word : BitVec 32} :
    fetch memory pc = some word ↔
      pc.toNat % 4 = 0 ∧ memory.fetchBytes pc.toNat 4 = some (wordBytes word) := by
  constructor
  · intro h
    unfold fetch at h
    split at h
    · rename_i aligned
      refine ⟨aligned, ?_⟩
      cases hb : memory.fetchBytes pc.toNat 4 with
      | none => simp [hb] at h
      | some bytes =>
        simp only [hb, Option.bind_some] at h
        rw [wordOfBytes_eq_some h]
    · cases h
  · rintro ⟨aligned, bytes⟩
    exact fetch_of_fetchBytes aligned bytes

/-- Fetch fails exactly on a misaligned PC or a failed four-byte execute access. -/
theorem fetch_eq_none_iff {memory : Memory} {pc : Word} :
    fetch memory pc = none ↔ pc.toNat % 4 ≠ 0 ∨ memory.fetchBytes pc.toNat 4 = none := by
  unfold fetch
  split
  · rename_i aligned
    cases hb : memory.fetchBytes pc.toNat 4 with
    | none => simp
    | some bytes =>
      obtain ⟨word, hw⟩ := wordOfBytes_isSome (Memory.readWith_length hb)
      simp [hw, aligned]
  · rename_i misaligned
    simp [misaligned]

/-! ## Execution -/

/-- The result of one step. Faults change nothing. -/
inductive Outcome where
  | retired (next : MState)
  | stopped
  | fetchFault
  | undecodable (word : BitVec 32)
  | targetMisaligned (instr : Instr) (target : Word)
  | dataMisaligned (instr : Instr) (address : Word)
  | dataFault (instr : Instr) (address : Word)

/-- `rs1 + sext(offset)`, modulo `2^64`. -/
def effectiveAddress (s : State) (base : Reg) (offset : BitVec 12) : Word :=
  s.read base + offset.signExtend 64

/-- The `JALR` target: `rs1 + sext(offset)` with bit 0 cleared. -/
def jalrTarget (s : State) (base : Reg) (offset : BitVec 12) : Word :=
  effectiveAddress s base offset &&& ~~~1#64

/-- Jump to `target`, writing nothing but the PC, unless it is misaligned. -/
def jumpTo (instr : Instr) (m : MState) (core : State) (target : Word) : Outcome :=
  if target.toNat % 4 = 0 then .retired { m with core := { core with pc := target } }
  else .targetMisaligned instr target

/-- Execute one decoded instruction. Operands are read from the incoming state. -/
def Instr.exec (instr : Instr) (m : MState) : Outcome :=
  let s := m.core
  match instr with
  | .compute c => .retired { m with core := c.step s }
  | .load op rd rs1 offset =>
    let address := effectiveAddress s rs1 offset
    if address.toNat % op.width = 0 then
      match m.memory.readBytes address.toNat op.width with
      | some bytes =>
        .retired { m with core := { s.write rd (op.value bytes) with pc := s.pc + 4 } }
      | none => .dataFault instr address
    else .dataMisaligned instr address
  | .store op rs1 rs2 offset =>
    let address := effectiveAddress s rs1 offset
    if address.toNat % op.width = 0 then
      match m.memory.writeBytes address.toNat (leBytes op.width (s.read rs2)) with
      | some memory => .retired ⟨{ s with pc := s.pc + 4 }, memory⟩
      | none => .dataFault instr address
    else .dataMisaligned instr address
  | .branch op rs1 rs2 half =>
    if op.eval (s.read rs1) (s.read rs2) then jumpTo instr m s (s.pc + branchOffset half)
    else .retired { m with core := { s with pc := s.pc + 4 } }
  | .jal rd half => jumpTo instr m (s.write rd (s.pc + 4)) (s.pc + jalOffset half)
  | .jalr rd rs1 offset => jumpTo instr m (s.write rd (s.pc + 4)) (jalrTarget s rs1 offset)
  | .ebreak => .stopped

namespace MState

/-- Fetch, decode and execute one instruction. -/
def step (m : MState) : Outcome :=
  match fetch m.memory m.core.pc with
  | none => .fetchFault
  | some word =>
    match decode word with
    | none => .undecodable word
    | some instr => instr.exec m

/-- Retirement only, as a partial transition function for `Machine.Execution.run`. -/
def stepOpt (m : MState) : Option MState :=
  match m.step with
  | .retired next => some next
  | _ => none

theorem stepOpt_eq_some_iff {m next : MState} :
    m.stepOpt = some next ↔ m.step = .retired next := by
  unfold stepOpt
  split <;> simp_all

/-- A finite run of retirements reaching an `EBREAK`. -/
def Stops (initial final : MState) : Prop :=
  ∃ n, Machine.Execution.run stepOpt n initial = some final ∧ final.step = .stopped

/-- One step executes the instruction whose encoding is fetched at the PC. -/
theorem step_of_fetch {m : MState} {instr : Instr}
    (fetched : fetch m.memory m.core.pc = some (encode instr)) : m.step = instr.exec m := by
  simp [step, fetched]

/-- One step executes the instruction whose little-endian bytes are executable
at the aligned PC. -/
theorem step_of_fetchBytes {m : MState} {instr : Instr} (aligned : m.core.pc.toNat % 4 = 0)
    (bytes : m.memory.fetchBytes m.core.pc.toNat 4 = some (encodeBytes instr)) :
    m.step = instr.exec m :=
  step_of_fetch (fetch_of_fetchBytes aligned bytes)

theorem step_fetchFault {m : MState} (h : fetch m.memory m.core.pc = none) :
    m.step = .fetchFault := by
  simp [step, h]

theorem step_undecodable {m : MState} {word : BitVec 32}
    (fetched : fetch m.memory m.core.pc = some word) (h : decode word = none) :
    m.step = .undecodable word := by
  simp [step, fetched, h]

end MState

/-! ## Per-instruction results -/

namespace Instr

variable (m : MState)

@[simp] theorem exec_compute (c : Compute) :
    (Instr.compute c).exec m = .retired { m with core := c.step m.core } := rfl

@[simp] theorem exec_ebreak : Instr.ebreak.exec m = .stopped := rfl

theorem exec_load {op : LoadOp} {rd rs1 : Reg} {offset : BitVec 12} {bytes : List Process.Byte}
    (aligned : (effectiveAddress m.core rs1 offset).toNat % op.width = 0)
    (read : m.memory.readBytes (effectiveAddress m.core rs1 offset).toNat op.width = some bytes) :
    (Instr.load op rd rs1 offset).exec m =
      .retired { m with
        core := { m.core.write rd (op.value bytes) with pc := m.core.pc + 4 } } := by
  simp [exec, aligned, read]

theorem exec_load_misaligned {op : LoadOp} {rd rs1 : Reg} {offset : BitVec 12}
    (misaligned : (effectiveAddress m.core rs1 offset).toNat % op.width ≠ 0) :
    (Instr.load op rd rs1 offset).exec m =
      .dataMisaligned (.load op rd rs1 offset) (effectiveAddress m.core rs1 offset) := by
  simp [exec, misaligned]

theorem exec_load_fault {op : LoadOp} {rd rs1 : Reg} {offset : BitVec 12}
    (aligned : (effectiveAddress m.core rs1 offset).toNat % op.width = 0)
    (fault : m.memory.readBytes (effectiveAddress m.core rs1 offset).toNat op.width = none) :
    (Instr.load op rd rs1 offset).exec m =
      .dataFault (.load op rd rs1 offset) (effectiveAddress m.core rs1 offset) := by
  simp [exec, aligned, fault]

theorem exec_store {op : StoreOp} {rs1 rs2 : Reg} {offset : BitVec 12} {after : Memory}
    (aligned : (effectiveAddress m.core rs1 offset).toNat % op.width = 0)
    (written : m.memory.writeBytes (effectiveAddress m.core rs1 offset).toNat
      (leBytes op.width (m.core.read rs2)) = some after) :
    (Instr.store op rs1 rs2 offset).exec m =
      .retired ⟨{ m.core with pc := m.core.pc + 4 }, after⟩ := by
  simp [exec, aligned, written]

/-- A permitted aligned store succeeds and installs the low bytes of `rs2`. -/
theorem exec_store_permitted {op : StoreOp} {rs1 rs2 : Reg} {offset : BitVec 12}
    (aligned : (effectiveAddress m.core rs1 offset).toNat % op.width = 0)
    (permitted : m.memory.Permitted .write (effectiveAddress m.core rs1 offset).toNat op.width) :
    (Instr.store op rs1 rs2 offset).exec m = .retired ⟨{ m.core with pc := m.core.pc + 4 },
      { regions := m.memory.regions,
        bytes := Memory.install m.memory.bytes (effectiveAddress m.core rs1 offset).toNat
          (leBytes op.width (m.core.read rs2)) }⟩ :=
  exec_store m aligned (MemoryLemmas.writeBytes_eq_some_iff.mpr
    ⟨by simpa using permitted, rfl⟩)

theorem exec_store_misaligned {op : StoreOp} {rs1 rs2 : Reg} {offset : BitVec 12}
    (misaligned : (effectiveAddress m.core rs1 offset).toNat % op.width ≠ 0) :
    (Instr.store op rs1 rs2 offset).exec m =
      .dataMisaligned (.store op rs1 rs2 offset) (effectiveAddress m.core rs1 offset) := by
  simp [exec, misaligned]

theorem exec_store_fault {op : StoreOp} {rs1 rs2 : Reg} {offset : BitVec 12}
    (aligned : (effectiveAddress m.core rs1 offset).toNat % op.width = 0)
    (denied : ¬ m.memory.Permitted .write (effectiveAddress m.core rs1 offset).toNat op.width) :
    (Instr.store op rs1 rs2 offset).exec m =
      .dataFault (.store op rs1 rs2 offset) (effectiveAddress m.core rs1 offset) := by
  have : m.memory.writeBytes (effectiveAddress m.core rs1 offset).toNat
      (leBytes op.width (m.core.read rs2)) = none :=
    MemoryLemmas.writeBytes_eq_none_iff.mpr (by simpa using denied)
  simp [exec, aligned, this]

theorem exec_branch_taken {op : BranchOp} {rs1 rs2 : Reg} {half : BitVec 12}
    (taken : op.eval (m.core.read rs1) (m.core.read rs2) = true)
    (aligned : (m.core.pc + branchOffset half).toNat % 4 = 0) :
    (Instr.branch op rs1 rs2 half).exec m =
      .retired { m with core := { m.core with pc := m.core.pc + branchOffset half } } := by
  unfold exec jumpTo; simp only [taken, aligned, ↓reduceIte]

theorem exec_branch_not_taken {op : BranchOp} {rs1 rs2 : Reg} {half : BitVec 12}
    (notTaken : op.eval (m.core.read rs1) (m.core.read rs2) = false) :
    (Instr.branch op rs1 rs2 half).exec m =
      .retired { m with core := { m.core with pc := m.core.pc + 4 } } := by
  simp [exec, notTaken]

theorem exec_branch_misaligned {op : BranchOp} {rs1 rs2 : Reg} {half : BitVec 12}
    (taken : op.eval (m.core.read rs1) (m.core.read rs2) = true)
    (misaligned : (m.core.pc + branchOffset half).toNat % 4 ≠ 0) :
    (Instr.branch op rs1 rs2 half).exec m =
      .targetMisaligned (.branch op rs1 rs2 half) (m.core.pc + branchOffset half) := by
  unfold exec jumpTo; simp only [taken, misaligned, ↓reduceIte]

theorem exec_jal {rd : Reg} {half : BitVec 20}
    (aligned : (m.core.pc + jalOffset half).toNat % 4 = 0) :
    (Instr.jal rd half).exec m = .retired { m with core :=
      { m.core.write rd (m.core.pc + 4) with pc := m.core.pc + jalOffset half } } := by
  unfold exec jumpTo; simp only [aligned, ↓reduceIte]

theorem exec_jal_misaligned {rd : Reg} {half : BitVec 20}
    (misaligned : (m.core.pc + jalOffset half).toNat % 4 ≠ 0) :
    (Instr.jal rd half).exec m = .targetMisaligned (.jal rd half) (m.core.pc + jalOffset half) := by
  unfold exec jumpTo; simp only [misaligned, ↓reduceIte]

theorem exec_jalr {rd rs1 : Reg} {offset : BitVec 12}
    (aligned : (jalrTarget m.core rs1 offset).toNat % 4 = 0) :
    (Instr.jalr rd rs1 offset).exec m = .retired { m with core :=
      { m.core.write rd (m.core.pc + 4) with pc := jalrTarget m.core rs1 offset } } := by
  unfold exec jumpTo; simp only [aligned, ↓reduceIte]

theorem exec_jalr_misaligned {rd rs1 : Reg} {offset : BitVec 12}
    (misaligned : (jalrTarget m.core rs1 offset).toNat % 4 ≠ 0) :
    (Instr.jalr rd rs1 offset).exec m =
      .targetMisaligned (.jalr rd rs1 offset) (jalrTarget m.core rs1 offset) := by
  unfold exec jumpTo; simp only [misaligned, ↓reduceIte]

/-- `JALR` reads `rs1` before writing `rd`, so `jalr ra, 0(ra)` jumps to the old `ra`. -/
theorem jalrTarget_bit0 (s : State) (rs1 : Reg) (offset : BitVec 12) :
    (jalrTarget s rs1 offset).getLsbD 0 = false := by
  simp [jalrTarget]

/-! ## Frames of retiring instructions -/

/-- Only stores change memory, and no instruction changes the mappings. -/
theorem exec_memory {instr : Instr} {m next : MState} (h : instr.exec m = .retired next)
    (notStore : ∀ op rs1 rs2 offset, instr ≠ .store op rs1 rs2 offset) :
    next.memory = m.memory := by
  cases instr with
  | compute c => cases h; rfl
  | load op rd rs1 offset =>
    simp only [exec] at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  | store op rs1 rs2 offset => exact absurd rfl (notStore op rs1 rs2 offset)
  | branch op rs1 rs2 half =>
    simp only [exec, jumpTo] at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h; rfl
  | jal rd half =>
    simp only [exec, jumpTo] at h
    split at h
    · cases h; rfl
    · cases h
  | jalr rd rs1 offset =>
    simp only [exec, jumpTo] at h
    split at h
    · cases h; rfl
    · cases h
  | ebreak => cases h

/-- A retiring store writes exactly the bytes of its access and no mapping. -/
theorem exec_store_writesOnly {op : StoreOp} {rs1 rs2 : Reg} {offset : BitVec 12} {m next : MState}
    (h : (Instr.store op rs1 rs2 offset).exec m = .retired next) :
    Memory.WritesOnly m.memory next.memory (effectiveAddress m.core rs1 offset).toNat op.width := by
  simp only [exec] at h
  split at h
  · split at h
    · rename_i after written
      cases h
      simpa using Memory.writeBytes_writesOnly written
    · cases h
  · cases h

/-- Store then load at the same address and width reads back the stored bytes,
provided the span is also readable. -/
theorem readBytes_after_store {op : StoreOp} {rs1 rs2 : Reg} {offset : BitVec 12} {m next : MState}
    (h : (Instr.store op rs1 rs2 offset).exec m = .retired next)
    (readable : m.memory.Permitted .read (effectiveAddress m.core rs1 offset).toNat op.width) :
    next.memory.readBytes (effectiveAddress m.core rs1 offset).toNat op.width =
      some (leBytes op.width (m.core.read rs2)) := by
  simp only [exec] at h
  split at h
  · split at h
    · rename_i after written
      cases h
      simpa using MemoryLemmas.readBytes_writeBytes written (by simpa using readable)
    · cases h
  · cases h

end Instr

/-! ## Straight-line register blocks -/

/-- Every encoded block is four bytes per instruction. -/
theorem encodeBlock_length (code : List Instr) :
    (byteDecoder.encodeBlock code).length = 4 * code.length := by
  induction code with
  | nil => rfl
  | cons instr rest ih =>
    simp only [Machine.Decoder.encodeBlock_cons, List.length_append, byteDecoder_encode,
      encodeBytes_length, ih, List.length_cons]
    omega

/-- A block of register-only instructions whose encodings are executable at an
aligned PC runs, one retirement per instruction, as `Block.run Compute.step`,
leaving memory unchanged. -/
theorem run_compute_block (code : List Compute) (m : MState)
    (aligned : m.core.pc.toNat % 4 = 0)
    (fetched : m.memory.fetchBytes m.core.pc.toNat (4 * code.length) =
      some (byteDecoder.encodeBlock (code.map Instr.compute))) :
    Machine.Execution.run MState.stepOpt code.length m =
      some ⟨Machine.Block.run Compute.step code m.core, m.memory⟩ := by
  induction code generalizing m with
  | nil => rfl
  | cons c rest ih =>
    have hlen := Memory.readWith_length fetched
    have first : m.memory.fetchBytes m.core.pc.toNat 4 = some (encodeBytes (.compute c)) := by
      have := MemoryLemmas.readWith_slice fetched 0 4 (by decide) (by simp; omega)
      simp only [Nat.add_zero, List.drop_zero, List.map_cons, Machine.Decoder.encodeBlock_cons,
        byteDecoder_encode] at this
      rw [List.take_left' (by simp)] at this
      exact this
    have hstep : m.stepOpt = some ⟨Compute.step c m.core, m.memory⟩ := by
      rw [MState.stepOpt_eq_some_iff, MState.step_of_fetchBytes aligned first]
      rfl
    simp only [List.length_cons, Machine.Execution.run_succ, hstep, Option.bind_some,
      Machine.Block.run_cons]
    cases rest with
    | nil => rfl
    | cons c' rest' =>
      have bound : m.core.pc.toNat + 4 * (rest'.length + 2) ≤ Process.addressLimit := by
        have := (Memory.checkSpan_iff _ _ _ _).mp (Memory.readWith_permitted fetched)
        simp only [List.length_cons] at this
        omega
      have hpc : (m.core.pc + 4).toNat = m.core.pc.toNat + 4 := by
        rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]
        apply Nat.mod_eq_of_lt
        simp only [Process.addressLimit, Nat.reducePow] at bound ⊢
        omega
      apply ih ⟨Compute.step c m.core, m.memory⟩
      · simp only [Compute.step_pc, hpc]; omega
      · simp only [Compute.step_pc, hpc]
        have := MemoryLemmas.readWith_slice fetched 4 (4 * (c' :: rest').length)
          (by simp) (by simp; omega)
        simp only [Memory.fetchBytes] at this ⊢
        rw [this]
        congr 1
        rw [List.map_cons, Machine.Decoder.encodeBlock_cons, byteDecoder_encode,
          List.drop_left' (by simp), List.take_of_length_le]
        rw [encodeBlock_length]
        simp

end Silmaril.RiscV.Ext
