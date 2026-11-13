module

public import Silmaril.Machine.RiscV.Ext.Retire.Defs
/-!
# Loaded-code witnesses for the extended machine

`fetchBytes_install` discharges the fetch premise of `run_compute_block` and
`MState.step_of_fetchBytes` for code installed in an executable region, so
those theorems apply to concrete loaded programs. The examples construct such a
state and show a stop at `EBREAK`, a two-instruction `ADDW`/`EBREAK` program
computing a sign-extended 32-bit sum, and a store/load round trip.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

open Silmaril.Process (Memory Region Permissions)

/-- Bytes installed inside a single executable region can be fetched. -/
theorem fetchBytes_install (memory : Memory) (region : Region) (member : region ∈ memory.regions)
    (executable : region.permissions.execute = true) (address : Nat) (bytes : List (BitVec 8))
    (lower : region.base ≤ address) (upper : address + bytes.length ≤ region.base + region.size)
    (limit : region.base + region.size ≤ Process.addressLimit)
    (start : address < Process.addressLimit) :
    ({ memory with bytes := Memory.install memory.bytes address bytes } : Memory).fetchBytes
      address bytes.length = some bytes := by
  apply Memory.readWith_eq
  · exact Memory.permitted_of_region _ .execute address bytes.length region member executable
      start (by omega) lower upper
  · exact fun index bound => Memory.install_get _ _ _ _ bound

/-- A readable, writable and executable region of one page at `0x1000`. -/
def demoRegion : Region := ⟨0x1000, 0x1000, ⟨true, true, true⟩⟩

/-- Memory with `demoRegion` and `code` installed at its base. -/
def demoMemory (code : List Instr) : Memory :=
  { regions := [demoRegion], bytes := Memory.install ∅ 0x1000 (byteDecoder.encodeBlock code) }

def demoState (code : List Instr) (s : State) : MState :=
  ⟨{ s with pc := 0x1000#64 }, demoMemory code⟩

private theorem demo_fetch (code : List Instr) (bound : 4 * code.length ≤ 0x1000) :
    (demoMemory code).fetchBytes 0x1000 (4 * code.length) =
      some (byteDecoder.encodeBlock code) := by
  have := fetchBytes_install ⟨[demoRegion], ∅⟩ demoRegion (by simp) rfl 0x1000
    (byteDecoder.encodeBlock code) (by decide)
    (by rw [encodeBlock_length]; simp [demoRegion]; omega) (by decide) (by decide)
  rwa [encodeBlock_length] at this

/-- `EBREAK` at the PC stops the machine immediately. -/
theorem demo_stops (s : State) : MState.Stops (demoState [.ebreak] s) (demoState [.ebreak] s) := by
  refine ⟨0, rfl, ?_⟩
  have fetched := demo_fetch [.ebreak] (by decide)
  rw [MState.step_of_fetchBytes (instr := .ebreak)
    (by show (0x1000#64 : Word).toNat % 4 = 0; decide)
    (by simpa [demoState, Machine.Decoder.encodeBlock] using fetched)]
  rfl

/-- `addw a0, a0, a1` followed by `ebreak`: one retirement, then a stop with
`a0` holding the sign-extended 32-bit sum of the incoming `a0` and `a1`. -/
theorem demo_addw (s : State) :
    let code : List Instr := [.compute (.regW .add 10#5 10#5 11#5), .ebreak]
    ∃ final, MState.Stops (demoState code s) final ∧
      final.core.read 10#5 = sext32 (low32 (s.read 10#5) + low32 (s.read 11#5)) ∧
      final.core.pc = 0x1004#64 ∧ final.memory = demoMemory code := by
  intro code
  have fetched := demo_fetch code (by decide)
  have first : Machine.Execution.run MState.stepOpt 1 (demoState code s) =
      some ⟨Compute.step (.regW .add 10#5 10#5 11#5) (demoState code s).core,
        demoMemory code⟩ := by
    have := run_compute_block [.regW .add 10#5 10#5 11#5] (demoState code s)
      (by show (0x1000#64 : Word).toNat % 4 = 0; decide)
      (by
        have := MemoryLemmas.readWith_slice fetched 0 4 (by decide) (by decide)
        simp only [demoState, code, Memory.fetchBytes, Machine.Decoder.encodeBlock,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.drop_zero,
          Nat.add_zero] at this ⊢
        rw [List.take_left' (by simp)] at this
        exact this)
    simpa [demoState] using this
  refine ⟨⟨Compute.step (.regW .add 10#5 10#5 11#5) (demoState code s).core, demoMemory code⟩,
    ⟨1, first, ?_⟩, ?_, ?_, rfl⟩
  · have second := MemoryLemmas.readWith_slice fetched 4 4 (by decide) (by decide)
    rw [MState.step_of_fetchBytes (instr := .ebreak)
      (by show ((0x1000#64 : Word) + 4).toNat % 4 = 0; decide)
      (by
        simp only [demoState, code, Memory.fetchBytes, Machine.Decoder.encodeBlock,
          List.flatMap_cons, List.flatMap_nil, List.append_nil] at second ⊢
        rw [List.drop_left' (by simp), List.take_of_length_le (by simp)] at second
        exact second)]
    rfl
  · exact (Compute.step_read_dest (.regW .add 10#5 10#5 11#5) _ (by decide)).trans rfl
  · rfl

/-- An aligned doubleword store to a writable, readable span, followed by a
load of the same span, returns the stored register value. -/
theorem store_then_load (m : MState) (base src rd : Reg) (offset : BitVec 12) (next : MState)
    (stored : (Instr.store .sd base src offset).exec m = .retired next)
    (readable : m.memory.Permitted .read (effectiveAddress m.core base offset).toNat 8)
    (sameBase : next.core.read base = m.core.read base) :
    (Instr.load .ld rd base offset).exec next =
      .retired { next with core :=
        { next.core.write rd (m.core.read src) with pc := next.core.pc + 4 } } := by
  have back := Instr.readBytes_after_store stored readable
  have aligned : (effectiveAddress m.core base offset).toNat % 8 = 0 := by
    simp only [Instr.exec] at stored
    split at stored
    · assumption
    · cases stored
  have hea : effectiveAddress next.core base offset = effectiveAddress m.core base offset := by
    simp [effectiveAddress, sameBase]
  rw [Instr.exec_load next (op := .ld) (by rw [hea]; exact aligned) (by rw [hea]; exact back)]
  simp [StoreOp.width]

end Silmaril.RiscV.Ext
