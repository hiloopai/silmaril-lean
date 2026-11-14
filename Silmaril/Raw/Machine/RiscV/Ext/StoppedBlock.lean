module

public import Silmaril.Machine.RiscV.Ext.Retire.Defs
/-!
# Certificates for fetched arithmetic blocks ending at EBREAK

The certificate checks executable backing for both the block and its stop
instruction. The conclusion uses the existing fetch/decode/execute machine,
preserves all memory, and identifies the complete final register state. No
source-language interpreter participates in this boundary.
-/

@[expose] public section
namespace Silmaril.RiscV.Ext

open Silmaril.Machine

/-- One contiguous executable image containing a base arithmetic block followed
by EBREAK. The end PC must remain within the address space. -/
theorem run_base_block_stops (code : List RiscV.Instr) (m : MState)
    (aligned : m.core.pc.toNat % 4 = 0)
    (bounded : m.core.pc.toNat + 4 * code.length < 2 ^ 64)
    (fetched : m.memory.fetchBytes m.core.pc.toNat (4 * code.length + 4) =
      some (RiscV.byteDecoder.encodeBlock code ++ encodeBytes .ebreak)) :
    MState.Stops m ⟨Block.run RiscV.step code m.core, m.memory⟩ := by
  by_cases empty : code = []
  · subst code
    refine ⟨0, rfl, ?_⟩
    change m.step = .stopped
    rw [MState.step_of_fetchBytes (instr := .ebreak) aligned
      (by simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add,
        Decoder.encodeBlock_nil, List.nil_append] using fetched)]
    rfl
  have length : (RiscV.byteDecoder.encodeBlock code).length = 4 * code.length := by
    have h := encodeBlock_length ((code.map Compute.base).map Instr.compute)
    rw [encodeBlock_base] at h
    simpa only [List.length_map] using h
  have positive : 0 < code.length := List.length_pos_iff.mpr empty
  have firstBytes := MemoryLemmas.readWith_slice fetched 0 (4 * code.length)
    (by omega) (by omega)
  simp only [Nat.add_zero, List.drop_zero] at firstBytes
  rw [List.take_left' (by omega)] at firstBytes
  have executed := run_base_block code m aligned firstBytes
  have suffix := MemoryLemmas.readWith_slice fetched (4 * code.length) 4
    (by omega) (by omega)
  rw [List.drop_left' (by omega), List.take_of_length_le (by simp)] at suffix
  have pc : (Block.run RiscV.step code m.core).pc.toNat =
      m.core.pc.toNat + 4 * code.length := by
    rw [RiscV.run_pc, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4 * code.length < 2 ^ 64), Nat.mod_eq_of_lt bounded]
  refine ⟨code.length, executed, ?_⟩
  rw [MState.step_of_fetchBytes (instr := .ebreak)
    (by change (Block.run RiscV.step code m.core).pc.toNat % 4 = 0
        rw [pc, Nat.add_mod, aligned]
        omega)
    (by change m.memory.fetchBytes (Block.run RiscV.step code m.core).pc.toNat 4 = _
        rw [pc]
        exact suffix)]
  rfl

end Silmaril.RiscV.Ext
