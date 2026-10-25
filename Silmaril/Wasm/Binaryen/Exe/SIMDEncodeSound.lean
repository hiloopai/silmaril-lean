module

public import Silmaril.Wasm.Binaryen.Exe.SIMDEncode
public import Silmaril.Wasm.Binaryen.Exe.MemoryEncodeSound
public import Silmaril.Wasm.Binaryen.Exe.FloatEncodeSound

@[expose] public section

/-! Soundness of the `0xFD` encoder against the existing Core grammar, and of vector
constants: their sixteen little-endian payload bytes reuse the scalar float encoder's
fixed-width byte writer and its inverse lemma.

Every entry of the encoder's opcode tables carries its Core rule, so soundness needs
only the comparison `vecInstrEqb`, once for all opcodes. -/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem vecInstrEqb_sound {i j : Wasm.Instr} (h : vecInstrEqb i j = true) : i = j := by
  unfold vecInstrEqb at h
  split at h <;> simp_all

theorem laneOf_laneByte (l : LaneIdx) : laneOf (laneByte l) = l := rfl

theorem fdPlain_lt (e : FDPlain) : e.n < 2 ^ 32 := by
  obtain ⟨n, i, h⟩ := e; cases h <;> decide

theorem fdMem_lt (e : FDMem) : e.n < 2 ^ 32 := by
  obtain ⟨n, i, h⟩ := e; cases h <;> decide

theorem fdMemLane_lt (e : FDMemLane) : e.n < 2 ^ 32 := by
  obtain ⟨n, i, h⟩ := e; cases h <;> decide

theorem fdLane_lt (e : FDLane) : e.n < 2 ^ 32 := by
  obtain ⟨n, i, h⟩ := e; cases h <;> decide

theorem u32_encU {n : Nat} (h : n < 2 ^ 32) : U32 (encU n) n := encU_sound h

theorem vecMemLane_laneByte {F : Forms} {bn b : List UInt8} {n : Nat}
    {mk : MemIdx → Wasm.MemArg → LaneIdx → Wasm.Instr} {x : MemIdx} {ao : Wasm.MemArg}
    {l : LaneIdx} (h : VecMemLaneOp n mk) (hn : U32 bn n) (hm : Memarg F b (x, ao)) :
    Core.Instr F ([0xFD] ++ bn ++ b ++ [laneByte l]) (mk x ao l) :=
  Core.Instr.vecMemLane (l := laneByte l) h hn hm

theorem vecLane_laneByte {F : Forms} {bn : List UInt8} {n : Nat} {mk : LaneIdx → Wasm.Instr}
    {l : LaneIdx} (h : VecLaneOp n mk) (hn : U32 bn n) :
    Core.Instr F ([0xFD] ++ bn ++ [laneByte l]) (mk l) :=
  Core.Instr.vecLane (l := laneByte l) h hn

/-- Every successful encoding denotes the original instruction in the Core grammar. -/
theorem encSIMDInstr_sound {i : Wasm.Instr} {bs : List UInt8}
    (h : encSIMDInstr i = .ok bs) : Core.Instr Forms.all bs i := by
  unfold encSIMDInstr at h
  split at h
  -- full-width and extending loads, stores
  iterate 2
    split at h
    · next e he =>
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      have hp := List.find?_some he
      rw [← vecInstrEqb_sound hp]
      exact .vecMem e.h (u32_encU (fdMem_lt e)) (encMemArg_sound hb)
    · exact absurd h throw_ne_ok
  -- lane loads and stores
  iterate 2
    split at h
    · next e he =>
      obtain ⟨b, hb, h⟩ := bind_ok h
      cases Except.ok.inj h
      have hp := List.find?_some he
      rw [← vecInstrEqb_sound hp]
      exact vecMemLane_laneByte e.h (u32_encU (fdMemLane_lt e)) (encMemArg_sound hb)
    · exact absurd h throw_ne_ok
  -- lane extraction and replacement
  iterate 2
    split at h
    · next e he =>
      cases Except.ok.inj h
      have hp := List.find?_some he
      rw [← vecInstrEqb_sound hp]
      exact vecLane_laneByte e.h (u32_encU (fdLane_lt e))
    · exact absurd h throw_ne_ok
  -- shuffle
  · split at h
    · next ls hl =>
      cases Except.ok.inj h
      have hn : U32 [13] 13 := by
        simpa [encU] using encU_sound (by decide : 13 < 2 ^ 32)
      have := Core.Instr.vecShuffle (F := Forms.all) hn
        (by simpa using hl : (ls.map laneByte).length = 16)
      simpa only [List.map_map, Function.comp_def, laneOf_laneByte, List.map_id',
        List.cons_append, List.nil_append] using this
    · exact absurd h throw_ne_ok
  -- immediate-free opcodes
  · split at h
    · next e he =>
      cases Except.ok.inj h
      have hp := List.find?_some he
      rw [← vecInstrEqb_sound hp]
      exact .prefixFD e.h (u32_encU (fdPlain_lt e))
    · exact absurd h throw_ne_ok

/-- Sixteen bytes encode precisely the original 128-bit vector literal. -/
theorem encVecConst_sound {F : Forms} (b : BitVec 128) :
    Core.Instr F ([0xFD, 0x0C] ++ encLE 16 b.toNat) (.vecConst b) := by
  have hx : b.toNat < 256 ^ 16 := b.isLt
  have hbits : BitVec.ofNat 128 (littleEndian (encLE 16 b.toNat)) = b := by
    simp only [littleEndian_encLE _ _ hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hn : U32 [0x0C] 12 := by
    simpa [encU] using encU_sound (by decide : 12 < 2 ^ 32)
  simpa only [hbits, List.cons_append, List.nil_append] using
    (Core.Instr.vecConst (F := F) hn (encLE_length 16 b.toNat))

end Silmaril.Wasm.Binaryen.Exe
