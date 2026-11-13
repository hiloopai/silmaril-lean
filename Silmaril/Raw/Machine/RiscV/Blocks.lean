module

public import Silmaril.Machine.RiscV.Basic.Defs
public import Silmaril.Machine.RiscV.Encoding.Defs
public import Silmaril.Machine.Block
public import Silmaril.Machine.Retire
public import Silmaril.Machine.Decoder

/-!
# Straight-line RV64 block invariants

`retireModel` instantiates the shared retirement laws with the local decoded
RV64 fragment: every instruction may write only its `rd` (a write to `x0` is
discarded) and advances the PC by four bytes. `byteDecoder` reads the local
32-bit codec as four little-endian bytes. Both are local handwritten models,
not proved to match the generated Sail model.
Instruction-address alignment, fetch from memory, and compressed encodings are
outside these instances.
-/

@[expose] public section

namespace Silmaril.RiscV

open Machine

/-- The local RV64 fragment as a sequential retirement model. -/
def retireModel : RetireModel Instr State Reg Word where
  read := State.read
  pc := State.pc
  step := step
  writes instr reg := reg = instr.dest
  pcDelta _ := 4
  step_pc instr state := step_pc instr state
  step_read_other instr state reg h := step_read_other instr state reg h

@[simp] theorem retireModel_read : retireModel.read = State.read := rfl
@[simp] theorem retireModel_pc : retireModel.pc = State.pc := rfl
@[simp] theorem retireModel_step : retireModel.step = step := rfl
@[simp] theorem retireModel_pcDelta (instr : Instr) : retireModel.pcDelta instr = 4 := rfl

@[simp] theorem retireModel_writes (instr : Instr) (reg : Reg) :
    retireModel.writes instr reg ↔ reg = instr.dest := Iff.rfl

/-- The PC accounts for the number of retired four-byte instructions, modulo 2^64. -/
theorem run_pc (code : List Instr) (s : State) :
    (Block.run step code s).pc = s.pc + BitVec.ofNat 64 (4 * code.length) :=
  retireModel.run_pc_uniform 4 (fun _ => rfl) code s

/-- Registers outside a block's destination set retain their architectural value. -/
theorem run_read_frame (code : List Instr) (s : State) (r : Reg)
    (h : ∀ i ∈ code, r ≠ i.dest) :
    (Block.run step code s).read r = s.read r :=
  retireModel.run_read_frame code s r h

/-- The four little-endian bytes of an instruction's 32-bit encoding. -/
def encodeBytes (instr : Instr) : List (BitVec 8) :=
  let word := encode instr
  [word.extractLsb' 0 8, word.extractLsb' 8 8, word.extractLsb' 16 8, word.extractLsb' 24 8]

/-- Decode one supported instruction from the first four bytes, little-endian. -/
def decodeBytes : List (BitVec 8) → Option (Instr × Nat)
  | byte0 :: byte1 :: byte2 :: byte3 :: _ =>
    (decode (byte3 ++ byte2 ++ byte1 ++ byte0)).map fun instr => (instr, 4)
  | _ => none

@[simp] theorem encodeBytes_length (instr : Instr) : (encodeBytes instr).length = 4 := rfl

theorem encodeBytes_word (instr : Instr) :
    (encode instr).extractLsb' 24 8 ++ (encode instr).extractLsb' 16 8 ++
      (encode instr).extractLsb' 8 8 ++ (encode instr).extractLsb' 0 8 = encode instr := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

theorem decodeBytes_length {bytes : List (BitVec 8)} {instr : Instr} {length : Nat}
    (h : decodeBytes bytes = some (instr, length)) : length = 4 ∧ 4 ≤ bytes.length := by
  match bytes, h with
  | _ :: _ :: _ :: _ :: _, h =>
    simp only [decodeBytes, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h
    simp

/-- The local RV64 codec as a byte decoder. It accepts exactly the four-byte
little-endian forms of `encode`, followed by any bytes. -/
def byteDecoder : Decoder Instr where
  decode := decodeBytes
  encode := encodeBytes
  decode_length_pos h := by rw [(decodeBytes_length h).1]; decide
  decode_length_le h := by rw [(decodeBytes_length h).1]; exact (decodeBytes_length h).2
  decode_append {bytes} _ _ extra h := by
    match bytes, h with
    | _ :: _ :: _ :: _ :: _, h => exact h
  decode_take {bytes} _ _ h := by
    obtain ⟨rfl, -⟩ := decodeBytes_length h
    match bytes, h with
    | _ :: _ :: _ :: _ :: _, h => exact h
  decode_encode_append instr rest := by
    simp [encodeBytes, decodeBytes, encodeBytes_word]

theorem decodeBytes_eq_some {bytes : List (BitVec 8)} {instr : Instr} {length : Nat}
    (h : decodeBytes bytes = some (instr, length)) :
    length = 4 ∧ bytes = encodeBytes instr ++ bytes.drop 4 := by
  match bytes, h with
  | byte0 :: byte1 :: byte2 :: byte3 :: rest, h =>
    simp only [decodeBytes, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, hdecode, rfl, rfl⟩ := h
    have hencode := encode_decode hdecode
    refine ⟨rfl, ?_⟩
    simp only [encodeBytes, hencode, List.drop_succ_cons, List.drop_zero, List.cons_append,
      List.nil_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [BitVec.extractLsb'_append_eq_of_le (show 8 ≤ 8 from Nat.le_refl 8),
        BitVec.extractLsb'_append_eq_of_le (show 8 ≤ 16 by decide),
        BitVec.extractLsb'_append_eq_of_le (show 8 ≤ 24 by decide), Nat.reduceSub,
        BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_eq_self]

/-- The PC advance of a block equals the byte length of its little-endian encoding. -/
theorem run_pc_encodeBlock (code : List Instr) (s : State) :
    (Block.run step code s).pc = s.pc + BitVec.ofNat 64 (byteDecoder.encodeBlock code).length :=
  byteDecoder.run_pc_encodeBlock retireModel (fun _ => rfl) code s

end Silmaril.RiscV
