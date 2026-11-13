module

public import Silmaril.Machine.RiscV.Basic.Defs
/-!
# Machine encodings for the RV64 integer arithmetic subset

The encoder uses the unprivileged RISC-V I, R, and U instruction formats.
The decoder recognizes exactly the instructions in `Instr`; in particular,
RV64 immediate shifts use a six-bit shift amount and check all six remaining
upper bits. It rejects unsupported opcodes and function fields, compressed
instructions, and instructions outside this arithmetic subset. Admitted words
have their ordinary base-integer meaning, excluding extension reinterpretations.

This is a handwritten codec with roundtrip proofs, not a proof that an upstream
Sail decoder or an implementation agrees with this model.

Adapted from sail-riscv revision `27224ccb2290f022e46213c05b3e72e8a9ea635e`.
Upstream copyright notices and BSD-2-Clause terms are retained in
`NOTICES/sail-riscv/LICENCE`.
-/

@[expose] public section

namespace Silmaril.RiscV

def ImmOp.funct3 : ImmOp → BitVec 3
  | .add => 0#3
  | .slt => 2#3
  | .sltu => 3#3
  | .xor => 4#3
  | .or => 6#3
  | .and => 7#3

def RegOp.funct3 : RegOp → BitVec 3
  | .add | .sub => 0#3
  | .sll => 1#3
  | .slt => 2#3
  | .sltu => 3#3
  | .xor => 4#3
  | .srl | .sra => 5#3
  | .or => 6#3
  | .and => 7#3

def RegOp.funct7 : RegOp → BitVec 7
  | .sub | .sra => 0x20#7
  | _ => 0#7

def ShiftOp.funct3 : ShiftOp → BitVec 3
  | .sll => 1#3
  | .srl | .sra => 5#3

def ShiftOp.funct6 : ShiftOp → BitVec 6
  | .sra => 0x10#6
  | _ => 0#6

def UpperOp.opcode : UpperOp → BitVec 7
  | .lui => 0x37#7
  | .auipc => 0x17#7

/-- Encode one instruction as a 32-bit RISC-V machine instruction. -/
def encode : Instr → BitVec 32
  | .imm op rd rs1 value => value ++ rs1 ++ ImmOp.funct3 op ++ rd ++ 0x13#7
  | .reg op rd rs1 rs2 => RegOp.funct7 op ++ rs2 ++ rs1 ++ RegOp.funct3 op ++ rd ++ 0x33#7
  | .shift op rd rs1 amount => ShiftOp.funct6 op ++ amount ++ rs1 ++ ShiftOp.funct3 op ++ rd ++ 0x13#7
  | .upper op rd value => value ++ rd ++ UpperOp.opcode op

/-- Decode only the supported RV64 arithmetic instructions. `none` means that
the word is outside this subset, not necessarily that the full ISA rejects it. -/
def decode (word : BitVec 32) : Option Instr :=
  let opcode := word.extractLsb' 0 7
  let rd := word.extractLsb' 7 5
  let funct3 := word.extractLsb' 12 3
  let rs1 := word.extractLsb' 15 5
  let rs2 := word.extractLsb' 20 5
  let funct7 := word.extractLsb' 25 7
  let funct6 := word.extractLsb' 26 6
  let immediate := word.extractLsb' 20 12
  let amount := word.extractLsb' 20 6
  if opcode = 0x13#7 then
    if funct3 = 0#3 then some (.imm .add rd rs1 immediate)
    else if funct3 = 2#3 then some (.imm .slt rd rs1 immediate)
    else if funct3 = 3#3 then some (.imm .sltu rd rs1 immediate)
    else if funct3 = 4#3 then some (.imm .xor rd rs1 immediate)
    else if funct3 = 6#3 then some (.imm .or rd rs1 immediate)
    else if funct3 = 7#3 then some (.imm .and rd rs1 immediate)
    else if funct3 = 1#3 ∧ funct6 = 0#6 then some (.shift .sll rd rs1 amount)
    else if funct3 = 5#3 ∧ funct6 = 0#6 then some (.shift .srl rd rs1 amount)
    else if funct3 = 5#3 ∧ funct6 = 0x10#6 then some (.shift .sra rd rs1 amount)
    else none
  else if opcode = 0x33#7 then
    if funct3 = 0#3 ∧ funct7 = 0#7 then some (.reg .add rd rs1 rs2)
    else if funct3 = 0#3 ∧ funct7 = 0x20#7 then some (.reg .sub rd rs1 rs2)
    else if funct3 = 1#3 ∧ funct7 = 0#7 then some (.reg .sll rd rs1 rs2)
    else if funct3 = 2#3 ∧ funct7 = 0#7 then some (.reg .slt rd rs1 rs2)
    else if funct3 = 3#3 ∧ funct7 = 0#7 then some (.reg .sltu rd rs1 rs2)
    else if funct3 = 4#3 ∧ funct7 = 0#7 then some (.reg .xor rd rs1 rs2)
    else if funct3 = 5#3 ∧ funct7 = 0#7 then some (.reg .srl rd rs1 rs2)
    else if funct3 = 5#3 ∧ funct7 = 0x20#7 then some (.reg .sra rd rs1 rs2)
    else if funct3 = 6#3 ∧ funct7 = 0#7 then some (.reg .or rd rs1 rs2)
    else if funct3 = 7#3 ∧ funct7 = 0#7 then some (.reg .and rd rs1 rs2)
    else none
  else if opcode = 0x37#7 then some (.upper .lui rd (word.extractLsb' 12 20))
  else if opcode = 0x17#7 then some (.upper .auipc rd (word.extractLsb' 12 20))
  else none

/-- Decoding recovers every instruction, including all register and immediate values. -/
@[simp] theorem decode_encode (instruction : Instr) :
    decode (encode instruction) = some instruction := by
  cases instruction with
  | imm op rd rs1 value =>
    cases op <;> simp only [encode, decode, ImmOp.funct3,
      BitVec.extractLsb'_append_eq_ite] <;> simp
  | reg op rd rs1 rs2 =>
    cases op <;> simp only [encode, decode, RegOp.funct3, RegOp.funct7,
      BitVec.extractLsb'_append_eq_ite] <;> simp
  | shift op rd rs1 amount =>
    cases op <;> simp only [encode, decode, ShiftOp.funct3, ShiftOp.funct6,
      BitVec.extractLsb'_append_eq_ite] <;> simp
  | upper op rd value =>
    cases op <;> simp only [encode, decode, UpperOp.opcode,
      BitVec.extractLsb'_append_eq_ite] <;> simp

/-- Distinct instructions in this subset have distinct machine encodings. -/
theorem encode_injective : Function.Injective encode := by
  intro first second h
  have := congrArg decode h
  simpa using this

private theorem reassembleI (word : BitVec 32) :
    (word.extractLsb' 20 12 ++ word.extractLsb' 15 5 ++ word.extractLsb' 12 3 ++
      word.extractLsb' 7 5 ++ word.extractLsb' 0 7) = word := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb',
    BitVec.extractLsb'_eq_self]

private theorem reassembleR (word : BitVec 32) :
    (word.extractLsb' 25 7 ++ word.extractLsb' 20 5 ++ word.extractLsb' 15 5 ++
      word.extractLsb' 12 3 ++ word.extractLsb' 7 5 ++ word.extractLsb' 0 7) = word := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb',
    BitVec.extractLsb'_eq_self]

private theorem reassembleShift (word : BitVec 32) :
    (word.extractLsb' 26 6 ++ word.extractLsb' 20 6 ++ word.extractLsb' 15 5 ++
      word.extractLsb' 12 3 ++ word.extractLsb' 7 5 ++ word.extractLsb' 0 7) = word := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb',
    BitVec.extractLsb'_eq_self]

private theorem reassembleU (word : BitVec 32) :
    (word.extractLsb' 12 20 ++ word.extractLsb' 7 5 ++ word.extractLsb' 0 7) = word := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb',
    BitVec.extractLsb'_eq_self]

/-- Every accepted word is exactly the machine encoding of its decoded instruction. -/
theorem encode_decode {word : BitVec 32} {instruction : Instr}
    (h : decode word = some instruction) : encode instruction = word := by
  simp only [decode] at h
  simp only [ite_eq_iff] at h
  repeat' rcases h with ⟨hc, h⟩ | ⟨hc, h⟩
  all_goals
    first
    | simpa [encode, ImmOp.funct3, *] using reassembleI word
    | simpa [encode, RegOp.funct3, RegOp.funct7, *] using reassembleR word
    | simpa [encode, ShiftOp.funct3, ShiftOp.funct6, *] using reassembleShift word
    | simpa [encode, UpperOp.opcode, *] using reassembleU word

/-- The decoder's accepted words are precisely this subset's encodings. -/
theorem decode_eq_some_iff {word : BitVec 32} {instruction : Instr} :
    decode word = some instruction ↔ encode instruction = word := by
  constructor
  · exact encode_decode
  · intro h
    rw [← h, decode_encode]

namespace EncodingExamples

/-- `addi x1, x0, 42`. -/
example : encode (.imm .add 1#5 0#5 42#12) = 0x02a00093#32 := by decide

example : decode 0x02a00093#32 = some (.imm .add 1#5 0#5 42#12) := by decide

/-- `sub x3, x1, x2`. -/
example : encode (.reg .sub 3#5 1#5 2#5) = 0x402081b3#32 := by decide

/-- RV64's largest immediate shift amount uses bit 25. -/
example : decode 0x03f11093#32 = some (.shift .sll 1#5 2#5 63#6) := by decide

example : decode 0x43f15093#32 = some (.shift .sra 1#5 2#5 63#6) := by decide

/-- `lui x1, 0x80000`. -/
example : decode 0x800000b7#32 = some (.upper .lui 1#5 0x80000#20) := by decide

/-- An unimplemented M-extension multiplication is outside the subset. -/
example : decode 0x022081b3#32 = none := by decide

/-- Reserved high bits on an immediate shift are rejected. -/
example : decode 0x04011093#32 = none := by decide

/-- `ecall`, although part of the full ISA, is outside this subset. -/
example : decode 0x00000073#32 = none := by decide

example : decode 0x00000000#32 = none := by decide

end EncodingExamples
end Silmaril.RiscV
