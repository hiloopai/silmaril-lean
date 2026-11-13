module

public import Silmaril.Machine.RiscV.Ext.Instr.Defs
public import Silmaril.Machine.RiscV.Encoding.Defs
/-!
# Machine encodings for the extended RV64 language

`encode` uses the standard 32-bit I, R, S, B, U and J formats of the RISC-V
unprivileged specification, and on `Instr.ofBase` it is exactly
`RiscV.encode` (`encode_ofBase`). `decode` accepts precisely the image of
`encode` (`decode_eq_some_iff`): a word decodes to `i` if and only if it is
`encode i`. Words outside the image, including compressed encodings, reserved
shift encodings, `FENCE`, `ECALL`, CSR and floating-point instructions, decode
to `none`. `none` means "outside this subset", not an architectural decision.

The decoder is implemented as the base decoder, falling back to a field parser
whose result is kept only if it re-encodes to the input word. The round trip
`decode_encode` is proved by computation on symbolic fields.

This is a handwritten codec, not a proof that the generated Sail decoder
agrees with it.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

/-! ## Function fields -/

def RegWOp.funct3 : RegWOp → BitVec 3
  | .add | .sub => 0#3
  | .sll => 1#3
  | .srl | .sra => 5#3

def RegWOp.funct7 : RegWOp → BitVec 7
  | .sub | .sra => 0x20#7
  | _ => 0#7

def shiftWFunct7 : ShiftOp → BitVec 7
  | .sra => 0x20#7
  | _ => 0#7

def MulOp.funct3 : MulOp → BitVec 3
  | .mul => 0#3
  | .mulh => 1#3
  | .mulhsu => 2#3
  | .mulhu => 3#3
  | .div => 4#3
  | .divu => 5#3
  | .rem => 6#3
  | .remu => 7#3

def MulWOp.funct3 : MulWOp → BitVec 3
  | .mulw => 0#3
  | .divw => 4#3
  | .divuw => 5#3
  | .remw => 6#3
  | .remuw => 7#3

def LoadOp.funct3 : LoadOp → BitVec 3
  | .lb => 0#3
  | .lh => 1#3
  | .lw => 2#3
  | .ld => 3#3
  | .lbu => 4#3
  | .lhu => 5#3
  | .lwu => 6#3

def StoreOp.funct3 : StoreOp → BitVec 3
  | .sb => 0#3
  | .sh => 1#3
  | .sw => 2#3
  | .sd => 3#3

def BranchOp.funct3 : BranchOp → BitVec 3
  | .eq => 0#3
  | .ne => 1#3
  | .lt => 4#3
  | .ge => 5#3
  | .ltu => 6#3
  | .geu => 7#3

/-! ## Encoding -/

/-- The 32-bit encoding of `EBREAK`. -/
def ebreakWord : BitVec 32 := 0x00100073#32

def Compute.encode : Compute → BitVec 32
  | .base instr => RiscV.encode instr
  | .addiw rd rs1 imm => imm ++ rs1 ++ 0#3 ++ rd ++ 0x1B#7
  | .shiftW op rd rs1 amount =>
      shiftWFunct7 op ++ amount ++ rs1 ++ ShiftOp.funct3 op ++ rd ++ 0x1B#7
  | .regW op rd rs1 rs2 => RegWOp.funct7 op ++ rs2 ++ rs1 ++ RegWOp.funct3 op ++ rd ++ 0x3B#7
  | .mulDiv op rd rs1 rs2 => 1#7 ++ rs2 ++ rs1 ++ MulOp.funct3 op ++ rd ++ 0x33#7
  | .mulDivW op rd rs1 rs2 => 1#7 ++ rs2 ++ rs1 ++ MulWOp.funct3 op ++ rd ++ 0x3B#7

/-- Encode one instruction as a 32-bit RISC-V machine instruction. -/
def encode : Instr → BitVec 32
  | .compute c => c.encode
  | .load op rd rs1 offset => offset ++ rs1 ++ LoadOp.funct3 op ++ rd ++ 0x03#7
  | .store op rs1 rs2 offset =>
      offset.extractLsb' 5 7 ++ rs2 ++ rs1 ++ StoreOp.funct3 op ++ offset.extractLsb' 0 5 ++ 0x23#7
  | .branch op rs1 rs2 half =>
      half.extractLsb' 11 1 ++ half.extractLsb' 4 6 ++ rs2 ++ rs1 ++ BranchOp.funct3 op ++
        half.extractLsb' 0 4 ++ half.extractLsb' 10 1 ++ 0x63#7
  | .jal rd half =>
      half.extractLsb' 19 1 ++ half.extractLsb' 0 10 ++ half.extractLsb' 10 1 ++
        half.extractLsb' 11 8 ++ rd ++ 0x6F#7
  | .jalr rd rs1 offset => offset ++ rs1 ++ 0#3 ++ rd ++ 0x67#7
  | .ebreak => ebreakWord

@[simp] theorem encode_ofBase (instr : RiscV.Instr) :
    encode (.ofBase instr) = RiscV.encode instr := rfl

/-! ## Decoding -/

/-- A permissive field parser for the instructions outside the base fragment.
Its result is only trusted after re-encoding (`decode`). -/
def parse (word : BitVec 32) : Option Instr :=
  let opcode := word.extractLsb' 0 7
  let rd := word.extractLsb' 7 5
  let funct3 := word.extractLsb' 12 3
  let rs1 := word.extractLsb' 15 5
  let rs2 := word.extractLsb' 20 5
  let funct7 := word.extractLsb' 25 7
  let immI := word.extractLsb' 20 12
  let immS := word.extractLsb' 25 7 ++ word.extractLsb' 7 5
  let halfB := word.extractLsb' 31 1 ++ word.extractLsb' 7 1 ++ word.extractLsb' 25 6 ++
    word.extractLsb' 8 4
  let halfJ := word.extractLsb' 31 1 ++ word.extractLsb' 12 8 ++ word.extractLsb' 20 1 ++
    word.extractLsb' 21 10
  if opcode = 0x1B#7 then
    if funct3 = 0#3 then some (.compute (.addiw rd rs1 immI))
    else if funct3 = 1#3 then some (.compute (.shiftW .sll rd rs1 rs2))
    else if funct3 = 5#3 then
      if funct7 = 0x20#7 then some (.compute (.shiftW .sra rd rs1 rs2))
      else some (.compute (.shiftW .srl rd rs1 rs2))
    else none
  else if opcode = 0x3B#7 then
    if funct7 = 1#7 then
      if funct3 = 0#3 then some (.compute (.mulDivW .mulw rd rs1 rs2))
      else if funct3 = 4#3 then some (.compute (.mulDivW .divw rd rs1 rs2))
      else if funct3 = 5#3 then some (.compute (.mulDivW .divuw rd rs1 rs2))
      else if funct3 = 6#3 then some (.compute (.mulDivW .remw rd rs1 rs2))
      else if funct3 = 7#3 then some (.compute (.mulDivW .remuw rd rs1 rs2))
      else none
    else if funct3 = 0#3 then
      if funct7 = 0x20#7 then some (.compute (.regW .sub rd rs1 rs2))
      else some (.compute (.regW .add rd rs1 rs2))
    else if funct3 = 1#3 then some (.compute (.regW .sll rd rs1 rs2))
    else if funct3 = 5#3 then
      if funct7 = 0x20#7 then some (.compute (.regW .sra rd rs1 rs2))
      else some (.compute (.regW .srl rd rs1 rs2))
    else none
  else if opcode = 0x33#7 then
    if funct3 = 0#3 then some (.compute (.mulDiv .mul rd rs1 rs2))
    else if funct3 = 1#3 then some (.compute (.mulDiv .mulh rd rs1 rs2))
    else if funct3 = 2#3 then some (.compute (.mulDiv .mulhsu rd rs1 rs2))
    else if funct3 = 3#3 then some (.compute (.mulDiv .mulhu rd rs1 rs2))
    else if funct3 = 4#3 then some (.compute (.mulDiv .div rd rs1 rs2))
    else if funct3 = 5#3 then some (.compute (.mulDiv .divu rd rs1 rs2))
    else if funct3 = 6#3 then some (.compute (.mulDiv .rem rd rs1 rs2))
    else some (.compute (.mulDiv .remu rd rs1 rs2))
  else if opcode = 0x03#7 then
    if funct3 = 0#3 then some (.load .lb rd rs1 immI)
    else if funct3 = 1#3 then some (.load .lh rd rs1 immI)
    else if funct3 = 2#3 then some (.load .lw rd rs1 immI)
    else if funct3 = 3#3 then some (.load .ld rd rs1 immI)
    else if funct3 = 4#3 then some (.load .lbu rd rs1 immI)
    else if funct3 = 5#3 then some (.load .lhu rd rs1 immI)
    else if funct3 = 6#3 then some (.load .lwu rd rs1 immI)
    else none
  else if opcode = 0x23#7 then
    if funct3 = 0#3 then some (.store .sb rs1 rs2 immS)
    else if funct3 = 1#3 then some (.store .sh rs1 rs2 immS)
    else if funct3 = 2#3 then some (.store .sw rs1 rs2 immS)
    else if funct3 = 3#3 then some (.store .sd rs1 rs2 immS)
    else none
  else if opcode = 0x63#7 then
    if funct3 = 0#3 then some (.branch .eq rs1 rs2 halfB)
    else if funct3 = 1#3 then some (.branch .ne rs1 rs2 halfB)
    else if funct3 = 4#3 then some (.branch .lt rs1 rs2 halfB)
    else if funct3 = 5#3 then some (.branch .ge rs1 rs2 halfB)
    else if funct3 = 6#3 then some (.branch .ltu rs1 rs2 halfB)
    else if funct3 = 7#3 then some (.branch .geu rs1 rs2 halfB)
    else none
  else if opcode = 0x6F#7 then some (.jal rd halfJ)
  else if opcode = 0x67#7 then some (.jalr rd rs1 immI)
  else if word = ebreakWord then some .ebreak
  else none

/-- Decode exactly the encodings of `Instr`. Base words decode as in `RiscV.decode`. -/
def decode (word : BitVec 32) : Option Instr :=
  match RiscV.decode word with
  | some instr => some (.ofBase instr)
  | none =>
    match parse word with
    | some instr => if encode instr = word then some instr else none
    | none => none

/-- Every accepted word is exactly the machine encoding of its decoded instruction. -/
theorem encode_decode {word : BitVec 32} {instr : Instr} (h : decode word = some instr) :
    encode instr = word := by
  unfold decode at h
  split at h
  · rename_i base hbase
    cases h
    exact RiscV.encode_decode hbase
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

private theorem half12 (h : BitVec 12) :
    h.extractLsb' 11 1 ++ h.extractLsb' 10 1 ++ h.extractLsb' 4 6 ++ h.extractLsb' 0 4 = h := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

private theorem half20 (h : BitVec 20) :
    h.extractLsb' 19 1 ++ h.extractLsb' 11 8 ++ h.extractLsb' 10 1 ++ h.extractLsb' 0 10 = h := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

private theorem immS12 (h : BitVec 12) : h.extractLsb' 5 7 ++ h.extractLsb' 0 5 = h := by
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

/-! The field parser recovers every non-base instruction from its encoding. -/

private abbrev Parses (instr : Instr) : Prop :=
  RiscV.decode (encode instr) = none ∧ parse (encode instr) = some instr

private theorem parses_addiw (rd rs1 : Reg) (imm : BitVec 12) :
    Parses (.compute (.addiw rd rs1 imm)) := by
  simp only [Parses, encode, Compute.encode, parse, RiscV.decode,
    BitVec.extractLsb'_append_eq_ite]; simp

private theorem parses_shiftW (op : ShiftOp) (rd rs1 : Reg) (amount : BitVec 5) :
    Parses (.compute (.shiftW op rd rs1 amount)) := by
  cases op <;> simp only [Parses, encode, Compute.encode, parse, RiscV.decode, shiftWFunct7,
    ShiftOp.funct3, BitVec.extractLsb'_append_eq_ite] <;> simp

private theorem parses_regW (op : RegWOp) (rd rs1 rs2 : Reg) :
    Parses (.compute (.regW op rd rs1 rs2)) := by
  cases op <;> simp only [Parses, encode, Compute.encode, parse, RiscV.decode, RegWOp.funct7,
    RegWOp.funct3, BitVec.extractLsb'_append_eq_ite] <;> simp

private theorem parses_mulDiv (op : MulOp) (rd rs1 rs2 : Reg) :
    Parses (.compute (.mulDiv op rd rs1 rs2)) := by
  cases op <;> simp only [Parses, encode, Compute.encode, parse, RiscV.decode, MulOp.funct3,
    BitVec.extractLsb'_append_eq_ite] <;> simp

private theorem parses_mulDivW (op : MulWOp) (rd rs1 rs2 : Reg) :
    Parses (.compute (.mulDivW op rd rs1 rs2)) := by
  cases op <;> simp only [Parses, encode, Compute.encode, parse, RiscV.decode, MulWOp.funct3,
    BitVec.extractLsb'_append_eq_ite] <;> simp

private theorem parses_load (op : LoadOp) (rd rs1 : Reg) (offset : BitVec 12) :
    Parses (.load op rd rs1 offset) := by
  cases op <;> simp only [Parses, encode, parse, RiscV.decode, LoadOp.funct3,
    BitVec.extractLsb'_append_eq_ite] <;> simp

private theorem parses_store (op : StoreOp) (rs1 rs2 : Reg) (offset : BitVec 12) :
    Parses (.store op rs1 rs2 offset) := by
  cases op <;> simp only [Parses, encode, parse, RiscV.decode, StoreOp.funct3,
    BitVec.extractLsb'_append_eq_ite] <;> simp [immS12]

set_option maxHeartbeats 2000000 in
private theorem parses_branch (op : BranchOp) (rs1 rs2 : Reg) (half : BitVec 12) :
    Parses (.branch op rs1 rs2 half) := by
  cases op <;> simp only [Parses, encode, parse, RiscV.decode, BranchOp.funct3,
    BitVec.extractLsb'_append_eq_ite] <;> simp [half12]

private theorem parses_jal (rd : Reg) (half : BitVec 20) : Parses (.jal rd half) := by
  simp only [Parses, encode, parse, RiscV.decode, BitVec.extractLsb'_append_eq_ite]
  simp [half20]

private theorem parses_jalr (rd rs1 : Reg) (offset : BitVec 12) :
    Parses (.jalr rd rs1 offset) := by
  simp only [Parses, encode, parse, RiscV.decode, BitVec.extractLsb'_append_eq_ite]; simp

private theorem parses_ebreak : Parses .ebreak := by decide

private theorem parse_encode (instr : Instr) (nonbase : ∀ b, instr ≠ .ofBase b) :
    Parses instr := by
  cases instr with
  | compute c =>
    cases c with
    | base b => exact absurd rfl (nonbase b)
    | addiw => exact parses_addiw ..
    | shiftW => exact parses_shiftW ..
    | regW => exact parses_regW ..
    | mulDiv => exact parses_mulDiv ..
    | mulDivW => exact parses_mulDivW ..
  | load => exact parses_load ..
  | store => exact parses_store ..
  | branch => exact parses_branch ..
  | jal => exact parses_jal ..
  | jalr => exact parses_jalr ..
  | ebreak => exact parses_ebreak

/-- Decoding recovers every instruction, including all register and immediate values. -/
@[simp] theorem decode_encode (instr : Instr) : decode (encode instr) = some instr := by
  by_cases hb : ∃ b, instr = .ofBase b
  · obtain ⟨b, rfl⟩ := hb
    simp [decode]
  · have nonbase : ∀ b, instr ≠ .ofBase b := fun b h => hb ⟨b, h⟩
    obtain ⟨hnone, hparse⟩ := parse_encode instr nonbase
    simp [decode, hnone, hparse]

/-- The decoder's accepted words are precisely the encodings. -/
theorem decode_eq_some_iff {word : BitVec 32} {instr : Instr} :
    decode word = some instr ↔ encode instr = word := by
  constructor
  · exact encode_decode
  · intro h
    rw [← h, decode_encode]

theorem encode_injective : Function.Injective encode := by
  intro first second h
  have := congrArg decode h
  simpa using this

/-- On base words the extended decoder is the base decoder. -/
theorem decode_ofBase_iff {word : BitVec 32} {instr : RiscV.Instr} :
    decode word = some (.ofBase instr) ↔ RiscV.decode word = some instr := by
  rw [decode_eq_some_iff, RiscV.decode_eq_some_iff, encode_ofBase]

theorem decode_of_base {word : BitVec 32} {instr : RiscV.Instr}
    (h : RiscV.decode word = some instr) : decode word = some (.ofBase instr) :=
  decode_ofBase_iff.mpr h

namespace EncodingExamples

/-- `addw a0, a0, a1`. -/
example : encode (.compute (.regW .add 10#5 10#5 11#5)) = 0x00b5053b#32 := by decide
/-- `mul a0, a0, a1`. -/
example : encode (.compute (.mulDiv .mul 10#5 10#5 11#5)) = 0x02b50533#32 := by decide
/-- `divw a0, a0, a1`. -/
example : encode (.compute (.mulDivW .divw 10#5 10#5 11#5)) = 0x02b5453b#32 := by decide
/-- `ld a0, 8(sp)`. -/
example : encode (.load .ld 10#5 2#5 8#12) = 0x00813503#32 := by decide
/-- `sd a0, 8(sp)`. -/
example : encode (.store .sd 2#5 10#5 8#12) = 0x00a13423#32 := by decide
/-- `beq a0, a1, -8`. -/
example : encode (.branch .eq 10#5 11#5 (BitVec.ofInt 12 (-4))) = 0xfeb50ce3#32 := by decide
/-- `jal ra, 16`. -/
example : encode (.jal 1#5 8#20) = 0x010000ef#32 := by decide
/-- `jalr x0, 0(ra)`, that is `ret`. -/
example : encode (.jalr 0#5 1#5 0#12) = 0x00008067#32 := by decide
example : decode 0x00100073#32 = some .ebreak := by decide
/-- `ecall` remains outside the subset. -/
example : decode 0x00000073#32 = none := by decide
/-- `slliw` with a reserved sixth shift-amount bit is rejected. -/
example : decode 0x0205109b#32 = none := by decide

end EncodingExamples

end Silmaril.RiscV.Ext
