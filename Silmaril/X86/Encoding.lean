module

public import Silmaril.X86.Semantics
public import Silmaril.Process.Memory

/-!
# Variable-length byte encodings for the x86-64 integer subset

Each instruction of `Instr` is encoded in its 64-bit-mode register-direct form,
following the Intel SDM opcode tables:

| Instruction | Bytes |
| --- | --- |
| `mov dst, src` | `REX.W(R=src, B=dst) 89 /r` |
| `op dst, src` | `REX.W(R=src, B=dst) opc /r`, opc = 01 ADD, 09 OR, 21 AND, 29 SUB, 31 XOR, 39 CMP |
| `op dst, imm32` | `REX.W(B=dst) 81 /digit id`, digit = 0 ADD, 1 OR, 4 AND, 5 SUB, 6 XOR, 7 CMP |
| `mov dst, imm32` | `REX.W(B=dst) C7 /0 id` |
| `not dst` / `neg dst` | `REX.W(B=dst) F7 /2` / `REX.W(B=dst) F7 /3` |

The ModRM byte always has `mod = 11` (register operand), and `id` is the 32-bit
immediate in little-endian order. The decoder accepts exactly these canonical
byte strings: one REX prefix with W = 1 and X = 0, followed by the opcode and a
`mod = 11` ModRM byte, and R = 0 in the `/digit` forms. It returns the decoded
instruction and the number of bytes consumed, and `none` otherwise. `none` means
"outside this canonical subset", not "invalid on hardware". Valid encodings
rejected here include redundant prefixes, a set X bit or a set R bit in a
`/digit` form (which processors ignore), the reversed-direction register forms
`REX.W 8B/03/0B/2B/23/33/3B /r` (for example `48 8B C7`, `mov rax, rdi`), the
accumulator forms `REX.W 05/0D/25/2D/35/3D id`, the sign-extended imm8 forms
`REX.W 83 /digit ib`, and all memory operands.

The proofs are a handwritten codec's round trip, canonicity and truncation
properties. They do not show agreement with the Sail, ACL2 or hardware decoders.
-/

@[expose] public section

namespace Silmaril.X86

/-- A byte of instruction memory, reducibly the same type as `Process.Byte`. -/
abbrev Byte := BitVec 8

example : Byte = Process.Byte := rfl

/-- `0100WRXB` with W = 1 and X = 0. -/
def rex (r b : BitVec 1) : Byte := 0b0100#4 ++ 1#1 ++ r ++ 0#1 ++ b

/-- A register-direct ModRM byte: `mod = 11`. -/
def modrm (reg rm : BitVec 3) : Byte := 3#2 ++ reg ++ rm

/-- A 32-bit immediate in little-endian byte order. -/
def imm32Bytes (imm : BitVec 32) : List Byte :=
  [imm.extractLsb' 0 8, imm.extractLsb' 8 8, imm.extractLsb' 16 8, imm.extractLsb' 24 8]

/-- The `OP r/m64, r64` opcode. -/
def AluOp.opcode : AluOp → Byte
  | .add => 0x01 | .or => 0x09 | .and => 0x21 | .sub => 0x29 | .xor => 0x31 | .cmp => 0x39

/-- The ModRM opcode extension of `81 /digit` (`OP r/m64, imm32`). -/
def AluOp.digit : AluOp → BitVec 3
  | .add => 0 | .or => 1 | .and => 4 | .sub => 5 | .xor => 6 | .cmp => 7

def AluOp.ofOpcode (b : Byte) : Option AluOp :=
  if b = 0x01 then some .add else if b = 0x09 then some .or
  else if b = 0x21 then some .and else if b = 0x29 then some .sub
  else if b = 0x31 then some .xor else if b = 0x39 then some .cmp else none

/-- Digits 2 and 3 (ADC and SBB) are outside the subset. -/
def AluOp.ofDigit (d : BitVec 3) : Option AluOp :=
  if d = 0 then some .add else if d = 1 then some .or
  else if d = 4 then some .and else if d = 5 then some .sub
  else if d = 6 then some .xor else if d = 7 then some .cmp else none

def encode : Instr → List Byte
  | .movRR dst src => [rex src.hi dst.hi, 0x89, modrm src.lo dst.lo]
  | .movRI dst imm => [rex 0 dst.hi, 0xC7, modrm 0 dst.lo] ++ imm32Bytes imm
  | .alu op dst src => [rex src.hi dst.hi, op.opcode, modrm src.lo dst.lo]
  | .aluI op dst imm => [rex 0 dst.hi, 0x81, modrm op.digit dst.lo] ++ imm32Bytes imm
  | .not dst => [rex 0 dst.hi, 0xF7, modrm 2 dst.lo]
  | .neg dst => [rex 0 dst.hi, 0xF7, modrm 3 dst.lo]

/-- Read a little-endian 32-bit immediate from the first four bytes. -/
def decodeImm32 : List Byte → Option (BitVec 32)
  | b0 :: b1 :: b2 :: b3 :: _ => some (b3 ++ b2 ++ b1 ++ b0)
  | _ => none

/-- Decode after a well-formed REX prefix and `mod = 11` ModRM byte, given the
REX.R and REX.B bits, the opcode, the ModRM `reg` and `rm` fields and the bytes
after the ModRM byte. -/
def decodeBody (r b : BitVec 1) (opc : Byte) (reg rm : BitVec 3) (rest : List Byte) :
    Option (Instr × Nat) :=
  let dst := Reg.ofBitVec (b ++ rm)
  if opc = 0x89#8 then some (.movRR dst (Reg.ofBitVec (r ++ reg)), 3)
  else match AluOp.ofOpcode opc with
  | some op => some (.alu op dst (Reg.ofBitVec (r ++ reg)), 3)
  | none =>
    if r = 0#1 then
      if opc = 0x81#8 then
        match AluOp.ofDigit reg, decodeImm32 rest with
        | some op, some imm => some (.aluI op dst imm, 7)
        | _, _ => none
      else if opc = 0xC7#8 ∧ reg = 0#3 then
        (decodeImm32 rest).map fun imm => (.movRI dst imm, 7)
      else if opc = 0xF7#8 ∧ reg = 2#3 then some (.not dst, 3)
      else if opc = 0xF7#8 ∧ reg = 3#3 then some (.neg dst, 3)
      else none
    else none

/-- Decode one instruction from the start of `bytes`, returning it with the
number of bytes consumed. Only the bytes of the instruction itself are read. -/
def decode : List Byte → Option (Instr × Nat)
  | p :: opc :: m :: rest =>
    if p.extractLsb' 3 5 = 0x09#5 ∧ p.extractLsb' 1 1 = 0#1 ∧ m.extractLsb' 6 2 = 3#2 then
      decodeBody (p.extractLsb' 2 1) (p.extractLsb' 0 1) opc (m.extractLsb' 3 3)
        (m.extractLsb' 0 3) rest
    else none
  | _ => none

/-! ## Lengths -/

/-- `Instr.length`, used by `step` to advance RIP, is the encoded length. -/
@[simp] theorem length_encode (i : Instr) : (encode i).length = i.length := by
  cases i <;> rfl

/-- `step` advances RIP by the number of encoded bytes, modulo 2^64. -/
theorem step_rip_encode (i : Instr) (s : State) :
    (step i s).rip = s.rip + BitVec.ofNat 64 (encode i).length := by
  rw [length_encode, step_rip]

/-! ## Field lemmas -/

section Fields

@[simp] theorem rex_type (r b : BitVec 1) : (rex r b).extractLsb' 3 5 = 0x09#5 := by
  revert r b; decide

@[simp] theorem rex_x (r b : BitVec 1) : (rex r b).extractLsb' 1 1 = 0#1 := by
  revert r b; decide

@[simp] theorem rex_r (r b : BitVec 1) : (rex r b).extractLsb' 2 1 = r := by
  revert r b; decide

@[simp] theorem rex_b (r b : BitVec 1) : (rex r b).extractLsb' 0 1 = b := by
  revert r b; decide

@[simp] theorem modrm_mod (reg rm : BitVec 3) : (modrm reg rm).extractLsb' 6 2 = 3#2 := by
  revert reg rm; decide

@[simp] theorem modrm_reg (reg rm : BitVec 3) : (modrm reg rm).extractLsb' 3 3 = reg := by
  revert reg rm; decide

@[simp] theorem modrm_rm (reg rm : BitVec 3) : (modrm reg rm).extractLsb' 0 3 = rm := by
  revert reg rm; decide

theorem rex_of_fields (p : Byte) (h1 : p.extractLsb' 3 5 = 0x09#5) (h2 : p.extractLsb' 1 1 = 0#1) :
    rex (p.extractLsb' 2 1) (p.extractLsb' 0 1) = p := by
  revert p; decide

theorem modrm_of_fields (m : Byte) (h : m.extractLsb' 6 2 = 3#2) :
    modrm (m.extractLsb' 3 3) (m.extractLsb' 0 3) = m := by
  revert m; decide

@[simp] theorem Reg.hi_ofBitVec (hi : BitVec 1) (lo : BitVec 3) :
    (Reg.ofBitVec (hi ++ lo)).hi = hi := by
  revert hi lo; decide

@[simp] theorem Reg.lo_ofBitVec (hi : BitVec 1) (lo : BitVec 3) :
    (Reg.ofBitVec (hi ++ lo)).lo = lo := by
  revert hi lo; decide

@[simp] theorem AluOp.ofOpcode_opcode (op : AluOp) : AluOp.ofOpcode op.opcode = some op := by
  cases op <;> decide

theorem AluOp.opcode_of_ofOpcode {b : Byte} {op : AluOp} (h : AluOp.ofOpcode b = some op) :
    op.opcode = b := by
  unfold AluOp.ofOpcode at h
  split_ifs at h <;> cases h <;> simp_all [AluOp.opcode]

@[simp] theorem AluOp.ofDigit_digit (op : AluOp) : AluOp.ofDigit op.digit = some op := by
  cases op <;> decide

theorem AluOp.digit_of_ofDigit {d : BitVec 3} {op : AluOp} (h : AluOp.ofDigit d = some op) :
    op.digit = d := by
  unfold AluOp.ofDigit at h
  split_ifs at h <;> cases h <;> simp_all [AluOp.digit]

@[simp] theorem length_imm32Bytes (imm : BitVec 32) : (imm32Bytes imm).length = 4 := rfl

@[simp] theorem decodeImm32_imm32Bytes (imm : BitVec 32) (rest : List Byte) :
    decodeImm32 (imm32Bytes imm ++ rest) = some imm := by
  simp only [imm32Bytes, decodeImm32, List.cons_append, List.nil_append, Option.some.injEq]
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb', BitVec.extractLsb'_eq_self]

theorem imm32Bytes_of_decodeImm32 {rest : List Byte} {imm : BitVec 32}
    (h : decodeImm32 rest = some imm) : imm32Bytes imm ++ rest.drop 4 = rest := by
  match rest, h with
  | b0 :: b1 :: b2 :: b3 :: tail, h =>
    simp only [decodeImm32, Option.some.injEq] at h
    subst h
    simp only [imm32Bytes, List.drop_succ_cons, List.drop_zero, List.cons_append,
      List.nil_append, List.cons.injEq, and_true]
    refine ⟨BitVec.extractLsb'_append_eq_right, ?_, ?_, ?_⟩
    · rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
      exact BitVec.extractLsb'_append_eq_right
    · rw [BitVec.extractLsb'_append_eq_of_le (by decide),
        BitVec.extractLsb'_append_eq_of_le (by decide)]
      exact BitVec.extractLsb'_append_eq_right
    · rw [BitVec.extractLsb'_append_eq_of_le (by decide),
        BitVec.extractLsb'_append_eq_of_le (by decide),
        BitVec.extractLsb'_append_eq_of_le (by decide)]
      exact BitVec.extractLsb'_eq_self

end Fields

/-! ## Round trip, canonicity and truncation -/

/-- Decoding an encoding consumes exactly its bytes, whatever follows it. -/
@[simp] theorem decode_encode_append (i : Instr) (rest : List Byte) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  cases i with
  | alu op dst src =>
    cases op <;> simp [encode, decode, decodeBody, AluOp.opcode, AluOp.ofOpcode]
  | _ => simp [encode, decode, decodeBody, AluOp.ofOpcode]

@[simp] theorem decode_encode (i : Instr) : decode (encode i) = some (i, (encode i).length) := by
  simpa using decode_encode_append i []

theorem encode_injective : Function.Injective encode := by
  intro i j h
  have := decode_encode i
  rw [h, decode_encode] at this
  exact (Prod.mk.inj (Option.some.inj this)).1.symm

private theorem decodeBody_sound {r b : BitVec 1} {opc : Byte} {reg rm : BitVec 3}
    {rest : List Byte} {i : Instr} {n : Nat}
    (h : decodeBody r b opc reg rm rest = some (i, n)) :
    n = (encode i).length ∧ encode i ++ rest.drop (n - 3) = rex r b :: opc :: modrm reg rm :: rest := by
  unfold decodeBody at h
  by_cases h89 : opc = 0x89#8
  · simp only [h89, ite_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst h89
    simp [encode]
  simp only [h89, ite_false] at h
  cases hop : AluOp.ofOpcode opc with
  | some op =>
    simp only [hop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encode, AluOp.opcode_of_ofOpcode hop]
  | none =>
  simp only [hop] at h
  by_cases hr : r = 0#1
  swap
  · simp [hr] at h
  subst hr
  by_cases h81 : opc = 0x81#8
  · subst h81
    cases hd : AluOp.ofDigit reg with
    | none => simp [hd] at h
    | some op =>
      cases himm : decodeImm32 rest with
      | none => simp [hd, himm] at h
      | some imm =>
        simp only [hd, himm, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [encode, AluOp.digit_of_ofDigit hd, imm32Bytes_of_decodeImm32 himm]
  simp only [h81, ite_true, ite_false] at h
  by_cases hc7 : opc = 0xC7#8 ∧ reg = 0#3
  · obtain ⟨rfl, rfl⟩ := hc7
    cases himm : decodeImm32 rest with
    | none => simp [himm] at h
    | some imm =>
      simp only [himm, and_self, ite_true, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [encode, imm32Bytes_of_decodeImm32 himm]
  simp only [hc7, ite_false] at h
  by_cases hf2 : opc = 0xF7#8 ∧ reg = 2#3
  · obtain ⟨rfl, rfl⟩ := hf2
    simp only [and_self, ite_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encode]
  simp only [hf2, ite_false] at h
  by_cases hf3 : opc = 0xF7#8 ∧ reg = 3#3
  · obtain ⟨rfl, rfl⟩ := hf3
    simp only [and_self, ite_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encode]
  simp [hf3] at h

/-- A successful decode consumes exactly the canonical encoding of its result,
which is a prefix of the input. -/
theorem decode_sound {bytes : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) :
    n = (encode i).length ∧ n ≤ bytes.length ∧ bytes = encode i ++ bytes.drop n := by
  match bytes, h with
  | p :: opc :: m :: rest, h =>
    simp only [decode] at h
    split_ifs at h with hc
    obtain ⟨h1, h2, h3⟩ := hc
    obtain ⟨hn, hb⟩ := decodeBody_sound h
    rw [rex_of_fields p h1 h2, modrm_of_fields m h3] at hb
    have hlen := congrArg List.length hb
    simp only [List.length_append, List.length_drop, List.length_cons] at hlen
    have h3n : 3 ≤ n := by
      subst hn; cases i <;> simp [encode, imm32Bytes]
    refine ⟨hn, by simp only [List.length_cons]; omega, ?_⟩
    have hdrop : (p :: opc :: m :: rest).drop n = rest.drop (n - 3) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      simp
    rw [hdrop, hb]

theorem decode_eq_some_iff {bytes : List Byte} {i : Instr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = (encode i).length ∧ encode i <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, -, hb⟩ := decode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

/-- Decoding reads no byte beyond the instruction: appending bytes to an input
that decodes does not change the result. -/
theorem decode_append {bytes more : List Byte} {i : Instr} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

/-- Canonicity: two encodings cannot overlap as prefixes of one byte string, so
at most one instruction decodes from any input. -/
theorem decode_unique {bytes : List Byte} {i j : Instr} (hi : encode i <+: bytes)
    (hj : encode j <+: bytes) : i = j := by
  obtain ⟨ri, rfl⟩ := hi
  obtain ⟨rj, hj⟩ := hj
  have h := decode_encode_append i ri
  rw [← hj, decode_encode_append] at h
  exact (Prod.mk.inj (Option.some.inj h)).1.symm

/-- Every proper prefix of an encoding is rejected. -/
theorem decode_take_of_lt (i : Instr) {k : Nat} (hk : k < (encode i).length) :
    decode ((encode i).take k) = none := by
  cases hd : decode ((encode i).take k) with
  | none => rfl
  | some res =>
    obtain ⟨j, n⟩ := res
    obtain ⟨hn, hle, hb⟩ := decode_sound hd
    have hji : j = i := decode_unique (bytes := encode i)
      ⟨_, (by rw [← List.append_assoc, ← hb, List.take_append_drop] :
        encode j ++ (((encode i).take k).drop n ++ (encode i).drop k) = encode i)⟩
      (List.prefix_refl _)
    subst hji
    simp only [List.length_take] at hle
    omega

end Silmaril.X86
