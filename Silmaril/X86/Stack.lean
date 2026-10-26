module

public import Silmaril.X86.Encoding
public import Silmaril.Machine.LittleEndian
public import Silmaril.Machine.Decoder

/-!
# Stack instructions and near CALL/RET for the x86-64 subset

A handwritten local model, following the Intel SDM, of four 64-bit-mode stack
instructions added to the register subset of `Semantics.lean`:

| Instruction | Bytes |
| --- | --- |
| `push r64` | `50+r` for `rax`–`rdi`; `41 50+r` (REX.B) for `r8`–`r15` |
| `pop r64` | `58+r`; `41 58+r` |
| `call rel32` | `E8 cd`, relative to the end of the instruction |
| `ret` | `C3` |

`Insn` wraps `Instr` with these forms. Its decoder accepts exactly the canonical
byte strings in the table together with those accepted by `decode`; other REX
prefixes, the operand-size prefix and `RET imm16` are rejected, although
processors accept some of them. The codec proofs are a round trip, canonicity
and prefix independence for this handwritten decoder only; `Insn.byteDecoder`
packages them as a shared `Machine.Decoder`.

Stack accesses are eight-byte little-endian (`Machine.LittleEndian`) reads and
writes through `Process.Memory`, so the permission check covers the whole
eight-byte span, which must lie below `2^64`. `PUSH` and `CALL` compute
`RSP - 8` modulo `2^64` and store there before committing the new RSP; `POP` and
`RET` load at RSP and then add eight. `PUSH RSP` stores the incoming RSP, and
`POP RSP` leaves the loaded value in RSP. No stack instruction changes the flags.

A failed access is reported as `none` and changes nothing. The model has no
canonical-address check (`#SS`/`#GP` on non-canonical addresses), no alignment
check, no shadow stack or CET, no segment state and no memory ordering; memory is
private and sequentially consistent. It is not derived from, or proved to
correspond with, the Sail, ACL2 or any hardware description.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords wordByte)

/-- Instructions of the memory-backed machine: the register subset together with
PUSH, POP, near relative CALL and near RET. -/
inductive Insn where
  | base (instr : Instr)
  /-- `push src` (`PUSH r64`). -/
  | push (src : Reg)
  /-- `pop dst` (`POP r64`). -/
  | pop (dst : Reg)
  /-- `call rel32`: the target is the next instruction's address plus the
  sign-extended displacement. -/
  | call (rel : BitVec 32)
  /-- `ret` (near return without an immediate). -/
  | ret
  deriving DecidableEq, Repr

/-! ## Encoding -/

/-- `50+rd`, the `PUSH r64` opcode byte for low register bits `lo`. -/
def pushOpcode (lo : BitVec 3) : Byte := 0b01010#5 ++ lo

/-- `58+rd`, the `POP r64` opcode byte for low register bits `lo`. -/
def popOpcode (lo : BitVec 3) : Byte := 0b01011#5 ++ lo

/-- The canonical REX prefix for `r8`–`r15` in PUSH and POP: only REX.B set. -/
def rexB : Byte := 0x41

/-- A one-byte `opcode+rd` form, with the REX.B prefix for the high registers. -/
def encodeRegOpcode (opcode : BitVec 3 → Byte) (r : Reg) : List Byte :=
  if r.hi = 0#1 then [opcode r.lo] else [rexB, opcode r.lo]

namespace Insn

def encode : Insn → List Byte
  | .base instr => X86.encode instr
  | .push src => encodeRegOpcode pushOpcode src
  | .pop dst => encodeRegOpcode popOpcode dst
  | .call rel => 0xE8 :: imm32Bytes rel
  | .ret => [0xC3]

/-- Encoded length in bytes. -/
def length : Insn → Nat
  | .base instr => instr.length
  | .push r | .pop r => if r.hi = 0#1 then 1 else 2
  | .call _ => 5
  | .ret => 1

/-- Decode one instruction from the start of `bytes`, with the number of bytes
consumed. Only the bytes of the instruction itself are read. -/
def decode : List Byte → Option (Insn × Nat)
  | [] => none
  | b :: rest =>
    if b = 0xC3#8 then some (.ret, 1)
    else if b = 0xE8#8 then (decodeImm32 rest).map fun rel => (.call rel, 5)
    else if b.extractLsb' 3 5 = 0b01010#5 then
      some (.push (Reg.ofBitVec (0#1 ++ b.extractLsb' 0 3)), 1)
    else if b.extractLsb' 3 5 = 0b01011#5 then
      some (.pop (Reg.ofBitVec (0#1 ++ b.extractLsb' 0 3)), 1)
    else if b = rexB then
      match rest with
      | c :: _ =>
        if c.extractLsb' 3 5 = 0b01010#5 then
          some (.push (Reg.ofBitVec (1#1 ++ c.extractLsb' 0 3)), 2)
        else if c.extractLsb' 3 5 = 0b01011#5 then
          some (.pop (Reg.ofBitVec (1#1 ++ c.extractLsb' 0 3)), 2)
        else none
      | [] => none
    else (X86.decode (b :: rest)).map fun decoded => (.base decoded.1, decoded.2)

/-! ## Codec laws -/

@[simp] theorem length_encode (i : Insn) : i.encode.length = i.length := by
  cases i with
  | base instr => exact X86.length_encode instr
  | push r => simp only [encode, encodeRegOpcode, length]; split <;> rfl
  | pop r => simp only [encode, encodeRegOpcode, length]; split <;> rfl
  | call rel => rfl
  | ret => rfl

theorem length_pos (i : Insn) : 0 < i.length := by
  cases i with
  | base instr => cases instr <;> simp [length, Instr.length]
  | push r | pop r => simp only [length]; split <;> omega
  | call rel | ret => simp [length]

theorem length_le (i : Insn) : i.length ≤ 7 := by
  cases i with
  | base instr => cases instr <;> simp [length, Instr.length]
  | push r | pop r => simp only [length]; split <;> omega
  | call rel | ret => simp [length]

private theorem encode_base_head (instr : Instr) :
    ∃ r b tail, X86.encode instr = rex r b :: tail := by
  cases instr <;> exact ⟨_, _, _, rfl⟩

private theorem rex_ne_ret (r b : BitVec 1) : rex r b ≠ 0xC3#8 := by revert r b; decide
private theorem rex_ne_call (r b : BitVec 1) : rex r b ≠ 0xE8#8 := by revert r b; decide
private theorem rex_ne_rexB (r b : BitVec 1) : rex r b ≠ rexB := by revert r b; decide
private theorem rex_not_push (r b : BitVec 1) : (rex r b).extractLsb' 3 5 ≠ 0b01010#5 := by
  revert r b; decide
private theorem rex_not_pop (r b : BitVec 1) : (rex r b).extractLsb' 3 5 ≠ 0b01011#5 := by
  revert r b; decide

@[simp] private theorem pushOpcode_type (lo : BitVec 3) :
    (pushOpcode lo).extractLsb' 3 5 = 0b01010#5 := by revert lo; decide
@[simp] private theorem popOpcode_type (lo : BitVec 3) :
    (popOpcode lo).extractLsb' 3 5 = 0b01011#5 := by revert lo; decide
@[simp] private theorem pushOpcode_lo (lo : BitVec 3) :
    (pushOpcode lo).extractLsb' 0 3 = lo := by revert lo; decide
@[simp] private theorem popOpcode_lo (lo : BitVec 3) :
    (popOpcode lo).extractLsb' 0 3 = lo := by revert lo; decide
private theorem pushOpcode_ne_ret (lo : BitVec 3) : pushOpcode lo ≠ 0xC3#8 := by revert lo; decide
private theorem pushOpcode_ne_call (lo : BitVec 3) : pushOpcode lo ≠ 0xE8#8 := by
  revert lo; decide
private theorem popOpcode_ne_ret (lo : BitVec 3) : popOpcode lo ≠ 0xC3#8 := by revert lo; decide
private theorem popOpcode_ne_call (lo : BitVec 3) : popOpcode lo ≠ 0xE8#8 := by revert lo; decide
private theorem popOpcode_not_push (lo : BitVec 3) :
    (popOpcode lo).extractLsb' 3 5 ≠ 0b01010#5 := by revert lo; decide

private theorem pushOpcode_of_type (b : Byte) (h : b.extractLsb' 3 5 = 0b01010#5) :
    pushOpcode (b.extractLsb' 0 3) = b := by revert b; decide
private theorem popOpcode_of_type (b : Byte) (h : b.extractLsb' 3 5 = 0b01011#5) :
    popOpcode (b.extractLsb' 0 3) = b := by revert b; decide

private theorem reg_of_fields (r : Reg) : Reg.ofBitVec (r.hi ++ r.lo) = r :=
  Reg.ofBitVec_hi_append_lo r

private theorem hi_cases (r : Reg) : r.hi = 0#1 ∨ r.hi = 1#1 := by
  cases r <;> decide

/-- Decoding an encoding consumes exactly its bytes, whatever follows it. -/
@[simp] theorem decode_encode_append (i : Insn) (rest : List Byte) :
    decode (i.encode ++ rest) = some (i, i.encode.length) := by
  cases i with
  | base instr =>
    obtain ⟨r, b, tail, htail⟩ := encode_base_head instr
    have hd := X86.decode_encode_append instr rest
    have e : (Insn.base instr).encode = rex r b :: tail := htail
    rw [htail, List.cons_append] at hd
    rw [e, List.cons_append]
    simp only [decode, rex_ne_ret, rex_ne_call, rex_not_push, rex_not_pop, rex_ne_rexB,
      ite_false, hd, Option.map_some, List.length_cons]
  | push src =>
    have reg := Reg.ofBitVec_hi_append_lo src
    rcases hi_cases src with h | h
    · have e : (Insn.push src).encode = [pushOpcode src.lo] := by
        simp [encode, encodeRegOpcode, h]
      rw [h] at reg
      rw [e]
      simp [decode, pushOpcode_ne_ret, pushOpcode_ne_call, reg]
    · have e : (Insn.push src).encode = [rexB, pushOpcode src.lo] := by
        simp [encode, encodeRegOpcode, h]
      rw [h] at reg
      rw [e]
      simp [decode, reg, rexB]
  | pop dst =>
    have reg := Reg.ofBitVec_hi_append_lo dst
    rcases hi_cases dst with h | h
    · have e : (Insn.pop dst).encode = [popOpcode dst.lo] := by
        simp [encode, encodeRegOpcode, h]
      rw [h] at reg
      rw [e]
      simp [decode, popOpcode_ne_ret, popOpcode_ne_call, reg]
    · have e : (Insn.pop dst).encode = [rexB, popOpcode dst.lo] := by
        simp [encode, encodeRegOpcode, h]
      rw [h] at reg
      rw [e]
      simp [decode, reg, rexB]
  | call rel => simp [encode, decode]
  | ret => simp [encode, decode]

/-- Bytes starting with a REX.W prefix are decoded by the register-subset decoder. -/
theorem decode_rex (r b : BitVec 1) (rest : List Byte) :
    decode (rex r b :: rest) =
      (X86.decode (rex r b :: rest)).map fun decoded => (.base decoded.1, decoded.2) := by
  simp only [decode, rex_ne_ret, rex_ne_call, rex_not_push, rex_not_pop, rex_ne_rexB, ite_false]

theorem decode_call_cons (rest : List Byte) :
    decode (0xE8#8 :: rest) = (decodeImm32 rest).map fun rel => (.call rel, 5) := by
  simp [decode]

@[simp] theorem decode_encode (i : Insn) : decode i.encode = some (i, i.encode.length) := by
  simpa using decode_encode_append i []

theorem encode_injective : Function.Injective encode := by
  intro i j h
  have := decode_encode i
  rw [h, decode_encode] at this
  exact (Prod.mk.inj (Option.some.inj this)).1.symm

/-- A successful decode consumes exactly the canonical encoding of its result,
which is a prefix of the input. -/
theorem decode_sound {bytes : List Byte} {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : n = i.encode.length ∧ bytes = i.encode ++ bytes.drop n := by
  match bytes, h with
  | b :: rest, h =>
    simp only [decode] at h
    by_cases hret : b = 0xC3#8
    · simp only [hret, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hret
      simp [encode]
    simp only [hret, ite_false] at h
    by_cases hcall : b = 0xE8#8
    · subst hcall
      simp only [ite_true] at h
      cases himm : decodeImm32 rest with
      | none => simp [himm] at h
      | some rel =>
        simp only [himm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [encode, imm32Bytes_of_decodeImm32 himm]
    simp only [hcall, ite_false] at h
    by_cases hpush : b.extractLsb' 3 5 = 0b01010#5
    · simp only [hpush, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [encode, encodeRegOpcode, pushOpcode_of_type b hpush]
    simp only [hpush, ite_false] at h
    by_cases hpop : b.extractLsb' 3 5 = 0b01011#5
    · simp only [hpop, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [encode, encodeRegOpcode, popOpcode_of_type b hpop]
    simp only [hpop, ite_false] at h
    by_cases hrex : b = rexB
    · subst hrex
      simp only [ite_true] at h
      match rest, h with
      | c :: tail, h =>
        simp only at h
        by_cases hpush' : c.extractLsb' 3 5 = 0b01010#5
        · simp only [hpush', ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [encode, encodeRegOpcode, pushOpcode_of_type c hpush']
        simp only [hpush', ite_false] at h
        by_cases hpop' : c.extractLsb' 3 5 = 0b01011#5
        · simp only [hpop', ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [encode, encodeRegOpcode, popOpcode_of_type c hpop']
        simp [hpop'] at h
    simp only [hrex, ite_false] at h
    cases hb : X86.decode (b :: rest) with
    | none => simp [hb] at h
    | some decoded =>
      obtain ⟨instr, m⟩ := decoded
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn, -, hbytes⟩ := X86.decode_sound hb
      exact ⟨hn, hbytes⟩

theorem decode_eq_some_iff {bytes : List Byte} {i : Insn} {n : Nat} :
    decode bytes = some (i, n) ↔ n = i.encode.length ∧ i.encode <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, hb⟩ := decode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

/-- Decoding reads no byte beyond the instruction. -/
theorem decode_append {bytes : List Byte} (more : List Byte) {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes ++ more) = some (i, n) := by
  obtain ⟨hn, rest, rfl⟩ := decode_eq_some_iff.mp h
  rw [List.append_assoc, decode_encode_append, hn]

/-- A successful decode consumes between one and seven bytes of its input. -/
theorem decode_length {bytes : List Byte} {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : n = i.length ∧ 0 < n ∧ n ≤ 7 ∧ n ≤ bytes.length := by
  obtain ⟨hn, hb⟩ := decode_sound h
  rw [length_encode] at hn
  have hlen := congrArg List.length hb
  simp only [List.length_append, List.length_drop, length_encode] at hlen
  exact ⟨hn, hn ▸ length_pos i, hn ▸ length_le i, by omega⟩

/-- Decoding depends only on the consumed bytes. -/
theorem decode_take {bytes : List Byte} {i : Insn} {n : Nat}
    (h : decode bytes = some (i, n)) : decode (bytes.take n) = some (i, n) := by
  obtain ⟨hn, hb⟩ := decode_sound h
  have : bytes.take n = i.encode := by
    rw [hb, hn, List.take_left]
  rw [this, decode_encode, hn]

/-- Two encodings cannot both be prefixes of one byte string. -/
theorem decode_unique {bytes : List Byte} {i j : Insn} (hi : i.encode <+: bytes)
    (hj : j.encode <+: bytes) : i = j := by
  obtain ⟨ri, rfl⟩ := hi
  obtain ⟨rj, hj⟩ := hj
  have h := decode_encode_append i ri
  rw [← hj, decode_encode_append] at h
  exact (Prod.mk.inj (Option.some.inj h)).1.symm

/-- Every proper prefix of an encoding is rejected. -/
theorem decode_take_of_lt (i : Insn) {k : Nat} (hk : k < i.encode.length) :
    decode (i.encode.take k) = none := by
  cases hd : decode (i.encode.take k) with
  | none => rfl
  | some res =>
    obtain ⟨j, n⟩ := res
    obtain ⟨hn, hb⟩ := decode_sound hd
    have hji : j = i := decode_unique (bytes := i.encode)
      ⟨_, (by rw [← List.append_assoc, ← hb, List.take_append_drop] :
        j.encode ++ ((i.encode.take k).drop n ++ i.encode.drop k) = i.encode)⟩
      (List.prefix_refl _)
    subst hji
    have := congrArg List.length hb
    simp only [List.length_take, List.length_append, List.length_drop] at this
    omega

/-- The stack-extended codec as a shared `Machine.Decoder`. It accepts exactly
the canonical encodings (`decode_eq_some_iff`). -/
def byteDecoder : Machine.Decoder Insn where
  decode := decode
  encode := encode
  decode_length_pos h := (decode_length h).2.1
  decode_length_le h := (decode_length h).2.2.2
  decode_append extra h := decode_append extra h
  decode_take h := decode_take h
  decode_encode_append instr rest := decode_encode_append instr rest

@[simp] theorem byteDecoder_decode : byteDecoder.decode = decode := rfl
@[simp] theorem byteDecoder_encode : byteDecoder.encode = encode := rfl

end Insn

/-! ## Eight-byte little-endian stack words -/

/-- The value of exactly eight little-endian bytes, least significant first. -/
def wordOfBytes? : List Byte → Option Word
  | [b0, b1, b2, b3, b4, b5, b6, b7] => some (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)
  | _ => none

theorem encodeWords_singleton (v : Word) :
    encodeWords [v] = [wordByte v 0, wordByte v 1, wordByte v 2, wordByte v 3,
      wordByte v 4, wordByte v 5, wordByte v 6, wordByte v 7] := by
  simp [encodeWords, List.ofFn_succ]

@[simp] theorem length_encodeWords_singleton (v : Word) : (encodeWords [v]).length = 8 := by
  simp

private theorem wordByte_eq (v : Word) (i : Nat) : wordByte v i = v.extractLsb' (8 * i) 8 :=
  BitVec.setWidth_ushiftRight_eq_extractLsb

/-- Serializing a word and reading it back is the identity. -/
@[simp] theorem wordOfBytes?_encodeWords (v : Word) : wordOfBytes? (encodeWords [v]) = some v := by
  rw [encodeWords_singleton]
  simp only [wordOfBytes?, wordByte_eq, Option.some.injEq]
  simp only [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb']
  exact BitVec.extractLsb'_eq_self

theorem wordOfBytes?_isSome {bytes : List Byte} (h : bytes.length = 8) :
    ∃ v, wordOfBytes? bytes = some v := by
  match bytes, h with
  | [_, _, _, _, _, _, _, _], _ => exact ⟨_, rfl⟩

/-- Memory permissions depend only on the region list. -/
theorem Memory.checkSpan_congr {first second : Memory} (h : first.regions = second.regions)
    (access : Process.Access) (address length : Nat) :
    first.checkSpan access address length = second.checkSpan access address length := by
  simp [Memory.checkSpan, Memory.permits, h]

/-- A read whose span avoids a write interval is unaffected by the write. -/
theorem Memory.readWith_writesOnly {before after : Memory} {address length : Nat}
    (frame : Memory.WritesOnly before after address length)
    (access : Process.Access) (start count : Nat)
    (disjoint : start + count ≤ address ∨ address + length ≤ start) :
    after.readWith access start count = before.readWith access start count := by
  have backing : ∀ k, k ≤ count →
      Memory.readBacking after.bytes (start + (count - k)) k =
        Memory.readBacking before.bytes (start + (count - k)) k := by
    intro k
    induction k with
    | zero => intro; rfl
    | succ k ih =>
      intro hk
      have same := frame.2 (start + (count - (k + 1))) (by omega)
      have next : start + (count - (k + 1)) + 1 = start + (count - k) := by omega
      simp only [Memory.readBacking, Std.ExtHashMap.get?_eq_getElem?] at same ⊢
      rw [same, next, ih (by omega)]
  have := backing count le_rfl
  simp only [Nat.sub_self, Nat.add_zero] at this
  simp only [Memory.readWith, Memory.checkSpan_congr frame.1, this]

/-! ## PUSH and POP on a state and memory -/

/-- Store `value` in the eight bytes at `RSP - 8` (modulo `2^64`) and then set
RSP to that address. `none` if the store is not permitted. -/
def pushWord (s : State) (memory : Memory) (value : Word) : Option (State × Memory) :=
  (memory.writeBytes (s.read .rsp - 8#64).toNat (encodeWords [value])).map fun after =>
    (s.write .rsp (s.read .rsp - 8#64), after)

/-- Load the eight bytes at RSP and then add eight to RSP (modulo `2^64`).
`none` if the load is not permitted or a byte has no backing. -/
def popWord (s : State) (memory : Memory) : Option (Word × State) := do
  let bytes ← memory.readBytes (s.read .rsp).toNat 8
  let value ← wordOfBytes? bytes
  pure (value, s.write .rsp (s.read .rsp + 8#64))

theorem pushWord_eq_none_iff (s : State) (memory : Memory) (value : Word) :
    pushWord s memory value = none ↔ ¬ memory.Permitted .write (s.read .rsp - 8#64).toNat 8 := by
  simp only [pushWord, Memory.writeBytes, length_encodeWords_singleton, Memory.Permitted]
  split <;> simp_all

theorem pushWord_eq_some {s : State} {memory : Memory} {value : Word}
    (permitted : memory.Permitted .write (s.read .rsp - 8#64).toNat 8) :
    pushWord s memory value = some (s.write .rsp (s.read .rsp - 8#64),
      { memory with
        bytes := Memory.install memory.bytes (s.read .rsp - 8#64).toNat (encodeWords [value]) }) := by
  have check : memory.checkSpan .write (s.read .rsp - 8#64).toNat 8 = true := permitted
  unfold pushWord Memory.writeBytes
  rw [length_encodeWords_singleton, ite_eq_left check]
  rfl

theorem pushWord_state {s t : State} {memory after : Memory} {value : Word}
    (h : pushWord s memory value = some (t, after)) :
    t = s.write .rsp (s.read .rsp - 8#64) := by
  simp only [pushWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl, _⟩ := h
  rfl

/-- PUSH changes exactly the eight bytes at the new RSP and no mapping. -/
theorem pushWord_writesOnly {s t : State} {memory after : Memory} {value : Word}
    (h : pushWord s memory value = some (t, after)) :
    Memory.WritesOnly memory after (s.read .rsp - 8#64).toNat 8 := by
  simp only [pushWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, written, _, rfl⟩ := h
  simpa using Memory.writeBytes_writesOnly written

theorem pushWord_get {s t : State} {memory after : Memory} {value : Word}
    (h : pushWord s memory value = some (t, after)) (index : Nat) (bound : index < 8) :
    after.bytes.get? ((s.read .rsp - 8#64).toNat + index) =
      some ((encodeWords [value])[index]'(by simpa using bound)) := by
  simp only [pushWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, written, _, rfl⟩ := h
  exact Memory.writeBytes_get written index (by simpa using bound)

theorem popWord_of_readBytes {s : State} {memory : Memory} {value : Word}
    (h : memory.readBytes (s.read .rsp).toNat 8 = some (encodeWords [value])) :
    popWord s memory = some (value, s.write .rsp (s.read .rsp + 8#64)) := by
  simp [popWord, h]

/-- POP faults exactly when the eight-byte load does. -/
theorem popWord_eq_none_iff (s : State) (memory : Memory) :
    popWord s memory = none ↔ memory.readBytes (s.read .rsp).toNat 8 = none := by
  cases h : memory.readBytes (s.read .rsp).toNat 8 with
  | none => simp [popWord, h]
  | some bytes =>
    obtain ⟨v, hv⟩ := wordOfBytes?_isSome (Memory.readWith_length h)
    simp [popWord, h, hv]

@[simp] private theorem State.write_write (s : State) (r : Reg) (v w : Word) :
    (s.write r v).write r w = s.write r w := by
  simp [State.write, Machine.RegisterFile.write_shadow]

@[simp] private theorem State.write_read (s : State) (r : Reg) : s.write r (s.read r) = s := by
  simp [State.write, State.read, Machine.RegisterFile.write_current]

/-- After a push, the eight pushed bytes can be read back, provided they are readable. -/
theorem pushWord_readBytes {s t : State} {memory after : Memory} {value : Word}
    (h : pushWord s memory value = some (t, after))
    (readable : memory.Permitted .read (s.read .rsp - 8#64).toNat 8) :
    after.readBytes (s.read .rsp - 8#64).toNat 8 = some (encodeWords [value]) := by
  have frame := pushWord_writesOnly h
  have := Memory.readWith_eq after .read (s.read .rsp - 8#64).toNat (encodeWords [value])
    (by simpa [Memory.Permitted, Memory.checkSpan_congr frame.1] using readable)
    (fun index bound => pushWord_get h index (by simpa using bound))
  rw [length_encodeWords_singleton] at this
  exact this

/-- Push-then-pop round trip: popping immediately after a push returns the
pushed value and restores the original state exactly, provided the pushed bytes
are readable. -/
theorem popWord_pushWord {s t : State} {memory after : Memory} {value : Word}
    (h : pushWord s memory value = some (t, after))
    (readable : memory.Permitted .read (s.read .rsp - 8#64).toNat 8) :
    popWord t after = some (value, s) := by
  have read := pushWord_readBytes h readable
  have ht := pushWord_state h
  subst ht
  rw [popWord_of_readBytes (by simpa using read)]
  simp

/-! ## Instruction semantics -/

namespace Insn

/-- Execute a decoded instruction, including its RIP update. The result is
`none` exactly when a stack access is not permitted (or its bytes have no
backing); a faulting instruction has no partial effect. -/
def exec (i : Insn) (s : State) (memory : Memory) : Option (State × Memory) :=
  let next := s.rip + BitVec.ofNat 64 i.length
  match i with
  | .base instr => some (X86.step instr s, memory)
  | .push src =>
    (pushWord s memory (s.read src)).map fun result => ({ result.1 with rip := next }, result.2)
  | .pop dst =>
    (popWord s memory).map fun result =>
      ({ result.2.write dst result.1 with rip := next }, memory)
  | .call rel =>
    (pushWord s memory next).map fun result =>
      ({ result.1 with rip := next + rel.signExtend 64 }, result.2)
  | .ret =>
    (popWord s memory).map fun result => ({ result.2 with rip := result.1 }, memory)

@[simp] theorem exec_base (instr : Instr) (s : State) (memory : Memory) :
    (Insn.base instr).exec s memory = some (X86.step instr s, memory) := rfl

/-- Every instruction changes at most the eight bytes at `RSP - 8` and no
mapping. `exec_memory_eq` shows that only PUSH and CALL change memory at all. -/
theorem exec_writesOnly {i : Insn} {s t : State} {memory after : Memory}
    (h : i.exec s memory = some (t, after)) :
    Memory.WritesOnly memory after (s.read .rsp - 8#64).toNat 8 := by
  cases i with
  | base instr =>
    simp only [exec_base, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, fun _ _ => rfl⟩
  | push src =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨u, m⟩, hp, -, rfl⟩ := h
    exact pushWord_writesOnly hp
  | pop dst =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    exact ⟨rfl, fun _ _ => rfl⟩
  | call rel =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨u, m⟩, hp, -, rfl⟩ := h
    exact pushWord_writesOnly hp
  | ret =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    exact ⟨rfl, fun _ _ => rfl⟩

/-- Instructions other than PUSH and CALL leave memory unchanged. -/
theorem exec_memory_eq {i : Insn} {s t : State} {memory after : Memory}
    (h : i.exec s memory = some (t, after)) (hpush : ∀ src, i ≠ .push src)
    (hcall : ∀ rel, i ≠ .call rel) :
    after = memory := by
  cases i with
  | base instr =>
    simp only [exec_base, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | push src => exact absurd rfl (hpush src)
  | pop dst =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    rfl
  | call rel => exact absurd rfl (hcall rel)
  | ret =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    rfl

/-- No instruction of `Insn` other than those of `Instr` changes the flags. -/
theorem exec_flags {i : Insn} {s t : State} {memory after : Memory}
    (h : i.exec s memory = some (t, after)) (hbase : ∀ instr, i ≠ .base instr) :
    t.flags = s.flags := by
  cases i with
  | base instr => exact absurd rfl (hbase instr)
  | push src =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨u, m⟩, hp, rfl, -⟩ := h
    rw [pushWord_state hp]; rfl
  | pop dst =>
    simp only [exec, popWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨v, u⟩, hp, rfl, -⟩ := h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨_, _, _, _, -, rfl⟩ := hp
    rfl
  | call rel =>
    simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨u, m⟩, hp, rfl, -⟩ := h
    rw [pushWord_state hp]; rfl
  | ret =>
    simp only [exec, popWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨v, u⟩, hp, rfl, -⟩ := h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨_, _, _, _, -, rfl⟩ := hp
    rfl

/-- `push src; pop dst` at consecutive addresses: `dst` receives the incoming
value of `src`, RSP and every other register are restored, the flags are
unchanged and RIP is past both instructions. The pushed bytes remain in memory. -/
theorem exec_push_pop {src dst : Reg} {s t : State} {memory after : Memory}
    (pushed : (Insn.push src).exec s memory = some (t, after))
    (readable : memory.Permitted .read (s.read .rsp - 8#64).toNat 8) :
    (Insn.pop dst).exec t after =
      some ({ s.write dst (s.read src) with
        rip := s.rip + BitVec.ofNat 64 ((Insn.push src).length + (Insn.pop dst).length) },
        after) := by
  simp only [exec, Option.map_eq_some_iff, Prod.mk.injEq] at pushed
  obtain ⟨⟨u, m⟩, hp, rfl, rfl⟩ := pushed
  have hu := pushWord_state hp
  subst hu
  have read := pushWord_readBytes hp readable
  have hpop : popWord { s.write .rsp (s.read .rsp - 8#64) with
      rip := s.rip + BitVec.ofNat 64 (Insn.push src).length } m =
      some (s.read src, { s with rip := s.rip + BitVec.ofNat 64 (Insn.push src).length }) := by
    rw [popWord_of_readBytes (by simpa [State.read, State.write] using read)]
    simp [State.read, State.write, Machine.RegisterFile.write_shadow,
      Machine.RegisterFile.write_current]
  simp only [exec, hpop, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  simp only [State.write, BitVec.ofNat_add, BitVec.add_assoc]

end Insn

end Silmaril.X86
