module

public import Silmaril.X86.Ext.Encoding

/-!
# Walking a byte string with the decoder

`decodeLengths fuel bytes` decodes `bytes` from the front, repeatedly, and
returns the length of each instruction; `decodeAll` returns the instructions
themselves. Both are `none` if an instruction fails to decode or if `fuel` runs
out before the input does.

This is the Lean form of the whole-image completeness check that
`scripts/x86-crosscheck.py --images` performs at runtime: given the `.text`
bytes of a function, it says that the model consumes every one of them.

## What a successful walk proves

`decode` is not just a parser. It re-encodes the instruction it has read and
requires the result to be a prefix of the input (`decode_eq_some_iff`), so a
successful walk says more than "the model admits these bytes":

* `decodeAll_eq_flatten` — the byte string is **exactly** the concatenation of
  the canonical encodings of the instructions read. Nothing is skipped, nothing
  is left over, and each instruction is written the way `encode` writes it, so
  `decode` and `encode` round-trip on every instruction in the image. A model
  that decoded some bytes to an instruction it would have spelled differently
  would fail the walk, not pass it with a different answer.
* `sum_decodeLengths` — the lengths sum to the size of the input, which is the
  arithmetic a reader can check against the symbol size from `readelf`.
* `covered_of_decodeAll` packages the first as `Covered`.

The fuel bound is an implementation detail: `decodeLengths_mono` shows that
more fuel never changes a successful answer, and every instruction is at least
one byte (`decode_length`), so `bytes.length` fuel always suffices
(`decodeLengths_length_fuel`).

These are facts about this handwritten local model only; they are not evidence
about hardware. The companion evidence for that is `scripts/x86-crosscheck.py`,
which compares the same encoder against `llvm-mc`.
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Byte)

/-- Decode `bytes` from the front, repeatedly, returning the instructions read.
`none` if some instruction fails to decode, if one claims zero length, or if
`fuel` runs out before the input does. -/
def decodeAll : Nat → List Byte → Option (List Instr)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bytes =>
    match decode bytes with
    | none => none
    | some (i, n) => if n = 0 then none else (decodeAll fuel (bytes.drop n)).map (i :: ·)

/-- The same walk, returning only the length of each instruction. This is the
form a `.text` image check uses: the list is legible against a disassembly and
its sum is the symbol size. -/
def decodeLengths : Nat → List Byte → Option (List Nat)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bytes =>
    match decode bytes with
    | none => none
    | some (_, n) =>
      if n = 0 then none else (decodeLengths fuel (bytes.drop n)).map (n :: ·)

/-- A byte string is *covered* when it is exactly a concatenation of canonical
encodings: every byte belongs to one instruction of the model, and every
instruction is written the way `encode` writes it. -/
def Covered (bytes : List Byte) : Prop := ∃ instrs : List Instr, bytes = (instrs.map encode).flatten

/-- A successful walk recovers the input exactly: the bytes are the
concatenation of the canonical encodings of the instructions read. -/
theorem decodeAll_eq_flatten : ∀ (fuel : Nat) {bytes : List Byte} {instrs : List Instr},
    decodeAll fuel bytes = some instrs → bytes = (instrs.map encode).flatten := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes instrs h
    cases bytes with
    | nil => simp only [decodeAll, Option.some.injEq] at h; subst h; simp
    | cons b t => simp [decodeAll] at h
  | succ fuel ih =>
    intro bytes instrs h
    cases bytes with
    | nil => simp only [decodeAll, Option.some.injEq] at h; subst h; simp
    | cons b t =>
      simp only [decodeAll] at h
      split at h
      · simp at h
      · rename_i i n hd
        split at h
        · simp at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨tail, htail, rfl⟩ := h
          rw [List.map_cons, List.flatten_cons, ← ih htail]
          exact (decode_sound hd).2

theorem covered_of_decodeAll {fuel : Nat} {bytes : List Byte} {instrs : List Instr}
    (h : decodeAll fuel bytes = some instrs) : Covered bytes :=
  ⟨instrs, decodeAll_eq_flatten fuel h⟩

/-- The two walks agree: the lengths are the encoded lengths of the
instructions. -/
theorem decodeLengths_eq_map : ∀ (fuel : Nat) (bytes : List Byte),
    decodeLengths fuel bytes = (decodeAll fuel bytes).map (·.map (fun i => (encode i).length)) := by
  intro fuel
  induction fuel with
  | zero => intro bytes; cases bytes <;> rfl
  | succ fuel ih =>
    intro bytes
    cases bytes with
    | nil => rfl
    | cons b t =>
      simp only [decodeLengths, decodeAll]
      cases hd : decode (b :: t) with
      | none => rfl
      | some r =>
        obtain ⟨i, n⟩ := r
        have hlen : n = (encode i).length := (decode_length hd).1
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, ite_false, ih]
          cases decodeAll fuel ((b :: t).drop n) with
          | none => rfl
          | some tail => simp [hlen]

/-- A successful *length* walk already proves coverage: it is the length form
of the same walk, so the instructions exist even though this walk discards
them. This is what lets an image theorem be stated with `decodeLengths`, whose
answer is a list of small numbers a reader can check against a disassembly,
and still conclude `Covered`. -/
theorem covered_of_decodeLengths {fuel : Nat} {bytes : List Byte} {lengths : List Nat}
    (h : decodeLengths fuel bytes = some lengths) : Covered bytes := by
  rw [decodeLengths_eq_map, Option.map_eq_some_iff] at h
  obtain ⟨instrs, hall, -⟩ := h
  exact covered_of_decodeAll hall

/-- The lengths of a successful walk sum to the length of the input. -/
theorem sum_decodeLengths {fuel : Nat} {bytes : List Byte} {lengths : List Nat}
    (h : decodeLengths fuel bytes = some lengths) : lengths.sum = bytes.length := by
  rw [decodeLengths_eq_map] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨instrs, hall, rfl⟩ := h
  rw [decodeAll_eq_flatten fuel hall]
  clear hall
  induction instrs with
  | nil => simp
  | cons i rest ih => simpa using ih

/-- A successful walk stays successful with more fuel. -/
theorem decodeLengths_mono : ∀ (fuel : Nat) {bytes : List Byte} {lengths : List Nat},
    decodeLengths fuel bytes = some lengths →
    ∀ more, decodeLengths (fuel + more) bytes = some lengths := by
  intro fuel
  induction fuel with
  | zero =>
    intro bytes lengths h more
    cases bytes with
    | nil => simpa [decodeLengths] using h
    | cons b t => simp [decodeLengths] at h
  | succ fuel ih =>
    intro bytes lengths h more
    cases bytes with
    | nil => simpa [decodeLengths] using h
    | cons b t =>
      have hstep : fuel + 1 + more = (fuel + more) + 1 := by omega
      rw [hstep]
      cases hd : decode (b :: t) with
      | none => simp [decodeLengths, hd] at h
      | some r =>
        obtain ⟨i, n⟩ := r
        by_cases hn : n = 0
        · simp [decodeLengths, hd, hn] at h
        · simp only [decodeLengths, hd, hn, ite_false, Option.map_eq_some_iff] at h ⊢
          obtain ⟨tail, htail, rfl⟩ := h
          exact ⟨tail, ih htail more, rfl⟩

/-- Every instruction is at least one byte, so `bytes.length` fuel is always
enough: a walk that fails with that much fuel fails for a real reason. -/
theorem decodeLengths_length_fuel {bytes : List Byte} {lengths : List Nat} {fuel : Nat}
    (h : decodeLengths fuel bytes = some lengths) :
    decodeLengths (fuel + bytes.length) bytes = some lengths :=
  decodeLengths_mono fuel h bytes.length

/-! ## Examples

A short prologue, as `clang -O2` emits one, walked end to end. The full `.text`
images of the pilot functions live in `tests/x86/` and are walked by
`scripts/x86-crosscheck.py --images`; the corresponding `rfl` theorems belong
with the modules that own those byte literals. -/

/-- `mov %al,%dl; mov %al,%cl; ret` — three instructions, five bytes. `88 c2`
is `88 /r` with `mod = 11`, the register-to-register byte move that
`clang -O0` emits in `MD5_memset` and at which the decoder used to stop. -/
example :
    decodeLengths 8 (List.map (BitVec.ofNat 8) [0x88, 0xC2, 0x88, 0xC1, 0xC3]) =
      some [2, 2, 1] := by decide

/-- Original SHA driver blocker at `0x40102f`: `test %cl,%cl` reads two
low-byte registers and consumes precisely `84 c9`. -/
example : decode [0x84, 0xC9] = some (.test8 (.reg .rcx) .rcx, 2) := by decide

/-- The TEST and its backward conditional branch occupy four bytes. -/
example : decodeLengths 2 [0x84, 0xC9, 0x75, 0xFC] = some [2, 2] := by decide

/-- Without REX, fields 4--7 denote AH/CH/DH/BH, not the low bytes of
RSP/RBP/RSI/RDI. Neither source nor register destination is silently reinterpreted. -/
example :
    decode [0x84, 0xE0] = none ∧ decode [0x84, 0xE8] = none ∧
    decode [0x84, 0xF0] = none ∧ decode [0x84, 0xF8] = none ∧
    decode [0x84, 0xC4] = none ∧ decode [0x84, 0xC5] = none ∧
    decode [0x84, 0xC6] = none ∧ decode [0x84, 0xC7] = none := by decide

/-- REX makes field 4 SPL; a memory SIB field 4 is independent of high-byte
register selection and needs no REX. -/
example : decode [0x40, 0x84, 0xE0] = some (.test8 (.reg .rax) .rsp, 3) := by decide
example : decode [0x84, 0x04, 0x24] =
    some (.test8 (.mem (Mem.ofReg .rsp none 0)) .rax, 3) := by decide

/-- Measured immediate-byte CMP spellings: SHA at `0x401033`/`0x4010d3`
and GCC SQLite at text offsets `0x217`/`0x294`. -/
example : decode [0x80, 0xF9, 0x5C] = some (.cmpI8 (.reg .rcx) 0x5C, 3) := by decide
example : decode [0x3C, 0x09] = some (.cmpA8 0x09, 2) := by decide
example : decode [0x80, 0xF9, 0x80] = some (.cmpI8 (.reg .rcx) 0x80, 3) := by decide
example : decode [0x3C, 0x5B] = some (.cmpA8 0x5B, 2) := by decide
example : decodeLengths 4 [0x80, 0xF9, 0x5C, 0x3C, 0x09, 0x80, 0xF9, 0x80, 0x3C, 0x5B] =
    some [3, 2, 3, 2] := by decide

/-- An immediate mutation changes the decoded comparison. Other `80 /digit`
operations and the legacy high-byte AH operand remain outside this subset. -/
example : decode [0x80, 0xF9, 0x5D] = some (.cmpI8 (.reg .rcx) 0x5D, 3) := by decide
example : decode [0x80, 0xC1, 0x5C] = none ∧ decode [0x80, 0xFC, 0x5C] = none := by decide
example : decode [0x40, 0x80, 0xFC, 0x5C] = some (.cmpI8 (.reg .rsp) 0x5C, 4) := by decide

/-- Original SHA CMOVAE at `0x401900`, including REX.W and REX.B. -/
example : decode [0x49, 0x0F, 0x43, 0xD4] =
    some (.cmov .q .ae .rdx (.reg .r12), 4) := by decide
example : decodeLengths 2 [0x49, 0x0F, 0x43, 0xD4, 0x0F, 0x43, 0xC1] =
    some [4, 3] := by decide
/-- Changing the condition or source changes the AST; truncation rejects. -/
example : decode [0x49, 0x0F, 0x42, 0xD4] =
    some (.cmov .q .b .rdx (.reg .r12), 4) := by decide
example : decode [0x49, 0x0F, 0x43, 0xD5] =
    some (.cmov .q .ae .rdx (.reg .r13), 4) := by decide
example : decode [0x49, 0x0F, 0x43] = none := by decide

/-- Original SHA unsigned MUL64 at `0x4019f9`, and the 32-bit form. -/
example : decode [0x48, 0xF7, 0xE7] = some (.mul .q (.reg .rdi), 3) := by decide
example : decode [0x41, 0xF7, 0xE0] = some (.mul .d (.reg .r8), 3) := by decide
example : decodeLengths 2 [0x48, 0xF7, 0xE7, 0xF7, 0xE0] = some [3, 2] := by decide
/-- The group digit and operand size remain significant; truncation rejects. -/
example : decode [0x48, 0xF7, 0xEF] = none ∧ decode [0x48, 0xF7] = none := by decide
example : decode [0xF7, 0xE7] = some (.mul .d (.reg .rdi), 2) := by decide

/-- Original SHA byte-immediate TEST at `0x401df7`, and its accumulator form. -/
example : decode [0x41, 0xF6, 0xC4, 0x01] = some (.testI8 (.reg .r12) 1, 4) := by decide
example : decode [0xA8, 0x80] = some (.testA8 0x80, 2) := by decide
example : decodeLengths 2 [0x41, 0xF6, 0xC4, 0x01, 0xA8, 0x80] = some [4, 2] := by decide
/-- Immediate mutations change the AST; F6 /1 and incomplete immediates reject. -/
example : decode [0x41, 0xF6, 0xC4, 0x02] = some (.testI8 (.reg .r12) 2, 4) := by decide
example : decode [0xF6, 0xC8, 1] = none ∧ decode [0xF6, 0xC0] = none := by decide
/-- Legacy high-byte registers are rejected; REX selects SPL instead of AH. -/
example : decode [0xF6, 0xC4, 1] = none ∧ decode [0xF6, 0xC5, 1] = none ∧
    decode [0xF6, 0xC6, 1] = none ∧ decode [0xF6, 0xC7, 1] = none := by decide
example : decode [0x40, 0xF6, 0xC4, 1] = some (.testI8 (.reg .rsp) 1, 4) := by decide

/-- `push rbp; push r15; push rbx; sub rsp, 0xa8; xor eax, eax`, then a
thirteen-byte NOP: six instructions, twenty-eight bytes. -/
example :
    decodeLengths 32
      (List.map (BitVec.ofNat 8)
        [0x55, 0x41, 0x57, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00, 0x00, 0x31, 0xC0,
          0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]) =
      some [1, 2, 1, 7, 2, 13] := by decide

/-- The lengths sum to the number of bytes, as `sum_decodeLengths` says they
must. -/
example : ([1, 2, 1, 7, 2, 13] : List Nat).sum = 26 := by decide

/-- An unknown opcode stops the walk rather than skipping bytes: `0F 38 F0` is
MOVBE, which is not in the model (and does not occur in any of the pinned
objects). -/
example :
    decodeLengths 8 (List.map (BitVec.ofNat 8) [0x55, 0x0F, 0x38, 0xF0, 0xC1]) = none := by decide

end Silmaril.X86.Ext
