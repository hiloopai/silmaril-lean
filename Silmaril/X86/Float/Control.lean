module

public import Silmaril.X86.Basic
public import Silmaril.X86.Encoding

/-!
# `Jcc rel8` and `UD2`

The two control-transfer instructions that WebAssembly lowering sequences use
to trap: a short conditional jump and the undefined instruction. Written from
the Intel 64 and IA-32 Architectures Software Developer's Manual (SDM),
Vol. 2A, `Jcc` (opcode `70+cc cb`: "Jump short if condition is met"), Vol. 2B,
`UD2` (opcode `0F 0B`: "Raise invalid opcode exception"), and the condition
table of Vol. 1, Appendix B ("EFLAGS Condition Codes"). It is a specification
from documents, not a correspondence with hardware.

* `condHolds cc flags` evaluates the four-bit condition code `cc` (the `tttn`
  field of the opcode) on the status flags, or returns `none` when the condition
  reads a flag the model leaves undefined.
* `CtlInstr` is `jcc cc rel` or `ud2`, with the canonical two-byte encodings and
  a decoder that is a prefix code (`CtlInstr.decode_eq_some_iff`).

Execution is defined by the fetch/decode machine (`Silmaril.X86.Float.Machine`):
a taken `Jcc` sets RIP to the address after it plus the sign-extended
displacement, a not-taken one falls through, and `UD2` raises #UD. Only the
`rel8` form is modeled; the target is not checked for canonical form.
-/

@[expose] public section

namespace Silmaril.X86.Float

/-- Combine two flag values; undefined if either is. -/
def condBoth (x y : Option Bool) (f : Bool → Bool → Bool) : Option Bool :=
  x.bind fun a => y.map fun b => f a b

/-- The condition with `tttn` encoding `cc` on the status flags (SDM Vol. 1,
Appendix B, Table B-1), or `none` when a flag it reads is undefined. -/
def condHolds (cc : BitVec 4) (f : X86.Flags) : Option Bool :=
  match cc.toNat with
  | 0 => f.overflow
  | 1 => f.overflow.map (!·)
  | 2 => f.carry
  | 3 => f.carry.map (!·)
  | 4 => f.zero
  | 5 => f.zero.map (!·)
  | 6 => condBoth f.carry f.zero (· || ·)
  | 7 => condBoth f.carry f.zero fun c z => !c && !z
  | 8 => f.sign
  | 9 => f.sign.map (!·)
  | 10 => f.parity
  | 11 => f.parity.map (!·)
  | 12 => condBoth f.sign f.overflow (· != ·)
  | 13 => condBoth f.sign f.overflow (· == ·)
  | 14 => f.zero.bind fun z => condBoth f.sign f.overflow fun s o => z || s != o
  | _ => f.zero.bind fun z => condBoth f.sign f.overflow fun s o => !z && s == o

/-- A modeled control-transfer instruction. -/
inductive CtlInstr where
  /-- `Jcc rel8`: jump by the sign-extended `rel` when condition `cc` holds. -/
  | jcc (cc : BitVec 4) (rel : BitVec 8)
  /-- `UD2`: raise #UD. -/
  | ud2
  deriving DecidableEq, Repr

namespace CtlInstr

/-- The canonical encodings: `70+cc rel` and `0F 0B`. -/
def encode : CtlInstr → List X86.Byte
  | .jcc cc rel => [0x7#4 ++ cc, rel]
  | .ud2 => [0x0F#8, 0x0B#8]

@[simp] theorem length_encode (i : CtlInstr) : i.encode.length = 2 := by
  cases i <;> rfl

/-- Decode one instruction from the front of the bytes. -/
def decode : List X86.Byte → Option (CtlInstr × Nat)
  | b :: rel :: _ =>
    if b.extractLsb' 4 4 = 0x7#4 then some (.jcc (b.extractLsb' 0 4) rel, 2)
    else if b = 0x0F#8 ∧ rel = 0x0B#8 then some (.ud2, 2)
    else none
  | _ => none

theorem jcc_high (cc : BitVec 4) : (0x7#4 ++ cc).extractLsb' 4 4 = 0x7#4 := by
  revert cc; decide

theorem jcc_low (cc : BitVec 4) : (0x7#4 ++ cc).extractLsb' 0 4 = cc := by
  revert cc; decide

theorem jcc_eta (b : X86.Byte) (h : b.extractLsb' 4 4 = 0x7#4) :
    0x7#4 ++ b.extractLsb' 0 4 = b := by
  revert b; decide

@[simp] theorem decode_encode_append (i : CtlInstr) (rest : List X86.Byte) :
    decode (i.encode ++ rest) = some (i, i.encode.length) := by
  cases i with
  | jcc cc rel => simp [decode, encode, jcc_high, jcc_low]
  | ud2 => simp [decode, encode]

/-- A successful decode consumed the canonical encoding of its result. -/
theorem decode_eq_some_iff {bytes : List X86.Byte} {i : CtlInstr} {n : Nat} :
    decode bytes = some (i, n) ↔ n = i.encode.length ∧ i.encode <+: bytes := by
  constructor
  · intro h
    match bytes, h with
    | b :: rel :: rest, h =>
      simp only [decode] at h
      split at h
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, rest, ?_⟩
        simp [encode, jcc_eta b hb]
      · split at h
        · rename_i hu
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨rfl, rfl⟩ := hu
          exact ⟨rfl, rest, rfl⟩
        · cases h
  · rintro ⟨rfl, rest, rfl⟩
    exact decode_encode_append i rest

end CtlInstr

end Silmaril.X86.Float
