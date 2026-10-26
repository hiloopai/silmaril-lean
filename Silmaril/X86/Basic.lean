module

public import Silmaril.Machine.RegisterFile
public import Silmaril.X86.Flags

/-!
# x86-64 long-mode registers and state for a small integer subset

A handwritten local model of 64-bit mode user state: the sixteen general-purpose
registers, RIP and the six arithmetic status flags (`Flags`). It is not derived
from, or proved to correspond with, the Sail, ACL2 or any hardware description.

Only full 64-bit register reads and writes are modeled. The 32-bit views
(`eax`, ..., including their zero-extending writes), the 16-bit views and the
8-bit views (including the REX-dependent `ah`/`spl` distinction and merging
writes) are out of scope, as are the remaining RFLAGS bits, memory, faults and
instruction fetch. Of segmentation only the FS base is modeled (`fsBase`),
because it is the only segment the pilot objects use; the segment *registers*,
their selectors, descriptors and limits are not.
-/

@[expose] public section

namespace Silmaril.X86

abbrev Word := BitVec 64

/-- The sixteen 64-bit general-purpose registers, in hardware-number order. -/
inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

namespace Reg

/-- The four-bit hardware register number (REX extension bit followed by the
three-bit ModRM field). -/
def toBitVec : Reg → BitVec 4
  | rax => 0 | rcx => 1 | rdx => 2 | rbx => 3
  | rsp => 4 | rbp => 5 | rsi => 6 | rdi => 7
  | r8 => 8 | r9 => 9 | r10 => 10 | r11 => 11
  | r12 => 12 | r13 => 13 | r14 => 14 | r15 => 15

def ofBitVec (b : BitVec 4) : Reg :=
  match b.toNat with
  | 0 => rax | 1 => rcx | 2 => rdx | 3 => rbx
  | 4 => rsp | 5 => rbp | 6 => rsi | 7 => rdi
  | 8 => r8 | 9 => r9 | 10 => r10 | 11 => r11
  | 12 => r12 | 13 => r13 | 14 => r14 | _ => r15

@[simp] theorem ofBitVec_toBitVec (r : Reg) : ofBitVec r.toBitVec = r := by
  cases r <;> rfl

@[simp] theorem toBitVec_ofBitVec (b : BitVec 4) : (ofBitVec b).toBitVec = b := by
  revert b
  decide

theorem toBitVec_injective : Function.Injective toBitVec := by
  intro r q h
  simpa using congrArg ofBitVec h

/-- The REX extension bit (REX.R or REX.B) of the register number. -/
def hi (r : Reg) : BitVec 1 := r.toBitVec.extractLsb' 3 1

/-- The three low bits of the register number, as held in a ModRM field. -/
def lo (r : Reg) : BitVec 3 := r.toBitVec.extractLsb' 0 3

/-- The register number is the concatenation of its REX bit and ModRM field. -/
theorem hi_append_lo (r : Reg) : r.hi ++ r.lo = r.toBitVec := by
  cases r <;> decide

@[simp] theorem ofBitVec_hi_append_lo (r : Reg) : ofBitVec (r.hi ++ r.lo) = r := by
  rw [hi_append_lo, ofBitVec_toBitVec]

end Reg

/-- Architectural state of the modeled subset.

`fsBase` is the hidden base of the FS segment, the only segmentation the model
has. It defaults to zero, so every state written without it — and every
`{ s with .. }` update — means exactly what it meant before this field existed.
See `Ext.Base.fs` for the one addressing form that reads it. -/
structure State where
  regs : Machine.RegisterFile Reg Word
  rip : Word
  flags : Flags
  /-- The hidden base of the FS segment (`Ext.Base.fs`). In 64-bit mode CS, DS,
  ES and SS are treated as having base zero, while FS and GS keep a base loaded
  from `FSBASE`/`GSBASE` (Intel SDM, Vol. 1, 3.4.4). Only FS is modeled. -/
  fsBase : Word := 0

namespace State

/-- A full 64-bit register read. -/
def read (s : State) (r : Reg) : Word := s.regs r

/-- A full 64-bit register write; RIP and the flags are unchanged. -/
def write (s : State) (r : Reg) (v : Word) : State :=
  { s with regs := Machine.RegisterFile.write s.regs r v }

@[simp] theorem read_write_same (s : State) (r : Reg) (v : Word) :
    (s.write r v).read r = v := by
  simp [read, write]

@[simp] theorem read_write_other (s : State) (r q : Reg) (v : Word) (h : q ≠ r) :
    (s.write r v).read q = s.read q := by
  simp [read, write, h]

theorem read_write (s : State) (r q : Reg) (v : Word) :
    (s.write r v).read q = if q = r then v else s.read q := by
  by_cases h : q = r
  · subst h; simp
  · simp [h]

@[simp] theorem write_rip (s : State) (r : Reg) (v : Word) : (s.write r v).rip = s.rip := rfl

@[simp] theorem write_flags (s : State) (r : Reg) (v : Word) :
    (s.write r v).flags = s.flags := rfl

@[simp] theorem write_fsBase (s : State) (r : Reg) (v : Word) :
    (s.write r v).fsBase = s.fsBase := rfl

/-- A register read sees only the register file: replacing RIP, the flags or
the FS base does not change it.

This is what lets `simp` see through the `{ t with rip := next }` that `Ext.retire`
builds. Before `fsBase` existed the record update had three fields and `simp`
could finish the job unaided; with a fourth it needs this step stated, or a
read of a retired state stops reducing and proofs in `X86/Lir/` that never
mention segmentation break. Stating it keeps the new field invisible to every
such proof. -/
@[simp] theorem read_mk_regs (s : State) (rip : Word) (flags : Flags) (fsBase : Word) (r : Reg) :
    (State.mk s.regs rip flags fsBase).read r = s.read r := rfl

end State
end Silmaril.X86
