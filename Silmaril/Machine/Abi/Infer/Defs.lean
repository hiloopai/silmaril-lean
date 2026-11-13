module

public import Silmaril.X86.CallingConvention
/-! # ABI inference from register usage

A lifter or decompiler summarises a machine function by its register usage
(`Usage`): the registers it may read before writing them (`reads`), the
registers whose exit value may differ from their entry value (`writes`, i.e.
net clobbers after save/restore pairs are recognised), and the registers it
writes on every path (`defs`).

A *candidate* is a calling-convention family, an integer arity and whether the
function returns an integer result. `consistent u c` is a decidable check that
the summary is compatible with the candidate:

* every read register is an argument register of the candidate's arity, a
  callee-saved register (which a prologue may read to save it), or the stack
  pointer;
* no callee-saved register is clobbered;
* a result-returning candidate defines the first result register on every path.

`infer u` enumerates the consistent candidates up to the register-argument
bound of each family (more arguments than argument registers go on the stack,
which register usage cannot observe, so larger arities behave like the bound).

The semantics (`Summarizes`, `Respects`) are over abstract register files
`R → Val` with an abstract type `E` of other observable effects (memory writes,
I/O). `Thms.consistent_iff` proves the check *exact*: it accepts iff every
function with that summary respects the candidate's register discipline.

Register usage cannot see the stack discipline, alignment, return address or
memory footprints; those remain obligations of the convention's full contract
(`Convention.translate`). Consistency is therefore evidence for a convention,
not a proof that a binary function implements it.

The families use public Silmaril `CallingConvention` data: `Silmaril.X86.sysv64`
and the Win64 integer data `ms64` below (Microsoft x64 calling convention:
RCX, RDX, R8, R9; result RAX; RBX, RBP, RDI, RSI, R12–R15 callee-saved; 32-byte
shadow space; 16-byte alignment).
-/

@[expose] public section
namespace Silmaril.Machine.Abi.Infer

open Silmaril.Machine (CallingConvention)
open Silmaril.X86 (Reg)

/-- The integer part of the Microsoft x64 (Win64) calling convention, as data. -/
def ms64 : CallingConvention Reg where
  intArgRegs := [.rcx, .rdx, .r8, .r9]
  intRetRegs := [.rax]
  calleeSaved := [.rbx, .rbp, .rdi, .rsi, .r12, .r13, .r14, .r15]
  stackPointer := .rsp
  stackAlign := 16
  entryResidue := 8
  redZone := 0
  shadowSpace := 32
  stackArgSlot := 8
  returnAddress := .onStack 0
  linkSize := 8

/-- A register-usage summary of one machine function. -/
structure Usage (R : Type) where
  /-- Registers possibly read before being written (upward-exposed uses). -/
  reads : List R
  /-- Registers whose exit value may differ from their entry value. -/
  writes : List R
  /-- Registers written on every path; well-formed summaries have `defs ⊆ writes`. -/
  defs : List R
  deriving DecidableEq, Repr

/-- Calling-convention families that inference distinguishes. -/
inductive Family where
  | sysv64
  | ms64
  deriving DecidableEq, Repr

/-- The register data of a family. -/
def Family.cc : Family → CallingConvention Reg
  | .sysv64 => Silmaril.X86.sysv64
  | .ms64 => Infer.ms64

/-- A candidate prototype shape under a family. -/
structure Candidate where
  family : Family
  arity : Nat
  returns : Bool
  deriving DecidableEq, Repr

section Generic

variable {R : Type} [DecidableEq R]

/-- Registers a callee of arity `n` may depend on: its argument registers, the
callee-saved registers and the stack pointer. -/
def allowed (cc : CallingConvention R) (n : Nat) : List R :=
  cc.intArgRegs.take n ++ cc.calleeSaved ++ [cc.stackPointer]

/-- The first integer result register, if any. -/
def resultReg (cc : CallingConvention R) : Option R := cc.intRetRegs.head?

/-- The decidable consistency check of a usage summary against a convention,
an arity and a result flag. -/
def consistentWith (cc : CallingConvention R) (n : Nat) (returns : Bool) (u : Usage R) : Bool :=
  u.reads.all (fun r => decide (r ∈ allowed cc n)) &&
    u.writes.all (fun r => decide (r ∉ cc.calleeSaved)) &&
    (!returns || (resultReg cc).all (fun r => decide (r ∈ u.defs)))

/-- `f` (entry registers to exit registers and other effects) has usage `u`:
registers outside `writes` are unchanged; exit registers and effects are
determined by `reads` together with a register's own entry value (a conditional
write keeps the old value on some path); registers in `defs` and the effects
are determined by `reads` alone. -/
structure Summarizes {Val E : Type} (u : Usage R) (f : (R → Val) → (R → Val) × E) : Prop where
  unchanged : ∀ s r, r ∉ u.writes → (f s).1 r = s r
  regs : ∀ s t, (∀ x ∈ u.reads, s x = t x) → ∀ r, s r = t r → (f s).1 r = (f t).1 r
  defs : ∀ s t, (∀ x ∈ u.reads, s x = t x) → ∀ r ∈ u.defs, (f s).1 r = (f t).1 r
  effects : ∀ s t, (∀ x ∈ u.reads, s x = t x) → (f s).2 = (f t).2

/-- `f` respects the register discipline of `cc` for arity `n`: callee-saved
registers are preserved (`CallingConvention.Preserved`), and the effects and
(if `returns`) the result register depend only on `allowed cc n`. -/
structure Respects {Val E : Type} (cc : CallingConvention R) (n : Nat) (returns : Bool)
    (f : (R → Val) → (R → Val) × E) : Prop where
  preserved : ∀ s, cc.Preserved s (f s).1
  effects : ∀ s t, (∀ x ∈ allowed cc n, s x = t x) → (f s).2 = (f t).2
  result : returns = true → ∀ s t, (∀ x ∈ allowed cc n, s x = t x) →
    ∀ r ∈ resultReg cc, (f s).1 r = (f t).1 r

end Generic

/-- Consistency of an x86 usage summary with a candidate. -/
def consistent (u : Usage Reg) (c : Candidate) : Bool :=
  consistentWith c.family.cc c.arity c.returns u

/-- Register-passed arity bound of a family; larger arities are indistinguishable
by register usage. -/
def Family.bound (fam : Family) : Nat := fam.cc.intArgRegs.length

/-- All candidates of a family up to its register bound. -/
def Family.candidates (fam : Family) : List Candidate :=
  (List.range (fam.bound + 1)).flatMap fun n => [⟨fam, n, false⟩, ⟨fam, n, true⟩]

/-- ABI inference as search: the consistent candidates of both families. -/
def infer (u : Usage Reg) : List Candidate :=
  (Family.sysv64.candidates ++ Family.ms64.candidates).filter (consistent u)

/-- The least consistent arity of a family and result flag, if any. -/
def minArity (u : Usage Reg) (fam : Family) (returns : Bool) : Option Nat :=
  (List.range (fam.bound + 1)).find? fun n => consistent u ⟨fam, n, returns⟩

end Silmaril.Machine.Abi.Infer
