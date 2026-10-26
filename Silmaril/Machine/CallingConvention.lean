module

public import Mathlib.Data.List.Basic

/-!
# Calling conventions, as data

A `CallingConvention` records the parts of a procedure-call ABI that a
machine-code contract has to quote: where the integer arguments and results
live, which registers the callee must give back unchanged, how the stack
pointer is aligned at a call, how far below the stack pointer a leaf may
scribble, and how the return address is found on entry.

It is deliberately *data*, not a predicate on a machine: the same record is
read by a contract over x86-64 (`Silmaril.X86.sysv64`), by one over AArch64 and
by one over RV64. Nothing here mentions an instruction set, a state type or a
memory; the structure is parametric in the register type alone, and the two
derived predicates (`Preserved`, `EntryAligned`) are parametric in the value
type and take the reads they compare as arguments.

## Provenance

This file originates in PR #887 (`x86/sha256-contract`, #882 Track 2b) and is
reproduced here **verbatim**, field for field, so that whichever of #887 and
#879 merges second sees identical content. Nothing in it has been renamed,
reordered or re-specified. The Wasm-specific extension #879 asks for is
strictly additive and lives in `Silmaril.Machine.CallingConvention.Wasm`,
which extends this structure rather than editing it.

## Relation to #879

#879 will land `Machine/Behaviour/{Semantics,Refinement}.lean` and restate
`Implements` as "`compile cc m` implements `m` under `cc`", replacing the
hard-coded `maxParams = 6`, alignment and saved-register sets in
`Wasm/Lower/X86.lean` and the RV64 backend with `cc` fields. **This module is the
`CallingConvention` #887 wrote as a placeholder for that work; #879 absorbs it
unchanged.** It was shaped so that #879 could:

* the register type is a parameter, so `sysv64`, `aapcs64` and `lp64` are three
  instances of one structure rather than three structures;
* `ReturnAddress` is an inductive rather than a `Nat` offset, so a link-register
  ABI (AArch64 `x30`, RV64 `ra`) needs no reshaping;
* `shadowSpace` and `stackArgSlot` are present but unused by `sysv64`, so Win64
  and stack-passed arguments need no reshaping;
* the Wasm-specific parts #879 lists — the `i32` zero/sign-extension rule
  (`ResultExt`), the float/SIMD register classes and multi-value returns — are
  **not** here. They are additive, and #879 added them in
  `Silmaril.Machine.CallingConvention.Wasm` as a `WasmConvention` that
  `extends` this structure: no existing field changed.

What this module does **not** claim: that any binary follows any convention.
That is a property of a particular program, stated per ISA (`#704`); here a
`CallingConvention` is only a description.

Note `Silmaril.Cerberus.Core.CallingConvention` is an unrelated two-constructor
enumeration from the Cerberus C semantics; the namespaces do not collide.
-/

@[expose] public section

namespace Silmaril.Machine

universe u v

/-- Where a callee finds the address it must return to, on entry. -/
inductive ReturnAddress (Reg : Type u) where
  /-- Pushed by the call instruction, at `stackPointer + offset` on entry
  (x86-64: `offset = 0`, i.e. `[rsp]`). -/
  | onStack (offset : Nat)
  /-- Left in a link register by the call instruction (AArch64 `x30`,
  RV64 `ra`). -/
  | inRegister (link : Reg)
  deriving DecidableEq

/-- The integer part of a procedure-call ABI. -/
structure CallingConvention (Reg : Type u) where
  /-- Integer and pointer arguments, in order: the `n`-th argument that is
  passed in a register goes in `intArgRegs[n]`. -/
  intArgRegs : List Reg
  /-- Integer and pointer results, in order. -/
  intRetRegs : List Reg
  /-- Registers the callee must restore before returning. By convention this
  list excludes `stackPointer`, whose discipline is `linkSize` below. -/
  calleeSaved : List Reg
  /-- The stack pointer. -/
  stackPointer : Reg
  /-- The stack pointer is a multiple of `stackAlign` immediately **before** a
  call instruction. -/
  stackAlign : Nat
  /-- The residue of the stack pointer modulo `stackAlign` **at callee entry**,
  after the call has pushed whatever it pushes. For x86-64 the call pushes
  eight bytes onto a 16-byte-aligned stack, so this is `8`; for a
  link-register ABI the call pushes nothing, so it is `0`. -/
  entryResidue : Nat
  /-- Bytes below the stack pointer a leaf function may use without adjusting
  it (the System V "red zone"). `0` when the ABI has none. -/
  redZone : Nat
  /-- Bytes **above** the return address that the caller reserves for the
  callee to spill register arguments into (Win64's 32-byte "shadow space").
  `0` when the ABI has none. -/
  shadowSpace : Nat
  /-- The size of one stack-passed argument slot. -/
  stackArgSlot : Nat
  /-- How the return address is found at entry. -/
  returnAddress : ReturnAddress Reg
  /-- Bytes the call instruction pushed, and hence the amount by which the
  stack pointer at the callee's `ret` exceeds its entry value. `8` for
  x86-64, `0` for a link-register ABI. -/
  linkSize : Nat

namespace CallingConvention

variable {Reg : Type u} {Val : Type v} (cc : CallingConvention Reg)

/-- How many integer arguments go in registers. -/
def maxIntArgs : Nat := cc.intArgRegs.length

/-- The register holding integer argument `i`, if it is passed in one. -/
def intArgReg? (i : Nat) : Option Reg := cc.intArgRegs[i]?

/-- The register holding integer result `i`, if there is one. -/
def intRetReg? (i : Nat) : Option Reg := cc.intRetRegs[i]?

/-- `after` restored every callee-saved register to its value in `before`.
`before` and `after` are register reads, so this is usable over any state
type. -/
def Preserved (before after : Reg → Val) : Prop :=
  ∀ r ∈ cc.calleeSaved, after r = before r

/-- The stack pointer value `sp` is aligned as the ABI requires immediately
before a call. -/
def CallAligned (sp : Nat) : Prop := sp % cc.stackAlign = 0

/-- The stack pointer value `sp` is aligned as the ABI requires at callee
entry. For `sysv64` this unfolds to `sp % 16 = 8`. -/
def EntryAligned (sp : Nat) : Prop := sp % cc.stackAlign = cc.entryResidue

/-- The lowest byte address a callee with frame size `frame` may touch, given
its entry stack pointer `sp`: the frame plus the red zone. `frame` is measured
from the entry stack pointer, so it includes anything the prologue pushed. -/
def frameFloor (sp frame : Nat) : Nat := sp - frame - cc.redZone

/-- The number of bytes at and below the entry stack pointer that a callee
with frame size `frame` may touch. -/
def frameExtent (frame : Nat) : Nat := frame + cc.redZone

/-- Sanity conditions on a convention. These are not deep; they exist so that
an instance can be checked by `decide` rather than read. -/
structure WellFormed : Prop where
  /-- A zero alignment would make `EntryAligned` meaningless. -/
  align_pos : 0 < cc.stackAlign
  /-- The entry residue is an actual residue. -/
  residue_lt : cc.entryResidue < cc.stackAlign
  /-- The call pushes a whole number of alignment-preserving units, so that
  `CallAligned sp` before the call gives `EntryAligned (sp - linkSize)`. -/
  residue_eq : cc.linkSize % cc.stackAlign = cc.entryResidue
  /-- No register carries two different arguments. -/
  argRegs_nodup : cc.intArgRegs.Nodup
  /-- No register carries two different results. -/
  retRegs_nodup : cc.intRetRegs.Nodup
  /-- The callee-saved list is a set. -/
  calleeSaved_nodup : cc.calleeSaved.Nodup
  /-- The stack pointer is not an argument register: its discipline is the
  stack discipline, not argument passing. -/
  sp_not_arg : cc.stackPointer ∉ cc.intArgRegs
  /-- The stack pointer is handled by `linkSize`, not by `Preserved`. -/
  sp_not_saved : cc.stackPointer ∉ cc.calleeSaved
  /-- An argument register is caller-saved. -/
  args_not_saved : ∀ r ∈ cc.intArgRegs, r ∉ cc.calleeSaved
  /-- A result register is caller-saved. -/
  rets_not_saved : ∀ r ∈ cc.intRetRegs, r ∉ cc.calleeSaved

/-! ## Elementary consequences -/

variable {cc}

theorem preserved_refl (read : Reg → Val) : cc.Preserved read read := fun _ _ => rfl

theorem Preserved.trans {a b c : Reg → Val} (hab : cc.Preserved a b)
    (hbc : cc.Preserved b c) : cc.Preserved a c :=
  fun r hr => (hbc r hr).trans (hab r hr)

/-- A convention with no callee-saved registers constrains nothing, which is
what `Preserved` then says. -/
theorem preserved_of_calleeSaved_nil (h : cc.calleeSaved = []) (a b : Reg → Val) :
    cc.Preserved a b := by
  intro r hr
  rw [h] at hr
  exact absurd hr (List.not_mem_nil)

/-- The frame floor is below the entry stack pointer whenever the frame fits. -/
theorem frameFloor_le (sp frame : Nat) : cc.frameFloor sp frame ≤ sp := by
  unfold frameFloor
  omega

/-- When the frame fits in the address space below `sp`, the extent is exact. -/
theorem frameFloor_add_frameExtent {sp frame : Nat} (h : cc.frameExtent frame ≤ sp) :
    cc.frameFloor sp frame + cc.frameExtent frame = sp := by
  unfold frameFloor frameExtent at *
  omega

end CallingConvention

end Silmaril.Machine
