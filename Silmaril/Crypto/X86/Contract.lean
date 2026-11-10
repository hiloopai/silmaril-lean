module

public import Silmaril.X86.Basic
public import Mathlib.Data.BitVec

/-!
# System V AMD64 contract for crypto kernels

Specifies the calling convention for kernels of the form:

    void f(uint64_t len, const uint8_t *in, uint8_t *out)

The contract covers:
- **Preconditions:** valid, non-overlapping buffers of the right sizes, and
  16-byte stack alignment (`stackAlignedAtEntry`, the §3.2.2 condition at the callee's entry
  point; nothing in this model establishes or consumes it yet, since `Silmaril.X86.Instr` has
  no `call`/`push`/`pop`).
- **Postconditions:** `out` holds `spec(in[0..len])`.
- **Callee-saved** registers preserved: RBX, RBP, R12–R15.
- **Stack** restored: RSP unchanged from entry.

This module states the contract only; no proof of it for a particular build is part of this
library.

## Argument registers (System V AMD64)
- RDI: `len` (uint64_t)
- RSI: `in` pointer (uint8_t *)
- RDX: `out` pointer (uint8_t *)
- (Optional key pointer in RCX for keyed variants)
-/

@[expose] public section

namespace Silmaril.Crypto.X86

open Silmaril.X86

/-- The three arguments of a `(len, in, out)` kernel. -/
structure KernelArgs where
  len : Word
  in_ptr : Word
  out_ptr : Word
  deriving DecidableEq, Repr

/-- Memory region: a contiguous byte range [base, base + size). -/
structure Region where
  base : Word
  size : Nat
  deriving DecidableEq, Repr

/-- Two regions are disjoint: no byte address belongs to both.

**This definition is wrong across the top of the address space** and is kept
only because it is already used. The comparison is `BitVec` `≤`, so
`r1.base + r1.size` wraps modulo `2^64`; two regions that both end exactly at
`2^64` are then reported disjoint even though they overlap. See
`not_disjoint_of_wrap` for a concrete counterexample with no wrapping region
at all. New statements should use `Regions.DisjointNat`. -/
def Regions.Disjoint (r1 r2 : Region) : Prop :=
  r1.base + BitVec.ofNat 64 r1.size ≤ r2.base ∨
  r2.base + BitVec.ofNat 64 r2.size ≤ r1.base

/-! ### Byte addresses, as naturals

`Process.Memory` indexes bytes by `Nat`, with every access checked against
`Process.addressLimit = 2^64` (`Memory.checkSpan`). The right reading of a
`Region` is therefore the half-open interval of **naturals**
`[base.toNat, base.toNat + size)`, and disjointness should be stated there. -/

/-- The byte addresses of a region, as naturals. -/
def Region.Covers (r : Region) (address : Nat) : Prop :=
  r.base.toNat ≤ address ∧ address < r.base.toNat + r.size

instance (r : Region) (address : Nat) : Decidable (r.Covers address) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The region does not run off the end of the address space, so every byte of
it is addressable and `Memory.checkSpan` can succeed on it. -/
def Region.NoWrap (r : Region) : Prop := r.base.toNat + r.size ≤ 2 ^ 64

/-- Disjointness of the natural-number intervals: the correct statement, and
the one `Process.Region.Disjoint` already uses. -/
def Regions.DisjointNat (r1 r2 : Region) : Prop :=
  r1.base.toNat + r1.size ≤ r2.base.toNat ∨ r2.base.toNat + r2.size ≤ r1.base.toNat

instance (r1 r2 : Region) : Decidable (Regions.DisjointNat r1 r2) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `DisjointNat` implies what disjointness should mean: no byte address lies
in both regions. -/
theorem Regions.DisjointNat.not_covers {r1 r2 : Region} (h : Regions.DisjointNat r1 r2)
    (address : Nat) : ¬ (r1.Covers address ∧ r2.Covers address) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rcases h with h | h <;> omega

/-- The converse needs both regions to be nonempty: an empty region covers no
address, so "no shared address" is no information about it. -/
theorem Regions.disjointNat_iff {r1 r2 : Region} (h1 : 0 < r1.size) (h2 : 0 < r2.size) :
    Regions.DisjointNat r1 r2 ↔ ∀ address, ¬ (r1.Covers address ∧ r2.Covers address) := by
  refine ⟨fun h => h.not_covers, fun h => ?_⟩
  rcases Nat.le_total r1.base.toNat r2.base.toNat with hb | hb
  · refine Or.inl (by_contra fun hc => h r2.base.toNat ⟨⟨hb, by omega⟩, ⟨Nat.le_refl _, by omega⟩⟩)
  · refine Or.inr (by_contra fun hc => h r1.base.toNat ⟨⟨Nat.le_refl _, by omega⟩, ⟨hb, by omega⟩⟩)

theorem Regions.DisjointNat.symm' {r1 r2 : Region} (h : Regions.DisjointNat r1 r2) :
    Regions.DisjointNat r2 r1 := Or.symm h

/-- The wraparound bug in `Regions.Disjoint`, concretely. Both regions end
exactly at `2^64`, so **neither wraps**; they overlap in their last two bytes;
and `Regions.Disjoint` still reports them disjoint, because
`r1.base + 4 = 0` in `BitVec 64`. -/
theorem not_disjoint_of_wrap :
    ∃ r1 r2 : Region, r1.NoWrap ∧ r2.NoWrap ∧
      Regions.Disjoint r1 r2 ∧
      (∃ address, r1.Covers address ∧ r2.Covers address) := by
  refine ⟨⟨BitVec.ofNat 64 18446744073709551612, 4⟩,
          ⟨BitVec.ofNat 64 18446744073709551614, 2⟩, ?_, ?_, Or.inl ?_,
          18446744073709551614, ?_, ?_⟩ <;>
    first
      | (unfold Region.NoWrap; decide)
      | decide

/-- Pairwise disjointness of a list of regions. -/
def Regions.PairwiseDisjoint (rs : List Region) : Prop :=
  rs.Pairwise Regions.DisjointNat

/-! ## Callee-saved register preservation -/

/-- The set of callee-saved registers per System V AMD64 ABI v1.0 §3.2.1. -/
def calleeSavedRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- A state s1 preserves callee-saved registers relative to initial state s0. -/
def calleeSavedPreserved (s0 s1 : State) : Prop :=
  ∀ r ∈ calleeSavedRegs, s1.read r = s0.read r

/-! ## Stack discipline -/

/-- The stack pointer is unchanged: epilogue restored RSP to its entry value. -/
def stackRestored (s0 s1 : State) : Prop :=
  s1.read .rsp = s0.read .rsp

/-- System V AMD64 ABI v1.0 §3.2.2: the stack pointer is 16-byte aligned immediately before a
`call`, so at the callee's entry point — the return address having been pushed — `rsp + 8` is
16-byte aligned. Nothing in this model establishes or consumes this: `Silmaril.X86.Instr` has
no `call`, `push` or `pop`. -/
def stackAlignedAtEntry (s : State) : Prop := ((s.read .rsp) + 8#64).toNat % 16 = 0

/-! ## Argument-loading -/

/-- The argument registers as loaded by the System V AMD64 calling convention. -/
def argsAsLoaded (args : KernelArgs) (s : State) : Prop :=
  s.read .rdi = args.len ∧
  s.read .rsi = args.in_ptr ∧
  s.read .rdx = args.out_ptr

end Silmaril.Crypto.X86
