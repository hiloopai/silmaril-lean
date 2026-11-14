module

public import Init.Data.Nat.Bitwise.Basic

/-!
# Finite sets of naturals as bit masks

`NatBitSet` stores a finite set of natural numbers as one `Nat`: `k` is a member
when bit `k` is set. The representation is canonical (every `Nat` is a set and
equal sets have equal masks, `NatBitSet.ext_iff`), and the kernel evaluates
membership, insertion, union, intersection and equality with its built-in
arbitrary-precision `Nat` operations, so these are cheap under `decide`.
Suited to dense sets of small numbers: the mask has `max + 1` bits.
-/

@[expose] public section

namespace Silmaril.Data

/-- A finite set of naturals: member `k` is bit `k` of `bits`. -/
structure NatBitSet where
  bits : Nat
  deriving DecidableEq, Repr, Inhabited

namespace NatBitSet

/-- The empty set. -/
def empty : NatBitSet := ⟨0⟩

/-- Membership, as a `Bool`. -/
def mem (s : NatBitSet) (k : Nat) : Bool := s.bits.testBit k

/-- Add `k`. -/
def insert (s : NatBitSet) (k : Nat) : NatBitSet := ⟨s.bits ||| 2 ^ k⟩

/-- Remove `k`. -/
def erase (s : NatBitSet) (k : Nat) : NatBitSet := ⟨s.bits &&& (s.bits ^^^ 2 ^ k)⟩

/-- Union. -/
def union (s t : NatBitSet) : NatBitSet := ⟨s.bits ||| t.bits⟩

/-- Intersection. -/
def inter (s t : NatBitSet) : NatBitSet := ⟨s.bits &&& t.bits⟩

/-- Difference. -/
def diff (s t : NatBitSet) : NatBitSet := ⟨s.bits &&& (s.bits ^^^ t.bits)⟩

/-- The set of the listed numbers. -/
def ofList (l : List Nat) : NatBitSet := l.foldl insert empty

end NatBitSet

end Silmaril.Data
