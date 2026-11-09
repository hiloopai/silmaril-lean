module

public import Silmaril.Formats.Compression.Inflate.Stream.Bits

/-!
# Source-shaped packed Huffman entry lookup

`code` in both pinned `inftrees.h` revisions has
unsigned-byte operation/bit fields and an unsigned-short value. This module
implements the slow LEN and DIST root/one-subtable lookup branches in
`inflate.c`, using an already-filled mathematical reservoir. Insufficient
buffered bits suspend without dropping code bits; table bounds failure is
separate from a source invalid-code operation. Refilling, pointers, packed
memory layout and the fast path remain separate refinements.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

structure Entry where
  op : UInt8
  bits : UInt8
  val : UInt16
  deriving Repr, DecidableEq, Inhabited

inductive Kind where
  | literalLength
  | distance
  deriving Repr, DecidableEq

inductive Meaning where
  | literal (value : Nat)
  | endBlock
  | baseExtra (base extraBits : Nat)
  | invalid
  deriving Repr, DecidableEq

/-- The source tests EOB before invalid in LEN, and only invalid in DIST. -/
def meaning (kind : Kind) (entry : Entry) : Meaning :=
  match kind with
  | .literalLength =>
    if entry.op.toNat = 0 then .literal entry.val.toNat
    else if entry.op.toNat.testBit 5 then .endBlock
    else if entry.op.toNat.testBit 6 then .invalid
    else .baseExtra entry.val.toNat (entry.op.toNat % 16)
  | .distance =>
    if entry.op.toNat.testBit 6 then .invalid
    else .baseExtra entry.val.toNat (entry.op.toNat % 16)

def isLink (kind : Kind) (entry : Entry) : Bool :=
  match kind with
  | .literalLength => decide (entry.op.toNat ≠ 0 ∧ entry.op.toNat < 16)
  | .distance => decide (entry.op.toNat < 16)

inductive LookupResult where
  | found (entry : Entry) (rest : Reservoir) (codeBits : Nat)
  | needInput (saved : Reservoir)
  | tableBounds
  deriving Repr, DecidableEq

/-- Source lookup order: index the root before checking its consumed bit
count; a link indexes the child before dropping the root's bits. The two
DROPBITS operations on a successful link remain separate. -/
def lookup (kind : Kind) (table : Array Entry) (rootBits : Nat) (state : Reservoir) : LookupResult :=
  match table[state.lowBits rootBits]? with
  | none => .tableBounds
  | some root =>
    if root.bits.toNat ≤ state.bits then
      if isLink kind root then
        let index := root.val.toNat +
          state.lowBits (root.bits.toNat + root.op.toNat) / 2 ^ root.bits.toNat
        match table[index]? with
        | none => .tableBounds
        | some leaf =>
          if root.bits.toNat + leaf.bits.toNat ≤ state.bits then
            .found leaf ((state.dropBits root.bits.toNat).dropBits leaf.bits.toNat)
              (root.bits.toNat + leaf.bits.toNat)
          else .needInput state
      else .found root (state.dropBits root.bits.toNat) root.bits.toNat
    else .needInput state

inductive Value where
  | literal (value : Nat)
  | endBlock
  | amount (value : Nat)
  deriving Repr, DecidableEq

inductive DecodeResult where
  | value (decoded : Value) (rest : Reservoir) (codeBits extraBits : Nat)
  | invalid (rest : Reservoir) (codeBits : Nat)
  | needCode (saved : Reservoir)
  | needExtra (base extraBits : Nat) (saved : Reservoir) (codeBits : Nat)
  | tableBounds
  deriving Repr, DecidableEq

/-- LENEXT/DISTEXT use the low four operation bits and read those extra bits
least-significant first. A suspension after the code retains a pending base. -/
def decode (kind : Kind) (table : Array Entry) (rootBits : Nat) (state : Reservoir) : DecodeResult :=
  match lookup kind table rootBits state with
  | .tableBounds => .tableBounds
  | .needInput saved => .needCode saved
  | .found entry rest codeBits =>
    match meaning kind entry with
    | .literal value => .value (.literal value) rest codeBits 0
    | .endBlock => .value .endBlock rest codeBits 0
    | .invalid => .invalid rest codeBits
    | .baseExtra base extra =>
      match rest.readBits extra with
      | .needInput saved => .needExtra base extra saved codeBits
      | .value amount after => .value (.amount (base + amount)) after codeBits extra

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
