module

public import Silmaril.Data.Layout.Bytes.Defs

/-!
# Bit-level specifications of integer members

A `BitRange` is a run of bits of an unsigned value (`lo`, `width`); `get` extracts it and
`set` replaces it, leaving every other bit alone. A `WordSpec` describes an integer member bit
by bit: named items with a role,

* `zero`: must be zero (alignment bits, must-be-zero fields);
* `reserved`: not interpreted, but kept by every writer (`WordSpec.Keeps`);
* `flag`: a one-bit boolean;
* `value`: a named number.

`WordSpec.Valid` checks the width and the zero items; `WordSpec.Keeps old new` relates two
values whose reserved items agree. The theorems (`Bits.Thms`) show that setting one item of a
well-formed spec (`WordSpec.WF`: items in range and pairwise disjoint) reads back, leaves the
other items unchanged, and keeps validity and the reserved bits.

Example: glibc's `mchunk_size` (`Silmaril.Data.Layout.Glibc.Malloc.chunkSizeSpec`) packs
`PREV_INUSE`, `IS_MMAPPED` and `NON_MAIN_ARENA` into the low bits of the chunk size.
-/

@[expose] public section

namespace Silmaril.Data.Layout

/-- Bits `[lo, lo + width)` of a value. -/
structure BitRange where
  lo : Nat
  width : Nat
  deriving DecidableEq, Repr

namespace BitRange

/-- The bits as a number. -/
def get (r : BitRange) (v : Nat) : Nat := (v >>> r.lo) % 2 ^ r.width

/-- Replace the bits by the low `width` bits of `x`. -/
def set (r : BitRange) (v x : Nat) : Nat := v ^^^ ((((v >>> r.lo) ^^^ x) % 2 ^ r.width) <<< r.lo)

/-- The ranges share no bit. -/
def Disjoint (r s : BitRange) : Prop := r.lo + r.width ≤ s.lo ∨ s.lo + s.width ≤ r.lo

instance (r s : BitRange) : Decidable (r.Disjoint s) := inferInstanceAs (Decidable (_ ∨ _))

end BitRange

inductive BitRole where
  | zero | reserved | flag | value
  deriving DecidableEq, Repr

structure BitItem where
  name : String
  range : BitRange
  role : BitRole
  deriving DecidableEq, Repr

/-- A bit-by-bit description of a `width`-bit unsigned member. -/
structure WordSpec where
  width : Nat
  items : List BitItem
  deriving DecidableEq, Repr

namespace WordSpec

def item? (S : WordSpec) (name : String) : Option BitItem := S.items.find? (·.name == name)

/-- The value of the item `name`. -/
def get? (S : WordSpec) (name : String) (v : Nat) : Option Nat :=
  (S.item? name).map fun it => it.range.get v

/-- Set the item `name` (zero and reserved items are not writable). -/
def set? (S : WordSpec) (name : String) (v x : Nat) : Option Nat :=
  (S.item? name).bind fun it =>
    if it.role = .flag ∨ it.role = .value then some (it.range.set v x) else none

/-- A flag item's value. -/
def flag? (S : WordSpec) (name : String) (v : Nat) : Option Bool :=
  (S.get? name v).map (· == 1)

/-- The value fits the width and every zero item is zero. -/
def Valid (S : WordSpec) (v : Nat) : Prop :=
  v < 2 ^ S.width ∧ ∀ it ∈ S.items, it.role = .zero → it.range.get v = 0

/-- Every reserved item of `new` is as in `old`. -/
def Keeps (S : WordSpec) (old new : Nat) : Prop :=
  ∀ it ∈ S.items, it.role = .reserved → it.range.get new = it.range.get old

/-- Items inside the width, pairwise disjoint. -/
def WF (S : WordSpec) : Prop :=
  (∀ it ∈ S.items, it.range.lo + it.range.width ≤ S.width) ∧
    S.items.Pairwise fun a b => a.range.Disjoint b.range

instance (S : WordSpec) (v : Nat) : Decidable (S.Valid v) := inferInstanceAs (Decidable (_ ∧ _))
instance (S : WordSpec) : Decidable S.WF := inferInstanceAs (Decidable (_ ∧ _))

end WordSpec

/-! ## Integer members with a bit specification -/

namespace DeclLayout

variable {M : Type} [ByteMem M]

/-- Item `item` of the integer member `name` (described by `S`) of a record at `base`. -/
def readBits (dm : DataModel) (L : DeclLayout) (S : WordSpec) (m : M) (base : Nat)
    (name item : String) : Option Nat :=
  (L.readInt dm m base name).bind (S.get? item)

/-- Set item `item` of the integer member `name`; the other bits are kept. -/
def writeBits (dm : DataModel) (L : DeclLayout) (S : WordSpec) (m : M) (base : Nat)
    (name item : String) (x : Nat) : Option M :=
  (L.readInt dm m base name).bind fun v =>
    (S.set? item v x).bind fun v' => L.writeInt dm m base name v'

end DeclLayout

end Silmaril.Data.Layout
