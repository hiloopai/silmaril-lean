module

public import Silmaril.Data.Layout.Defs

/-!
# Byte views of laid-out structs

`ByteMem M`: a memory of bytes addressed by naturals, with a partial lookup (a hole or an
out-of-range address is `none`) and a total single-byte store. Two laws suffice for every
frame lemma: a store at a present address is read back, and a store leaves other addresses
alone. Instances (`Silmaril.Data.Layout.Bytes.Process`, `Silmaril.Data.Layout.Bytes.Wasm`, here): the byte map of x86 process memories
(`Silmaril.Process.ByteMemory`, an `ExtHashMap Nat (BitVec 8)`), Wasm linear memories
(`ByteArray`), and partial functions `Nat → Option Byte`.

On top: multi-byte `read`/`write`, integer codecs by endianness (`decode`/`encode`), and the
lens of a laid-out struct at a base address: `readField`/`writeField`, by `PlacedField` or by
member name, and `readInt`/`writeInt` of integer members. Padding is specified by a
`PadSpec` (don't care, zero, preserved) and checked by `PadOK`. The frame lemmas (writing a
member leaves the other members and the padding alone) are in `Bytes.Thms`.
-/

@[expose] public section

namespace Silmaril.Data.Layout

/-- A byte: `Silmaril.Process.Byte`. -/
abbrev Byte := BitVec 8

/-- A byte-addressed memory: partial lookup, total store, two laws. -/
class ByteMem (M : Type) where
  get? : M → Nat → Option Byte
  set : M → Nat → Byte → M
  get?_set_self : ∀ m a v, (get? m a).isSome → get? (set m a v) a = some v
  get?_set_ne : ∀ m a b v, a ≠ b → get? (set m a v) b = get? m b

namespace ByteMem

variable {M : Type} [ByteMem M]

/-- `n` bytes from address `a`; `none` if any is missing. -/
def read (m : M) (a : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => match get? m a, read m (a + 1) n with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- Store bytes from address `a`. -/
def write (m : M) (a : Nat) : List Byte → M
  | [] => m
  | b :: bs => write (set m a b) (a + 1) bs

/-- Every byte of `[a, a + n)` is present. -/
def Readable (m : M) (a n : Nat) : Prop := ∀ i < n, (get? m (a + i)).isSome

end ByteMem

/-- Partial functions as byte memories (the shape of abstract memories). -/
instance : ByteMem (Nat → Option Byte) where
  get? m a := m a
  set m a v := fun b => if b = a then some v else m b
  get?_set_self _ _ _ _ := by simp
  get?_set_ne _ a b _ h := by simp [Ne.symm h]

/-! ## Integer codecs -/

/-- Little-endian value of a byte list. -/
def leDecode : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leDecode bs

/-- The `n` low-order bytes of `v`, least significant first. -/
def leEncode : Nat → Nat → List Byte
  | 0, _ => []
  | n + 1, v => BitVec.ofNat 8 v :: leEncode n (v / 256)

def decode : Endian → List Byte → Nat
  | .little, bs => leDecode bs
  | .big, bs => leDecode bs.reverse

def encode : Endian → Nat → Nat → List Byte
  | .little, n, v => leEncode n v
  | .big, n, v => (leEncode n v).reverse

/-- Two's complement reading of an `n`-byte unsigned value. -/
def toSigned (n v : Nat) : Int :=
  if v < 2 ^ (8 * n - 1) then v else (v : Int) - 2 ^ (8 * n)

/-! ## Struct lenses -/

namespace DeclLayout

variable {M : Type} [ByteMem M]

/-- The bytes of member `f` of a record at `base`. -/
def readField (m : M) (base : Nat) (f : PlacedField) : Option (List Byte) :=
  ByteMem.read m (base + f.off) f.size

/-- Store the bytes of member `f` of a record at `base` (callers pass `f.size` bytes). -/
def writeField (m : M) (base : Nat) (f : PlacedField) (bs : List Byte) : M :=
  ByteMem.write m (base + f.off) bs

/-- The bytes of the member called `name`. -/
def read? (L : DeclLayout) (m : M) (base : Nat) (name : String) : Option (List Byte) :=
  (L.field? name).bind fun f => readField m base f

/-- Store the member called `name`; `none` if there is no such member or the byte count is
not the member's size. -/
def write? (L : DeclLayout) (m : M) (base : Nat) (name : String) (bs : List Byte) : Option M :=
  (L.field? name).bind fun f =>
    if bs.length = f.size then some (writeField m base f bs) else none

/-- An integer member as an unsigned value. -/
def readInt (dm : DataModel) (L : DeclLayout) (m : M) (base : Nat) (name : String) :
    Option Nat :=
  (L.read? m base name).map (decode dm.endian)

/-- Store an integer member (reduced modulo its width). -/
def writeInt (dm : DataModel) (L : DeclLayout) (m : M) (base : Nat) (name : String) (v : Nat) :
    Option M :=
  (L.field? name).bind fun f => some (writeField m base f (encode dm.endian f.size v))

/-- The whole record. -/
def readAll (L : DeclLayout) (m : M) (base : Nat) : Option (List Byte) :=
  ByteMem.read m base L.shape.size

end DeclLayout

/-! ## Padding -/

/-- What a specification says about the padding bytes of a record. -/
inductive PadSpec where
  /-- Unspecified: any value, may change. -/
  | dontCare
  /-- Every padding byte is zero. -/
  | zero
  /-- Every padding byte keeps its previous value. -/
  | preserved
  deriving DecidableEq, Repr

/-- The padding of the record `L` at `base` in `after` meets `spec` (`before` is the state
the record had earlier, for `preserved`). -/
def PadOK {M : Type} [ByteMem M] (L : DeclLayout) (spec : PadSpec) (before after : M)
    (base : Nat) : Prop :=
  match spec with
  | .dontCare => True
  | .zero => ∀ k, L.isPad k = true → ByteMem.get? after (base + k) = some 0
  | .preserved => ∀ k, L.isPad k = true →
      ByteMem.get? after (base + k) = ByteMem.get? before (base + k)

/-- A record image with zero padding: the given member bytes at their offsets
(`(name, bytes)`; absent members are zero too). The fixed-offset encoder of the record. -/
def DeclLayout.image (L : DeclLayout) (vals : String → Option (List Byte)) : List Byte :=
  (List.range L.shape.size).map fun k =>
    match L.fields.find? (fun f => f.off ≤ k && k < f.off + f.size) with
    | none => 0
    | some f => match vals f.name with
      | some bs => bs.getD (k - f.off) 0
      | none => 0

end Silmaril.Data.Layout
