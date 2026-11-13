module

public import Silmaril.Compiler.Native.Lower.Defs
/-! Byte-image obligations for the actual native initializer. Constant encoding
uses the lowerer's existing literal and target-layout helpers. This interface
does not supply a C evaluation or whole-program preservation theorem. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Initialization

/-- Byte `index` of a natural number in little-endian storage. -/
def byte (value index : Nat) : UInt8 := ((value >>> (8 * index)) % 256).toUInt8

/-- Exact byte encoding, including the unchanged image extent and all bytes
outside the destination interval. The bounds needed for a successful write are
premises of the encoding theorem, rather than hidden in this relation. -/
def EncodesLE (before after : ByteArray) (offset width value : Nat) : Prop :=
  after.size = before.size ∧ ∀ address,
    after[address]! = if offset ≤ address ∧ address < offset + width then
      byte value (address - offset) else before[address]!

end Silmaril.Compiler.Native.Initialization
