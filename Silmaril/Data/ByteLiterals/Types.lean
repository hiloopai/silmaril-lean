module

public import Silmaril.Data.IncludeBytes.Types
public import Init.Data.BitVec

/-! Data-only byte-array conversions; compact generated terms need no elaborator
or Mathlib import. Literal macros and inverse proofs live in `ByteLiterals`. -/
@[expose] public section
namespace Silmaril.ByteLiterals

def toBitVecBytes (bytes : ByteArray) : Array (BitVec 8) :=
  (bytes.data.toList.map fun byte => BitVec.ofNat 8 byte.toNat).toArray


def toByteArray (bytes : Array (BitVec 8)) : ByteArray :=
  ⟨(bytes.toList.map fun byte => UInt8.ofNat byte.toNat).toArray⟩


end Silmaril.ByteLiterals
