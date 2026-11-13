module

public import Silmaril.Wasm.Component.Reference.ABI.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs
public import Silmaril.Wasm.Execution.Memory

/-!
# Canonical integer record buffers

Native `ByteArray` operations encode booleans and integers in little-endian
memory. The low-level scalar helpers allow unaligned access; `storeRecord` and
`loadRecord` impose canonical record alignment and full bounds, including tail
padding. Fields are aligned individually and padding bytes are untouched.

These codecs operate on an already allocated buffer. They do not implement
realloc, ownership, post-return, or an indirect component call. Scalar records
are a shared foundation for indirect parameter/result tuples. Natural offsets
are bounded by the supplied byte array; pointer-width validation belongs to the
calling adapter that supplies an offset.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

open Silmaril.Wasm.Execution

def Scalar.byteCount : Scalar → Nat
  | .bool | .u8 | .s8 => 1
  | .u16 | .s16 => 2
  | .u32 | .s32 => 4
  | .u64 | .s64 => 8

def Scalar.alignment (t : Scalar) : Alignment := (primitiveLayout .i32 t.primitive).alignment

/-- Canonical scalar storage uses little-endian bytes, including two's-complement
signed integers; there is no core-stack sign extension in memory. -/
def ScalarValue.store (memory : ByteArray) (start : Nat) (v : ScalarValue) : Option ByteArray :=
  Memory.store memory start (v.bits.setWidth (8 * v.type.byteCount))

def Scalar.load (t : Scalar) (memory : ByteArray) (start : Nat) : Option ScalarValue :=
  (Memory.load memory start t.byteCount).map fun bits => ⟨t, t.liftBits bits⟩

def storeFields : ByteArray → Nat → List ScalarValue → Option ByteArray
  | memory, _, [] => some memory
  | memory, cursor, v :: vs => do
      let start := alignTo cursor v.type.alignment
      let next ← v.store memory start
      storeFields next (start + v.type.byteCount) vs

def loadFields : ByteArray → Nat → List Scalar → Option (List ScalarValue)
  | _, _, [] => some []
  | memory, cursor, t :: ts => do
      let start := alignTo cursor t.alignment
      let v ← t.load memory start
      let vs ← loadFields memory (start + t.byteCount) ts
      return v :: vs

/-- The record convention is also the convention for an indirect parameter tuple. -/
def scalarRecordLayout (ts : List Scalar) : Layout :=
  recordLayout (ts.map fun t => primitiveLayout .i32 t.primitive)

def storeRecord (memory : ByteArray) (start : Nat) (vs : List ScalarValue) : Option ByteArray :=
  let l := scalarRecordLayout (vs.map ScalarValue.type)
  if start % l.alignment.bytes = 0 ∧ start + l.size ≤ memory.size then
    storeFields memory start vs
  else none

def loadRecord (ts : List Scalar) (memory : ByteArray) (start : Nat) :
    Option (List ScalarValue) :=
  let l := scalarRecordLayout ts
  if start % l.alignment.bytes = 0 ∧ start + l.size ≤ memory.size then
    loadFields memory start ts
  else none

@[simp] theorem Scalar.primitiveLayout_size (t : Scalar) :
    (primitiveLayout .i32 t.primitive).size = t.byteCount := by
  cases t <;> rfl

/-- End of the last field, before any record tail padding. -/
def endFields : Nat → List Scalar → Nat
  | cursor, [] => cursor
  | cursor, t :: ts => endFields (alignTo cursor t.alignment + t.byteCount) ts

end Silmaril.Wasm.Component.ABI
