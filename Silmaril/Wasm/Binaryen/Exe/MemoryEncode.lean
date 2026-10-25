module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBase

@[expose] public section

/-! # Scalar memory encoding

The executable memory fragment uses explicit memory indices, 64-bit offsets and
either 32-bit or 64-bit memory limits. Unsupported alignment exponents fail
before bytes are emitted. Memory-zero encodings retain their original bytes.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- Core 3.0 memory arguments: alignment exponent and a `u64` offset. -/
def encMemArg (x : MemIdx) (a : MemArg) : Except String (List UInt8) :=
  if a.align.val < 64 then
    if x.toNat = 0 then
      pure (encU a.align.val ++ encU a.offset.val)
    else
      pure (encU (a.align.val + 64) ++ encIdx x ++ encU a.offset.val)
  else throw "encoder: only alignment exponents below 64 are supported"

/-- Integer loads, including sign- and zero-extending packed loads. -/
def intLoadOpcode : IntType → Option (PackSize × Signedness) → Except String UInt8
  | .i32, none => pure 0x28
  | .i64, none => pure 0x29
  | .i32, some (.i8, .signed) => pure 0x2C
  | .i32, some (.i8, .unsigned) => pure 0x2D
  | .i32, some (.i16, .signed) => pure 0x2E
  | .i32, some (.i16, .unsigned) => pure 0x2F
  | .i64, some (.i8, .signed) => pure 0x30
  | .i64, some (.i8, .unsigned) => pure 0x31
  | .i64, some (.i16, .signed) => pure 0x32
  | .i64, some (.i16, .unsigned) => pure 0x33
  | .i64, some (.i32, .signed) => pure 0x34
  | .i64, some (.i32, .unsigned) => pure 0x35
  | _, _ => throw "encoder: invalid packed integer load"

/-- Integer stores, including truncating packed stores. -/
def intStoreOpcode : IntType → Option PackSize → Except String UInt8
  | .i32, none => pure 0x36
  | .i64, none => pure 0x37
  | .i32, some .i8 => pure 0x3A
  | .i32, some .i16 => pure 0x3B
  | .i64, some .i8 => pure 0x3C
  | .i64, some .i16 => pure 0x3D
  | .i64, some .i32 => pure 0x3E
  | _, _ => throw "encoder: invalid packed integer store"

/-- Core 3.0 index immediate for size, grow and bulk-memory instructions.
The minimal encoding of memory zero remains the reserved byte `0x00`. -/
def encMemoryIdx (x : MemIdx) : Except String (List UInt8) :=
  pure (encIdx x)

/-- A defined memory, with optional maximum and address-width-specific limits.
The i32 branch retains the original u32 check and byte encoding. -/
def encMemory (m : MemoryType) : Except String (List UInt8) :=
  match m.address with
  | .i32 => do
    let lo ← encU32 m.limits.min.val
    match m.limits.max with
    | none => pure ([0x00] ++ lo)
    | some hi => pure ([0x01] ++ lo ++ (← encU32 hi.val))
  | .i64 =>
    match m.limits.max with
    | none => pure ([0x04] ++ encU m.limits.min.val)
    | some hi => pure ([0x05] ++ encU m.limits.min.val ++ encU hi.val)

end Silmaril.Wasm.Binaryen.Exe
