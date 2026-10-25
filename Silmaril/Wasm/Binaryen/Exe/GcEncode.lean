module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBase

@[expose] public section

/-! # Reference and GC type encodings

Heap types and reference types of the GC slice of the profile. The encoder is canonical:
a nullable reference to an abstract heap type uses the one-byte shorthand (`funcref`
is `0x70`), every other reference type the prefixed form `0x63`/`0x64` (5.2:34–37), and
a concrete heap type is its type index as a non-negative `s33` (5.2:30).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- Abstract heap types (5.2:16–28). -/
def encAbsHeapType : AbsHeapType → UInt8
  | .exn => 0x69 | .array => 0x6A | .struct => 0x6B | .i31 => 0x6C
  | .eq => 0x6D | .any => 0x6E | .extern => 0x6F | .func => 0x70
  | .none => 0x71 | .noextern => 0x72 | .nofunc => 0x73 | .noexn => 0x74

/-- The inverse of `encAbsHeapType` on single bytes. -/
def absHeapTypeOf? : Nat → Option AbsHeapType
  | 0x69 => some .exn | 0x6A => some .array | 0x6B => some .struct | 0x6C => some .i31
  | 0x6D => some .eq | 0x6E => some .any | 0x6F => some .extern | 0x70 => some .func
  | 0x71 => some .none | 0x72 => some .noextern | 0x73 => some .nofunc | 0x74 => some .noexn
  | _ => none

/-- Heap types (5.2:30–31). -/
def encHeapType : HeapType → List UInt8
  | .abstract ht => [encAbsHeapType ht]
  | .typeIdx x => encS x.toNat

/-- Reference types, canonically (see the module docstring). -/
def encRefType (r : RefType) : List UInt8 :=
  match r.nullable, r.heap with
  | true, .abstract ht => [encAbsHeapType ht]
  | true, .typeIdx x => [0x63] ++ encS x.toNat
  | false, ht => [0x64] ++ encHeapType ht

/-- The cast flags of `br_on_cast(_fail)` (5.3:20–24): bit 0 the source's nullability,
bit 1 the target's. -/
def encCastOp (n₁ n₂ : Bool) : UInt8 :=
  (if n₁ then 1 else 0) + (if n₂ then 2 else 0)

/-- Packed storage types (5.2:55–57). -/
def encPackType : PackType → UInt8
  | .i8 => 0x78
  | .i16 => 0x77

end Silmaril.Wasm.Binaryen.Exe
