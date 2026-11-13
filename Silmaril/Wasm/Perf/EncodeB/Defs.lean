module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Component.BinaryAsync.Defs

/-!
# Component encoders into a `ByteArray`

`Binary.encode` and `BinaryAsync.EncodeX.ast` build a `List UInt8` of the whole component (an
embedded core module of a few MB becomes a list of a few million cells) and convert it at the
end. `encodeF` and `astXB` append each top-level section to a `ByteArray`, core modules as
their own `ByteArray` with the `u32` size prefix, the other sections through the list encoders
as before.

This module depends on the component binary syntax and its list encoders only (it imports no
theorem header), so code that wants the fast encoder calls `encodeF` directly. `Thms.lean`:
`encodeF_eq`, `astXB_eq`; `encode_eq_encodeF` is registered with `@[csimp]`. The canonicity
check of `wasm-wac` over `astXB` is `Perf.CanonB`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.EncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

/-- A byte list as a `ByteArray`. -/
@[inline] def toBA (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- `Encode.section_ s` appended to `acc`. -/
def secB (acc : ByteArray) : Section → Option ByteArray
  | .coreModule m => do
    let len ← Silmaril.Parse.ByteParse.Enc.u32 m.size
    pure ((acc.push 0x01 ++ toBA len) ++ m)
  | s => (Encode.section_ s).map (acc ++ toBA ·)

/-- `Encode.sections ss` appended to `acc`. -/
def secsB : List Section → ByteArray → Option ByteArray
  | [], acc => some acc
  | s :: ss, acc => do
    let acc ← secB acc s
    secsB ss acc

/-- **`Binary.encode` into a `ByteArray`** (`encodeF_eq`). -/
def encodeF : Ast → Option ByteArray
  | .mk ss => secsB ss (toBA preambleBytes)

/-- `EncodeX.section_ s` appended to `acc`. -/
def secXB (acc : ByteArray) : SectionX → Option ByteArray
  | .coreModule m => do
    let len ← Silmaril.Parse.ByteParse.Enc.u32 m.size
    pure ((acc.push 0x01 ++ toBA len) ++ m)
  | s => (EncodeX.section_ s).map (acc ++ toBA ·)

/-- `EncodeX.sections ss` appended to `acc`. -/
def secsXB : List SectionX → ByteArray → Option ByteArray
  | [], acc => some acc
  | s :: ss, acc => do
    let acc ← secXB acc s
    secsXB ss acc

/-- `EncodeX.ast` into a `ByteArray` (`astXB_eq`). -/
def astXB : AstX → Option ByteArray
  | .mk ss => secsXB ss (toBA preambleBytes)

end Silmaril.Wasm.Perf.EncodeB
