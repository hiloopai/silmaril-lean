module

public import Silmaril.Wasm.Wac.Splice.Defs

/-!
# `Splice.splice` into a `ByteArray`

`Wac.Splice.splice` (the bytes `wasm-wac compose --wasm` and `plug` write) turns every embedded
package into a `List UInt8` (`r.data.toList`), measures and prefixes it as a list, appends the
lists and converts the result back. `spliceF` appends each package's `ByteArray` to a
`ByteArray` accumulator, with the same `u32` size prefix; the other sections are encoded as
before (`Encode.section_`) and appended. `Thms.lean`: `spliceF_eq : spliceF = Splice.splice`,
registered with `@[csimp]`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.Splice

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wac.Splice (RawTable rawSec rawSecs splice)

/-- A byte list as a `ByteArray`. -/
@[inline] def toBA (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- `rawSec raw s` appended to `acc`. -/
def rawSecF (raw : RawTable) (acc : ByteArray) : Section → Option ByteArray
  | .imports [⟨n, .component t⟩] =>
    match raw.lookup n.name with
    | some r => do
      let len ← Silmaril.Parse.ByteParse.Enc.u32 r.size
      pure ((acc.push 0x04 ++ toBA len) ++ r)
    | none => (Encode.section_ (.imports [⟨n, .component t⟩])).map (acc ++ toBA ·)
  | s => (Encode.section_ s).map (acc ++ toBA ·)

/-- `rawSecs raw ss` appended to `acc`. -/
def rawSecsF (raw : RawTable) : List Section → ByteArray → Option ByteArray
  | [], acc => some acc
  | s :: ss, acc => do
    let acc ← rawSecF raw acc s
    rawSecsF raw ss acc

/-- **`Splice.splice` into a `ByteArray`** (`spliceF_eq`). -/
def spliceF (raw : RawTable) (c : Ast) : Option ByteArray :=
  rawSecsF raw c.sections (toBA preambleBytes)

end Silmaril.Wasm.Perf.Splice
