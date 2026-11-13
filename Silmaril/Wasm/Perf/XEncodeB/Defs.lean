module

public import Silmaril.Wasm.JcoTool.Emit.Defs
public import Silmaril.Wasm.Perf.EncodeB.Defs

/-!
# `XAst.encode` into a `ByteArray`

`XAst.encode` (the bytes of every component `wasm-jco new` writes) encodes the sections as one
`List UInt8` and turns it into a `ByteArray` at the end: the input core module, embedded as it
is, becomes a list of its bytes (on a 10.8 MB module about 260 MB of list cells, and most of the
emission time). `xencodeF` appends each section to a `ByteArray` accumulator, the core modules
as `ByteArray`s (`EncodeB.secB`); built-in sections are encoded as before and appended.

`Thms.lean`: `xencodeF_eq`, registered with `@[csimp]`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.XEncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Perf.EncodeB (toBA)

/-- `XSection.encode s` appended to `acc`. -/
def xsecB (acc : ByteArray) : XSection → Option ByteArray
  | .sec s => Silmaril.Wasm.Perf.EncodeB.secB acc s
  | s => s.encode.map (acc ++ toBA ·)

/-- `XSection.encodeAll ss` appended to `acc`. -/
def xsecsB : List XSection → ByteArray → Option ByteArray
  | [], acc => some acc
  | s :: ss, acc => do
    let acc ← xsecB acc s
    xsecsB ss acc

/-- **`XAst.encode` into a `ByteArray`** (`xencodeF_eq`). -/
def xencodeF (c : XAst) : Option ByteArray := xsecsB c.sections (toBA preambleBytes)

end Silmaril.Wasm.Perf.XEncodeB
