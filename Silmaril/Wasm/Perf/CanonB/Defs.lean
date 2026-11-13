module

public import Silmaril.Wasm.Perf.EncodeB.Defs
public import Silmaril.Wasm.Wac.SpliceX.Defs

/-!
# The canonicity check of `wasm-wac` over the `ByteArray` encoder

`canonPkgF` is `SpliceX.canonPkg` (the canonicity check of `wasm-wac compose --wasm` and
`plug`) comparing `ByteArray`s (`EncodeB.astXB`) instead of byte lists; `canonTableF` is
`SpliceX.canonTable` over it. `Thms.lean`: `canonPkgF_eq`, and `canonTable_eq_canonTableF`,
registered with `@[csimp]`. Runtime code (`Wac.EmitX`, `Wac.EndToEndR`) calls `canonTableF`
directly, so it imports no theorem header.

New definitions (moved from `Perf.EncodeB`, whose encoders do not depend on `wasm-wac`).
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.EncodeB

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

/-- **`SpliceX.canonPkg` with `astXB`** (`canonPkgF_eq`). -/
def canonPkgF (p : String × ByteArray) : Option (String × AstX) :=
  match parseX p.2 with
  | .ok a => if astXB a = some p.2 then some (p.1, a) else none
  | .error _ => none

/-- `SpliceX.canonTable` with `canonPkgF` (`canonTable_eq_canonTableF`). -/
def canonTableF (raw : Silmaril.Wasm.Wac.Splice.RawTable) :
    Option Silmaril.Wasm.Wac.SpliceX.PkgTableX :=
  raw.mapM canonPkgF

end Silmaril.Wasm.Perf.EncodeB
