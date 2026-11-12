module

public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Defs

/-!
# SpecTec ↔ Core 3.0, round 4, track r4-fwd: the storage-type byte primitive `$zbytes_`

The pinned script declares `$zbytes_(storagetype, lit_(storagetype)) : byte*`
(`3.1-numerics.scalar.spectec:18,37`) `hint(builtin)` with no clause, so `callDef` always takes
`B`'s answer. `array.new_data-num` and `array.init_data-num` (`Step_read` 76, 102) read the fields
they allocate or write through it: `$zbytes_(zt, c) = $data(z, y).BYTES[j : $zsize(zt)/8]`.

`zbytesCall` interprets it by Core's little-endian encoding, as `nbytesCall` and
`ibytesCall` do for `$nbytes_` and `$ibytes_`:

* at a packed type (`I8`, `I16`) and at `V128`, the literal is a `%`-wrapped natural and the
  encoding is `ibytesCall` at the type's width;
* at a number type, `nbytesCall` (the literal is a numeral, `fN` encoding for floats);
* elsewhere (reference types, junk) `nbytesCall` has no answer, since `Floats.decNumType` fails.

`Prims.builtins` answers `$zbytes_` by it (`Prims.call`). `$inv_zbytes_` (the declared inverse) is
not consulted by the declarative reading: the rules quantify over the literal `c` and only state
`$zbytes_(zt, c) = …`, so the forward lemmas instantiate `c` with Core's read value.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.ZBytes

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-- `$zbytes_(zt, c)`: the little-endian encoding of the literal `c` of storage type `zt`. -/
noncomputable def zbytesCall (zt c : Value) : Option Value :=
  match zt with
  | .case "I8" (.tuple []) => FwdMem.ibytesCall (.num (.natN 8)) c
  | .case "I16" (.tuple []) => FwdMem.ibytesCall (.num (.natN 16)) c
  | .case "V128" (.tuple []) => FwdMem.ibytesCall (.num (.natN 128)) c
  | _ => FwdMem.nbytesCall zt c

/-- `B` answers `$zbytes_` by `zbytesCall` (proved for `Prims.builtins`, `R4Fwd.zB_builtins`). -/
def ZB (B : Builtins) : Prop :=
  ∀ zt c v, zbytesCall zt c = some v → B.call "zbytes_" [.val zt, .val c] = some v

end Silmaril.Wasm.SpecTec.Sim.ZBytes
