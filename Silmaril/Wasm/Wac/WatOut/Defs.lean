module

public import Silmaril.Wasm.Wac.EndToEnd.Defs
public import Silmaril.Wasm.Component.Wat.Defs
public import Silmaril.Wasm.Perf.WatPrint.Defs

/-!
# `wasm-wac compose` without `--wasm`: the WAT, from WAC text and package bytes

`wasm-wac compose IN.wac --deps DIR` prints the composition as component WAT. Until now it ran
`Bridge.composeWatXV` on packages decoded by `Bridge.decodePkg`, which no theorem covered and
which read packages differently from `compose --wasm` (`TypeOf.decodeAnyX`). This module puts
the WAT path, and the `--wasm --import-dependencies` path, into pure functions of the WAC text
and the package bytes, sharing `EndToEnd.readPkgs` and `Emit.composeAst` with `composeText`:

* **`composeWatText src raw`**: read the text (`Bridge.readDocX`), the packages from their bytes
  (`EndToEnd.readPkgs`), elaborate and validate (`Emit.composeAst`: `Bridge.elabDocXV`, then
  `Bridge.encode`) and print the component with the proved printer `Component.Wat.print`;
* **`composeImpText src raw`**: the same composition as bytes, packages imported (`Emit.composeWasm
  … [] false`), what `compose --wasm --import-dependencies` writes.

Theorems in `Silmaril.Wasm.Wac.WatOut.Thms`: the printed text reads back (`Wat.read`) as the
normal form of the composition, which is in the composition profile and lowers to the
elaborated graph; it is exactly the text of the component the `--import-dependencies` bytes
parse to.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WatOut

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

/-- **`wasm-wac compose IN.wac --deps DIR`**: the WAT of the composition, from the WAC text
and the package bytes. -/
def composeWatText (src : String) (raw : List (String × ByteArray)) : Except String String :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, _) =>
      match Emit.composeAst env noms d with
      | .error e => .error e
      | .ok c => .ok (Silmaril.Wasm.Perf.WatPrint.printF c)

/-- **`wasm-wac compose IN.wac --deps DIR --wasm --import-dependencies`**: the bytes of the
composition with the packages imported, from the WAC text and the package bytes. -/
def composeImpText (src : String) (raw : List (String × ByteArray)) : Except String ByteArray :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, _) => Emit.composeWasm env noms [] false d

end Silmaril.Wasm.Wac.WatOut
