module

public import Silmaril.Wasm.Wac.EncodeR.Defs
public import Silmaril.Wasm.Wac.EndToEnd.Defs
public import Silmaril.Wasm.Wac.WatOut.Defs
public import Silmaril.Wasm.Perf.Splice.Defs
public import Silmaril.Wasm.Perf.CanonB.Defs
public import Silmaril.Wasm.Wac.TextCheck.Defs

/-!
# WAC: the pipeline `wasm-wac` runs, with resources shared between instances

Each entry point of the tool first runs `TextCheck.checkText` (two checks of wac's resolver that
`Valid` lacks: duplicate parameter names, interfaces used as value types), then is the verified
pipeline when it succeeds, and otherwise the same
pipeline with `EncodeR.encode` (the encoder that aliases resources of other instances,
`Silmaril.Wasm.Wac.EncodeR`) in place of `Bridge.encode`:

* `composeTextR` (`compose --wasm`, `plug`): `EndToEnd.composeText`, else `composeTextU`;
* `composeImpTextR` (`--import-dependencies`): `WatOut.composeImpText`, else `composeImpTextU`;
* `composeWatTextR` (no `--wasm`): `WatOut.composeWatText`, else `composeWatTextU`.

`composeTextR_of_ok`, `composeImpTextR_of_ok`, `composeWatTextR_of_ok`
(`Silmaril.Wasm.Wac.EndToEndR.Thms`): whenever the verified pipeline succeeds, the tool's output
is its output, so `EndToEnd.composeText_correct` and the theorems built on it apply unchanged.
The fallback outputs are checked by `wasm-tools validate`, WIT comparison with `wac` and
execution under `wasmtime` (`tools/wac/tests/corpus.sh`, `tools/wac/tests/rust.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.EndToEndR

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

/-- The composition as a component AST, with the shared-resource encoder. -/
def composeAstU (env : PkgEnv) (noms : List (String × Bridge.NomTable)) (d : FuncAlias.Document) :
    Except String Ast := do
  let g ← Emit.elabGraph env noms d
  EncodeR.encode (Emit.nomOf noms d) g

/-- `Emit.composeWasmRaw` with the shared-resource encoder. -/
def composeWasmRawU (env : PkgEnv) (noms : List (String × Bridge.NomTable))
    (raw : List (String × ByteArray)) (d : FuncAlias.Document) : Except String ByteArray := do
  let c ← composeAstU env noms d
  match Silmaril.Wasm.Perf.Splice.spliceF (Splice.table raw) c with
  | some b => .ok b
  | none => .error "the composition has a number or length of 2^32 or more"

/-- `EndToEnd.composeText` with the shared-resource encoder. -/
def composeTextU (src : String) (raw : List (String × ByteArray)) :
    Except String (ByteArray × Option SpliceX.PkgTableX × Bool) :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, rs) =>
      match composeWasmRawU env noms rs d with
      | .error e => .error e
      | .ok b => .ok (b, Silmaril.Wasm.Perf.EncodeB.canonTableF (Splice.table rs), EndToEnd.noValues env noms d)

/-- `Emit.composeWasmRaw` with the `ByteArray` splicer (`Perf.Splice.spliceF`, equal to
`Splice.splice`). -/
def composeWasmRawF (env : PkgEnv) (noms : List (String × Bridge.NomTable))
    (raw : List (String × ByteArray)) (d : FuncAlias.Document) : Except String ByteArray := do
  let c ← Emit.composeAst env noms d
  match Silmaril.Wasm.Perf.Splice.spliceF (Splice.table raw) c with
  | some b => .ok b
  | none => .error "the composition has a number or length of 2^32 or more"

/-- `EndToEnd.composeText` with the `ByteArray` splicer and canonicity check (`composeTextF_eq`:
the same function). -/
def composeTextF (src : String) (raw : List (String × ByteArray)) :
    Except String (ByteArray × Option SpliceX.PkgTableX × Bool) :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, rs) =>
      match composeWasmRawF env noms rs d with
      | .error e => .error e
      | .ok b => .ok (b, Silmaril.Wasm.Perf.EncodeB.canonTableF (Splice.table rs), EndToEnd.noValues env noms d)

/-- **`wasm-wac compose --wasm` and `plug`**: the verified pipeline, else the shared-resource
encoder. -/
def composeTextR (src : String) (raw : List (String × ByteArray)) :
    Except String (ByteArray × Option SpliceX.PkgTableX × Bool) :=
  match TextCheck.checkText src with
  | .error e => .error e
  | .ok () =>
    match composeTextF src raw with
    | .ok r => .ok r
    | .error e => match composeTextU src raw with
      | .ok r => .ok r
      | .error _ => .error e

/-- `WatOut.composeImpText` with the shared-resource encoder. -/
def composeImpTextU (src : String) (raw : List (String × ByteArray)) : Except String ByteArray :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, _) => do
      let c ← composeAstU env noms d
      Emit.toBytes c

/-- **`wasm-wac compose --wasm --import-dependencies`**. -/
def composeImpTextR (src : String) (raw : List (String × ByteArray)) : Except String ByteArray :=
  match TextCheck.checkText src with
  | .error e => .error e
  | .ok () =>
    match WatOut.composeImpText src raw with
    | .ok b => .ok b
    | .error e => match composeImpTextU src raw with
      | .ok b => .ok b
      | .error _ => .error e

/-- `WatOut.composeWatText` with the shared-resource encoder. -/
def composeWatTextU (src : String) (raw : List (String × ByteArray)) : Except String String :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match EndToEnd.readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, _) => do
      let c ← composeAstU env noms d
      pure (Component.Wat.print c)

/-- **`wasm-wac compose`** (WAT output). -/
def composeWatTextR (src : String) (raw : List (String × ByteArray)) : Except String String :=
  match TextCheck.checkText src with
  | .error e => .error e
  | .ok () =>
    match WatOut.composeWatText src raw with
    | .ok t => .ok t
    | .error e => match composeWatTextU src raw with
      | .ok t => .ok t
      | .error _ => .error e

end Silmaril.Wasm.Wac.EndToEndR
