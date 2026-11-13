module

public import Silmaril.Wasm.Wac.EmitX.Defs
public import Silmaril.Wasm.Wac.TypeOfX.Defs
public import Silmaril.Wasm.Wac.Bridge.ComposeX.Defs

/-!
# `wasm-wac compose --wasm` from WAC text and package bytes

`Emit.composeWasmX` starts from an elaboration document and a package environment that the
tool's I/O code assembled. This module puts the whole pipeline of `wasm-wac compose --wasm`
and `wasm-wac plug` into one pure function, so that its theorem covers everything between
the bytes read and the bytes written:

* `readPkgs raw ks`: for each package key `k` of the document, its bytes `raw.lookup k`, and
  its type and nominal table, decoded from those bytes (`TypeOf.decodeAnyX`: the world by
  projection, else inference over the parse with the async built-ins);
* `noValues env noms d`: the check that the elaborated graph has no value nodes
  (`Bridge.NoValue`, the one hypothesis of the lowering theorems);
* **`composeText src raw`**: read the WAC text (`Bridge.readDocX`: the verified lexer and
  parser of `Silmaril.Wasm.Wac.Text`, then `Bridge.ofDocX`), read the packages, and run
  `Emit.composeWasmX`. It returns the bytes, the canonicity table (`some` when every package's
  bytes are the canonical encoding of their parse) and the result of `noValues`.

Theorems in `Silmaril.Wasm.Wac.EndToEnd.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.EndToEnd

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

/-- The packages of keys `ks`: their types, nominal tables and bytes, read from `raw`. -/
def readPkgs (raw : List (String × ByteArray)) : List String →
    Except String (PkgEnv × List (String × Bridge.NomTable) × List (String × ByteArray))
  | [] => .ok ([], [], [])
  | k :: ks =>
    match raw.lookup k with
    | none => .error s!"package `{k}` not given"
    | some bytes =>
      match TypeOf.decodeAnyX bytes with
      | .error e => .error e
      | .ok (p, n) =>
        match readPkgs raw ks with
        | .error e => .error e
        | .ok (env, noms, rs) => .ok ((k, p) :: env, (k, n) :: noms, (k, bytes) :: rs)

/-- The elaborated graph has no value nodes (`false` when the document does not elaborate). -/
def noValues (env : PkgEnv) (noms : List (String × Bridge.NomTable)) (d : FuncAlias.Document) :
    Bool :=
  match Bridge.elabDocXV (Emit.tablesOf noms d) env d with
  | .ok g => g.nodes.all fun nd => Bridge.kindSort nd.kind != .value
  | .error _ => false

/-- **`wasm-wac compose --wasm` (and `plug`), from the WAC text and the package bytes.** -/
def composeText (src : String) (raw : List (String × ByteArray)) :
    Except String (ByteArray × Option SpliceX.PkgTableX × Bool) :=
  match Bridge.readDocX src with
  | .error e => .error e
  | .ok d =>
    match readPkgs raw (Bridge.pkgKeysX d) with
    | .error e => .error e
    | .ok (env, noms, rs) =>
      match Emit.composeWasmX env noms rs d with
      | .error e => .error e
      | .ok (b, t) => .ok (b, t, noValues env noms d)

end Silmaril.Wasm.Wac.EndToEnd
