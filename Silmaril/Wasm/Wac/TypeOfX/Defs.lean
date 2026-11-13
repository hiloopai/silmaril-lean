module

public import Silmaril.Wasm.Wac.TypeOf.Defs
public import Silmaril.Wasm.Wac.TargetsT.Defs
public import Silmaril.Wasm.Component.BinaryAsync.Defs

/-!
# WAC: the type of a component binary with async built-ins

`TypeOf.typeOf` infers a package's type from the base component AST, which has no async
canonical built-ins, so stream components (`task.return`, `stream.read`, …) needed a trusted
sidecar `NAME.wit.wasm` for their type. Here the binary is read with the extended verified
parser `BinaryAsync.parseX`, and the type is inferred from its erasure (`AstX.erase`: the
built-ins dropped). The built-ins define core functions only, and `typeOf` reads no core
function, so nothing the inference reads is lost.

* `importNames`, `exportNames`: the names of a component's top-level `import` and `export`
  sections, in order (the specification of the names `typeOf` reports);
* `typeOfX`, `decodeAnyX`: the inference on extended components and on binaries;
* `TargetsX.check`: `wasm-wac targets` on binaries with async built-ins (`TargetsT`'s verdict
  `fitsB` on the inferred type).

Theorems (`Silmaril.Wasm.Wac.TypeOfX.Thms`): `typeOf_names` (the imports `typeOf` reports are
exactly the component's imports, by name and in order, and its exports are among the
component's exports, in order), `typeOfX_ofAst` (on base components `typeOfX` is `typeOf`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync

/-- The names of the top-level imports of a component's sections, in order. -/
def importNamesOf (ss : List Section) : List String :=
  ss.flatMap fun | .imports xs => xs.map (·.name.name) | _ => []

/-- The names of the top-level exports of a component's sections, in order. -/
def exportNamesOf (ss : List Section) : List String :=
  ss.flatMap fun | .exports xs => xs.map (·.name.name) | _ => []

/-- The names of the top-level imports of a component, in order. -/
def importNames (c : Ast) : List String := importNamesOf c.sections

/-- The names of the top-level exports of a component, in order. -/
def exportNames (c : Ast) : List String := exportNamesOf c.sections

/-- **The type of an extended component**: `typeOf` of its erasure. -/
def typeOfX (c : AstX) : Except String (PkgType × Bridge.NomTable) := typeOf c.erase

/-- **A package from its binary**, with the async built-ins: `Bridge.decodePkg` when it
applies, else `typeOfX` of the extended parse. -/
def decodeAnyX (b : ByteArray) : Except String (PkgType × Bridge.NomTable) :=
  match Bridge.decodePkg b with
  | .ok r => .ok r
  | .error e => match parseX b with
    | .error e' => .error s!"{e}; extended parse: {reprStr e'}"
    | .ok c => match typeOfX c with
      | .ok r => .ok r
      | .error e' => .error s!"{e}; by inference: {e'}"

end Silmaril.Wasm.Wac.TypeOf

namespace Silmaril.Wasm.Wac.TargetsX

open Silmaril.Wasm.Wac.TargetsT

/-- **`wasm-wac targets` on binaries with async built-ins**: as `TargetsT.check`, with the
component's type from `decodeAnyX`. -/
def check (comp wit : ByteArray) (w : Option String) : Except String (Bool × List String) := do
  let (p, _) ← TypeOf.decodeAnyX comp
  let (q, _) ← Bridge.decodePkg wit
  let (wi, we) ← worldOf q.defs w
  pure (fitsB p.imports p.exports wi we, misfits p.imports p.exports wi we)

end Silmaril.Wasm.Wac.TargetsX
