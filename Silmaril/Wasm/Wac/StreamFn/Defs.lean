module

public import Silmaril.Wasm.Wac.StreamPkg.Defs

/-!
# WAC: stream packages read as the functions they export

`StreamPkg.lowerXf κ` reads a stream transformer package as the stage `Streams.Alg.stage k`: a
component that *imports* `src` and *exports* `src`, and pulls its whole input from its import.
That is the batch view of a pipeline plugged by imports. The packages `wasm-streams-gen` and
`wasm-jco new` build, and that `tools/wac/tests/streams.sh` composes, have a different shape:
they import nothing and export one function `tI: async func(in: stream<u8>) -> stream<u8>`,
which a driver package imports by that name and calls (`let sI = new test:K-tI {}; let d = new
test:drv { tI: sI["tI"] }`). Under `lowerXf` the export is named `src`, so a driver's argument
`sI["tI"]` resolves to no export of the stage and the reading of such a composition traps.

This module gives the reading that keeps the shape and the name:

* `FCode`: a core module exporting one function `name`, implementing the code `code`;
* `fnComp n k`: the component with no imports and one export `n`, the function of `k`;
* `callSem`: its semantics: a call with the stream as a list of values answers `k.run` of it
  (the whole output; the batch view of one call);
* `fnShape a`: the shape of a stream package as `wasm-jco new` and wit-component build it:
  its first (main) core module, its only function export, no component imports;
* `lowerFn κ a`: the package read from its AST as `fnComp s.name k`, where `fnShape a = some s`
  and `κ s.core = some k`;
* `readFn κ other`: `lowerFn κ`, and `other` for every package that is not a stream package
  (a driver, for instance; its reading is the caller's choice);
* `binShapes b`: the shapes of the packages embedded in a binary, as `Emit.binPkgs` reads them.

`κ` is the same parameter as in `StreamPkg`: which code a core module implements. Theorems in
`Silmaril.Wasm.Wac.StreamFn.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamFn

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Games
open Silmaril.Wasm.Component.Streams.Alg Silmaril.Wasm.Wac.StreamPkg

/-- A core module exporting the function `name`, implementing the code `code`. -/
structure FCode where
  /-- The name of its only export. -/
  name : String
  /-- The code it implements. -/
  code : TCode

/-- An `FCode` imports nothing and exports its one function. -/
instance : CoreModule FCode := ⟨fun _ => [], fun m => [(m.name, ⟨[], []⟩)]⟩

/-- **A stream package as a function**: no imports, the export `n` is the function of `k`. -/
def fnComp (n : String) (k : TCode) : Comp FCode :=
  .mk [] [.core ⟨n, k⟩ []] [⟨n, ftS, Impl.fwd 0⟩]

/-- The answer to a call: `f` of the list of values passed. -/
def callAns (f : List Val → List Val) : Payload → Option Payload
  | .vals xs => some (.vals (f xs))
  | .flat _ => none

/-- **The call semantics**: a call answers the whole output of the code. -/
def callSem : CoreSem FCode where
  sem m := Strategy.ofHandler fun q => .pure (callAns m.code.run q.2)

/-- **The shape of a stream package as the tools build it**: its first core module (the main
module; `wasm-jco new` and wit-component put their shim and fixup modules after it), its only
function export, and no component imports. `StreamPkg.xfShape` asks for exactly one core module,
which no component built by `wasm-jco new` or wit-component has (both add a shim and a fixup
module for the async built-ins), so `lowerXf` reads none of them. -/
def fnShape (a : AstX) : Option XfShape :=
  match coreModules a, funcExports a, importNames a with
  | m :: _, [n], [] => some ⟨m, n⟩
  | _, _, _ => none

/-- **Read a stream package as the function it exports.** -/
def lowerFn (κ : Interp) (a : AstX) : Option (Comp FCode) :=
  (fnShape a).bind fun s => (κ s.core).map (fnComp s.name)

/-- Stream packages by `lowerFn κ`, every other package by `other`. -/
def readFn (κ : Interp) (other : AstX → Option (Comp FCode)) (a : AstX) : Option (Comp FCode) :=
  match lowerFn κ a with
  | some c => some c
  | none => other a

/-- **The shapes of the packages embedded in a binary**, in component index order: `some s`
for a stream package (`fnShape`), `none` for any other package or an imported component.
`wasm-wac shapes` prints it, so the tests see which packages `lowerFn κ` reads. -/
def binShapes (b : ByteArray) : Except String (List (Option XfShape)) :=
  match parseX b with
  | .ok a => .ok ((SpliceX.pkgsOf a).map fun o => o.bind fnShape)
  | .error _ => .error "the binary does not parse"

/-- Two tables of packages agree up to the codes' whole outputs, export names kept: the same
names, and each pair of packages is the same AST or two stream packages with the same export
name whose codes have the same whole output. -/
def RunAgreeF (κ : Interp) (tbl tbl' : SpliceX.PkgTableX) : Prop :=
  ∀ n, (tbl.lookup n = tbl'.lookup n) ∨
    ∃ a a' s s' k k', tbl.lookup n = some a ∧ tbl'.lookup n = some a' ∧ fnShape a = some s ∧
      κ s.core = some k ∧ fnShape a' = some s' ∧ κ s'.core = some k' ∧ s.name = s'.name ∧
      k.run = k'.run

end Silmaril.Wasm.Wac.StreamFn
