module

public import Silmaril.Wasm.Wac.EmitX.Defs
public import Silmaril.Wasm.Component.Streams.Alg.Defs

/-!
# WAC: stream transformer packages lowered to the component IR

A stream transformer package (`name: async func(in: stream<u8>) -> stream<u8>`, the components
`wasm-streams-gen` + `wasm-jco new` build, `docs/projects/wasm-components.md`) is a component with the
async built-ins: one core module, `canon` built-ins (`stream.read`, `task.return`, …), a
`canon lift` with a callback, and one function export; it imports nothing at the component
level. `lowerXf κ a` reads such a component from its extended AST (`AstX`, as embedded in a
composed binary) and lowers it to the component IR of the streams track's batch view
(`Streams.Alg`): the stage component `stage k`, whose core module is the code `k`.

* `xfShape a`: the shape read off the AST: the component's only core module (its bytes) and its
  only function export, and no component imports;
* `Interp`: **which code a core module implements**, `κ : ByteArray → Option TCode`. No
  WebAssembly semantics of core modules calling the async built-ins exists in this library, so
  this is the parameter of the lowering, the one trusted link: for the generated components it
  is the claim that `KM.coreWat` compiles the kernel correctly, which
  `tools/wasm-streams/tests/jco.sh` and `tools/wac/tests/streams.sh` test (not proved);
* `lowerXf κ`: the package lowering (`AstX → Option (Comp TCode)`) that `Emit.binPkgs` uses to
  read the meanings of the packages embedded in a composed binary.

Theorems in `Silmaril.Wasm.Wac.StreamPkg.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamPkg

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.BinaryAsync
open Silmaril.Wasm.Component.Streams.Alg

/-- The core modules defined at the top level of a component, in order. -/
def coreModules (a : AstX) : List ByteArray :=
  a.sections.flatMap fun | .coreModule m => [m] | _ => []

/-- The names of the top-level function exports, in order. -/
def funcExports (a : AstX) : List String :=
  a.sections.flatMap fun
    | .exports xs => (xs.filter fun e => decide (e.item.sort = .func)).map (·.name.name)
    | _ => []

/-- The names of the component-level imports, in order. -/
def importNames (a : AstX) : List String :=
  a.sections.flatMap fun | .imports xs => xs.map (·.name.name) | _ => []

/-- The shape of a stream transformer package. -/
structure XfShape where
  /-- The bytes of its only core module. -/
  core : ByteArray
  /-- The name of its only function export. -/
  name : String

/-- **Read the shape of a stream transformer package**: one core module, one function export,
no component imports. -/
def xfShape (a : AstX) : Option XfShape :=
  match coreModules a, funcExports a, importNames a with
  | [m], [n], [] => some ⟨m, n⟩
  | _, _, _ => none

/-- Which code of the batch view a core module implements. -/
abbrev Interp := ByteArray → Option TCode

/-- **Lower a stream transformer package to the component IR.** -/
def lowerXf (κ : Interp) (a : AstX) : Option (Comp TCode) :=
  (xfShape a).bind fun s => (κ s.core).map stage

/-- The component of a package that is not lowered: the identity stage. -/
def dflt : Comp TCode := stage .id

end Silmaril.Wasm.Wac.StreamPkg
