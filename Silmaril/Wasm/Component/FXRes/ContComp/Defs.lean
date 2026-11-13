module

public import Silmaril.Wasm.Component.FXRes.ContEngine.Defs
public import Silmaril.Wasm.Spec.Component.RefMulti.Defs
public import Silmaril.Wasm.Models.FXAsyncFX.Defs

/-!
# `cont` as a resource type of a component over the WasmFX engine with a continuation table

A component that exposes continuations through the Component Model: it defines a resource type
`cont` whose representation is an `i32`, **the index of the continuation in the continuation
table of the engine store** of `fxCE P` (`Silmaril.Wasm.Component.FXRes.ContEngine`), and exports

* `make() -> own<cont>`: `ref.func g; cont.new; call $cont_new; call $resource.new`: a
  continuation of the Core function `g` (which returns `42`) is created in the thread's store,
  moved into the engine's table by the built-in `new` (a host call of the FX thread), and its
  table index becomes the representation of a fresh `own<cont>` handle;
* `run(own<cont>) -> u32`: `local.get 0; call $resource.rep; call $cont_take; resume;
  local.get 0; call $resource.drop`: the handle's representation names the table entry, the
  built-in `take` moves the continuation into the store of the calling thread (another export
  call than the one that made it), it is resumed, and the handle is dropped (`cont` has no
  destructor).

* `contCore`, `contFxs`, `contModule`: the core module (imports `res.new`, `res.rep`,
  `res.drop`; the Core function `g`) and its FX functions `make`, `run`. In the FX function
  index space the Core functions come first (`new 0`, `rep 1`, `drop 2`, `g 3`), then the FX
  functions (`make 4`, `run 5`), then the continuation built-ins (`new 6`, `take 7`,
  `drop 8`, `ContEngine.prepareC?`).
* `contComp`: the component; `Xc`, `contProg`: its interface and the reference program run by
  the reference component machine over `fxCE P`.

Not done: validation of the component (the reference validator `check?` is stated for Core 3.0
modules, and `StepFX'` code is untyped) and concrete machine runs of its exports.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContComp

open Silmaril.Wasm Silmaril.Wasm.Component
open Silmaril.Wasm.Models.FX (InstrFX FXInstr)
open Silmaril.Wasm.Models.FXAsyncFX (ix)
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Numerics (Profile)

/-- The core function types: `[i32] → [i32]` (`res.new`, `res.rep`, `run`), `[i32] → []`
(`res.drop`), `[] → [i32]` (`g`, `make`). -/
def contTypes : List Silmaril.Wasm.RecType :=
  [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]

/-- The Core part: the resource built-ins as imports, and `g` returning `42`. -/
def contCore : Silmaril.Wasm.Module where
  types := contTypes
  imports := [⟨"res", "new", .func ⟨0⟩⟩, ⟨"res", "rep", .func ⟨0⟩⟩, ⟨"res", "drop", .func ⟨1⟩⟩]
  funcs := [⟨⟨2⟩, [], [.intConst .i32 42]⟩]

/-- `make`: a continuation of `g`, moved into the engine's table, as an `own<cont>` handle. -/
def makeBody : List InstrFX :=
  [.core (.refFunc (ix 3)), .fx (.contNew (ix 2)), .core (.call (ix 6)), .core (.call (ix 0))]

/-- `run`: take the continuation of the handle's representation, resume it, drop the handle. -/
def runBody : List InstrFX :=
  [.core (.localGet (ix 0)), .core (.call (ix 1)), .core (.call (ix 7)),
    .fx (.resume (ix 2) []), .core (.localGet (ix 0)), .core (.call (ix 2))]

/-- The FX functions. -/
def contFxs : List FXDecl :=
  [⟨"make", ⟨[], [.i32]⟩, [], makeBody⟩, ⟨"run", ⟨[.i32], [.i32]⟩, [], runBody⟩]

/-- The FX module. -/
def contModule : ModuleFX := ⟨contCore, contFxs⟩

/-- **The component defining the resource type `cont`.** -/
def contComp : Silmaril.Wasm.Component.Reference.CompAst ModuleFX :=
  [ .type (.resource .i32 none)
  , .export_ { name := "cont" } ⟨.type, 0⟩ none
  , .canon (.builtin (.resourceNew 0))
  , .canon (.builtin (.resourceRep 0))
  , .canon (.builtin (.resourceDrop 0))
  , .coreModule contModule
  , .coreInstance (.exports [("new", ⟨.func, 0⟩), ("rep", ⟨.func, 1⟩), ("drop", ⟨.func, 2⟩)])
  , .coreInstance (.instantiate 0 [("res", 0)])
  , .alias (.coreExport 1 "make" .func)
  , .alias (.coreExport 1 "run" .func)
  , .type (.val (.own 1))
  , .type (.func { params := [], result := some (.idx 2) })
  , .type (.func { params := [("k", .idx 2)], result := some (.prim .u32) })
  , .canon (.lift 3 [] 3)
  , .export_ { name := "make" } ⟨.func, 0⟩ none
  , .canon (.lift 4 [] 4)
  , .export_ { name := "run" } ⟨.func, 2⟩ none ]

/-- The interface: `make() -> own<cont>`, `run(own<cont>) -> u32`. -/
def Xc : CIface := ⟨[], [⟨[], [.own 0]⟩, ⟨[.own 0], [.prim .u32]⟩]⟩

/-- The export names. -/
def contNames : Xc.Exp → String
  | ⟨0, _⟩ => "make"
  | _ => "run"

/-- **The component as a reference program over `fxCE P`.** -/
def contProg (P : Profile) : RefProg (fxCE P) Xc := ⟨contComp, [], contNames⟩

end Silmaril.Wasm.Component.FXRes.ContComp
