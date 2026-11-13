module

public import Silmaril.Wasm.Wac.World.Defs
public import Silmaril.Wasm.Wac.Example.Defs

/-!
# WAC: typed targets checking on the worked composition

The composition of `Silmaril.Wasm.Wac.Example` (`greeter` and `app` sharing the import
`host`, exporting `app.run`), typed by the kinds of its packages, checked against
three target worlds given in binary form (as `Targets.worldOfPackage` returns them):

* `world` imports the instance `host { print: func() }` and exports `run: func()`:
  satisfied;
* `worldPrintArg`: `print` takes a parameter. The names and sorts are those of
  `world`, so the untyped `Targets.Fits` holds, but the typed check fails;
* `worldMore` also exports `stop: func()`: neither check holds.

Theorems in `Silmaril.Wasm.Wac.WorldExample.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WorldExample

open Silmaril.Wasm.Component.Binary

/-- `func()`. -/
def s0 : Wit.Binary.Sig := ⟨false, [], none⟩

/-- The instance `host`. -/
def hostK : Kind := .inst none [("print", .func s0)]

/-- The packages: `example:greeter` (index 0) and `example:app` (index 1). -/
def K : Nat → Kind
  | 0 => .comp none [("host", hostK)] [("greet", .func s0)]
  | 1 => .comp none [("greeter", .inst none [("greet", .func s0)]), ("host", hostK)]
      [("run", .func s0)]
  | _ => .comp none [] []

/-- The kinds of the composition's imports. -/
def imps : Externs := [("host", hostK)]

/-- A world `import host: interface { print: func(); } export run: func();` with the
type of `print` given. -/
def worldWith (print : Silmaril.Wasm.Component.Binary.FuncType) (more : List ComponentDecl) : Wit.Project.WorldType :=
  [.inst (.type (.instance [.type (.func print), .export ⟨"print", .plain0⟩ (.func 0)])),
   .import ⟨"host", .plain0⟩ (.instance 0),
   .inst (.type (.func ⟨[], none, false⟩)),
   .inst (.export ⟨"run", .plain0⟩ (.func 1))] ++ more

def world : Wit.Project.WorldType := worldWith ⟨[], none, false⟩ []

def worldPrintArg : Wit.Project.WorldType := worldWith ⟨[("x", .prim .u32)], none, false⟩ []

def worldMore : Wit.Project.WorldType :=
  worldWith ⟨[], none, false⟩ [.inst (.export ⟨"stop", .plain0⟩ (.func 1))]

end Silmaril.Wasm.Wac.WorldExample
