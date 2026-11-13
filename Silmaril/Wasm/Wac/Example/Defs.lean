module

public import Silmaril.Wasm.Wac.Lower.Defs
public import Silmaril.Wasm.Wac.Seq.Defs
public import Silmaril.Wasm.Component.Wat.Defs

/-!
# WAC: a worked composition

The composition (WAC)

```
package example:composition;
let greeter = new example:greeter { ... };
let app = new example:app { greeter, ... };
export app.run;
```

encoded in the composition profile of component WAT (`text`, the spelling of
`Wat.print`; the packages' definitions are elided: their interfaces are `sigs`). The
theorems of `Silmaril.Wasm.Wac.Example.Thms` check, by kernel evaluation, that the text is read in the profile, that it prints
back, and the composition graph and composed component it lowers to; and promotion
and plugging on graphs.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Example

open Silmaril.Wasm.Component

/-- The composition, in WAT. -/
def text : String :=
  "(component
  (type (func))
  (type (instance (export \"print\" (func (type 0)))))
  (import \"host\" (instance (type 1)))
  (component)
  (component)
  (instance (instantiate 0 (with \"host\" (instance 0))))
  (instance (instantiate 1 (with \"greeter\" (instance 1)) (with \"host\" (instance 0))))
  (alias export 2 \"run\" (func))
  (export \"run\" (func 0)))\n"

/-- The composition, as abstract syntax. -/
def ast : Binary.Ast := .mk [
  .types [.func ⟨[], none, false⟩, .instance [.export ⟨"print", .plain0⟩ (.func 0)]],
  .imports [⟨⟨"host", .plain0⟩, .instance 1⟩],
  .component (.mk []), .component (.mk []),
  .instances [.instantiate 0 [("host", ⟨.instance, 0⟩)],
    .instantiate 1 [("greeter", ⟨.instance, 1⟩), ("host", ⟨.instance, 0⟩)]],
  .aliases [⟨.func, .export 2 "run"⟩],
  .exports [⟨⟨"run", .plain0⟩, ⟨.func, 0⟩, none⟩]]

/-- A function type `() -> u32`. -/
def ft : FuncTy := ⟨[], [.u32]⟩

/-- `example:greeter` imports `host#print` and exports `greet`; `example:app` imports
`greeter#greet` and `host#print` and exports `run`. -/
def pkgs : Nat → Comp Unit
  | 0 => .mk [("host#print", ft)] [] [⟨"greet", ft, Impl.trap⟩]
  | 1 => .mk [("greeter#greet", ft), ("host#print", ft)] [] [⟨"run", ft, Impl.trap⟩]
  | _ => .mk [] [] []

def sigs (k : Nat) : PkgSig := sigOf (pkgs k)

/-- The expected composition graph. -/
def expected : Graph where
  imports := [("host#print", ft)]
  nodes := [⟨0, [("host#print", .imp "host#print")]⟩,
    ⟨1, [("greeter#greet", .out 0 "greet"), ("host#print", .imp "host#print")]⟩]
  exports := [("run", .out 1 "run")]

def lowered : Option Graph := (Lower.graph sigs ast).toOption


/-- The composed component: one import, two nested instances wired in the environment
`[host#print, greet, run]`, and the export `run`. -/
def composed : Comp Unit := expected.toComp pkgs


/-- Promotion: the same composition without arguments; the imports `host#print` of both
instances are promoted and merged, `greeter#greet` of `app` too. -/
def implicit : Graph where
  nodes := [⟨0, []⟩, ⟨1, [("greeter#greet", .out 0 "greet")]⟩]
  exports := [("run", .out 1 "run")]


/-- Plugging: `greeter` alone, plugged into `app` alone (whose import `greeter#greet`
is satisfied by the export of `greeter` of that name). -/
def greeterG : Graph where
  nodes := [⟨0, []⟩]
  exports := [("greeter#greet", .out 0 "greet")]

def appG : Graph where
  nodes := [⟨1, []⟩]
  exports := [("run", .out 0 "run")]


end Silmaril.Wasm.Wac.Example
