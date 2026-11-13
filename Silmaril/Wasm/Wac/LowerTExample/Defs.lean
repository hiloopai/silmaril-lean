module

public import Silmaril.Wasm.Wac.LowerT.Defs
public import Silmaril.Wasm.Wac.Example.Defs

/-!
# WAC: the typed lowering on the worked composition

The worked composition of `Silmaril.Wasm.Wac.Example` declares the import
`host: instance { print: func() }`, while its packages import `host#print` at the type
`() -> u32` (`Example.ft`). The untyped `Lower.graph` accepts it (the declared import
takes the packages' type); the typed lowering rejects it. Its instance type also
refers to the type `0` of the component, which inside an instance type is the
instance type's own (empty) type space; `wac` defines the function type inside the
instance type. `astT` is the composition in that layout, with
`print: func() -> u32`; it lowers to `Example.expected`, with the import's type read
from the WAT.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.LowerTExample

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary

/-- The worked composition with `print` of the result type `r`. -/
def astWith (r : Option Silmaril.Wasm.Component.Binary.ValType) : Binary.Ast := .mk [
  .types [.instance [.type (.func ⟨[], r, false⟩),
    .export ⟨"print", .plain0⟩ (.func 0)]],
  .imports [⟨⟨"host", .plain0⟩, .instance 0⟩],
  .component (.mk []), .component (.mk []),
  .instances [.instantiate 0 [("host", ⟨.instance, 0⟩)],
    .instantiate 1 [("greeter", ⟨.instance, 1⟩), ("host", ⟨.instance, 0⟩)]],
  .aliases [⟨.func, .export 2 "run"⟩],
  .exports [⟨⟨"run", .plain0⟩, ⟨.func, 0⟩, none⟩]]

/-- `print: func() -> u32`. -/
def astT : Binary.Ast := astWith (some (.prim .u32))

/-- `print: func()`, in the layout of `wac`: the argument types do not match. -/
def astUnit : Binary.Ast := astWith none

end Silmaril.Wasm.Wac.LowerTExample
