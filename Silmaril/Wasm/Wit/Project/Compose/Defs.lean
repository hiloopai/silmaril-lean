module

public import Silmaril.Wasm.Wit.Project.Infer.Defs

/-!
# The projection and composition: definitions

The component-level composition operations of WAC-style compositions, on the binary
AST: a composition is built by appending items to a component (`extendC`):

* `instantiateC c k args`: instantiate component `k` with the arguments `args`;
* `aliasC c sort i n`: alias export `n` of instance `i`, of sort `sort`;
* `exportC c e`: export an item (with or without type ascription).

`projState c` is the state of the projection with inference after the items of `c`;
`projectI c` reads the world from it. The theorems
(`Silmaril.Wasm.Wit.Project.Compose.Thms`) say how each operation changes the world.

The composition operations of the component IR (`Silmaril.Wasm.Component.Comp`:
flattening, fusion, the optimiser) are covered by `Silmaril.Wasm.Wit.Project.IR`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary

/-- Append items to a component. -/
def extendC (c : Ast) (secs : List Section) : Ast := .mk (c.sections ++ secs)

/-- Instantiate component `k` with the arguments `args`. -/
def instantiateC (c : Ast) (k : Nat) (args : List (String × SortIdx)) : Ast :=
  extendC c [.instances [.instantiate k args]]

/-- Alias export `n` of instance `i`. -/
def aliasC (c : Ast) (sort : ItemSort) (i : Nat) (n : String) : Ast :=
  extendC c [.aliases [⟨sort, .export i n⟩]]

/-- Silmaril.Wasm.Component.Binary.Export an item. -/
def exportC (c : Ast) (e : Silmaril.Wasm.Component.Binary.Export) : Ast := extendC c [.exports [e]]

/-- The state of the projection with inference after the items of `c`. -/
def projState (c : Ast) : Option IState := replayI {} (c.sections.flatMap splitSection)

end Silmaril.Wasm.Wit.Project
