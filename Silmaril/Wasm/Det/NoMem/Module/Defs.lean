module

public import Silmaril.Wasm.Det.NoMem.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The memory-free, float-free subset: an executable check on modules

* `instPrep m`: silmaril-lean's validation `validate?` and allocation `prepare?` of a Core
  `Module` against fresh host functions for its imports (`Silmaril.Wasm.Game.importStore`, as the
  verifier of `Silmaril.Wasm.Verify` and the instance construction of `Silmaril.Wasm.Game.SpecInst`);
* `instC₀ m`: the specification's instantiation configuration (segment initialisation, then the
  start function: `Config.withStart`), over the allocated store;
* `plainsB`: administrative code made of subset instructions only;
* `moduleB m`: the module validates and allocates, every function of the allocated store is in
  the subset (`storeB`), and so is the instantiation code. Then the instance is deterministic
  modulo traps and imports at every profile, instantiation phase included
  (`Silmaril.Wasm.Det.NoMem.detInst_of_moduleB`);
* `moduleFnB m a`: the per-function check `detFnB` in the allocated store.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- Validation and allocation of a module against fresh host functions for its imports. -/
def instPrep (m : Module) : Option (Config Nat × Option FuncIdx) :=
  (validate? m).bind fun mt =>
    prepare? evalConst? (importStore (CExternType.funcs mt.imports)) m (importAddrs mt)

/-- The instantiation configuration (segment initialisation, then the start function). -/
def instC₀ (m : Module) : Config Nat :=
  match instPrep m with
  | some (c, st) => c.withStart st
  | none => ⟨{}, {}, []⟩

/-- The allocated store of a module (before the instantiation phase runs). -/
def instStore (m : Module) : Store Nat := (instC₀ m).store

/-- Administrative code made of subset instructions only. -/
def plainsB (q : Nat → Bool) (ind : Bool) (fs : List Nat) : List Admin → Bool
  | [] => true
  | .plain i :: l => instrB q ind fs i && plainsB q ind fs l
  | _ :: _ => false

/-- **The module check**: the module validates and allocates, and its allocated functions and
instantiation code are in the subset. -/
def moduleB (m : Module) : Bool :=
  (instPrep m).isSome && storeB (instC₀ m).store &&
    plainsB (fun _ => true) true (instC₀ m).frame.module.funcs (instC₀ m).code

/-- **The per-function check in a module**: `detFnB` in the allocated store. -/
def moduleFnB (m : Module) (a : Nat) : Bool := detFnB (instStore m) a

end Silmaril.Wasm.Det.NoMem
