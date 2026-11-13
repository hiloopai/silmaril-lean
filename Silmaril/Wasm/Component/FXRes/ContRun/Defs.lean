module

public import Silmaril.Wasm.Component.FXRes.ContComp.Defs
public import Silmaril.Wasm.Resource.CompToy.Defs

/-!
# Running the `cont` component over the WasmFX engine with a continuation table: definitions

The component `contComp` (`Silmaril.Wasm.Component.FXRes.ContComp`) defines the resource type
`cont`, whose representation is the index of a continuation in the continuation table of the
engine store of `fxCE P`. This module names the configuration the reference component machine
reaches when it instantiates `contComp` from the empty store:

* `contInst P`: the configuration after instantiating `contComp` over `fxCE P` with the host
  state `()`, computed by the silent evaluator `silentRun` (`Silmaril.Wasm.Resource.CompToy`) of
  the instantiation program from the empty store. It is irreducible for the elaborator; its
  fields are read off by kernel evaluation (`Silmaril.Proofs.Wasm.Component.FXRes.ContRun`);
* `contEs`: the function exports, `make` and `run`, component functions `0` and `1`;
* `contStart P`: the configuration after the instantiation host event.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContRun

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.FXRes.ContEngine Silmaril.Wasm.Component.FXRes.ContComp
open Silmaril.Wasm.Resource.CompToy (silentRun)
open Silmaril.Wasm.Numerics (Profile)

variable (P : Profile)

/-- The function exports of `contComp`: `make` and `run`, component functions `0` and `1`. -/
def contEs : List (String × FuncId) := [("make", ⟨0⟩), ("run", ⟨1⟩)]

/-- **The configuration after instantiating `contComp`** over `fxCE P`, computed by `silentRun`
of the instantiation program from the empty store (host in control). -/
@[irreducible] noncomputable def contInst : Config (fxCE P) Unit :=
  match silentRun (instantiateProg (E := fxCE P) contComp []) (initConfig ()) with
  | some (_, _, m) => m
  | none => initConfig ()

/-- The configuration after the instantiation host event. -/
noncomputable def contStart : Config (fxCE P) Unit :=
  { (initConfig () : Config (fxCE P) Unit) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg contComp []))] }

end Silmaril.Wasm.Component.FXRes.ContRun
