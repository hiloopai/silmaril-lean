module

public import Silmaril.Wasm.Component.FXEngine.Defs

/-!
# A module with an FX function: definitions

A concrete IR module over the WasmFX engine (`fxXG P`) whose only export is an FX function that
uses stack switching.

* `gMod`: a Core 3.0 module with one function `g : [] → [i32]` returning `42` and no exports;
* `runDecl`: the FX function `run : [] → [i32]` with body
  `ref.func 0; cont.new 0; resume 0` (make a continuation of `g` and resume it, with no handler
  clauses);
* `exMod`: the FX module (`gMod` and `run`), `exIface` its interface `run : [] → [i32]`, and
  `exNum` the IR module over the FX engine;
* `exS`, `exI`: its instantiated store and instance over the empty store (computed by
  `prepareFX?`); `exS₁` the store after the Core part, before `run` is allocated.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.FXEngine

/-- The Core part: one function `g : [] → [i32]` returning `42`. -/
def gMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 42]⟩]

/-- The FX function `run : [] → [i32]`: `ref.func 0; cont.new 0; resume 0`. -/
def runDecl : FXDecl :=
  { name := "run", type := ⟨[], [.int .i32]⟩, locals := [],
    body := [.core (.refFunc ⟨0⟩), .fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [])] }

/-- The FX module. -/
def exMod : ModuleFX := ⟨gMod, [runDecl]⟩

/-- Its interface: `run : [] → [i32]`. -/
def exIface : CoreIface := [("run", ⟨[], [.int .i32]⟩)]

/-- The IR module over the FX engine. -/
def exNum : FXNumModule := ⟨exMod, exIface⟩

/-- Instantiation over the empty store. -/
def exPrep : Option (Store (FXCode Nat) × InstFX × Option Nat) := prepareFX? {} exMod []

/-- The instantiated store. -/
def exS : Store (FXCode Nat) := (exPrep.map (·.1)).getD {}

/-- The instance. -/
def exI : InstFX := (exPrep.map (·.2.1)).getD ⟨{}, []⟩

/-- The store after the Core part. -/
def exS₁ : Store (FXCode Nat) :=
  ((Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store (FXCode Nat)) gMod []).map
    (·.1)).getD {}

/-- The FX function `run` in the instance. -/
abbrev runF : Silmaril.Wasm.Models.FX.FuncFX := runDecl.func exI.core

/-- The value `42 : i32`. -/
abbrev v42 : Execution.Core.Val := .num ⟨.int .i32, 42⟩

/-- The flat value `42 : i32`. -/
abbrev y42 : Flat := ⟨.int .i32, 42⟩

end Silmaril.Wasm.Component.FXExample
