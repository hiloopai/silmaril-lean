module

public import Silmaril.Wasm.Component.FXEngineV.Defs

/-!
# A module whose code suspends: definitions

A concrete IR module with two FX functions, for the WasmFX engine with suspension `fxEV P`
(`Silmaril.Wasm.Component.FXEngineV`).

* `tMod`: the Core part, one function type `[] → []` and one tag of that type, no functions;
* `susDecl`: the FX function `sus : [] → [i32]` (function index 0) with body
  `suspend 0; i32.const 7`;
* `runDecl`: the FX function `run : [] → [i32]` (function index 1) with body
  ```
  block (result i32)
    ref.func 0; cont.new 0; resume 0 (on 0 0); unreachable
  end
  resume 0
  ```
  It makes a continuation of `sus` and resumes it under a handler for tag 0 whose clause
  branches out of the block; `sus` suspends at once, so the block ends with the captured
  continuation, which `run` resumes (with no handler) to its end, returning `7`.
* `exMod`, `exIface` (`run : [] → [i32]`), `exNum`; `exS`, `exI` its store and instance over
  the empty store (computed by `prepareFXV?`).

The block's result type `i32` stands for the continuation type (`StepFX'` is untyped and only
uses the arity).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXSuspend

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV

/-- The Core part: the type `[] → []` and one tag of that type. -/
def tMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  tags := [⟨0⟩]

/-- `sus : [] → [i32]`: `suspend 0; i32.const 7`. -/
def susDecl : FXDecl :=
  { name := "sus", type := ⟨[], [.int .i32]⟩, locals := [],
    body := [.fx (.suspend ⟨0⟩), .core (.intConst .i32 7)] }

/-- The block of `run`. -/
def blockBody : List Silmaril.Wasm.Models.FX.InstrFX :=
  [.core (.refFunc ⟨0⟩), .fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ [.onLabel ⟨0⟩ ⟨0⟩]),
    .core .unreachable]

/-- `run : [] → [i32]`. -/
def runDecl : FXDecl :=
  { name := "run", type := ⟨[], [.int .i32]⟩, locals := [],
    body := [.block (.value (.num (.int .i32))) blockBody, .fx (.resume ⟨0⟩ [])] }

/-- The FX module. -/
def exMod : ModuleFX := ⟨tMod, [susDecl, runDecl]⟩

/-- Its interface: `run : [] → [i32]`. -/
def exIface : CoreIface := [("run", ⟨[], [.int .i32]⟩)]

/-- The IR module. -/
def exNum : FXNumModule := ⟨exMod, exIface⟩

/-- Instantiation over the empty store. -/
def exPrep : Option (Store (FXCode Nat) × InstFX × Option Nat) := prepareFXV? {} exMod []

/-- The instantiated store. -/
def exS : Store (FXCode Nat) := (exPrep.map (·.1)).getD {}

/-- The instance. -/
def exI : InstFX := (exPrep.map (·.2.1)).getD ⟨{}, []⟩

/-- The instance seen by the FX functions (`sus` at address 0, `run` at address 1). -/
abbrev exI' : ModuleInst := fxInst exI.core 0 2

/-- The FX function `sus`. -/
abbrev susF : Silmaril.Wasm.Models.FX.FuncFX := susDecl.func exI'

/-- The FX function `run`. -/
abbrev runF : Silmaril.Wasm.Models.FX.FuncFX := runDecl.func exI'

/-- The value `7 : i32`. -/
abbrev v7 : Execution.Core.Val := .num ⟨.int .i32, 7⟩

/-- The flat value `7 : i32`. -/
abbrev y7 : Flat := ⟨.int .i32, 7⟩

end Silmaril.Wasm.Component.FXSuspend
