module

public import Silmaril.Wasm.Component.FXTyped.Defs
public import Silmaril.Wasm.Component.FXSuspend.Defs
public import Silmaril.Wasm.Component.Reference.Litmus.Defs

/-!
# Components with FX functions for `SimpleFX.Typed`: definitions

Three concrete `SimpleFX` components over the WasmFX engine with suspension `fxEV P`.

* `susC`: **code that suspends**. The Core part is `FXSuspend.tMod` (one function type and one
  tag, no functions, no exports). The FX functions are `sus : [] → [i32]` (`suspend 0;
  i32.const 7`, as in `FXSuspend`) and `run : [] → []`, which is `FXSuspend.runDecl`'s body
  followed by `drop`: it makes a continuation of `sus`, resumes it under a handler for tag 0,
  `sus` suspends, the handler branches out with the continuation, and the second `resume` runs
  `sus` to its end; `run` drops the `7`. The lifted export is `run: func()`.
* `mixC`: **a Core export and an FX export**. The Core part is the litmus adder
  (`Litmus.binMod .add`, in the split fragment), lifted as `add: func(u32, u32) -> u32`; the FX
  function `go : [] → []` makes a continuation of the adder, resumes it on `1, 2` and drops the
  result, lifted as `go: func()`.
* `badC`: **an ill-typed FX function**. `bad : [] → [i32]` has the body `i64.const 0`. `StepFX'`
  checks only the arity of returned values, so it returns an `i64`; lifted as
  `bad: func() -> u32`.

`tStore`, `tInst`: the store and the scalar instance of `tMod`, instantiated against no imports.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXTypedEx

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.FXRefV
open Silmaril.Wasm.Component.FXSuspend (tMod susDecl runDecl)

/-- The Core part of `susC` and `badC`: `tMod`, with no function exports. -/
def tNum : NumModule := ⟨tMod, []⟩

/-- The store of the instance of `tMod`. -/
def tStore : Store Nat :=
  match instantiateOnce? (Silmaril.Wasm.Game.importStore []) tMod [] with
  | some (s, _, _) => s
  | none => {}

/-- The scalar instance of `tMod`. -/
def tInst : Silmaril.Wasm.Game.ScalarInstance where
  imports := []
  exports := []
  addrs := []
  store := tStore

/-! ## Code that suspends -/

/-- `run : [] → []`: `FXSuspend.runDecl`'s body, then `drop`. -/
def run0Decl : FXDecl :=
  { name := "run", type := ⟨[], []⟩, locals := [], body := runDecl.body ++ [.core .drop] }

/-- **A component whose FX code suspends.** -/
def susC : SimpleFX := ⟨tNum, [susDecl, run0Decl], [⟨"run", ⟨[], []⟩, 1⟩]⟩

/-! ## A Core export and an FX export -/

/-- `go : [] → []`: `i32.const 1; i32.const 2; ref.func 0; cont.new 0; resume 0; drop`. -/
def goDecl : FXDecl :=
  { name := "go", type := ⟨[], []⟩, locals := [],
    body := [.core (.intConst .i32 1), .core (.intConst .i32 2), .core (.refFunc ⟨0⟩),
      .fx (.contNew ⟨0⟩), .fx (.resume ⟨0⟩ []), .core .drop] }

/-- **The adder and an FX function that resumes it.** -/
def mixC : SimpleFX :=
  ⟨Litmus.binMod .add, [goDecl], [⟨"add", ⟨[.u32, .u32], [.u32]⟩, 0⟩, ⟨"go", ⟨[], []⟩, 1⟩]⟩

/-! ## An ill-typed FX function -/

/-- `bad : [] → [i32]` with the body `i64.const 0`. -/
def badDecl : FXDecl :=
  { name := "bad", type := ⟨[], [.int .i32]⟩, locals := [], body := [.core (.intConst .i64 0)] }

/-- **A component whose FX function returns a value of the wrong type.** -/
def badC : SimpleFX := ⟨tNum, [badDecl], [⟨"bad", ⟨[], [.u32]⟩, 0⟩]⟩

end Silmaril.Wasm.Component.FXTypedEx
