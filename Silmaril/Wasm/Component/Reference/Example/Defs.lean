module

public import Silmaril.Wasm.Component.Reference.Defs

/-!
# Example: the Core 3.0 adder component

The adder component (Explainer.md, "Canonical ABI") with its core module written as a
WebAssembly 3.0 module, and the specification embedder over the concrete Core 3.0 engine
`core3 neverFail` with its interpreter `core3Exec neverFail`:

```wat
(component
  (core module $M
    (type (func (param i32 i32) (result i32)))
    (func (export "add") (type 0) local.get 0 local.get 1 i32.add))
  (core instance $m (instantiate $M))
  (func $add (param "a" u32) (param "b" u32) (result u32)
    (canon lift (core func $m "add")))
  (export "add" (func $add)))
```
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.Core3Adder

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- `(type (func (param i32 i32) (result i32))) (func (export "add") (type 0) local.get 0
local.get 1 i32.add)`, the function type a singleton final recursion group. -/
def addCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add]⟩]
  exports := [⟨"add", .func ⟨0⟩⟩]

/-- The adder component over `addCore3`. -/
def adder3 : Core3Component := Syntax.BuilderExamples.adder addCore3

/-- Its type: no imports, the single export `add : func(a: u32, b: u32) -> u32`. -/
def adder3Type : ComponentType := ⟨[], [], [], [("add", .func Validation.DefsTests.adderFunc)]⟩

/-- A Boolean test for `adder3Type` (`ComponentType` has no `DecidableEq`). -/
def isAdder3Type : Except Validation.ValidationError ComponentType → Bool
  | .ok ⟨[], [], [], [(n, .func ft)]⟩ =>
    n == "add" && decide (ft = Validation.DefsTests.adderFunc)
  | _ => false

/-- No host waitable is ever ready. -/
def noReady : HostReady Unit := fun _ _ => false

/-- The specification embedder over `core3 neverFail` without host functions. -/
def emb : Embedder (core3 Silmaril.Wasm.SingleThreaded.neverFail) Unit :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := noReady, host := HostImpl.none }

/-- The deterministic first-alternative oracle. -/
abbrev first : Oracle (core3 Silmaril.Wasm.SingleThreaded.neverFail) := Oracle.first

/-- Instantiation, then the call of `"add"` on `[u32 3, u32 4]`, summarised. -/
def runSummary : Option (Machine.Outcome × Option (Option (List Val))) :=
  (emb.instantiateRun first 400 adder3 [] (initConfig ())).bind fun (r, _, es) =>
    (es.lookup "add").bind fun f =>
      (emb.callTop first 400 ⟨0⟩ f [Value.Val.u32 3, Value.Val.u32 4] r.config).map
        fun r' => (r'.outcome, r'.config.result? ⟨0⟩)

end Silmaril.Wasm.Component.Reference.Core3Adder
