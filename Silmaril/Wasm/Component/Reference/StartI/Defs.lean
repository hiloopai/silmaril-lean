module

public import Silmaril.Wasm.Component.Reference.Start.Defs

/-!
# Components with imports whose core module has a start function

A `SimpleI` component's module may have a start function. The reference machine runs it during
the core instantiation of `instantiate 0 (with "env" …)`, after the `canon lower` trampolines of
the imports have been allocated, so the start function may call imports (host callouts through
the trampolines). The IR's plays begin with an export question, so they cannot show such calls.
This header states the **hypothesis route**: the start phase makes no import call.

* `ImpModule.noStart`, `SimpleI.noStart`: the module without its start function.
* `ImpModule.IsInstS m I start`: `I` is the instance of `m` (against fresh host functions for its
  imports) **before** its start function runs (`Silmaril.Wasm.Game.IsInstanceStart`), `start` the
  start function's address, with `m`'s import and export types.
* `ImpModule.StartNoCall P m`: **the start phase makes no import call**: no Core 3.0 run of the
  start phase of an instance of `m`, at profile `P` without host functions, reaches a
  host-call redex (`Silmaril.Wasm.SingleThreaded.decompose?`). A semantic condition on Core
  runs, not a syntactic one.
* `ImpModule.StartFails P m`: the start phase of an instance may trap or throw.
* `impSemS P : CoreSem ImpModule`: the union of the instance's strategy (`core3SemAt`) at every
  store the start phase may return at, without host calls, together with the strategy trapping on
  every question when the start phase may fail or there is no instance. Under `StartNoCall` these
  are all the outcomes of the start phase but divergence.
* `SimpleI.InstS c`: as `SimpleI.Inst`, with a start function allowed.

The soundness theorems are in `StartI.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

/-- The module without its start function. -/
def ImpModule.noStart (m : ImpModule) : ImpModule :=
  ⟨{ m.mod with start := none }, m.imports, m.exports⟩

/-- The component with the module without its start function. -/
def SimpleI.noStart (c : SimpleI) : SimpleI := ⟨c.mod.noStart, c.imports, c.exports⟩

/-- `I` is the instance of `m` against fresh host functions for its imports **before its start
function runs**, `start` the start function's address (`none` exactly when `m` has no start
function), with `m`'s import and export types. -/
def ImpModule.IsInstS (m : ImpModule) (I : ScalarInstance) (start : Option Nat) : Prop :=
  (∃ mt, IsInstanceStart m.mod mt I start) ∧ I.imports = m.imports.map (fun p => fnOf p.2) ∧
    I.exports = m.exports.map fun p => fnOf p.2

/-- **The start phase makes no import call**: no Core 3.0 run of the start phase of an instance
of `m` before its start function, at profile `P` and without host functions, reaches a
configuration whose next redex is a call of a host function (an import). -/
def ImpModule.StartNoCall (P : Profile) (m : ImpModule) : Prop :=
  ∀ I start, m.IsInstS I start → ∀ c' : Silmaril.Wasm.Execution.Core.Config Nat,
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (startConfig I.store start) c' →
    Silmaril.Wasm.SingleThreaded.decompose? c'.store c'.code = none

/-- The start phase of an instance of `m` may fail: it traps or throws an uncaught exception,
without host calls. -/
def ImpModule.StartFails (P : Profile) (m : ImpModule) : Prop :=
  ∃ I start, m.IsInstS I start ∧ ∃ (c' : Silmaril.Wasm.Execution.Core.Config Nat)
    (r : Silmaril.Wasm.Execution.Core.Result),
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (startConfig I.store start) c' ∧ c'.code = r.toAdmin ∧
    (r = .trap ∨ ∃ x, r = .throw x)

/-- The numeric instance of `m` given by `I` (for `I` with the import and export types of
`m`). -/
def ImpModule.numAt (m : ImpModule) (I : ScalarInstance)
    (h : I.imports = m.imports.map (fun p => fnOf p.2) ∧
      I.exports = m.exports.map fun p => fnOf p.2) : NumInstance :=
  { inst := I, imports := m.imports, exports := m.exports, imports_eq := h.1,
    exports_eq := h.2 }

/-- The strategies a module with imports and a start function may denote: the instance's
strategy at every store the start phase may return at (without host calls), and the strategy
trapping on every question when the start phase may fail or there is no instance. -/
noncomputable def impStartStrategies (P : Profile) (m : ImpModule) :
    Set (Strategy (CoreIface.sig (CoreModule.imports m)) (CoreIface.sig (CoreModule.exports m))) :=
  {σ | ∃ I start s', ∃ h : m.IsInstS I start,
      StartsTo P Silmaril.Wasm.SingleThreaded.Det.noHost I.store start s' ∧
      σ = core3SemAt P (m.numAt I h.2) s'} ∪
    {σ | σ = trapAll _ _ ∧ ((¬ ∃ I start, m.IsInstS I start) ∨ m.StartFails P)}

/-- **The IR's Core 3.0 semantics of modules with imports and a start function that makes no
import call, at profile `P`**: the union of `impStartStrategies P m`. -/
noncomputable def impSemS (P : Profile) : CoreSem ImpModule where
  sem m := sSup (impStartStrategies P m)

/-- **The module of `c` is wired as `SimpleI.toRef` assumes, with a start function allowed**:
as `SimpleI.Inst`, with an instance before the start function (`ImpModule.IsInstS`). -/
structure SimpleI.InstS (c : SimpleI) : Prop where
  inst : ∃ I start, c.mod.IsInstS I start
  names : funcExportNames c.mod.mod = c.mod.exports.map (·.1)
  importNames : (c.imports.map (·.1)).Nodup
  env : c.mod.mod.imports.map (fun i => (i.moduleName, i.name)) =
    c.imports.map fun p => ("env", p.1)
  importTypes : ∃ mt, Silmaril.Wasm.Validation.validate? c.mod.mod = some mt ∧
    mt.imports = c.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩)

end Silmaril.Wasm.Component.Reference

/-! ## A litmus component with an import and a start function -/

namespace Silmaril.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- A module importing `env.g`, whose start function sets a global that an export reads:
`(type (func (param i32) (result i32))) (type (func)) (type (func (result i32)))
(import "env" "g" (func (type 0))) (global (mut i32) (i32.const 0))
(func $start (type 1) i32.const 42 global.set 0) (func (type 2) global.get 0)
(export "f" (func 0)) (export "get" (func 2)) (start $start)`. -/
def startICore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  imports := [⟨"env", "g", .func ⟨0⟩⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨1⟩, [], [.intConst .i32 42, .globalSet ⟨0⟩]⟩, ⟨⟨2⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩, ⟨"get", .func ⟨2⟩⟩]
  start := some ⟨1⟩

/-- The module with its import and export interfaces. -/
def startIMod : ImpModule :=
  ⟨startICore3, [("g", ⟨[.int .i32], [.int .i32]⟩)],
    [("f", ⟨[.int .i32], [.int .i32]⟩), ("get", ⟨[], [.int .i32]⟩)]⟩

/-- `(import "g" (func (param u32) (result u32)))`, lowered into `startICore3`; exports
`f: func(u32) -> u32` (the import, forwarded) and `get: func() -> u32` (the value the start
function stored). -/
def startIS : SimpleI :=
  ⟨startIMod, [("g", ⟨[.u32], [.u32]⟩)], [⟨"f", ⟨[.u32], [.u32]⟩, 0⟩, ⟨"get", ⟨[], [.u32]⟩, 1⟩]⟩

end Silmaril.Wasm.Component.Reference.Litmus
