module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Game.Start.Defs

/-!
# Simple components whose core module has a start function

A `Simple` component's module may have a start function. The reference machine runs it during
core instantiation (`Instantiate.instantiateCore`, `runStart`): the start function is lifted at
`func()` with default options (one more component function, allocated before the exports' lifts)
and called as a synchronous task with a `Caller.sub .start` record. A trap of the start function
is a trap of the instantiation, its divergence a divergence of the instantiation.

* `NumModule.IsInstS m I start`: `I` is the instance of the import-free module `m` before its
  start function runs (`Silmaril.Wasm.Game.IsInstanceStart`, `start` the start function's address),
  with `m`'s export types; `NumModule.IsInst` is the case `start = none`.
* `NumModule.StartFails P m`: the start phase of an instance may trap or throw (closed world, at
  profile `P`).
* `modSemS P : CoreSem NumModule`: the IR's core semantics of modules with a start function. A
  module denotes the union of the strategies of its instance **after** the start function, over
  the stores the start phase may return at (`StartsTo`), together with the strategy trapping on
  every question when the start phase may fail (or the module has no instance).
* `Simple.InstS c`: as `Simple.Inst`, with a start function allowed.

The soundness theorems (`Simple.sound_start`, `Simple.sound_seq_start`) are in `Start.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

/-- The module without its start function. -/
def NumModule.noStart (m : NumModule) : NumModule := ⟨{ m.mod with start := none }, m.exports⟩

/-- `I` is the instance of the import-free module `m` before its start function runs, `start`
the start function's address (`none` exactly when `m` has no start function), with `m`'s export
types. -/
def NumModule.IsInstS (m : NumModule) (I : ScalarInstance) (start : Option Nat) : Prop :=
  (∃ mt, IsInstanceStart m.mod mt I start) ∧ I.imports = [] ∧
    I.exports = m.exports.map fun p => fnOf p.2

/-- The start phase of an instance of `m` may fail: it traps or throws an uncaught exception
(closed world: `m` has no imports). -/
def NumModule.StartFails (P : Profile) (m : NumModule) : Prop :=
  ∃ I start, m.IsInstS I start ∧ ∃ (c' : Silmaril.Wasm.Execution.Core.Config Nat)
    (r : Silmaril.Wasm.Execution.Core.Result),
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (startConfig I.store start) c' ∧ c'.code = r.toAdmin ∧
    (r = .trap ∨ ∃ x, r = .throw x)

/-- The numeric instance of `m` given by `I` (for `I` with the import and export types of
`m`). -/
def NumModule.numAt (m : NumModule) (I : ScalarInstance)
    (h : I.imports = [] ∧ I.exports = m.exports.map fun p => fnOf p.2) : NumInstance :=
  { inst := I, imports := [], exports := m.exports, imports_eq := h.1, exports_eq := h.2 }

/-- `core3Sem P` with the instance's strategy from the store `s` instead of its instantiation
store: `(core3Sem P).sem n = core3SemAt P n n.inst.store`. -/
noncomputable def core3SemAt (P : Profile) (n : NumInstance)
    (s : Silmaril.Wasm.Execution.Core.Store Nat) :
    Strategy (CoreIface.sig (CoreModule.imports n)) (CoreIface.sig (CoreModule.exports n)) :=
  (Strategy.ofHandler (importH n)).comp ((n.inst.strategy P s).comp (Strategy.ofHandler (exportH n)))

/-- The strategies a module with a start function may denote: the instance's strategy at every
store the start phase may return at, and the strategy trapping on every question when the start
phase may fail or there is no instance. -/
noncomputable def startStrategies (P : Profile) (m : NumModule) :
    Set (Strategy (CoreIface.sig (CoreModule.imports m)) (CoreIface.sig (CoreModule.exports m))) :=
  {σ | ∃ I start s', ∃ h : m.IsInstS I start,
      StartsTo P Silmaril.Wasm.SingleThreaded.Det.noHost I.store start s' ∧
      σ = core3SemAt P (m.numAt I h.2) s'} ∪
    {σ | σ = trapAll _ _ ∧ ((¬ ∃ I start, m.IsInstS I start) ∨ m.StartFails P)}

/-- **The IR's Core 3.0 semantics of import-free modules with a start function, at profile
`P`**: the union of `startStrategies P m`. On a module without a start function whose instance
exists, it contains `modSem P` (`modSem_le_modSemS`, `Start.Thms`). -/
noncomputable def modSemS (P : Profile) : CoreSem NumModule where
  sem m := sSup (startStrategies P m)

/-- **The module of `c` is instantiated as `Simple.toRef` assumes, with a start function
allowed**: it has an instance before its start function (`NumModule.IsInstS`), and the names of
`c.mod.exports` are the module's function export names in order. -/
structure Simple.InstS (c : Simple) : Prop where
  inst : ∃ I start, c.mod.IsInstS I start
  names : funcExportNames c.mod.mod = c.mod.exports.map (·.1)

end Silmaril.Wasm.Component.Reference

/-! ## A litmus component with a start function -/

namespace Silmaril.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- A module whose start function sets a global that its export reads:
`(global (mut i32) (i32.const 0)) (func $start i32.const 42 global.set 0)
(func (export "get") (result i32) global.get 0) (start $start)`. -/
def startCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 42, .globalSet ⟨0⟩]⟩, ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"get", .func ⟨1⟩⟩]
  start := some ⟨0⟩

/-- The module with its export interface. -/
def startMod : NumModule := ⟨startCore3, [("get", ⟨[], [.int .i32]⟩)]⟩

/-- `get() -> u32`, the value the start function stored. -/
def startS : Simple := ⟨startMod, [⟨"get", ⟨[], [.u32]⟩, 0⟩]⟩

end Silmaril.Wasm.Component.Reference.Litmus
