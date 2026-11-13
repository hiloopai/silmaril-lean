module

public import Silmaril.Wasm.Component.Semantics.Defs
public import Silmaril.Wasm.Game.Strategy.Defs
public import Silmaril.Wasm.SingleThreaded.Interface

/-!
# Core 3.0 instances as a core semantics of the component IR

The component IR (`Silmaril.Wasm.Component`, `Comp.den C`) is parametric in a core semantics
`C : CoreSem M`. This module gives one built from silmaril's Core 3.0 semantics, at an
**arbitrary** profile `P`: core modules are numeric Core 3.0 instances `NumInstance` (a
`Silmaril.Wasm.Game.ScalarInstance` whose import and export function types are numeric, with
names), and `core3Sem P` is the game-semantic strategy of the instance
(`ScalarInstance.strategy P`, the relational single-threaded machine `InternalP P` with the
store persisting across calls) seen through the IR's dynamically typed signatures:

* an export question `(j, .flat xs)` is the call of export `j` on the Core values of `xs` when
  they have its parameter types, and traps (`none`) otherwise; its answer is the flat results,
  and a trap or an uncaught exception is a trap (REF `call_and_trap_on_throw`);
* an import call of the instance is the IR question `(i, .flat xs)`; an answer of the right
  result types resumes the instance with those values, any other answer is a trap.

This is the core semantics that the component IR's soundness against the reference machine
(`Silmaril.Wasm.Component.Reference`) is to be stated with: the IR's core instance strategies are
the Core 3.0 strategies, and the component machine runs the same Core 3.0 code with `core3P P`.
That adequacy is not proved here (see `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Game
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Numerics (Profile)

/-- The scalar function type of a flat core function type. -/
def fnOf (ft : CoreFuncTy) : FnType :=
  ⟨ft.params.map .num, ft.results.map .num⟩

/-- A Core 3.0 instance with numeric, named imports and exports. -/
structure NumInstance where
  /-- The instance (types, export addresses, store after instantiation). -/
  inst : ScalarInstance
  /-- The named imports. -/
  imports : CoreIface
  /-- The named exports. -/
  exports : CoreIface
  imports_eq : inst.imports = imports.map fun p => fnOf p.2
  exports_eq : inst.exports = exports.map fun p => fnOf p.2

instance : CoreModule NumInstance := ⟨NumInstance.imports, NumInstance.exports⟩

namespace NumInstance

variable (m : NumInstance)

theorem imports_length : m.imports.length = m.inst.imports.length := by
  rw [m.imports_eq, List.length_map]

theorem exports_length : m.exports.length = m.inst.exports.length := by
  rw [m.exports_eq, List.length_map]

end NumInstance

open Classical in
/-- The values `vs` with the scalar types `ts`, if they have them. -/
noncomputable def typed? (ts : List ScalarType) (vs : List Silmaril.Wasm.Execution.Core.Val) : Option (Typed ts) :=
  if h : List.Forall₂ ScalarType.HasVal ts vs then some ⟨vs, h⟩ else none

/-- The payload of an answer: flat results; a trap or an exception is a trap. -/
def answerPayload {ft : FnType} : Answer ft → Option Payload
  | .values vs => (vs.1.mapM Silmaril.Wasm.SingleThreaded.toFlat?).map .flat
  | .trap => none
  | .throw _ => none

/-- The answer of an import of type `ft` to an IR answer: flat values of the result types, or
a trap. -/
noncomputable def payloadAnswer (ft : FnType) : Option Payload → Answer ft
  | some (.flat ys) =>
    match typed? ft.results (ys.map Silmaril.Wasm.SingleThreaded.ofFlat) with
    | some vs => .values vs
    | none => .trap
  | _ => .trap

/-- The export side: IR questions to the instance's typed export calls. -/
noncomputable def exportH (m : NumInstance) :
    Handler (ifaceSig m.inst.exports) (CoreIface.sig m.exports) := fun q =>
  let j : Fin m.inst.exports.length := Fin.cast m.exports_length q.1
  match q.2 with
  | .flat xs =>
    match typed? (m.inst.exports.get j).params (xs.map Silmaril.Wasm.SingleThreaded.ofFlat) with
    | some args => .call ⟨j, args⟩ fun a => .pure (answerPayload a)
    | none => .pure none
  | .vals _ => .pure none

/-- The import side: the instance's typed import calls as IR questions. -/
noncomputable def importH (m : NumInstance) :
    Handler (CoreIface.sig m.imports) (ifaceSig m.inst.imports) := fun q =>
  .call (Fin.cast m.imports_length.symm q.1,
      .flat (q.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?))
    fun r => .pure (payloadAnswer _ r)

/-- **The Core 3.0 core semantics at profile `P`**: the strategy of each numeric Core 3.0
instance at its instantiation store, through the IR's dynamically typed signatures. -/
noncomputable def core3Sem (P : Profile) : CoreSem NumInstance where
  sem m := (Strategy.ofHandler (importH m)).comp
    ((m.inst.strategy P m.inst.store).comp (Strategy.ofHandler (exportH m)))

end Silmaril.Wasm.Component.Reference
