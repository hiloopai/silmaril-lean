module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstGlob10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitness10

/-!
# A V1 instantiation with a global, to which the globals form of the 1.0 run theorem applies

`globModule`: an earlier witness `addModule0` with one immutable `i32` global initialised to `7`.
It has a global, so the copied `InstantiationBounds` (and with it `wholeRunFwd10InvV_empty`) do
not apply to it. Instantiated into the empty store (`inst_glob`, by evaluation of V1's
`prepare?`; validity by hand), it satisfies every hypothesis of `wholeRunFwd10InvG_empty`: the
segment bounds, the IL typing of the invocation on `1, 2` (kernel evaluation of the type
checker), and Core's `InvokeOk`. So **`wholeRunFwd10InvG_glob`**: every V1 run of that
invocation is a run of the 1.0 script. `globModule_has_global` records that the global is there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstWitnessG10

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Validation
open Silmaril.Wasm.V1.Validation.Examples (addType addBody addBody_typed)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps Instantiation prepare?)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10)
open Silmaril.Wasm.SpecTec.Sim10.InstG (ModBoundsG wholeRunFwd10InvG_empty)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addModule0 addArgs addModule0_valid)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)

/-- The global `(global i32 (i32.const 7))`. -/
def glob7 : V1.Global := ⟨⟨.const, .i32⟩, [.intConst .i32 7]⟩

/-- `addModule0` with the global `glob7`. -/
def globModule : V1.Module := { addModule0 with globals := [glob7] }

theorem globModule_has_global : globModule.globals ≠ [] := by simp [globModule]

/-- **`globModule` is valid.** -/
theorem globModule_valid : ModuleValid globModule where
  types := addModule0_valid.types
  imports := addModule0_valid.imports
  functions := by
    intro f hf
    simp only [globModule, addModule0, Scalar.Module.ofFunction, List.mem_singleton] at hf
    subst f
    exact ⟨addType, rfl, Nat.le_refl 1, addBody_typed _⟩
  tables := addModule0_valid.tables
  memories := addModule0_valid.memories
  globals := by
    intro g hg
    simp only [globModule, List.mem_singleton] at hg
    subst hg
    refine ⟨.cons (.intConst _ _) (.nil _), fun i hi => ?_⟩
    cases hi with
    | head => exact .intConst _ _
    | tail _ h => cases h
  elements := by simp [globModule, addModule0, Scalar.Module.ofFunction]
  data := by simp [globModule, addModule0, Scalar.Module.ofFunction]
  start := addModule0_valid.start
  exports := by simp [globModule, addModule0, Scalar.Module.ofFunction]
  uniqueExports := addModule0_valid.uniqueExports
  singleTable := by decide
  singleMemory := by decide

/-- The store `prepare?` allocates for `globModule` in the empty store. -/
def globStore : Store Empty :=
  match prepare? ({} : Store Empty) globModule [] with
  | some p => p.store
  | none => {}

/-- The module instance `prepare?` allocates for `globModule`. -/
def globMod : Execution.Runtime.ModuleInst :=
  match prepare? ({} : Store Empty) globModule [] with
  | some p => p.module
  | none => {}

/-- `prepare?` succeeds, with no start function (evaluation). -/
theorem prep_glob : prepare? ({} : Store Empty) globModule [] = some ⟨globStore, globMod, []⟩ :=
  rfl

/-- The instantiated store holds the global. -/
theorem globStore_globals : globStore.globals = [⟨.int .i32 7, .const⟩] := rfl

/-- **The V1 instantiation of `globModule` into the empty store**, under any host. -/
theorem inst_glob (host : HostSemantics Empty) :
    Instantiation host {} globModule [] globStore globMod (.values []) :=
  ⟨globModule_valid, .nil, _, prep_glob, rfl, .refl⟩

/-- The arguments fit the function's type. -/
theorem invokeOk_glob : Execution.Core.InvokeOk (coreStore10 globStore) 0
    (addArgs.map Execution.Runtime.Value.toCore) :=
  ⟨_, _, _, rfl, Silmaril.Wasm.Validation.Expand.iff.mpr rfl,
    .cons (.num _) (.cons (.num _) .nil)⟩

/-- `globModule` has small segments. -/
theorem bounds_glob : ModBoundsG globModule := by
  constructor <;> simp [globModule, addModule0, Scalar.Module.ofFunction]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The image of the invocation is typed (kernel evaluation of the type checker). -/
theorem typed10_glob (B : Builtins) :
    Typed10 (simEnv10 B) Empty.elim (invokeCfg10 globStore addArgs ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- **The globals form applies**: every V1 run of the invocation of the function of a module
with a global is a run of the 1.0 script, with no Core `StoreOk` hypothesis. -/
theorem wholeRunFwd10InvG_glob (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Empty} (h : Steps host (invokeCfg10 globStore addArgs ⟨0⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) Empty.elim c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV Empty.elim (invokeCfg10 globStore addArgs ⟨0⟩)) (configV Empty.elim c') :=
  wholeRunFwd10InvG_empty (inst_glob host) bounds_glob (typed10_glob _) invokeOk_glob h

end Silmaril.Wasm.SpecTec.Sim10.InstWitnessG10
