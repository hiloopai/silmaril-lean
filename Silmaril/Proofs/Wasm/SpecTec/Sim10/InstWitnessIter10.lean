module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstErase10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessG10

/-!
# Two V1 instantiations in a row, to which the iterated form of the 1.0 run theorem applies

`addModule0` is instantiated into the empty store, then `globModule` (with a global) into the
result (`inst_iter`, by evaluation of V1's `prepare?`). The second store is reached
(`reach_iter`), so **`wholeRunFwd10InvRU_iter`**: every V1 run of the invocation of the second
module's function (address `1`) on `1, 2` is a run of the 1.0 script. The image typing is a
kernel evaluation of the type checker; Core's `InvokeOk` is by hand.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstWitnessIter10

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Steps Instantiation prepare?)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10)
open Silmaril.Wasm.SpecTec.Sim10.InstG (ModBoundsG Reach10 reach10_one reach10_okU
  wholeRunFwd10InvRU)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addModule0 addArgs addStore0 inst_add0)
open Silmaril.Wasm.SpecTec.Sim10.InstWitnessG10 (globModule globModule_valid)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)

theorem addStore0_tables : addStore0.tables = [] := rfl

theorem boundsG_add0 : ModBoundsG addModule0 := by
  constructor <;> simp [addModule0, Scalar.Module.ofFunction]

/-- The first store is reached. -/
theorem reach_add0 (host : HostSemantics Empty) : Reach10 addStore0 :=
  reach10_one (inst_add0 host) boundsG_add0

/-- The store after the second instantiation. -/
def iterStore : Store Empty :=
  match prepare? addStore0 globModule [] with
  | some p => p.store
  | none => {}

/-- The module instance of the second instantiation. -/
def iterMod : Execution.Runtime.ModuleInst :=
  match prepare? addStore0 globModule [] with
  | some p => p.module
  | none => {}

theorem prep_iter : prepare? addStore0 globModule [] = some ⟨iterStore, iterMod, []⟩ := rfl

/-- Two functions and one global after the second instantiation. -/
theorem iterStore_shape : iterStore.funcs.length = 2 ∧ iterStore.globals.length = 1 :=
  ⟨rfl, rfl⟩

/-- **The second instantiation**, into the store of the first. -/
theorem inst_iter (host : HostSemantics Empty) :
    Instantiation host addStore0 globModule [] iterStore iterMod (.values []) :=
  ⟨globModule_valid, .nil, _, prep_iter, rfl, .refl⟩

/-- **The second store is reached.** -/
theorem reach_iter (host : HostSemantics Empty) : Reach10 iterStore :=
  .inst (reach_add0 host) (inst_iter host)
    ⟨(reach10_okU (reach_add0 host)).wf, fun _ h => by simp [addStore0_tables, Execution.Runtime.Store.mapCode] at h,
      by simp [globModule, addModule0, Scalar.Module.ofFunction, V1.Module.toLime],
      by simp [globModule, addModule0, Scalar.Module.ofFunction, V1.Module.toLime],
      by simp [globModule, addModule0, Scalar.Module.ofFunction, V1.Module.toLime],
      by simp [globModule, addModule0, Scalar.Module.ofFunction, V1.Module.toLime]⟩

theorem invokeOk_iter : Execution.Core.InvokeOk (coreStore10 iterStore) 1
    (addArgs.map Execution.Runtime.Value.toCore) :=
  ⟨_, _, _, rfl, Silmaril.Wasm.Validation.Expand.iff.mpr rfl,
    .cons (.num _) (.cons (.num _) .nil)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The image of the invocation is typed (kernel evaluation of the type checker). -/
theorem typed10_iter (B : Builtins) :
    Typed10 (simEnv10 B) Empty.elim (invokeCfg10 iterStore addArgs ⟨1⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- **The iterated form applies**: every V1 run of the invocation of the function allocated by
the second of two instantiations is a run of the 1.0 script. -/
theorem wholeRunFwd10InvRU_iter (host host' : HostSemantics Empty) (nd : Bool)
    (r : RelaxedChoice) {c' : Config Empty} (h : Steps host' (invokeCfg10 iterStore addArgs ⟨1⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) Empty.elim c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV Empty.elim (invokeCfg10 iterStore addArgs ⟨1⟩)) (configV Empty.elim c') :=
  wholeRunFwd10InvRU (reach_iter host) (typed10_iter _) invokeOk_iter h

end Silmaril.Wasm.SpecTec.Sim10.InstWitnessIter10
