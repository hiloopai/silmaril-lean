module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstHost10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessIter10

/-!
# A V1 instantiation into a store with a host function

`hostBase`: the V1 store (host type `Nat`) holding one host function of type `[] → []`. It is
not host-free (`not_noHost_hostBase`), so an earlier `Reach10` (from the empty store) does not
contain it or anything instantiated into it. Its Core image is valid (`storeOk_hostBase`, Core's
host-function rule) and it satisfies `StoreWF`.

`addModule0` is instantiated into it (`inst_hostB`, by evaluation of V1's `prepare?`, under every
V1 host). So **`reachH_hostB`** and **`coreOk_hostB`**: the result is reached from `hostBase` in
the sense of `ReachH10`, and its Core image is valid, by `reachH10_ok`. The result still holds
the host function (`not_noHost_hostB`), so no invocation over it is IL-typed
(`not_typed10_hostB`): the forward run theorems hold there only vacuously.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Steps Instantiation prepare?)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10)
open Silmaril.Wasm.SpecTec.Sim10.InstG (InstBoundsG)
open Silmaril.Wasm.SpecTec.Sim10.InstH (ReachH10 HostChain10 hostChain10_empty reachH10_ok
  noHost10_of_typed10_invoke noHost10_of_typed10T_invoke)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addModule0 addModule0_valid)
open Silmaril.Wasm.SpecTec.Sim10.InstWitnessIter10 (boundsG_add0)
open Silmaril.Wasm.SpecTec.Sim10.Whole (NoHost10)

/-- One host function of type `[] → []` (host code `0`). -/
def hostBase : Store Nat := { funcs := [.host ⟨[], []⟩ 0] }

/-- **`hostBase` holds a host function.** -/
theorem not_noHost_hostBase : ¬ NoHost10 hostBase := fun h => h 0 ⟨[], []⟩ 0 rfl

/-- **The Core image of `hostBase` is valid** (Core's host-function rule). -/
theorem storeOk_hostBase : Execution.Core.StoreOk (coreStore10 hostBase) := by
  constructor <;>
    simp [coreStore10, hostBase, Execution.Runtime.Store.toCore, Execution.Runtime.Store.mapCode,
      Execution.Runtime.FuncInst.mapCode, Execution.Runtime.FuncInst.toCore]
  exact .host (Lime1.Validation.tyOk_toDefType _ _)
    (Validation.Expand.iff.mpr (V1.FuncType.toDefType_expand _)) rfl

/-- `hostBase` satisfies the simulation's `StoreWF`. -/
theorem storeWF_hostBase : Lime1.Execution.StoreWF (hostBase.mapCode V1.Func.toLime) := by
  refine ⟨fun i t m c h => ?_, fun i mi h => ?_⟩
  · cases i with
    | zero =>
      simp [hostBase, Execution.Runtime.Store.mapCode, Execution.Runtime.FuncInst.mapCode] at h
    | succ i => simp [hostBase, Execution.Runtime.Store.mapCode] at h
  · simp [hostBase, Execution.Runtime.Store.mapCode] at h

/-- The store after instantiating `addModule0` into `hostBase`. -/
def hostB : Store Nat :=
  match prepare? hostBase addModule0 [] with
  | some p => p.store
  | none => {}

/-- The module instance allocated there. -/
def hostBMod : Execution.Runtime.ModuleInst :=
  match prepare? hostBase addModule0 [] with
  | some p => p.module
  | none => {}

theorem prep_hostB : prepare? hostBase addModule0 [] = some ⟨hostB, hostBMod, []⟩ := rfl

/-- **The V1 instantiation of `addModule0` into `hostBase`**, under every V1 host. -/
theorem inst_hostB (host : HostSemantics Nat) :
    Instantiation host hostBase addModule0 [] hostB hostBMod (.values []) :=
  ⟨addModule0_valid, .nil, _, prep_hostB, rfl, .refl⟩

/-- The bounds of the instantiation. -/
theorem bounds_hostB : InstBoundsG (hostBase.mapCode V1.Func.toLime) addModule0.toLime where
  storeWF := storeWF_hostBase
  tables := fun _ ht => by simp [hostBase, Execution.Runtime.Store.mapCode] at ht
  data := fun d hd => by
    simp only [V1.Module.toLime, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact boundsG_add0.data d' hd'
  elemSize := fun e he => by
    simp only [V1.Module.toLime, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact boundsG_add0.elemSize e' he'
  elemCount := by simpa [V1.Module.toLime] using boundsG_add0.elemCount
  dataCount := by simpa [V1.Module.toLime] using boundsG_add0.dataCount

/-- **The result is reached from `hostBase`.** -/
theorem reachH_hostB : ReachH10 hostBase hostB :=
  .inst .base hostChain10_empty (inst_hostB _) bounds_hostB

/-- **Its Core image is valid, and it satisfies `StoreWF`**, through the route with hosts. -/
theorem coreOk_hostB : Execution.Core.StoreOk (coreStore10 hostB) ∧
    Lime1.Execution.StoreWF (hostB.mapCode V1.Func.toLime) :=
  reachH10_ok reachH_hostB storeOk_hostBase storeWF_hostBase

/-- The result still holds the host function. -/
theorem not_noHost_hostB : ¬ NoHost10 hostB := fun h => h 0 ⟨[], []⟩ 0 rfl

/-- **No invocation over the result is IL-typed** (`simEnv10` and `simEnv10T`, every builtins). -/
theorem not_typed10_hostB (hn : Nat → String) (B : Builtins) (args : List Execution.Runtime.Value)
    (a : Execution.Runtime.FuncAddr) :
    ¬ Typed10 (simEnv10 B) hn (invokeCfg10 hostB args a) ∧
      ¬ Typed10 (StoreFix.simEnv10T B) hn (invokeCfg10 hostB args a) :=
  ⟨fun h => not_noHost_hostB (noHost10_of_typed10_invoke h),
    fun h => not_noHost_hostB (noHost10_of_typed10T_invoke h)⟩

end Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10
