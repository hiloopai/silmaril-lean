module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostImplInst10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostImplWit10

/-!
# An exported host function, called through the 1.0 script with no Core hypothesis

`reexModule` imports one function of type `[] → []` and exports it under the empty name. It is
valid (`reexModule_valid`, a hand proof). Instantiated into round 6's `hostBase` with the host
function at address `0` as its import (`inst_reex`, by evaluation of V1's `prepare?`, under
every host), its instance exports address `0`, which holds the **host** function.

`wholeRunFwd10ImplRHE` then applies with every hypothesis discharged except the run itself:
the base store is valid in Core (`storeOk_hostBase`), the 32-bit bounds hold (`bounds_reex`),
the implemented invocation is IL-typed (`typed10_impl_reex`, kernel evaluation of the type
checker), and Core's `InvokeOk` is derived from V1 validation. So **`wholeRunFwd10ImplRHE_reex`**:
every V1 run under `noopHost` of the invocation of the exported function is, read through
`noopFn`, a run of the 1.0 script, and **`exportHostCall_run10`**: the first step of that run is a
host call (`Step.invokeHost`), and the one-step run has an IL run between typed images.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostReadWitE

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Validation
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps Instantiation prepare?
  ImportsMatch ExternMatches)
open Silmaril.Wasm.Execution.Runtime (Value FuncInst FuncAddr ExternVal)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10 emptyHost10 frame0)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.InstG (InstBoundsG ModBoundsG)
open Silmaril.Wasm.SpecTec.Sim10.InstH (hostChain10_empty)
open Silmaril.Wasm.SpecTec.Sim10.InstInvoke (FuncAt)
open Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10 (hostBase storeOk_hostBase storeWF_hostBase)
open Silmaril.Wasm.SpecTec.Sim10.HostStub (HostCall)
open Silmaril.Wasm.SpecTec.Sim10.HostRead
open Silmaril.Wasm.SpecTec.Sim10.HostReadWit (noopHost sig0 impl0 hostImpl_noop implOk_noop)
open Silmaril.Wasm.SpecTec.Sim10 (Typed10 configV simEnv10)

/-- A module that imports a function `[] → []` and exports it under the empty name. -/
def reexModule : V1.Module :=
  { types := [⟨[], []⟩], imports := [⟨"env", "f", .func ⟨0⟩⟩], exports := [⟨"", .func ⟨0⟩⟩] }

/-- The import is valid. -/
theorem reex_imports : ∀ i ∈ reexModule.imports, ImportValid reexModule.types i := by
  intro i hi
  simp only [reexModule, List.mem_singleton] at hi
  subst i
  exact ⟨.func ⟨[], []⟩, rfl, by simp [ExternTypeValid, FuncTypeValid]⟩

/-- The export is valid. -/
theorem reex_exports : ∀ e ∈ reexModule.exports, ExportValid (moduleContext reexModule) e := by
  intro e he
  simp only [reexModule, List.mem_singleton] at he
  subst e
  exact ⟨.func ⟨[], []⟩, rfl⟩

/-- **`reexModule` is valid.** -/
theorem reexModule_valid : ModuleValid reexModule where
  types := by simp [reexModule, FuncTypeValid]
  imports := reex_imports
  functions := by simp [reexModule]
  tables := by simp [reexModule]
  memories := by simp [reexModule]
  globals := by simp [reexModule]
  elements := by simp [reexModule]
  data := by simp [reexModule]
  start := by simp [StartValid, reexModule]
  exports := reex_exports
  uniqueExports := by simp [reexModule]
  singleTable := by decide
  singleMemory := by decide

/-- The host function at address `0` matches the import. -/
theorem imports_reex : ImportsMatch hostBase reexModule [.func ⟨0⟩] :=
  .cons ⟨.func ⟨[], []⟩, rfl, .func ⟨0⟩ _ ⟨[], []⟩ rfl rfl⟩ .nil

/-- The store `prepare?` returns. -/
def reexStore : Store Nat :=
  match prepare? hostBase reexModule [.func ⟨0⟩] with
  | some p => p.store
  | none => {}

/-- The module instance it allocates. -/
def reexMod : Execution.Runtime.ModuleInst :=
  match prepare? hostBase reexModule [.func ⟨0⟩] with
  | some p => p.module
  | none => {}

theorem prep_reex : prepare? hostBase reexModule [.func ⟨0⟩] = some ⟨reexStore, reexMod, []⟩ :=
  rfl

/-- **The V1 instantiation of `reexModule` into `hostBase`**, under every host. -/
theorem inst_reex (host : HostSemantics Nat) :
    Instantiation host hostBase reexModule [.func ⟨0⟩] reexStore reexMod (.values []) :=
  ⟨reexModule_valid, imports_reex, _, prep_reex, rfl, .refl⟩

theorem boundsG_reex : ModBoundsG reexModule := by
  constructor <;> simp [reexModule]

/-- The bounds of the instantiation. -/
theorem bounds_reex : InstBoundsG (hostBase.mapCode V1.Func.toLime) reexModule.toLime where
  storeWF := storeWF_hostBase
  tables := fun _ ht => by simp [hostBase, Execution.Runtime.Store.mapCode] at ht
  data := fun d hd => by
    simp only [V1.Module.toLime, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact boundsG_reex.data d' hd'
  elemSize := fun e he => by
    simp only [V1.Module.toLime, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact boundsG_reex.elemSize e' he'
  elemCount := by simpa [V1.Module.toLime] using boundsG_reex.elemCount
  dataCount := by simpa [V1.Module.toLime] using boundsG_reex.dataCount

/-- The instance exports address `0`. -/
theorem export_reex : (⟨"", .func ⟨0⟩⟩ : Execution.Runtime.ExportInst) ∈ reexMod.exports := by
  decide

/-- Address `0` of the result holds the host function. -/
theorem reexStore_funcs : reexStore.funcs = [.host ⟨[], []⟩ 0] := rfl

theorem hostTyped_hostBase : HostTyped sig0 hostBase.funcs := by
  intro a t h e
  match a, e with
  | 0, e =>
    simp only [hostBase, List.getElem?_cons_zero, Option.some.injEq, FuncInst.host.injEq] at e
    exact e.1.symm
  | n + 1, e => simp [hostBase] at e

/-- The empty host has every implementation. -/
theorem hostImpl_empty : HostImpl impl0 sig0 (emptyHost10 (H := Nat)) :=
  fun _ _ _ _ _ _ _ _ _ _ hb => hb.elim

/-- The exported function's validated type is `[] → []`. -/
theorem ft_reex {ft : V1.FuncType} (h : FuncAt reexStore ft ⟨0⟩) : ft = ⟨[], []⟩ := by
  obtain ⟨fi, hfi, rfl⟩ := h
  rw [reexStore_funcs] at hfi
  cases hfi
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The implemented invocation of the exported host function is IL-typed** (`simEnv10`). -/
theorem typed10_impl_reex (B : Builtins) (hn : Nat → String) :
    Typed10 (simEnv10 B) hn (invokeCfg10 (implS impl0 reexStore) [] ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- **The forward run for the exported host function, host calls included, with no Core
hypothesis on the invocation**: every V1 run under `noopHost` of the invocation is, read
through `noopFn`, a run of the 1.0 script. -/
theorem wholeRunFwd10ImplRHE_reex (hn : Nat → String) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Nat} (h : Steps noopHost (invokeCfg10 reexStore [] ⟨0⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (implC impl0 c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (implC impl0 (invokeCfg10 reexStore [] ⟨0⟩)))
        (configV hn (implC impl0 c')) := by
  obtain ⟨ft, hfa, hrun⟩ := wholeRunFwd10ImplRHE (hn := hn) (nd := nd) (r := r) (host := noopHost)
    .base storeOk_hostBase storeWF_hostBase hostChain10_empty (inst_reex emptyHost10) bounds_reex
    hostImpl_empty hostImpl_noop implOk_noop hostTyped_hostBase export_reex rfl
  obtain rfl := ft_reex hfa
  exact hrun [] rfl c' (typed10_impl_reex _ hn) h

/-- The invocation of the exported function under `noopHost` is a host call. -/
theorem step_noop_reex :
    Step noopHost (invokeCfg10 reexStore [] ⟨0⟩) ⟨reexStore, frame0, []⟩ ∧
      HostCall (invokeCfg10 reexStore [] ⟨0⟩) :=
  ⟨.invokeHost reexStore reexStore frame0 ⟨0⟩ ⟨[], []⟩ 0 [] (.values []) rfl rfl ⟨rfl, rfl⟩,
    .here [] rfl⟩

/-- **An exported host function, called, is a run of the 1.0 script**: from V1 instantiation
and V1 validation only (no Core hypothesis on the invocation), the one-step V1 run that calls
the host function has an IL run between typed images. -/
theorem exportHostCall_run10 (hn : Nat → String) (nd : Bool) (r : RelaxedChoice) :
    HostCall (invokeCfg10 reexStore [] ⟨0⟩) ∧
      Step noopHost (invokeCfg10 reexStore [] ⟨0⟩) ⟨reexStore, frame0, []⟩ ∧
      Typed10 (simEnv10 (fwdB10 nd r)) hn (implC impl0 ⟨reexStore, frame0, []⟩) ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (implC impl0 (invokeCfg10 reexStore [] ⟨0⟩)))
        (configV hn (implC impl0 ⟨reexStore, frame0, []⟩)) := by
  have hrun := wholeRunFwd10ImplRHE_reex hn nd r (.single step_noop_reex.1)
  exact ⟨step_noop_reex.2, step_noop_reex.1, hrun.1, hrun.2⟩

end Silmaril.Wasm.SpecTec.Sim10.HostReadWitE
