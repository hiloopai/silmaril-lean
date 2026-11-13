module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstInvoke10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessIter10

/-!
# An exported function, invoked with no `InvokeOk` hypothesis

`addModuleE`: silmaril's validation example `addModule` with its export renamed to the empty
name. Instantiated into the empty store (`inst_addE`, by evaluation of V1's `prepare?`), its
instance exports the function at address `0`. `wholeRunFwd10InvRUE` gives the export's validated
type; here it is `addType` (`ft_addE`), and the invocation on `1, 2` is IL-typed
(`typed10_addE`, kernel evaluation of the type checker). So **`wholeRunFwd10InvRUE_addE`**: every
V1 run of that invocation is a run of the 1.0 script, with Core's `InvokeOk` derived rather than
assumed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstWitnessExp10

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Validation
open Silmaril.Wasm.V1.Validation.Examples (addType addBody addBody_typed)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Steps Instantiation prepare?)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10)
open Silmaril.Wasm.SpecTec.Sim10.InstG (ModBoundsG Reach10 boundsG_empty)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addArgs)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)

/-- `addModule` with its export renamed to the empty name. -/
def addModuleE : V1.Module := Scalar.Module.ofFunction addType [] addBody (some "")

/-- The export is valid. -/
theorem addModuleE_exports : ∀ e ∈ addModuleE.exports, ExportValid (moduleContext addModuleE) e := by
  intro e he
  simp [addModuleE, Scalar.Module.ofFunction] at he
  subst e
  exact ⟨.func addType, rfl⟩

/-- **`addModuleE` is valid.** -/
theorem addModuleE_valid : ModuleValid addModuleE where
  types := by simp [addModuleE, Scalar.Module.ofFunction, FuncTypeValid, addType]
  imports := by simp [addModuleE, Scalar.Module.ofFunction]
  functions := by
    intro f hf
    simp only [addModuleE, Scalar.Module.ofFunction, List.mem_singleton] at hf
    subst f
    exact ⟨addType, rfl, Nat.le_refl 1, addBody_typed _⟩
  tables := by simp [addModuleE, Scalar.Module.ofFunction]
  memories := by simp [addModuleE, Scalar.Module.ofFunction]
  globals := by simp [addModuleE, Scalar.Module.ofFunction]
  elements := by simp [addModuleE, Scalar.Module.ofFunction]
  data := by simp [addModuleE, Scalar.Module.ofFunction]
  start := by simp [StartValid, addModuleE, Scalar.Module.ofFunction]
  exports := addModuleE_exports
  uniqueExports := by simp [addModuleE, Scalar.Module.ofFunction]
  singleTable := by decide
  singleMemory := by decide

/-- The store `prepare?` allocates for `addModuleE` in the empty store. -/
def addStoreE : Store Empty :=
  match prepare? ({} : Store Empty) addModuleE [] with
  | some p => p.store
  | none => {}

/-- The module instance it allocates. -/
def addModE : Execution.Runtime.ModuleInst :=
  match prepare? ({} : Store Empty) addModuleE [] with
  | some p => p.module
  | none => {}

theorem prep_addE : prepare? ({} : Store Empty) addModuleE [] = some ⟨addStoreE, addModE, []⟩ :=
  rfl

/-- **The V1 instantiation of `addModuleE` into the empty store**, under every host. -/
theorem inst_addE (host : HostSemantics Empty) :
    Instantiation host {} addModuleE [] addStoreE addModE (.values []) :=
  ⟨addModuleE_valid, .nil, _, prep_addE, rfl, .refl⟩

/-- The instance exports the function at address `0`. -/
theorem export_addE : (⟨"", .func ⟨0⟩⟩ : Execution.Runtime.ExportInst) ∈ addModE.exports := by
  decide

theorem boundsG_addE : ModBoundsG addModuleE := by
  constructor <;> simp [addModuleE, Scalar.Module.ofFunction]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The image of the invocation is typed (kernel evaluation of the type checker). -/
theorem typed10_addE (B : Builtins) :
    Typed10 (simEnv10 B) Empty.elim (invokeCfg10 addStoreE addArgs ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- The function at address `0` has type `addType`, so the export's type is `addType`. -/
theorem ft_addE {ft : V1.FuncType} (h : InstInvoke.FuncAt addStoreE ft ⟨0⟩) : ft = addType := by
  obtain ⟨fi, hfi, rfl⟩ := h
  have e : addStoreE.funcs[0]? = some (.wasm addType addModE ⟨⟨0⟩, [], addBody⟩) := rfl
  rw [hfi] at e
  cases e
  rfl

/-- The arguments `1, 2` have the parameter types of `addType`. -/
theorem addArgs_types : addArgs.map Execution.Runtime.Value.type = addType.params := rfl

/-- **The export form applies**: every V1 run of the invocation of the exported function on
`1, 2` is a run of the 1.0 script; Core's `InvokeOk` is derived from V1 validation. -/
theorem wholeRunFwd10InvRUE_addE (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Empty} (h : Steps host (invokeCfg10 addStoreE addArgs ⟨0⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) Empty.elim c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV Empty.elim (invokeCfg10 addStoreE addArgs ⟨0⟩)) (configV Empty.elim c') := by
  obtain ⟨ft, hfa, hrun⟩ := InstInvoke.wholeRunFwd10InvRUE (hn := Empty.elim) (host' := host)
    (nd := nd) (r := r) .empty (inst_addE host) (boundsG_empty boundsG_addE) export_addE rfl
  obtain rfl := ft_addE hfa
  exact hrun addArgs addArgs_types c' (typed10_addE _) h

end Silmaril.Wasm.SpecTec.Sim10.InstWitnessExp10
