module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstValid10
public import Silmaril.Wasm.V1.Validation.Examples

/-!
# A V1 instantiation for which the instantiation form of the 1.0 run theorem applies

`addModule0`: silmaril's validation example `addModule` (one function `[i32 i32] → [i32]`,
`local.get 0; local.get 1; i32.add`) without its export. Instantiated into the empty store
(`inst_add0`, by evaluation of V1's `prepare?`; validity is a hand proof, as for `addModule`),
it satisfies every hypothesis of `wholeRunFwd10InvV_empty`: the module bounds
(`bounds_add0`), the IL typing of the invocation on `i32.const 1, i32.const 2` (kernel
evaluation of the type checker, `typed10_add0`), and Core's `InvokeOk` (`invokeOk_add0`). So
**`wholeRunFwd10InvV_add0`**: every V1 run of that invocation is a run of the 1.0 script, with no
Core `StoreOk` hypothesis anywhere; `step_invoke_add0` is its first step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstWitness10

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Validation
open Silmaril.Wasm.V1.Validation.Examples (addType addBody addBody_typed)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps Instantiation prepare?
  expression)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10 ModBounds10 wholeRunFwd10InvV_empty)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)

/-- `addModule` without its export. -/
def addModule0 : V1.Module := Scalar.Module.ofFunction addType [] addBody none

/-- **`addModule0` is valid.** -/
theorem addModule0_valid : ModuleValid addModule0 where
  types := by simp [addModule0, Scalar.Module.ofFunction, FuncTypeValid, addType]
  imports := by simp [addModule0, Scalar.Module.ofFunction]
  functions := by
    intro f hf
    simp only [addModule0, Scalar.Module.ofFunction, List.mem_singleton] at hf
    subst f
    exact ⟨addType, rfl, Nat.le_refl 1, addBody_typed _⟩
  tables := by simp [addModule0, Scalar.Module.ofFunction]
  memories := by simp [addModule0, Scalar.Module.ofFunction]
  globals := by simp [addModule0, Scalar.Module.ofFunction]
  elements := by simp [addModule0, Scalar.Module.ofFunction]
  data := by simp [addModule0, Scalar.Module.ofFunction]
  start := by simp [StartValid, addModule0, Scalar.Module.ofFunction]
  exports := by simp [addModule0, Scalar.Module.ofFunction]
  uniqueExports := by simp [addModule0, Scalar.Module.ofFunction]
  singleTable := by decide
  singleMemory := by decide

/-- The store `prepare?` allocates for `addModule0` in the empty store. -/
def addStore0 : Store Empty :=
  match prepare? ({} : Store Empty) addModule0 [] with
  | some p => p.store
  | none => {}

/-- The module instance `prepare?` allocates for `addModule0`. -/
def addMod0 : Execution.Runtime.ModuleInst :=
  match prepare? ({} : Store Empty) addModule0 [] with
  | some p => p.module
  | none => {}

/-- `prepare?` succeeds, with no start function (evaluation). -/
theorem prep_add0 : prepare? ({} : Store Empty) addModule0 [] = some ⟨addStore0, addMod0, []⟩ :=
  rfl

/-- **The V1 instantiation of `addModule0` into the empty store**, under any host. -/
theorem inst_add0 (host : HostSemantics Empty) :
    Instantiation host {} addModule0 [] addStore0 addMod0 (.values []) :=
  ⟨addModule0_valid, .nil, _, prep_add0, rfl, .refl⟩

/-- The arguments `1, 2`. -/
def addArgs : List Execution.Runtime.Value := [.int .i32 1, .int .i32 2]

/-- The arguments fit the function's type. -/
theorem invokeOk_add0 : Execution.Core.InvokeOk (coreStore10 addStore0) 0
    (addArgs.map Execution.Runtime.Value.toCore) :=
  ⟨_, _, _, rfl, Silmaril.Wasm.Validation.Expand.iff.mpr rfl,
    .cons (.num _) (.cons (.num _) .nil)⟩

/-- `addModule0` has no globals and small segments. -/
theorem bounds_add0 : ModBounds10 addModule0 := by
  constructor <;> simp [addModule0, Scalar.Module.ofFunction]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The image of the invocation is typed (kernel evaluation of the type checker). -/
theorem typed10_add0 (B : Builtins) :
    Typed10 (simEnv10 B) Empty.elim (invokeCfg10 addStore0 addArgs ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- **The instantiation form applies**: every V1 run of the invocation of the instantiated
function is a run of the 1.0 script, with no Core `StoreOk` hypothesis. -/
theorem wholeRunFwd10InvV_add0 (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Empty} (h : Steps host (invokeCfg10 addStore0 addArgs ⟨0⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) Empty.elim c' ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV Empty.elim (invokeCfg10 addStore0 addArgs ⟨0⟩)) (configV Empty.elim c') :=
  wholeRunFwd10InvV_empty (inst_add0 host) bounds_add0 (typed10_add0 _) invokeOk_add0 h

/-- **The first step of the invocation**: V1 opens the function's frame. -/
theorem step_invoke_add0 (host : HostSemantics Empty) :
    Step host (invokeCfg10 addStore0 addArgs ⟨0⟩)
      ⟨addStore0, Valid.frame0,
        [.frame 1 ⟨addArgs, addMod0⟩ [.label 1 [] (expression addBody)]]⟩ :=
  .invokeWasm _ _ ⟨0⟩ addType addMod0 ⟨⟨0⟩, [], addBody⟩ addArgs rfl rfl (by decide)

/-- **Non-vacuity**: that step is a step of the 1.0 script. -/
theorem sstep10_invoke_add0 (host : HostSemantics Empty) (nd : Bool) (r : RelaxedChoice) :
    Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
      (configV Empty.elim (invokeCfg10 addStore0 addArgs ⟨0⟩))
      (configV Empty.elim
        ⟨addStore0, Valid.frame0,
          [.frame 1 ⟨addArgs, addMod0⟩ [.label 1 [] (expression addBody)]]⟩) :=
  (wholeRunFwd10InvV_add0 host nd r (Relation.ReflTransGen.single (step_invoke_add0 host))).2

end Silmaril.Wasm.SpecTec.Sim10.InstWitness10
