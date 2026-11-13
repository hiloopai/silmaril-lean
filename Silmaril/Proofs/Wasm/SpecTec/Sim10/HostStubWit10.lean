module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostStubCore10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstWitnessHost10

/-!
# The stub restatement is not vacuous

Round 6's witness `hostB` is `addModule0` instantiated into `hostBase`, a store holding one host
function (address `0`); the instantiated `add` function is at address `1`. No invocation over
`hostB` is IL-typed (`InstWitnessHost10.not_typed10_hostB`), so round 6's forward theorems say
nothing there.

Through the stub: the invocation of `add` on `1, 2` over `stubS hostB` **is** IL-typed, in
`simEnv10` and in `simEnv10T` (`typed10_stub_hostB`, `typed10T_stub_hostB`, kernel evaluation of
the type checker at fuel 2000), Core's `InvokeOk` holds (`invokeOk_hostB1`), and the invocation
takes a step under the empty host (`step_hostB1`). So **`wholeRunFwd10StubRH_hostB`**: every V1
run of that invocation that calls no host function is, read through the stub, a run of the 1.0
script, and the run is not empty.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostStubWit

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Validation.Examples (addType addBody)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10 emptyHost10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addArgs)
open Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10 (hostBase hostB hostBMod reachH_hostB
  storeOk_hostBase storeWF_hostBase not_typed10_hostB)
open Silmaril.Wasm.SpecTec.Sim10.HostStub

/-- The `add` function sits at address `1` of `hostB`, after the host function. -/
theorem hostB_funcs1 : hostB.funcs[1]? = some (.wasm addType hostBMod ⟨⟨0⟩, [], addBody⟩) := rfl

/-- Core's `InvokeOk` for `add` on `1, 2`. -/
theorem invokeOk_hostB1 : Execution.Core.InvokeOk (coreStore10 hostB) 1
    (addArgs.map Execution.Runtime.Value.toCore) :=
  ⟨_, _, _, rfl, Silmaril.Wasm.Validation.Expand.iff.mpr rfl,
    .cons (.num _) (.cons (.num _) .nil)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The stubbed invocation is IL-typed** (`simEnv10`), although `hostB` holds a host
function. -/
theorem typed10_stub_hostB (B : Builtins) (hn : Nat → String) :
    Typed10 (simEnv10 B) hn (invokeCfg10 (stubS hostB) addArgs ⟨1⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The same in `simEnv10T`.** -/
theorem typed10T_stub_hostB (B : Builtins) (hn : Nat → String) :
    Typed10 (simEnv10T B) hn (invokeCfg10 (stubS hostB) addArgs ⟨1⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- The invocation of `add` takes a step under the empty host (it calls no host function). -/
theorem step_hostB1 : ∃ c', Step emptyHost10 (invokeCfg10 hostB addArgs ⟨1⟩) c' :=
  ⟨_, .invokeWasm _ _ ⟨1⟩ addType hostBMod ⟨⟨0⟩, [], addBody⟩ addArgs hostB_funcs1 rfl
    (by decide)⟩

/-- **The forward run at `hostB`, through the stub**: every V1 run of `add` on `1, 2` that calls
no host function is a run of the 1.0 script between the stubbed images. Unlike round 6's
`wholeRunFwd10InvRH`, the typing hypothesis is discharged. -/
theorem wholeRunFwd10StubRH_hostB (hn : Nat → String) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Nat} (h : Steps emptyHost10 (invokeCfg10 hostB addArgs ⟨1⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 hostB addArgs ⟨1⟩))) (configV hn (stubC c')) :=
  wholeRunFwd10StubRH reachH_hostB storeOk_hostBase storeWF_hostBase
    (typed10_stub_hostB _ hn) invokeOk_hostB1 h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10StubRHT_hostB (hn : Nat → String) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Nat} (h : Steps emptyHost10 (invokeCfg10 hostB addArgs ⟨1⟩) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 hostB addArgs ⟨1⟩))) (configV hn (stubC c')) :=
  wholeRunFwd10StubRHT reachH_hostB storeOk_hostBase storeWF_hostBase
    (typed10T_stub_hostB _ hn) invokeOk_hostB1 h

/-- **Not vacuous**: without the stub the invocation image is not typed, with it it is, and the
run has a first step. -/
theorem stub_nonvacuous (B : Builtins) (hn : Nat → String) :
    ¬ Typed10 (simEnv10 B) hn (invokeCfg10 hostB addArgs ⟨1⟩) ∧
      Typed10 (simEnv10 B) hn (stubC (invokeCfg10 hostB addArgs ⟨1⟩)) ∧
      ∃ c', Step emptyHost10 (invokeCfg10 hostB addArgs ⟨1⟩) c' :=
  ⟨(not_typed10_hostB hn B addArgs ⟨1⟩).1, typed10_stub_hostB B hn, step_hostB1⟩

end Silmaril.Wasm.SpecTec.Sim10.HostStubWit
