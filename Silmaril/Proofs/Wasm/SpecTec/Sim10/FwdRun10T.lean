module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRed10T
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdValid

/-!
# The forward 1.0 half in `simEnv10T`: one invariant, along runs

* `valTyped10T`, **`typed10_step10T`**: subject reduction in `simEnv10T` (`SubjRed10T`), stores
  included: a V1 step from a configuration typed in `simEnv10T` with `GSetOk` reaches one typed
  in `simEnv10T`.
* **`wholeStepFwd10T_one`**: the forward whole step in `simEnv10T` under the one invariant
  `Typed10 (simEnv10T _) ∧ Plain10 ∧ GSetOk ∧ MemsAligned10`, with no hypothesis on the
  successor. It is round 4's `wholeStepFwd10` with `simEnv10` replaced by `simEnv10T`; so a
  storing program, and a store holding storing functions, are covered.
* `wholeStepFwd10T_stores_one`: an earlier union `wholeStepFwd10T_stores`, first branch, is an
  instance (it is typed in `simEnv10`, which grows into `simEnv10T`).
* **`wholeRunFwd10T`**: the same along V1 runs, given `GSetOk` along the run; `Plain10`,
  `MemsAligned10` and `simEnv10T` typing are invariants (`NoHost10` from the `simEnv10T`
  typing, `noHost10_of_typedT`).
* In `Sim10.Valid`: **`wholeRunFwd10CT`** (from `CoreTyped10`, so `GSetOk` along the run) and
  **`wholeRunFwd10InvT`**: round 4's `Task.wholeRunFwd10Inv` with the image of the invocation
  typed in `simEnv10T` instead of `simEnv10`, and the run read in `simEnv10T`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- Every V1 value is a typed `val` in `simEnv10T`. -/
theorem valTyped10T : ValTyped10T B := fun v => typedV10T (valTyped10 v)

/-- **Subject reduction in `simEnv10T`, for every V1 step.** -/
theorem typed10_step10T {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hc : Typed10 (simEnv10T B) hn c) (hg : GSetOk c.store c.frame c.code) :
    Typed10 (simEnv10T B) hn c' :=
  typed10_stepT valTyped10T h hc hg

/-- A state typed in `simEnv10T` has no host function. -/
theorem noHost10_of_typedT {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) : NoHost10 s :=
  fun i _ _ hs => not_typed_host10T (a := ⟨i⟩) hz hs

/-- **The forward 1.0 whole step in `simEnv10T` under one invariant**, without a hypothesis on
the successor: it is typed in `simEnv10T`, and the images are related by a step. -/
theorem wholeStepFwd10T_one {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') :=
  have hc' := typed10_step10T h hc hg
  ⟨hc', wholeStepFwd10T_inv hc hc' hpl hg hal h⟩

/-- **The first branch 's `wholeStepFwd10T_stores` is an instance of the one
invariant.** -/
theorem wholeStepFwd10T_stores_one {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (h : Step host c c') (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn c)
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) :
    SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') :=
  (wholeStepFwd10T_one (StoreAgree.typed10T_of_typed10 hc) hpl hg hal h).2

/-- **The forward 1.0 half in `simEnv10T` along a V1 run**, given `GSetOk` along the run. -/
theorem wholeRunFwd10T {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hal : MemsAligned10 c.store) (hg : ∀ d, Steps host c d → GSetOk d.store d.frame d.code)
    (h : Steps host c c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact ⟨hc, .refl⟩
  | @tail b d hcb hbd ih =>
    have hnh : NoHost10 c.store := noHost10_of_typedT (typedV_state_of_typed10T hc)
    have hal' : MemsAligned10 b.store := (memsAligned10_steps hcb hnh hal).2
    have hpl' : Plain10 b.code := plain10_steps hcb hpl
    have hstep := wholeStepFwd10T_one ih.1 hpl' (hg b hcb) hal' hbd
    exact ⟨hstep.1, ih.2.tail hstep.2⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 Plain10 MemsAligned10 wholeRunFwd10T
  noHost10_of_typedT typedV_state_of_typed10T plain10_invoke)

variable {H : Type}

/-- **The forward 1.0 half in `simEnv10T` along a V1 run from a `CoreTyped10` configuration.** -/
theorem wholeRunFwd10CT {hn : H → String} {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {c c' : Config H} (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn c)
    (hpl : Plain10 c.code) (hal : MemsAligned10 c.store) (hcore : CoreTyped10 c)
    (h : Steps host c c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r))) (configV hn c) (configV hn c') :=
  have hnh := noHost10_of_typedT (typedV_state_of_typed10T hc)
  wholeRunFwd10T hc hpl hal (fun _ hd => gsetOk_steps hd hnh hcore) h

/-- **Round 4's `Task.wholeRunFwd10Inv` in `simEnv10T`**: from an invocation whose image is typed
in `simEnv10T` (so the store may hold functions that store), with a valid Core store, fitting
arguments and `StoreWF`, every V1 run is a run of `simEnv10T (fwdB10 nd r)` between the
images. -/
theorem wholeRunFwd10InvT {hn : H → String} {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {s : Store H} {args : List Execution.Runtime.Value}
    {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hs : Execution.Core.StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value
      (args.map Execution.Runtime.Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  wholeRunFwd10CT hc (plain10_invoke args a) (memsAligned10_of_storeOk hs)
    (coreTyped10_invoke hs hinv hwf) h

end Silmaril.Wasm.SpecTec.Sim10.Valid
