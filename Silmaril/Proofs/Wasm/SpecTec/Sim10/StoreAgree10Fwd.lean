module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreAgree10Derive
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdValid
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdBoth

/-!
# The forward 1.0 results, at the corrected script `simEnv10T`

Typing grows from `simEnv10` to `simEnv10T` (`typRepair10T`) and every step moves
(`sstepB10T_of_sstepB10`), so every forward theorem of the 1.0 route holds with its conclusion
read in `simEnv10T`, with no new hypothesis:

* `typed10T_of_typed10`: a configuration typed in `simEnv10` is typed in `simEnv10T`;
* `wholeStepFwd10T`: an earlier `Task.wholeStepFwd10`, concluding in `simEnv10T`;
* `wholeRunFwd10CT`, `wholeRunFwd10InvT`: an earlier `Task.wholeRunFwd10C` and
  `Task.wholeRunFwd10Inv`, concluding in `simEnv10T`;
* `wholeStep10_fwdT`: the forward half of `wholeStep10_both`, in `simEnv10T`.

These cover the configurations typed in `simEnv10`, which hold no `STORE`. The store rules
themselves, at configurations typed only in `simEnv10T`, are in `StoreTop10T` and `StoreCtx10T`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Store Config HostSemantics Step Steps)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10 Plain10 MemsAligned10)
open Silmaril.Wasm.SpecTec.Sim10.Valid (CoreTyped10 invokeCfg10 coreStore10)

variable {H : Type} {hn : H → String}

/-- **Typing grows**: a configuration typed in `simEnv10` is typed in `simEnv10T`. -/
theorem typed10T_of_typed10 {B : Builtins} {c : Config H} (h : Typed10 (simEnv10 B) hn c) :
    Typed10 (simEnv10T B) hn c :=
  Sim20.StoreAgree.hasTyp_repair (envSame10T B) (typRepair10T B) h

/-- **The forward 1.0 whole step, in `simEnv10T`.** -/
theorem wholeStepFwd10T {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {c c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') :=
  let h' := Whole.wholeStepFwd10 H hn host nd r c c' hc hpl hg hal h
  ⟨typed10T_of_typed10 h'.1, sstepB10T_of_sstepB10 h'.2⟩

/-- **The forward 1.0 run, in `simEnv10T`**, from Core typing. -/
theorem wholeRunFwd10CT {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {c c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hal : MemsAligned10 c.store) (hcore : CoreTyped10 c) (h : Steps host c c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r))) (configV hn c) (configV hn c') :=
  let h' := Valid.wholeRunFwd10C H hn host nd r c c' hc hpl hal hcore h
  ⟨typed10T_of_typed10 h'.1, rtc_sstepB10T_of_sstepB10 h'.2⟩

/-- **The forward 1.0 run from an invocation, in `simEnv10T`.** -/
theorem wholeRunFwd10InvT {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {s : Store H}
    {args : List Execution.Runtime.Value} {a : Execution.Runtime.FuncAddr} {c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 s args a))
    (hs : Execution.Core.StoreOk (coreStore10 s))
    (hi : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Execution.Runtime.Value.toCore))
    (hw : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (invokeCfg10 s args a)) (configV hn c') :=
  let h' := Valid.wholeRunFwd10Inv H hn host nd r s args a c' hc hs hi hw h
  ⟨typed10T_of_typed10 h'.1, rtc_sstepB10T_of_sstepB10 h'.2⟩

/-- **The forward half of `wholeStep10_both`, in `simEnv10T`.** -/
theorem wholeStep10_fwdT {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {c c' : Config H}
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn c) (hg : GoodV1 c) (hpl : Plain10 c.code)
    (hal : MemsAligned10 c.store) (h : Step host c c') :
    SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') :=
  (wholeStepFwd10T hc hpl hg.2.2.2 hal h).2

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
