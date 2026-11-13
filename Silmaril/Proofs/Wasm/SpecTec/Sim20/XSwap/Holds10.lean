module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Step10
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.XSwap.Holds
public import Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.Thms

/-!
# the 1.0 `$utf8` forward theorem

* **`swapStep10_holds`**: the leaf `Utf8Swap10.Task.swapStep10`, from `Typ10.sstepB_swap` at
  `EraseAll.hyps10`.
* **`stepFwd10U_holds`**: every V1 step from a configuration typed in `utf8Env10T (fwdB10 nd r)`
  (export names may be non-empty) that satisfies round 4's other invariants is a step of
  `utf8Env10T` between the images; `wholeRunFwd10U_holds`: so is every run.
* **`unstripStep10_inv`**: round 8's leg 3 (`Utf8Strip10.Task.unstripStep10`) under round 4's
  invariants. The frozen statement assumes only `Typed10` of the source; it is not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Config HostSemantics Step Steps)
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk Typed10)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T)

/-- **The leaf `Utf8Swap10.Task.swapStep10` holds.** -/
theorem swapStep10_holds : Sim10.Utf8Swap10.Task.swapStep10 := by
  intro nd r τ hinv K hK v w h
  let _ : XTau := tauOf τ hinv
  have hS := Typ10.sstepB_swap (EraseAll.hyps10 nd r) (K := K) hK hinv h
  rwa [swapX_eq_swapV τ hinv, swapX_eq_swapV τ hinv] at hS

variable {H : Type} {hn : H → String}

/-- **The 1.0 forward step at non-empty export names.** -/
theorem stepFwd10U_holds {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    SStepB (utf8Env10T (fwdB10 nd r)) (Sim10.configV hn c) (Sim10.configV hn c') :=
  Sim10.Utf8Swap10.stepFwd10U_of_swapStep10 swapStep10_holds hc hpl hg hal h

/-- **Leg 3 for 1.0, under round 4's invariants.** -/
theorem unstripStep10_inv {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c')
    (_ : SStepB (utf8Env10T (fwdB10 nd r)) (Sim10.configV hn (Sim10.Utf8Strip10.stripConfig10 c))
      (Sim10.configV hn (Sim10.Utf8Strip10.stripConfig10 c'))) :
    SStepB (utf8Env10T (fwdB10 nd r)) (Sim10.configV hn c) (Sim10.configV hn c') :=
  stepFwd10U_holds hc hpl hg hal h

/-- **The 1.0 forward run at non-empty export names.** -/
theorem wholeRunFwd10U_holds {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hal : MemsAligned10 c.store) (hg : ∀ d, Steps host c d → GSetOk d.store d.frame d.code)
    (h : Steps host c c') :
    Typed10 (utf8Env10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (utf8Env10T (fwdB10 nd r))) (Sim10.configV hn c)
        (Sim10.configV hn c') := by
  induction h with
  | refl => exact ⟨hc, .refl⟩
  | @tail b d hcb hbd ih =>
    have hnh := Sim10.Utf8Strip10.noHost10_of_typedU (Sim10.Utf8Fix.bytesB10_utf8 _) hc
    have hal' : MemsAligned10 b.store := (Sim10.Whole.memsAligned10_steps hcb hnh hal).2
    have hpl' : Plain10 b.code := Sim10.Whole.plain10_steps hcb hpl
    exact ⟨Sim10.Utf8Strip10.stepFwd10U_typed ih.1 hpl' (hg b hcb) hal' hbd,
      .tail ih.2 (stepFwd10U_holds ih.1 hpl' (hg b hcb) hal' hbd)⟩

end Silmaril.Wasm.SpecTec.Sim20.XSwap
