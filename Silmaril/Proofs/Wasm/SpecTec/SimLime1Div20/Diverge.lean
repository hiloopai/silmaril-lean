module

public import Silmaril.Wasm.SpecTec.SimLime1Div.Thms

/-!
# Lime1 and 1.0 divergence into the SpecTec scripts

`SimLime1Div.divergeL1T` takes Lime1 divergence to the wasm-3.0 script. Here:

* `infinite_of_transGen`: if every configuration satisfying `Q` has a `Q`-successor reached by a
  non-empty `R`-run between the images, the image of a `Q`-configuration starts an infinite
  `R`-run;
* **`divergeL1_20`**: a diverging Lime1 configuration simulated by a 2.0 configuration that only
  reaches good configurations gives an infinite run of the corrected **wasm-2.0 script**,
  **conditional on the 2.0 forward obligation `Sim10.Fwd20`** (as `SimLime1.compositeL1`);
* **`divergeV1T`**: a diverging 1.0 configuration whose Lime1 image is simulated by a good Core
  configuration gives an infinite run of the **wasm-3.0 script**, with no hypothesis on the 1.0
  side (the copied `V1.Execution.Diverges.toLime`, then `divergeL1T`);
* `divergeV1_20`: the same into the 2.0 script, conditional on `Sim10.Fwd20`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20

open Silmaril Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim (HostFinite configV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

variable {H : Type}

/-- **Infinite runs from non-empty runs between images.** -/
theorem infinite_of_transGen {A B : Type} {R : B → B → Prop} (f : A → B) (Q : A → Prop)
    (step : ∀ x, Q x → ∃ y, Q y ∧ Relation.TransGen R (f x) (f y)) {x : A} (hx : Q x) :
    InfiniteTrace R (f x) := by
  refine InfiniteTrace.coinduct (fun z => ∃ y, Q y ∧ Relation.ReflTransGen R z (f y)) ?_
    ⟨x, hx, .refl⟩
  rintro z ⟨y, hy, hz⟩
  rcases Relation.ReflTransGen.cases_head hz with rfl | ⟨w, hzw, hw⟩
  · obtain ⟨y', hy', hT⟩ := step y hy
    obtain ⟨w, hzw, hw⟩ := Relation.TransGen.head'_iff.mp hT
    exact ⟨w, hzw, y', hy', hw⟩
  · exact ⟨w, hzw, y, hy, hw⟩

/-- The invariant of the 2.0 coinduction: a diverging Lime1 configuration, a simulating 2.0
configuration that only reaches good configurations. -/
def Inv20 (src : Lime1.Execution.HostSemantics H) (tgt : V2.Execution.HostSemantics H)
    (Good : V2.Execution.Config H → Prop)
    (x : Lime1.Execution.Config H × V2.Execution.Config H) : Prop :=
  Lime1.Execution.Diverges src x.1 ∧ Lime1.Execution.ToV2.Sim x.1 x.2 ∧
    Silmaril.Wasm.SpecTec.Sim10.RunGood20 tgt Good x.2

/-- **Lime1 divergence reaches the corrected wasm-2.0 script**, given `Sim10.Fwd20`. -/
theorem divergeL1_20 (hn : H → String) (src : Lime1.Execution.HostSemantics H)
    (tgt : V2.Execution.HostSemantics H) (B : Builtins) (Good : V2.Execution.Config H → Prop)
    (hosts : Lime1.Execution.ToV2.HostCompatible src tgt)
    (hF : Silmaril.Wasm.SpecTec.Sim10.Fwd20 hn tgt B Good)
    {a : Lime1.Execution.Config H} {c : V2.Execution.Config H}
    (hdiv : Lime1.Execution.Diverges src a) (hs : Lime1.Execution.ToV2.Sim a c)
    (hg : Silmaril.Wasm.SpecTec.Sim10.RunGood20 tgt Good c) :
    InfiniteTrace (SStepB (Silmaril.Wasm.SpecTec.Sim20.StepFix.simEnv20S B))
      (Silmaril.Wasm.SpecTec.Sim20.configV hn c) := by
  refine infinite_of_transGen (fun x => Silmaril.Wasm.SpecTec.Sim20.configV hn x.2)
    (Inv20 src tgt Good) ?_ (x := (a, c)) ⟨hdiv, hs, hg⟩
  rintro ⟨a₁, c₁⟩ ⟨hdiv₁, hs₁, hg₁⟩
  obtain ⟨a₂, hstep, hdiv₂⟩ := hdiv₁.unfold
  obtain ⟨c₂, hcc, hs₂⟩ := Lime1.Execution.Step.toV2 hosts hstep hs₁
  have hg₂ : Silmaril.Wasm.SpecTec.Sim10.RunGood20 tgt Good c₂ := fun e he =>
    hg₁ e (hcc.to_reflTransGen.trans he)
  exact ⟨(a₂, c₂), ⟨hdiv₂, hs₂, hg₂⟩, Silmaril.Wasm.SpecTec.Sim10.transGen_fwd20 hF hcc hg₁⟩

/-- **1.0 divergence reaches the wasm-3.0 script**, through Lime1 and Core 3.0. -/
theorem divergeV1T (hn : H → String) (hinj : Function.Injective hn)
    (host : Execution.Core.HostSemantics H) (hf : HostFinite host)
    (hh : Execution.Core.HostOk host) (src : V1.Execution.HostSemantics H)
    (hosts : Lime1.Execution.HostCompatible (src.mapCode V1.Func.toLime) host)
    {a : V1.Execution.Config H} {c : Execution.Core.Config H}
    (hdiv : V1.Execution.Diverges src a) (hs : Lime1.Execution.Sim a.toLime c)
    (hgood : Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c) :
    InfiniteTrace (Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.BStep hn host) (configV hn c) :=
  Silmaril.Proofs.Wasm.SpecTec.SimLime1Div.divergeL1T hn hinj host hf hh _ hosts
    (V1.Execution.Diverges.toLime
      (Execution.Runtime.HostSemantics.compatible_mapCode V1.Func.toLime src) hdiv) hs hgood

/-- 1.0 divergence reaches the corrected wasm-2.0 script, given `Sim10.Fwd20`. -/
theorem divergeV1_20 (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : V2.Execution.HostSemantics H) (B : Builtins) (Good : V2.Execution.Config H → Prop)
    (hosts : Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt)
    (hF : Silmaril.Wasm.SpecTec.Sim10.Fwd20 hn tgt B Good)
    {a : V1.Execution.Config H} {c : V2.Execution.Config H}
    (hdiv : V1.Execution.Diverges src a) (hs : Lime1.Execution.ToV2.Sim a.toLime c)
    (hg : Silmaril.Wasm.SpecTec.Sim10.RunGood20 tgt Good c) :
    InfiniteTrace (SStepB (Silmaril.Wasm.SpecTec.Sim20.StepFix.simEnv20S B))
      (Silmaril.Wasm.SpecTec.Sim20.configV hn c) :=
  divergeL1_20 hn _ tgt B Good hosts hF
    (V1.Execution.Diverges.toLime
      (Execution.Runtime.HostSemantics.compatible_mapCode V1.Func.toLime src) hdiv) hs hg

end Silmaril.Proofs.Wasm.SpecTec.SimLime1Div20
