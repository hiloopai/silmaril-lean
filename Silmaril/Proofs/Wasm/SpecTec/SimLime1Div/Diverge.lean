module

public import Silmaril.Wasm.SpecTec.SimLime1.Thms

/-!
# Lime1 divergence reaches the wasm-3.0 script

`compositeL1T` matches one Lime1 step by a non-empty run of wasm-3.0 backend steps, and
`compositeL1_steps` matches finite Lime1 runs. This file adds infinite runs: a diverging Lime1
configuration, simulated by a Core configuration that only reaches good configurations, gives an
**infinite run of wasm-3.0 backend steps** from the encoding of that Core configuration.

The proof chains Round 6's one-step forward theorem along its own invariant `SimRel`, as
`Sim20.stepsT_sim` does for finite runs:

* the copied `Lime1.Execution.Diverges.toCore` turns the Lime1 trace into a Core trace;
* `step_inv`: from a Core configuration `c₁` that diverges and only reaches good configurations,
  with `SimRel c₁ d₁`, one Core step `c₁ → c₂` gives a non-empty backend run from
  `configV d₁` to `configV d₂` with `SimRel c₂ d₂`, and `c₂` again diverges and only reaches good
  configurations;
* `coreDiv_script`: `InfiniteTrace.coinduct` over the invariant "a backend run reaches the
  encoding of such a `d₁`" peels one backend step at a time.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.SimLime1Div

open Silmaril Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (HostFinite configV)
open Silmaril.Wasm.SpecTec.Sim.Round4 (SimRel)
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)

variable {H : Type}

/-- The wasm-3.0 backend step at Round 6's builtins. -/
abbrev BStep (hn : H → String) (host : Execution.Core.HostSemantics H) :=
  Silmaril.Wasm.SpecTec.Sim.Round6.Int.backend.step (BI Profile.spec hn host)

/-- The invariant of the coinduction: a Core configuration that diverges and only reaches good
configurations, related by `SimRel` to `d`. -/
def Inv (hn : H → String) (host : Execution.Core.HostSemantics H)
    (c d : Execution.Core.Config H) : Prop :=
  Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c ∧
    Execution.Core.Diverges Profile.spec host c ∧ SimRel (BI Profile.spec hn host) hn c d

/-- A configuration that only reaches good configurations is `SimRel`-related to itself. -/
theorem simRel_self (hn : H → String) {host : Execution.Core.HostSemantics H}
    {c : Execution.Core.Config H} (hg : Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c) :
    SimRel (BI Profile.spec hn host) hn c c := by
  obtain ⟨⟨ts, hok⟩, hb, -⟩ := Silmaril.Wasm.SpecTec.Sim20.runGood_parts hg
  exact ⟨Silmaril.Wasm.SpecTec.Sim.Bwd.ConfigEq.refl _,
    Silmaril.Wasm.SpecTec.Sim.Round5.Target.typed_of_configOk_sel _ hn hok (hb _ .refl)⟩

/-- **One Core step of a diverging good configuration is a non-empty backend run**, and the
invariant is kept. -/
theorem step_inv (hn : H → String) (hinj : Function.Injective hn)
    {host : Execution.Core.HostSemantics H} (hf : HostFinite host)
    (hh : Execution.Core.HostOk host) {c d : Execution.Core.Config H} (hI : Inv hn host c d) :
    ∃ c' d', Inv hn host c' d' ∧
      Relation.TransGen (BStep hn host) (configV hn d) (configV hn d') := by
  obtain ⟨hg, hdiv, hrel⟩ := hI
  obtain ⟨c', hstep, hdiv'⟩ := hdiv.unfold
  obtain ⟨⟨ts, hok⟩, hb, hd⟩ := Silmaril.Wasm.SpecTec.Sim20.runGood_parts hg
  obtain ⟨d', hrel', hT⟩ := Silmaril.Wasm.SpecTec.Sim20.stepsT_sim hinj hf hh
    (Silmaril.Wasm.SpecTec.Sim.Round6.Int.openR_backend hinj hf hh) hok hb hrel
    (Silmaril.Wasm.SpecTec.Sim20.detTrans_of_trans (.single hstep) hd)
  exact ⟨c', d', ⟨fun e he => hg e (.head hstep he), hdiv', hrel'⟩, hT⟩

/-- **A diverging Core configuration that only reaches good configurations has an infinite run
of wasm-3.0 backend steps** from its encoding. -/
theorem coreDiv_script (hn : H → String) (hinj : Function.Injective hn)
    {host : Execution.Core.HostSemantics H} (hf : HostFinite host)
    (hh : Execution.Core.HostOk host) {c : Execution.Core.Config H}
    (hdiv : Execution.Core.Diverges Profile.spec host c)
    (hg : Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c) :
    InfiniteTrace (BStep hn host) (configV hn c) := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ c₁ d₁, Inv hn host c₁ d₁ ∧ Relation.ReflTransGen (BStep hn host) x (configV hn d₁))
    ?_ ⟨c, c, ⟨hg, hdiv, simRel_self hn hg⟩, .refl⟩
  rintro x ⟨c₁, d₁, hI, hx⟩
  rcases Relation.ReflTransGen.cases_head hx with rfl | ⟨y, hxy, hy⟩
  · obtain ⟨c₂, d₂, hI₂, hT⟩ := step_inv hn hinj hf hh hI
    obtain ⟨y, hxy, hy⟩ := Relation.TransGen.head'_iff.mp hT
    exact ⟨y, hxy, c₂, d₂, hI₂, hy⟩
  · exact ⟨y, hxy, c₁, d₁, hI, hy⟩

/-- **Lime1 divergence reaches the wasm-3.0 script**: a diverging Lime1 configuration simulated
by a Core configuration that only reaches good configurations gives an infinite run of wasm-3.0
backend steps from the encoding of that Core configuration. No hypothesis on the Lime1 side. -/
theorem divergeL1T (hn : H → String) (hinj : Function.Injective hn)
    (host : Execution.Core.HostSemantics H) (hf : HostFinite host)
    (hh : Execution.Core.HostOk host) (src : Lime1.Execution.HostSemantics H)
    (hosts : Lime1.Execution.HostCompatible src host)
    {a : Lime1.Execution.Config H} {c : Execution.Core.Config H}
    (hdiv : Lime1.Execution.Diverges src a) (hs : Lime1.Execution.Sim a c)
    (hgood : Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c) :
    InfiniteTrace (BStep hn host) (configV hn c) :=
  coreDiv_script hn hinj hf hh (Lime1.Execution.Diverges.toCore hosts hdiv hs) hgood

end Silmaril.Proofs.Wasm.SpecTec.SimLime1Div
