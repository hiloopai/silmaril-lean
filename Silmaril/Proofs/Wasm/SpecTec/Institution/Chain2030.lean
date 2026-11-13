module

public import Silmaril.Wasm.SpecTec.Institution.Chain2030.Defs
public import Silmaril.Wasm.SpecTec.Institution.Wasm20.Thms
public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Thms

/-!
# The SpecTec specification institution: the chain wasm-2.0 → wasm-3.0

* `blind_sat`, `blind_existential`, `blind_respects`, `blind_rename`: a value-blind sentence
  only asks which calls have an observation, so it transfers along any map that keeps
  observations nonempty, and it respects every relation.
* `core_step_of_v2_step`: a V2 step from a configuration gives a Core step from every Core
  configuration simulating it (the first step of `Step.toCore`'s run).
* `toV2`: the wasm-2.0 model to V2, on pairs (`model_subset_v2`), preserving existential
  sentences; it is `toModelSE` read from the model's side.
* `toCore`: V2 to the Core step chart on `DomDet`, along the second component, preserving
  value-blind sentences.
* `chain`: `toV2`, `toCore` and `Wasm30.toModel` composed: **the wasm-2.0 model to the wasm-3.0
  model**, preserving value-blind sentences. `progress_chain`, `stuck_chain`: stated directly.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Chain2030

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Institution

variable {H : Type}

/-! ## Value-blind sentences -/

/-- **A value-blind sentence transfers along nonempty observations.** -/
theorem blind_sat {obs obs' : Unit → Set Value} (h : ∀ u, (obs u).Nonempty → (obs' u).Nonempty) :
    ∀ {s : BSen Unit Value}, Blind s → s.Sat obs → s.Sat obs'
  | .always _ _, hb, _ => hb.elim
  | .may u _, hb, ⟨b, hm, _⟩ => by
    obtain ⟨b', hb'⟩ := h u ⟨b, hm⟩
    exact ⟨b', hb', hb b'⟩
  | .and _ _, hb, hs => ⟨blind_sat h hb.1 hs.1, blind_sat h hb.2 hs.2⟩
  | .top, _, _ => trivial

/-- Value-blind sentences are existential. -/
theorem blind_existential : ∀ {s : BSen Unit Value}, Blind s → s.Existential
  | .always _ _, hb => hb.elim
  | .may _ _, _ => trivial
  | .and _ _, hb => ⟨blind_existential hb.1, blind_existential hb.2⟩
  | .top, _ => trivial

/-- Value-blind sentences respect every relation. -/
theorem blind_respects (R : Value → Value → Prop) :
    ∀ {s : BSen Unit Value}, Blind s → s.Respects R
  | .always _ _, hb => hb.elim
  | .may _ _, hb => fun b b' _ => ⟨fun _ => hb b', fun _ => hb b⟩
  | .and _ _, hb => ⟨blind_respects R hb.1, blind_respects R hb.2⟩
  | .top, _ => trivial

/-- Renaming keeps value-blindness. -/
theorem blind_rename (σ : Unit → Unit) : ∀ {s : BSen Unit Value}, Blind s → Blind (s.rename σ)
  | .always _ _, hb => hb.elim
  | .may _ _, hb => hb
  | .and _ _, hb => ⟨blind_rename σ hb.1, blind_rename σ hb.2⟩
  | .top, _ => trivial

/-- `progress` is value-blind. -/
theorem blind_progress : Blind Wasm20.progress := fun _ => trivial

/-! ## One V2 step gives a Core step -/

/-- **A V2 step gives a Core step** from every simulating Core configuration: the first step of
the nonempty Core run of `Step.toCore`. -/
theorem core_step_of_v2_step {P : Profile} {host : Silmaril.Wasm.V2.Execution.HostSemantics H}
    {tgt : Silmaril.Wasm.Execution.Core.HostSemantics H}
    (hc : Silmaril.Wasm.V2.Execution.HostCompatible host tgt)
    {a b : Silmaril.Wasm.V2.Execution.Config H} {c : Silmaril.Wasm.Execution.Core.Config H}
    (hs : Silmaril.Wasm.V2.Execution.Step P host a b) (hsim : Silmaril.Wasm.V2.Execution.Sim a c) :
    ∃ c₁, Silmaril.Wasm.Execution.Core.Step P tgt c c₁ := by
  obtain ⟨c', hrun, -⟩ := Silmaril.Wasm.V2.Execution.Step.toCore hc hs hsim
  obtain ⟨c₁, h₁, -⟩ := Relation.TransGen.head'_iff.1 hrun
  exact ⟨c₁, h₁⟩

/-! ## The three transitions -/

/-- **The wasm-2.0 model to V2, on pairs**: on `DomS` the model's step facts are V2
observations, so existential sentences are preserved. -/
noncomputable def toV2 (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String) :
    Transition (m20Chart P tgt hn) (v2PChart P host tgt hn) :=
  BTrans.ofSubsetExist id id (fun _ h => h)
    (fun p hp u => Wasm20.model_subset_v2 P host hn p.1 hp.1 u)

/-- **V2 to Core, along the simulation**: a V2 successor of the first component gives a Core
successor of the second, so value-blind sentences are preserved. -/
def toCore (P : Profile) (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H) (hn : H → String)
    (hc : Silmaril.Wasm.V2.Execution.HostCompatible host tgt) :
    Transition (v2PChart P host tgt hn)
      (Atlas.SpecTec.coreChart P tgt hn (Wasm30.DomDet P tgt)) where
  pt := Prod.snd
  sen := id
  cls := Blind
  dir := .preserves
  dom_pt _ hp := hp.2.2
  sat p _ hp hb := by
    refine ⟨fun _ h => blind_sat (fun u hne => ?_) hb h, fun e => absurd e (by decide)⟩
    obtain ⟨_, c', hs, -⟩ := hne
    obtain ⟨c₁, h₁⟩ := core_step_of_v2_step hc hs hp.2.1
    exact ⟨_, c₁, h₁, rfl⟩

section Chain

variable (hn : H → String) (hinj : Function.Injective hn)
  (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
  (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H)
  (hf : Silmaril.Wasm.SpecTec.Sim.HostFinite tgt) (hh : Silmaril.Wasm.Execution.Core.HostOk tgt)
  (nd : Bool) (r : RelaxedChoice)
  (hc : Silmaril.Wasm.V2.Execution.HostCompatible host tgt)

/-- **The chain wasm-2.0 → wasm-3.0**: `toV2`, `toCore` and `Wasm30.toModel` composed, from the
step chart of the wasm-2.0 model (on pairs in `PairDom`) to the step chart of the wasm-3.0 model,
preserving value-blind sentences. -/
noncomputable def chain :
    Transition (m20Chart (Profile.spec nd r) tgt hn)
      (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))) :=
  ((toV2 (Profile.spec nd r) host tgt hn).comp
      ((toCore (Profile.spec nd r) host tgt hn hc).comp
        (Wasm30.toModel hn hinj tgt hf hh nd r))).restrictCls Blind
    fun _ hb => ⟨blind_existential hb, blind_rename id hb,
      blind_respects _ (blind_rename id hb)⟩

/-- The chain preserves. -/
theorem chain_dir : (chain hn hinj host tgt hf hh nd r hc).dir = Dir.preserves := rfl

/-- The chain's point map is the second component, encoded. -/
theorem chain_pt (p : Pair H) :
    (chain hn hinj host tgt hf hh nd r hc).pt p = Silmaril.Wasm.SpecTec.Sim.configV hn p.2 := rfl

end Chain

/-- **Progress, from the wasm-2.0 model to the wasm-3.0 model**: on `PairDom`, if the wasm-2.0
model steps from the image of the V2 configuration, the wasm-3.0 model steps from the image of
the Core configuration. -/
theorem progress_chain (hn : H → String) (hinj : Function.Injective hn)
    (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (hf : Silmaril.Wasm.SpecTec.Sim.HostFinite tgt) (hh : Silmaril.Wasm.Execution.Core.HostOk tgt)
    (nd : Bool) (r : RelaxedChoice) (hc : Silmaril.Wasm.V2.Execution.HostCompatible host tgt)
    {p : Pair H} (hp : PairDom (Profile.spec nd r) tgt p)
    (h : (m20Chart (Profile.spec nd r) tgt hn).Sat p Wasm20.progress) :
    (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn p.2) Wasm20.progress :=
  ((chain hn hinj host tgt hf hh nd r hc).sat p Wasm20.progress hp blind_progress).1 rfl h

/-- **Stuckness, from the wasm-3.0 model to the wasm-2.0 model**: the contrapositive. -/
theorem stuck_chain (hn : H → String) (hinj : Function.Injective hn)
    (host : Silmaril.Wasm.V2.Execution.HostSemantics H)
    (tgt : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (hf : Silmaril.Wasm.SpecTec.Sim.HostFinite tgt) (hh : Silmaril.Wasm.Execution.Core.HostOk tgt)
    (nd : Bool) (r : RelaxedChoice) (hc : Silmaril.Wasm.V2.Execution.HostCompatible host tgt)
    {p : Pair H} (hp : PairDom (Profile.spec nd r) tgt p)
    (h : (Wasm30.modelChart (Wasm30.stepModel (Wasm30.builtins hn hinj tgt hf hh nd r))).Sat
      (Silmaril.Wasm.SpecTec.Sim.configV hn p.2) Wasm20.stuckSen) :
    (m20Chart (Profile.spec nd r) tgt hn).Sat p Wasm20.stuckSen := fun w hw =>
  let ⟨w', hw', _⟩ := progress_chain hn hinj host tgt hf hh nd r hc hp ⟨w, hw, trivial⟩
  h w' hw'

end Silmaril.Wasm.SpecTec.Institution.Chain2030
