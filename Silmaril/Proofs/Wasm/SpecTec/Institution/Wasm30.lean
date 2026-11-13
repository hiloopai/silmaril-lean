module

public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Defs
public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms

/-!
# The SpecTec specification institution and the Wasm atlas: wasm-3.0 transitions

* `modelChart_canon`: the step chart of the declarative canonical model is
  `Atlas.SpecTec.specChart env`.
* `mem_modelChart_iff`: a model's observations are the step facts it satisfies.
* `stepModel_facts`: round 6's whole-step theorem as a statement about the step facts of the
  backend canonical models `stepModel B`.
* `builtins`, `toModel`: on the deterministic part of the domain, a transition from the Core step
  chart to `modelChart (stepModel B)`, equal on `CfgRel`-respecting sentences;
  `sat_iff_stepModel` states it directly.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Wasm30

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim

/-- The step chart of `DDerives env (otherwise env)` is the atlas's SpecTec step chart. -/
theorem modelChart_canon (env : Env) :
    modelChart (canon env (otherwise env)) = Atlas.SpecTec.specChart env :=
  rfl

/-- A model observes `w` at `v` exactly when it satisfies the step fact `stepFact v w`, at any
conclusion reading. -/
theorem mem_modelChart_iff {S : Sig} (alts : Reading) (M : Model S) (v w : Value) :
    M.D "Step" "%~>%" [] (.tuple [v, w]) ↔ (stepFact v w).Sat alts M.env M.D :=
  Iff.rfl

variable {H : Type}

/-- **in the institution**: for every injective encoding, finite `HostOk` host and spec
profile there are primitives `B` such that, on valid `BoundedSel` configurations, Core steps are
matched (up to Core's choice and `ConfigEq`) by step facts of the backend canonical model
`stepModel B`, and every step fact of `stepModel B` from the image of `c` is the image of a Core
step up to `ConfigEq`. -/
theorem stepModel_facts (hn : H → String) (hinj : Function.Injective hn)
    (host : HostSemantics H) (hf : HostFinite host) (hh : HostOk host) (nd : Bool)
    (r : RelaxedChoice) : ∃ B : Builtins,
      (∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → Round5.Target.BoundedSel c →
        (∀ c₁, Step (Profile.spec nd r) host c c₁ → Round5.Target.BoundedSel c₁) →
        Step (Profile.spec nd r) host c c' →
        ∃ c'', Step (Profile.spec nd r) host c c'' ∧
          ((∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') → c'' = c') ∧
          ∃ d', Bwd.ConfigEq c'' d' ∧ (stepFact (configV hn c) (configV hn d')).Sat backend
            (stepModel B).env (stepModel B).D) ∧
      (∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
        Round5.Target.BoundedSel c →
        (stepFact (configV hn c) w).Sat backend (stepModel B).env (stepModel B).D →
        ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c') :=
  Round6.Int.wholeStepValidR_backend H hn hinj host hf hh nd r

/-- The primitives of `stepModel_facts`. -/
noncomputable def builtins (hn : H → String) (hinj : Function.Injective hn)
    (host : HostSemantics H) (hf : HostFinite host) (hh : HostOk host) (nd : Bool)
    (r : RelaxedChoice) : Builtins :=
  Classical.choose (stepModel_facts hn hinj host hf hh nd r)

section Transition

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- On `DomDet`, Core successors are step facts of `stepModel` up to `CfgRel`. -/
theorem fwd_upto (c : Config H) (hc : DomDet (Profile.spec nd r) host c) (u : Unit) :
    ∀ b ∈ Atlas.SpecTec.coreObs (Profile.spec nd r) host hn c u,
      ∃ b' ∈ {w | (stepModel (builtins hn hinj host hf hh nd r)).D "Step" "%~>%" []
          (.tuple [configV hn c, w])}, Atlas.SpecTec.CfgRel hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  have hspec := (Classical.choose_spec (stepModel_facts hn hinj host hf hh nd r)).1
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc.1
  obtain ⟨c'', _, huniq, d', he, hd⟩ := hspec c c' ts hok hb hsucc hs
  have hc'' : c'' = c' := huniq (fun c₃ h₃ => hc.2 c₃ c' h₃ hs)
  exact ⟨configV hn d', hd, c', d', hc'' ▸ he, rfl, rfl⟩

/-- On `DomDet`, step facts of `stepModel` are Core successors up to `CfgRel`. -/
theorem bwd_upto (c : Config H) (hc : DomDet (Profile.spec nd r) host c) (u : Unit) :
    ∀ b' ∈ {w | (stepModel (builtins hn hinj host hf hh nd r)).D "Step" "%~>%" []
          (.tuple [configV hn c, w])},
      ∃ b ∈ Atlas.SpecTec.coreObs (Profile.spec nd r) host hn c u,
        Atlas.SpecTec.CfgRel hn b b' := by
  intro w hw
  have hspec := (Classical.choose_spec (stepModel_facts hn hinj host hf hh nd r)).2
  obtain ⟨⟨ts, hok⟩, hb, _⟩ := hc.1
  obtain ⟨c', d', he, rfl, hs⟩ := hspec c ts w hok hb hw
  exact ⟨configV hn c', ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

end Transition

/-- **The wasm-3.0 semi-comorphism**: on the deterministic part 's domain, the Core
step chart maps to the step chart of the backend canonical model of the fixed wasm-3.0 script,
equal on every sentence that respects `CfgRel` (configurations up to `CALL_REF` annotations). -/
noncomputable def toModel (hn : H → String) (hinj : Function.Injective hn)
    (host : HostSemantics H) (hf : HostFinite host) (hh : HostOk host) (nd : Bool)
    (r : RelaxedChoice) :
    Transition (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (DomDet (Profile.spec nd r) host))
      (modelChart (stepModel (builtins hn hinj host hf hh nd r))) :=
  BTrans.ofUpTo (Atlas.SpecTec.CfgRel hn) (configV hn) id (fun _ _ => trivial)
    (fwd_upto (hinj := hinj) (hf := hf) (hh := hh)) (bwd_upto (hinj := hinj) (hf := hf) (hh := hh))

/-- **The semi-comorphism, stated directly**: a `CfgRel`-respecting step sentence holds of a
configuration in `DomDet` in Core iff it holds of its encoding in `stepModel`. -/
theorem sat_iff_stepModel (hn : H → String) (hinj : Function.Injective hn)
    (host : HostSemantics H) (hf : HostFinite host) (hh : HostOk host) (nd : Bool)
    (r : RelaxedChoice) {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {s : BSen Unit Value} (hs : s.Respects (Atlas.SpecTec.CfgRel hn)) :
    (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (DomDet (Profile.spec nd r) host)).Sat c s ↔
      (modelChart (stepModel (builtins hn hinj host hf hh nd r))).Sat (configV hn c) s :=
  BSen.sat_iff_upto (fwd_upto (hinj := hinj) (hf := hf) (hh := hh) c hc)
    (bwd_upto (hinj := hinj) (hf := hf) (hh := hh) c hc) hs

end Silmaril.Wasm.SpecTec.Institution.Wasm30
