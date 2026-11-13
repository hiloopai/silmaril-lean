module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Nondet

/-!
# The wasm-3.0 semi-comorphism off the deterministic domain: transitions

Everything is generic in primitives `B` with `Halves B hn P host`; `halves_BI` and
`halves_builtins` supply them at `Profile.spec nd r` (injective `hn`, finite `HostOk` host).

* `toModelUniv`, `toModelExist`: on all of `Dom`, `stepModel B` keeps Core's universal and
  reflects into Core its existential `CfgRel`-respecting sentences (directions `preserves`,
  `reflects`). Backward half only.
* `sat_iff_indep`: **two-sided, pointwise**: on `Dom`, a `CfgRel`-respecting sentence whose atoms
  cannot tell Core's successors of `c` apart holds in Core iff it holds in `stepModel B`.
* `toModelUpTo K`: **two-sided, uniform**: on `DomUpTo K` the transition is `equal` on sentences
  respecting `CfgRel` and `K`. `toModelUpTo_eq_sat` recovers `Wasm30.sat_iff_stepModel` (`K := Eq`,
  `DomDet ⊆ DomUpTo Eq`); `canStep_iff` is `K := ⊤` (progress is two-sided on all of `Dom`).
* `sat_iff_primitives`: the fragment does not depend on the admissible primitives.
* `mstep_iff_backend`: `stepModel B`'s step facts are `Round6.Int.backend`'s steps, the
  observations of `Atlas.SpecTecR6.readChart Round6.Int.backend B` (by `Iff.rfl`).
* `unionObs_bwd`, `unionObs_nonempty`, `toUnion`: the set-valued model; under the frozen
  `Task.choiceCover` it is equal to Core on every `CfgRel`-respecting sentence.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Nondet

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30

variable {H : Type} {hn : H → String} {host : HostSemantics H} {P : Profile} {B : Builtins}

/-- The Core step chart on a fragment `D`. -/
local notation "CC" D => Atlas.SpecTec.coreChart P host hn D

/-- **`stepModel B`'s step facts are the backend reading's steps.** So `modelChart (stepModel B)`
has the observations of `Atlas.SpecTecR6.readChart Round6.Int.backend B`. -/
theorem mstep_iff_backend (v w : Value) : MStep B v w ↔ Round6.Int.backend.step B v w :=
  Iff.rfl

/-! ## One-sided, on all of `Dom` -/

/-- **Core safety holds in `stepModel B`** on all of `Dom`: universal `CfgRel`-respecting
sentences. -/
def toModelUniv (hB : Halves B hn P host) :
    Transition (CC (Dom P host)) (modelChart (stepModel B)) where
  pt := configV hn
  sen s := s
  cls s := s.Universal ∧ s.Respects (Atlas.SpecTec.CfgRel hn)
  dir := .preserves
  dom_pt _ _ := trivial
  sat c _ hc hs := ⟨fun _ h => sat_upto_univ' (bwd_rel hB hc) hs.1 hs.2 h,
    fun e => absurd e (by decide)⟩

/-- **`stepModel B`'s witnesses are Core witnesses** on all of `Dom`: existential
`CfgRel`-respecting sentences. -/
def toModelExist (hB : Halves B hn P host) :
    Transition (CC (Dom P host)) (modelChart (stepModel B)) where
  pt := configV hn
  sen s := s
  cls s := s.Existential ∧ s.Respects (Atlas.SpecTec.CfgRel hn)
  dir := .reflects
  dom_pt _ _ := trivial
  sat c _ hc hs := ⟨fun e => absurd e (by decide),
    fun _ h => sat_upto_exist' (bwd_rel hB hc) hs.1 hs.2 h⟩

/-! ## Two-sided -/

/-- **Two-sided, pointwise**: on `Dom`, every `CfgRel`-respecting sentence that is
choice-independent on Core's successors of `c` holds in Core iff it holds in `stepModel B`. -/
theorem sat_iff_indep (hB : Halves B hn P host) {c : Config H} (hc : Dom P host c)
    {s : BSen Unit Value} (hs : s.Respects (Atlas.SpecTec.CfgRel hn))
    (hi : Indep (Atlas.SpecTec.coreObs P host hn c) s) :
    (CC (Dom P host)).Sat c s ↔ (modelChart (stepModel B)).Sat (configV hn c) s :=
  sat_iff_resolve (fwd_resolve hB hc) (bwd_rel hB hc) hs hi

/-- **Two-sided, uniform**: on `DomUpTo K`, equal on the sentences that respect `CfgRel` and
`K`. -/
def toModelUpTo (K : Value → Value → Prop) (hB : Halves B hn P host) :
    Transition (CC (DomUpTo K P host hn)) (modelChart (stepModel B)) where
  pt := configV hn
  sen s := s
  cls s := s.Respects (Atlas.SpecTec.CfgRel hn) ∧ s.Respects K
  dir := .equal
  dom_pt _ _ := trivial
  sat _ _ hc hs :=
    have e := sat_iff_indep hB hc.1 hs.1 (indep_of_domUpTo hc hs.2)
    ⟨fun _ => e.1, fun _ => e.2⟩

theorem toModelUpTo_dir (K : Value → Value → Prop) (hB : Halves B hn P host) :
    (toModelUpTo K hB).dir = .equal := rfl

/-- **`DomDet` again**: at `K := Eq` the uniform statement is `Wasm30.sat_iff_stepModel`'s, for
any admissible primitives. -/
theorem sat_iff_of_domDet (hB : Halves B hn P host) {c : Config H} (hc : DomDet P host c)
    {s : BSen Unit Value} (hs : s.Respects (Atlas.SpecTec.CfgRel hn)) :
    (CC (DomDet P host)).Sat c s ↔ (modelChart (stepModel B)).Sat (configV hn c) s :=
  sat_iff_indep hB hc.1 hs (indep_of_domUpTo (domUpTo_eq_of_domDet hc) (respects_eq s))

/-- **Progress is two-sided on all of `Dom`** (`K := ⊤`): Core can step from `c` iff
`stepModel B` has a step fact from `c`'s image. -/
theorem canStep_iff (hB : Halves B hn P host) {c : Config H} (hc : Dom P host c) :
    (∃ c', Step P host c c') ↔ ∃ w, MStep B (configV hn c) w := by
  have e := sat_iff_indep hB hc (s := .may () fun _ => True) (fun _ _ _ => Iff.rfl)
    (fun _ _ _ _ => Iff.rfl)
  constructor
  · rintro ⟨c', hs⟩
    obtain ⟨w, hw, -⟩ := e.1 ⟨configV hn c', ⟨c', hs, rfl⟩, trivial⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨_, ⟨c', hs, -⟩, -⟩ := e.2 ⟨w, hw, trivial⟩
    exact ⟨c', hs⟩

/-- **Stuckness is two-sided on all of `Dom`.** -/
theorem stuck_iff (hB : Halves B hn P host) {c : Config H} (hc : Dom P host c) :
    (∀ c', ¬ Step P host c c') ↔ ∀ w, ¬ MStep B (configV hn c) w := by
  have e := canStep_iff hB hc
  constructor
  · intro h w hw
    obtain ⟨c', hs⟩ := e.2 ⟨w, hw⟩
    exact h c' hs
  · intro h c' hs
    obtain ⟨w, hw⟩ := e.1 ⟨c', hs⟩
    exact h w hw

/-- **The fragment does not depend on the primitives**: two admissible choices satisfy the same
choice-independent `CfgRel`-respecting sentences at every point of `Dom`. -/
theorem sat_iff_primitives {B₁ B₂ : Builtins} (h₁ : Halves B₁ hn P host)
    (h₂ : Halves B₂ hn P host) {c : Config H} (hc : Dom P host c) {s : BSen Unit Value}
    (hs : s.Respects (Atlas.SpecTec.CfgRel hn))
    (hi : Indep (Atlas.SpecTec.coreObs P host hn c) s) :
    (modelChart (stepModel B₁)).Sat (configV hn c) s ↔
      (modelChart (stepModel B₂)).Sat (configV hn c) s :=
  (sat_iff_indep h₁ hc hs hi).symm.trans (sat_iff_indep h₂ hc hs hi)

/-! ## At the concrete primitives -/

/-- **The headline, at the concrete primitives** `Round4Int.BI (Profile.spec nd r) hn host`: on
round 6's whole domain, a `CfgRel`-respecting step sentence that cannot tell Core's successors
apart holds in Core iff it holds in the backend canonical model. -/
theorem sat_iff_indep_BI (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {nd : Bool} {r : RelaxedChoice} {c : Config H} (hc : Dom (Profile.spec nd r) host c)
    {s : BSen Unit Value} (hs : s.Respects (Atlas.SpecTec.CfgRel hn))
    (hi : Indep (Atlas.SpecTec.coreObs (Profile.spec nd r) host hn c) s) :
    (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host)).Sat c s ↔
      (modelChart (stepModel (Round4Int.BI (Profile.spec nd r) hn host))).Sat (configV hn c) s :=
  sat_iff_indep (halves_BI hinj hf hh nd r) hc hs hi

/-! ## The set-valued model -/

/-- Every observation of the union model is a Core observation up to `CfgRel`. -/
theorem unionObs_bwd {c : Config H} (hc : Dom P host c) (u : Unit) :
    ∀ b' ∈ unionObs hn P host (configV hn c) u, ∃ b ∈ Atlas.SpecTec.coreObs P host hn c u,
      Atlas.SpecTec.CfgRel hn b b' := by
  rintro w ⟨B, hB, hw⟩
  exact bwd_rel hB hc u w hw

/-- The union model contains each admissible model. -/
theorem mobs_subset_unionObs (hB : Halves B hn P host) (c : Config H) (u : Unit) :
    mobs B hn c u ⊆ unionObs hn P host (configV hn c) u :=
  fun _ hw => ⟨B, hB, hw⟩

/-- **The union model, under `Task.choiceCover`**, is equal to Core on every `CfgRel`-respecting
step sentence, on all of `Dom` at `Profile.spec nd r`. -/
def toUnion (hT : Task.choiceCover) (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (nd : Bool) (r : RelaxedChoice) :
    Transition (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host))
      (unionChart hn (Profile.spec nd r) host) :=
  BTrans.ofUpTo (Atlas.SpecTec.CfgRel hn) (configV hn) id (fun _ _ => trivial)
    (fun c hc u => by
      rintro b ⟨c', hs, rfl⟩
      obtain ⟨B, hB, d', he, hd⟩ := hT H hn hinj host hf hh nd r c hc c' hs
      exact ⟨configV hn d', ⟨B, hB, hd⟩, c', d', he, rfl, rfl⟩)
    (fun _ hc u => unionObs_bwd hc u)

theorem toUnion_dir (hT : Task.choiceCover) (hinj : Function.Injective hn) (hf : HostFinite host)
    (hh : HostOk host) (nd : Bool) (r : RelaxedChoice) :
    (toUnion hT hinj hf hh nd r).dir = .equal := rfl

end Silmaril.Wasm.SpecTec.Institution.Nondet
