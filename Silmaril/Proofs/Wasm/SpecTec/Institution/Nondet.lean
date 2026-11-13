module

public import Silmaril.Wasm.SpecTec.Institution.Nondet.Defs
public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms

/-!
# The wasm-3.0 semi-comorphism off the deterministic domain: proofs

* `sat_iff_resolve`: the generic lemma. If every source observation `b` is matched by a target
  observation related to *some* source observation `b₀` (forward up to choice), every target
  observation is related to a source observation (backward), and the atoms of `s` respect the
  relation and cannot tell source observations apart (`Indep`), then source and target satisfy
  `s` alike.
* `sat_upto_univ'`, `sat_upto_exist'`: the one-sided halves that need only the backward
  inclusion.
* `halves_builtins`, `halves_BI`: `Halves` at `Wasm30.builtins` (by choice) and at the concrete
  primitives `Round4Int.BI`.
* `fwd_resolve`, `bwd_rel`: `Halves` as observation inclusions of the two step charts.
* `indep_of_domUpTo`, `domUpTo_eq_of_domDet`, `domUpTo_top`: the uniform fragments.
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

/-! ## Behaviour sentences under a resolution -/

section Generic

variable {C B : Type} {obs obs' : C → Set B} {R : B → B → Prop}

/-- **Two-sided satisfaction under a resolution of choice**, on choice-independent sentences. -/
theorem sat_iff_resolve (h₁ : ∀ c, ∀ b ∈ obs c, ∃ b₀ ∈ obs c, ∃ b' ∈ obs' c, R b₀ b')
    (h₂ : ∀ c, ∀ b' ∈ obs' c, ∃ b ∈ obs c, R b b') {s : BSen C B} (hs : s.Respects R)
    (hi : Indep obs s) : s.Sat obs ↔ s.Sat obs' := by
  induction s with
  | always c φ =>
    show (∀ b ∈ obs c, φ b) ↔ ∀ b ∈ obs' c, φ b
    constructor
    · intro h b' hb'
      obtain ⟨b, hb, r⟩ := h₂ c b' hb'
      exact (hs b b' r).1 (h b hb)
    · intro h b hb
      obtain ⟨b₀, hb₀, b', hb', r⟩ := h₁ c b hb
      have h₀ : φ b₀ := (hs b₀ b' r).2 (h b' hb')
      exact (hi b₀ hb₀ b hb).1 h₀
  | may c φ =>
    show (∃ b ∈ obs c, φ b) ↔ ∃ b ∈ obs' c, φ b
    constructor
    · rintro ⟨b, hb, hφ⟩
      obtain ⟨b₀, hb₀, b', hb', r⟩ := h₁ c b hb
      have h₀ : φ b₀ := (hi b hb b₀ hb₀).1 hφ
      exact ⟨b', hb', (hs b₀ b' r).1 h₀⟩
    · rintro ⟨b', hb', hφ⟩
      obtain ⟨b, hb, r⟩ := h₂ c b' hb'
      exact ⟨b, hb, (hs b b' r).2 hφ⟩
  | «and» s t ih₁ ih₂ => exact and_congr (ih₁ hs.1 hi.1) (ih₂ hs.2 hi.2)
  | top => exact Iff.rfl

/-- Backward inclusion alone: universal respecting sentences go from source to target. -/
theorem sat_upto_univ' (h₂ : ∀ c, ∀ b' ∈ obs' c, ∃ b ∈ obs c, R b b') {s : BSen C B}
    (hu : s.Universal) (hs : s.Respects R) (h : s.Sat obs) : s.Sat obs' := by
  induction s with
  | always c φ =>
    intro b' hb'
    obtain ⟨b, hb, r⟩ := h₂ c b' hb'
    exact (hs b b' r).1 (h b hb)
  | may c φ => exact hu.elim
  | «and» s t ih₁ ih₂ => exact ⟨ih₁ hu.1 hs.1 h.1, ih₂ hu.2 hs.2 h.2⟩
  | top => trivial

/-- Backward inclusion alone: existential respecting witnesses go from target to source. -/
theorem sat_upto_exist' (h₂ : ∀ c, ∀ b' ∈ obs' c, ∃ b ∈ obs c, R b b') {s : BSen C B}
    (he : s.Existential) (hs : s.Respects R) (h : s.Sat obs') : s.Sat obs := by
  induction s with
  | always c φ => exact he.elim
  | may c φ =>
    obtain ⟨b', hb', hφ⟩ := h
    obtain ⟨b, hb, r⟩ := h₂ c b' hb'
    exact ⟨b, hb, (hs b b' r).2 hφ⟩
  | «and» s t ih₁ ih₂ => exact ⟨ih₁ he.1 hs.1 h.1, ih₂ he.2 hs.2 h.2⟩
  | top => trivial

/-- Atoms respecting both `R` and `K` respect their composite. -/
theorem respects_comp {K : B → B → Prop} {s : BSen C B} (hK : s.Respects K)
    (hR : s.Respects R) : s.Respects (fun b b' => ∃ m, K b m ∧ R m b') := by
  induction s with
  | always _ φ => exact fun b b' ⟨m, k, r⟩ => (hK b m k).trans (hR m b' r)
  | may _ φ => exact fun b b' ⟨m, k, r⟩ => (hK b m k).trans (hR m b' r)
  | «and» s t ih₁ ih₂ => exact ⟨ih₁ hK.1 hR.1, ih₂ hK.2 hR.2⟩
  | top => trivial

/-- `K`-respecting sentences are choice-independent on sets whose elements are `K`-related. -/
theorem indep_of_respects {K : B → B → Prop} {S : C → Set B}
    (hS : ∀ c, ∀ b ∈ S c, ∀ b' ∈ S c, K b b') {s : BSen C B} (hK : s.Respects K) :
    Indep S s := by
  induction s with
  | always c φ => exact fun b hb b' hb' => hK b b' (hS c b hb b' hb')
  | may c φ => exact fun b hb b' hb' => hK b b' (hS c b hb b' hb')
  | «and» s t ih₁ ih₂ => exact ⟨ih₁ hK.1, ih₂ hK.2⟩
  | top => trivial

/-- Every sentence respects equality. -/
theorem respects_eq (s : BSen C B) : s.Respects (· = ·) := by
  induction s with
  | always _ φ => exact fun b b' e => e ▸ Iff.rfl
  | may _ φ => exact fun b b' e => e ▸ Iff.rfl
  | «and» s t ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | top => trivial

/-- Choice independence on a smaller observation set. -/
theorem indep_mono {S S' : C → Set B} (h : ∀ c, S c ⊆ S' c) {s : BSen C B} (hi : Indep S' s) :
    Indep S s := by
  induction s with
  | always c φ => exact fun b hb b' hb' => hi b (h c hb) b' (h c hb')
  | may c φ => exact fun b hb b' hb' => hi b (h c hb) b' (h c hb')
  | «and» s t ih₁ ih₂ => exact ⟨ih₁ hi.1, ih₂ hi.2⟩
  | top => trivial

end Generic

/-! ## The halves at the two choices of primitives -/

variable {H : Type} {hn : H → String} {host : HostSemantics H} {P : Profile}

/-- **`Halves` at `Wasm30.builtins`** (the primitives of `stepModel_facts`, by choice). -/
theorem halves_builtins (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (nd : Bool) (r : RelaxedChoice) :
    Halves (builtins hn hinj host hf hh nd r) hn (Profile.spec nd r) host := by
  have hspec := Classical.choose_spec (stepModel_facts hn hinj host hf hh nd r)
  refine ⟨fun c hc c' hs => ?_, fun c hc w hw => ?_⟩
  · obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc
    exact hspec.1 c c' ts hok hb hsucc hs
  · obtain ⟨⟨ts, hok⟩, hb, _⟩ := hc
    exact hspec.2 c ts w hok hb hw

/-- **`Halves` at the concrete primitives** `Round4Int.BI (Profile.spec nd r) hn host`, from
`Round6.Int.openR_backend`: no choice of primitives. -/
theorem halves_BI (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (nd : Bool) (r : RelaxedChoice) :
    Halves (Round4Int.BI (Profile.spec nd r) hn host) hn (Profile.spec nd r) host := by
  have O := Round6.Int.openR_backend (nd := nd) (r := r) hinj hf hh
  refine ⟨fun c hc c' hs => ?_, fun c hc w hw => ?_⟩
  · obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc
    exact Round6.Target.fwdR_of_open hinj hf hh O c c' ts hok hb hsucc hs
  · obtain ⟨⟨ts, hok⟩, hb, _⟩ := hc
    exact Round6.Target.bwdR_of_open hinj hf (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) O c ts w hok hb hw

/-! ## `Halves` as observation inclusions -/

section Obs

variable {B : Builtins}

/-- The observations of `modelChart (stepModel B)` at an encoded configuration. -/
abbrev mobs (B : Builtins) (hn : H → String) (c : Config H) (_ : Unit) : Set Value :=
  {w | MStep B (configV hn c) w}

/-- Forward up to choice, as observations: every Core observation is matched by a model
observation related by `CfgRel` to *some* Core observation. -/
theorem fwd_resolve (hB : Halves B hn P host) {c : Config H} (hc : Dom P host c) (u : Unit) :
    ∀ b ∈ Atlas.SpecTec.coreObs P host hn c u, ∃ b₀ ∈ Atlas.SpecTec.coreObs P host hn c u,
      ∃ b' ∈ mobs B hn c u, Atlas.SpecTec.CfgRel hn b₀ b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨c'', hs'', -, d', he, hd⟩ := hB.fwd c hc c' hs
  exact ⟨configV hn c'', ⟨c'', hs'', rfl⟩, configV hn d', hd, c'', d', he, rfl, rfl⟩

/-- Backward, as observations: every model observation is related to a Core observation. -/
theorem bwd_rel (hB : Halves B hn P host) {c : Config H} (hc : Dom P host c) (u : Unit) :
    ∀ b' ∈ mobs B hn c u, ∃ b ∈ Atlas.SpecTec.coreObs P host hn c u,
      Atlas.SpecTec.CfgRel hn b b' := by
  intro w hw
  obtain ⟨c', d', he, rfl, hs⟩ := hB.bwd c hc w hw
  exact ⟨configV hn c', ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

/-- On `DomUpTo K`, Core's observations are pairwise `K`-related. -/
theorem coreObs_rel {K : Value → Value → Prop} {c : Config H} (hc : DomUpTo K P host hn c)
    (u : Unit) : ∀ b ∈ Atlas.SpecTec.coreObs P host hn c u,
      ∀ b' ∈ Atlas.SpecTec.coreObs P host hn c u, K b b' := by
  rintro b ⟨c₁, h₁, rfl⟩ b' ⟨c₂, h₂, rfl⟩
  exact hc.2 c₁ c₂ h₁ h₂

/-- On `DomUpTo K` with `K` reflexive, forward up to choice is forward up to `K ; CfgRel`. -/
theorem fwd_upTo (hB : Halves B hn P host) {K : Value → Value → Prop} {c : Config H}
    (hc : DomUpTo K P host hn c) (u : Unit) :
    ∀ b ∈ Atlas.SpecTec.coreObs P host hn c u, ∃ b' ∈ mobs B hn c u,
      ∃ m, K b m ∧ Atlas.SpecTec.CfgRel hn m b' := by
  intro b hb
  obtain ⟨b₀, hb₀, b', hb', r⟩ := fwd_resolve hB hc.1 u b hb
  exact ⟨b', hb', b₀, coreObs_rel hc u b hb b₀ hb₀, r⟩

end Obs

/-! ## The uniform fragments -/

/-- `DomDet` is determinism up to equality. -/
theorem domUpTo_eq_of_domDet {c : Config H} (hc : DomDet P host c) :
    DomUpTo (· = ·) P host hn c :=
  ⟨hc.1, fun c₁ c₂ h₁ h₂ => congrArg (configV hn) (hc.2 c₁ c₂ h₁ h₂)⟩

/-- All of `Dom` is determinism up to the total relation. -/
theorem domUpTo_top {c : Config H} (hc : Dom P host c) :
    DomUpTo (fun _ _ => True) P host hn c :=
  ⟨hc, fun _ _ _ _ => trivial⟩

/-- On `DomUpTo K`, `K`-respecting sentences are choice-independent. -/
theorem indep_of_domUpTo {K : Value → Value → Prop} {c : Config H} (hc : DomUpTo K P host hn c)
    {s : BSen Unit Value} (hK : s.Respects K) :
    Indep (Atlas.SpecTec.coreObs P host hn c) s :=
  indep_of_respects (coreObs_rel hc) hK

end Silmaril.Wasm.SpecTec.Institution.Nondet
