module

public import Silmaril.Project.Shapes.Component.Via.Defs
public import Silmaril.Project.Components.SemVer.Thms
public import Silmaril.Wasi.Versions.Stateful.Thms

/-!
# Standard problem shapes: WASI versions and upgrades of components (theorems)

PROVED:

* `ImplementsVia.of_sat`: a component whose returns satisfy `A` under the theory `B` on its
  host's answers (`agP B (retG A)`) implements `A` via `B` (`Silmaril.Wasi.Versions.link_model`).
* `ImplementsVia.lower`, `ImplementsVia.upper`: a stronger theory below, or a weaker one above,
  keeps the relation; `ImplementsVia.prod_left`: a theory `B ⊗ B'` below may be weakened to `B`.
* `ImportsVia.of_eqs`, `WitUpgrade.of_summaries`, `ReleaseImplementsVia.of_eqs`: the shapes on
  values from the decoded terms (the transfer from a known parse).
* `summaryUpgrade_refl`, `summaryUpgrade_trans`: a release is an upgrade of itself, and
  upgrades compose.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Components.SemVer
open Silmaril.Wasm (Wit.Version)

variable {I X : Set FnName} {SA SB SB' SA' : Type}

/-- **From the contract to the implementation morphism.** -/
theorem ImplementsVia.of_sat {σ : Strategy (nsig I) (nsig X)} {A : Protocol SA WEv}
    {B : Protocol SB WEv} (h : (agP B (Silmaril.Wasi.Versions.retG A)).holds σ) :
    ImplementsVia σ A B :=
  fun _ _ hη => Silmaril.Wasi.Versions.link_model h hη

/-- A stronger theory of the hosts below. -/
theorem ImplementsVia.lower {σ : Strategy (nsig I) (nsig X)} {A : Protocol SA WEv}
    {B : Protocol SB WEv} {B' : Protocol SB' WEv} (h : ImplementsVia σ A B)
    (hB : ∀ t, B'.Accepts t → B.Accepts t) : ImplementsVia σ A B' :=
  fun Y η hη => h Y η fun s hs => hB _ (hη s hs)

/-- A weaker theory above. -/
theorem ImplementsVia.upper {σ : Strategy (nsig I) (nsig X)} {A : Protocol SA WEv}
    {A' : Protocol SA' WEv} {B : Protocol SB WEv} (h : ImplementsVia σ A B)
    (hA : ∀ t, A.Accepts t → A'.Accepts t) : ImplementsVia σ A' B :=
  fun Y η hη s hs => hA _ (h Y η hη s hs)

/-- Hosts of a product theory are hosts of its left factor. -/
theorem ImplementsVia.prod_left {σ : Strategy (nsig I) (nsig X)} {A : Protocol SA WEv}
    {B : Protocol SB WEv} (B' : Protocol SB' WEv) (h : ImplementsVia σ A B) :
    ImplementsVia σ A (B.prod B') :=
  h.lower fun t ht => ((Silmaril.Wasm.Resource.Protocol.accepts_prod_iff B B' t).1 ht).1

/-- `ImportsVia` from the decoded world and core imports. -/
theorem ImportsVia.of_eqs {Xw : Value Silmaril.Project.Formats.EmbeddedWorld}
    {M : Value Silmaril.Wasm.Module} {ns : String} {v : Wit.Version} {L : List FnName}
    {w : Silmaril.Project.Formats.EmbeddedWorld} {imps : List CoreImport}
    (hw : Xw.parse = some w) (hm : M.parse.map coreImports = some imps)
    (h : ViaOk w imps ns v L) : ImportsVia Xw M ns v L := by
  cases hM : M.parse with
  | none => rw [hM] at hm; cases hm
  | some m =>
    rw [hM] at hm
    have him : coreImports m = imps := Option.some.inj hm
    refine ⟨w, hw, m, hM, ?_⟩
    show ViaOk w (coreImports m) ns v L
    rw [him]
    exact h

/-- `ReleaseImplementsVia` from the decoded terms and the implementation morphism. -/
theorem ReleaseImplementsVia.of_eqs {X' : Set FnName}
    {Xw : Value Silmaril.Project.Formats.EmbeddedWorld} {M : Value Silmaril.Wasm.Module}
    {ns : String} {v : Wit.Version} {L : List FnName} {σ : Strategy (nsig {f | f ∈ L}) (nsig X')}
    {A : Protocol SA WEv} {B : Protocol SB WEv}
    {w : Silmaril.Project.Formats.EmbeddedWorld} {imps : List CoreImport}
    (hw : Xw.parse = some w) (hm : M.parse.map coreImports = some imps)
    (h : ViaOk w imps ns v L) (hσ : ImplementsVia σ A B) :
    ReleaseImplementsVia Xw M ns v L σ A B :=
  ⟨ImportsVia.of_eqs hw hm h, hσ⟩

/-- `WitUpgrade` from the summaries of the two decoded packages. -/
theorem WitUpgrade.of_summaries {X₁ X₂ : Value Silmaril.Wasm.Wit.Binary.Package}
    {s₁ s₂ : PackageSummary} (h₁ : X₁.parse.map summary = some s₁)
    (h₂ : X₂.parse.map summary = some s₂) (h : SummaryUpgrade s₁ s₂) : WitUpgrade X₁ X₂ := by
  cases e₁ : X₁.parse with
  | none => rw [e₁] at h₁; cases h₁
  | some p₁ =>
    cases e₂ : X₂.parse with
    | none => rw [e₂] at h₂; cases h₂
    | some p₂ =>
      rw [e₁] at h₁
      rw [e₂] at h₂
      refine ⟨p₁, e₁, p₂, e₂, ?_⟩
      show SummaryUpgrade (summary p₁) (summary p₂)
      rw [Option.some.inj h₁, Option.some.inj h₂]
      exact h

/-- A release with a version and no pre-release is an upgrade of itself. -/
theorem summaryUpgrade_refl {s : PackageSummary} {u : Wit.Version} (hv : binVersion? s.1 = some u)
    (hu : u.pre = []) : SummaryUpgrade s s := by
  refine ⟨rfl, rfl, ?_, fun i hi => ⟨i, hi, rfl, List.Subset.refl _, List.Subset.refl _⟩⟩
  rw [hv]
  exact upgrade_refl hu

/-- The version condition of `SummaryUpgrade`. -/
theorem summaryUpgrade_version {s₁ s₂ : PackageSummary} (h : SummaryUpgrade s₁ s₂) :
    ∃ u u', binVersion? s₁.1 = some u ∧ binVersion? s₂.1 = some u' ∧ Upgrade u u' := by
  obtain ⟨_, _, hv, _⟩ := h
  revert hv
  cases binVersion? s₁.1 <;> cases binVersion? s₂.1 <;> simp

/-- **Upgrades compose.** -/
theorem summaryUpgrade_trans {s₁ s₂ s₃ : PackageSummary} (h₁ : SummaryUpgrade s₁ s₂)
    (h₂ : SummaryUpgrade s₂ s₃) : SummaryUpgrade s₁ s₃ := by
  obtain ⟨u, u', e, e', hu⟩ := summaryUpgrade_version h₁
  obtain ⟨u'', u''', e'', e''', hu'⟩ := summaryUpgrade_version h₂
  rw [e'] at e''
  cases e''
  refine ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, ?_, fun i hi => ?_⟩
  · rw [e, e''']
    exact upgrade_trans hu hu'
  · obtain ⟨j, hj, hij, ht, hf⟩ := h₁.2.2.2 i hi
    obtain ⟨k, hk, hjk, ht', hf'⟩ := h₂.2.2.2 j hj
    exact ⟨k, hk, hij.trans hjk, List.Subset.trans ht ht', List.Subset.trans hf hf'⟩

end Silmaril.Project.Shapes.Component

end
