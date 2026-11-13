module

public import Silmaril.Wasm.Det.Core.Component.Defs

/-!
# Determinism modulo traps and imports for components (proofs)

`returns_of_export`: a `returns` behaviour of `exportBehaviours` comes from an instantiation and
a resolved call of the export; `exportBehaviours_returns_eq`: under `CompDet`, two `returns`
behaviours of the same export call coincide. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Core.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine Outcome exportBehaviours
  callBehaviours instBehaviours InstResult)
open Silmaril.Wasm.Det.Core.Component

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- The only call outcome observed as `returns r` is `resolved r`. -/
theorem ofCall_returns {out : CallOutcome} {r : Option (List Value.Val)}
    (h : Outcome.returns r = Outcome.ofCall out) : out = .resolved r := by
  cases out with
  | resolved r' =>
    have h' : Outcome.returns r = Outcome.returns r' := h
    cases h'
    rfl
  | trap => cases h
  | deadlock => cases h

/-- **A `returns` behaviour of an export call** comes from a non-trapping instantiation and a
resolved call of the export. -/
theorem returns_of_export {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E} {name : String}
    {vals : List Value.Val} {r : Option (List Value.Val)}
    (hb : Outcome.returns r ∈ exportBehaviours prof h σ0 comp args name vals) :
    ∃ m₁ i es f m', Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₁ i es ∧
      es.lookup name = some f ∧ Calls prof h.hr h.dispatch m₁ ⟨0⟩ f vals m' (.resolved r) := by
  rcases hb with ⟨m₁, i, es, f, hi, hf, hc⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · rcases hc with ⟨m', out, hcall, hout⟩ | ⟨hb, -⟩
    · have ho : out = .resolved r := ofCall_returns hout
      subst ho
      exact ⟨m₁, i, es, f, m', hi, hf, hcall⟩
    · cases hb
  · cases hb
  · cases hb

/-- **Same export call, same non-trapping result**: under `CompDet`, two `returns` behaviours of
the same export call on the same values are equal. -/
theorem exportBehaviours_returns_eq {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    (hD : CompDet prof h σ0 comp args) {name : String} {vals : List Value.Val}
    {r₁ r₂ : Option (List Value.Val)}
    (h₁ : Outcome.returns r₁ ∈ exportBehaviours prof h σ0 comp args name vals)
    (h₂ : Outcome.returns r₂ ∈ exportBehaviours prof h σ0 comp args name vals) : r₁ = r₂ := by
  obtain ⟨m₁, i₁, es₁, f₁, m₁', hi₁, hf₁, hc₁⟩ := returns_of_export h₁
  obtain ⟨m₂, i₂, es₂, f₂, m₂', hi₂, hf₂, hc₂⟩ := returns_of_export h₂
  have hinst : m₁ = m₂ ∧ i₁ = i₂ ∧ es₁ = es₂ := hD.1 m₁ m₂ i₁ i₂ es₁ es₂ hi₁ hi₂
  obtain ⟨rfl, -, rfl⟩ := hinst
  have hf : f₁ = f₂ := Option.some.inj (hf₁.symm.trans hf₂)
  subst hf
  have hreach : CompReach prof h σ0 comp args m₁ es₁ := .inst hi₁
  have hout : CallOutcome.resolved r₁ = .resolved r₂ :=
    (hD.2 m₁ es₁ hreach name f₁ hf₁ ⟨0⟩ vals m₁' m₂' _ _ hc₁ hc₂ (by simp) (by simp)).1
  cases hout
  rfl

end Silmaril.Proofs.Wasm.Det.Core.Component
