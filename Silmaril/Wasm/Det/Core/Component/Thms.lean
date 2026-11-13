module

public import Silmaril.Wasm.Det.Core.Component.Defs
public import Silmaril.Proofs.Wasm.Det.Core.Component

/-!
# Determinism and statelessness modulo traps and imports for components: theorems

Over the reference Component Model machine, against a fixed host, at every component choice
profile and core engine (in particular `core3P P` for every Core profile `P`):

* `exportBehaviours_returns_eq`: under `CompDet`, two `returns` behaviours of the same export
  call (`exportBehaviours`, instantiation from the empty store then the call) are equal;
* `CompDet.calls`: under `CompDet`, from a reachable configuration, two non-trapping calls of
  an export end with the same outcome in the same configuration;
* `CompStateless.calls`, `CompStateless.history`: under `CompStateless`, calls of an export from
  two reachable configurations, in particular from the freshly instantiated one and from one
  reached after any history of calls, have the same non-trapping outcome.

Proofs: `Silmaril.Proofs.Wasm.Det.Core.Component`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Core.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference (Host initConfig Engine Outcome exportBehaviours)

variable {E : Engine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- **Same export call, same non-trapping result.** -/
theorem exportBehaviours_returns_eq {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    (hD : CompDet prof h σ0 comp args) {name : String} {vals : List Value.Val}
    {r₁ r₂ : Option (List Value.Val)}
    (h₁ : Outcome.returns r₁ ∈ exportBehaviours prof h σ0 comp args name vals)
    (h₂ : Outcome.returns r₂ ∈ exportBehaviours prof h σ0 comp args name vals) : r₁ = r₂ :=
  Silmaril.Proofs.Wasm.Det.Core.Component.exportBehaviours_returns_eq hD h₁ h₂

/-- **Same call state, same non-trapping outcome**: from a reachable configuration, two
non-trapping calls of an export end with the same outcome in the same configuration. -/
theorem CompDet.calls {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    (hD : CompDet prof h σ0 comp args) {m : Config E σ} {es : List (String × FuncId)}
    (hm : CompReach prof h σ0 comp args m es) {name : String} {f : FuncId}
    (hf : es.lookup name = some f) {c : CallId} {vals : List Value.Val} {m₁ m₂ : Config E σ}
    {out₁ out₂ : CallOutcome} (h₁ : Calls prof h.hr h.dispatch m c f vals m₁ out₁)
    (h₂ : Calls prof h.hr h.dispatch m c f vals m₂ out₂) (ht₁ : out₁ ≠ .trap)
    (ht₂ : out₂ ≠ .trap) : out₁ = out₂ ∧ m₁ = m₂ :=
  hD.2 m es hm name f hf c vals m₁ m₂ out₁ out₂ h₁ h₂ ht₁ ht₂

/-- **Statelessness: non-trapping outcomes do not depend on the call state.** -/
theorem CompStateless.calls {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    (hS : CompStateless prof h σ0 comp args) {m₁ m₂ : Config E σ}
    {es₁ es₂ : List (String × FuncId)} (hm₁ : CompReach prof h σ0 comp args m₁ es₁)
    (hm₂ : CompReach prof h σ0 comp args m₂ es₂) {name : String} {f₁ f₂ : FuncId}
    (hf₁ : es₁.lookup name = some f₁) (hf₂ : es₂.lookup name = some f₂) {c : CallId}
    {vals : List Value.Val} {m₁' m₂' : Config E σ} {out₁ out₂ : CallOutcome}
    (h₁ : Calls prof h.hr h.dispatch m₁ c f₁ vals m₁' out₁)
    (h₂ : Calls prof h.hr h.dispatch m₂ c f₂ vals m₂' out₂) (ht₁ : out₁ ≠ .trap)
    (ht₂ : out₂ ≠ .trap) : out₁ = out₂ :=
  hS m₁ es₁ m₂ es₂ hm₁ hm₂ name f₁ f₂ hf₁ hf₂ c vals m₁' m₂' out₁ out₂ h₁ h₂ ht₁ ht₂

/-- **Statelessness: earlier calls do not affect later non-trapping outcomes.** A call from a
configuration reached after any history of calls has the non-trapping outcome of the same call
right after instantiation. -/
theorem CompStateless.history {prof : ProfileKind} {h : Host E σ} {σ0 : σ}
    {comp : Syntax.Component E.Module} {args : Instantiate.Exports E}
    (hS : CompStateless prof h σ0 comp args) {m₀ m : Config E σ} {i : InstId}
    {es₀ es : List (String × FuncId)}
    (hi : Instantiates prof h.hr h.dispatch (initConfig σ0) comp args m₀ i es₀)
    (hm : CompReach prof h σ0 comp args m es) {name : String} {f₀ f : FuncId}
    (hf₀ : es₀.lookup name = some f₀) (hf : es.lookup name = some f) {c : CallId}
    {vals : List Value.Val} {m₀' m' : Config E σ} {out₀ out : CallOutcome}
    (h₀ : Calls prof h.hr h.dispatch m₀ c f₀ vals m₀' out₀)
    (h₁ : Calls prof h.hr h.dispatch m c f vals m' out) (ht₀ : out₀ ≠ .trap)
    (ht : out ≠ .trap) : out = out₀ :=
  CompStateless.calls hS hm (.inst hi) hf hf₀ h₁ h₀ ht ht₀

end Silmaril.Wasm.Det.Core.Component
