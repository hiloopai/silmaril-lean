module

public import Silmaril.Servers.WasiContext.Defs
public import Silmaril.Servers.WasiHttp.Thms
public import Silmaril.Servers.Exchange.Thms
public import Silmaril.Servers.Context.Thms
import Silmaril.Proofs.Servers.WasiContext.Basic

/-!
# `wasi:http` components, hosts as contexts: theorems

* **The linked server is read off the host's observation** (`linkServer_eq`):
  `linkServer η σ = readExch (interacts η σ)`, and likewise with request bodies.
* **Host equivalence gives HTTP observational equivalence** under every host it covers
  (`linkServer_eq_of_hostEquivOn`, and for the per-request-instance core reading
  `httpReading_equivAt`); host refinement (inclusion of interactions) gives HTTP refinement
  (`linkServer_refines_of_interacts`, `httpReading_refinesAt`).
* **Strategy refinement is a host refinement** (`interacts_mono`): a component whose plays are
  among another's has, under every host, fewer HTTP exchanges.

The assumptions are exactly these: the context is a host of the slice's imports, the component
is a strategy of `nsig proxyImports ↠ nsig X`, and the observation is `interacts`. Nothing is
claimed for observations that hide the import events (the composite `link η σ`).
-/

@[expose] public section

namespace Silmaril.Servers.WasiContext

open Silmaril.Servers.Exchange
open Silmaril.Games Silmaril.Wasi Silmaril.Servers.Calls Silmaril.Servers.WasiHttp
open Silmaril.Servers.Observe Silmaril.Servers.Hosts Silmaril.Servers.Context

variable {Y : Silmaril.Games.Sig.{0}} {X : Set FnName}

/-- **The linked server is read off what the host observes.** -/
theorem linkServer_eq (η : Host Y proxyImports)
    (σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) :
    linkServer η σ = readExch (interacts η σ) :=
  Proofs.Servers.WasiContext.linkServer_eq η σ

theorem readExch_mono {U V : Set (List (Move (nsig proxyImports) (nsig X)))} (h : U ⊆ V) :
    Refines (readExch U) (readExch V) := fun _ ⟨u, hu, hf⟩ => ⟨u, h hu, hf⟩

/-- **Host equivalence gives equal linked servers** under every host it covers. -/
theorem linkServer_eq_of_hostEquivOn {Hs : Set (Host Y proxyImports)}
    {σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)} (h : HostEquivOn Hs σ₁ σ₂)
    {η : Host Y proxyImports} (hη : η ∈ Hs) : linkServer η σ₁ = linkServer η σ₂ := by
  rw [linkServer_eq, linkServer_eq, h η hη]

theorem linkServer_eq_of_hostEquiv {σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    (h : HostEquiv σ₁ σ₂) (η : Host Y proxyImports) : linkServer η σ₁ = linkServer η σ₂ := by
  rw [linkServer_eq, linkServer_eq, h Y η]

/-- **Host refinement gives HTTP refinement.** -/
theorem linkServer_refines_of_interacts {η : Host Y proxyImports}
    {σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    (h : interacts η σ₁ ⊆ interacts η σ₂) : Refines (linkServer η σ₁) (linkServer η σ₂) := by
  rw [linkServer_eq, linkServer_eq]; exact readExch_mono h

theorem interacts_mono (η : Host Y proxyImports)
    {σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)} (h : σ₁ ≤ σ₂) :
    interacts η σ₁ ⊆ interacts η σ₂ := fun _ ⟨hu, hs⟩ => ⟨h hu, hs⟩

theorem httpReading_mono : Monotone (httpReading Y X).read := fun _ _ h =>
  Beh.ofModel_refines_iff.2 (fresh_mono (readExch_mono h))

/-- **Host equivalence over `Hs` gives HTTP observational equivalence, a fresh instance per
request, under every host of `Hs`.** -/
theorem httpReading_equivAt {Hs : Set (Host Y proxyImports)}
    {σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)} (h : HostEquivOn Hs σ₁ σ₂) :
    EquivAt Hs ((httpReading Y X).beh σ₁) ((httpReading Y X).beh σ₂) := fun η hη => by
  simp only [Reading.beh, httpReading, id, hostLang, h η hη]

/-- **Host refinement over `Hs` gives HTTP refinement under every host of `Hs`.** -/
theorem httpReading_refinesAt {Hs : Set (Host Y proxyImports)}
    {σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)}
    (h : ∀ η ∈ Hs, interacts η σ₁ ⊆ interacts η σ₂) :
    RefinesAt Hs ((httpReading Y X).beh σ₁) ((httpReading Y X).beh σ₂) := fun η hη =>
  httpReading_mono (h η hη)

/-- The core reading of the linked server, as an HTTP behaviour, is the reading's. -/
theorem httpReading_beh (η : Host Y proxyImports)
    (σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) :
    (httpReading Y X).beh σ η = Beh.ofModel (fresh (linkServer η σ)) := by
  rw [linkServer_eq]; rfl

end Silmaril.Servers.WasiContext
