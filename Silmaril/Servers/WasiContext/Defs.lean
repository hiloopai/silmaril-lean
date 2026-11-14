module

public import Silmaril.Servers.WasiHttp.Defs
public import Silmaril.Servers.Context.Defs

/-!
# `wasi:http` components: hosts as contexts

The instance of `Silmaril.Servers.Context` for the `wasi:http` proxy world slice of
`Silmaril.Servers.WasiHttp`. A component is a strategy `σ` over the slice's imports
(`proxyImports`) and exports; a context is a host `η : Host Y proxyImports` (pure functions of
the past calls through `concrete impl`, nondeterministic or stateful hosts are all hosts).

**Exact observation.** What the context `η` observes of `σ` is `interacts η σ`: the plays of
`σ` that interact with some play of `η`, *including the import calls and their answers*. This
is the observation the HTTP reading needs: `linkServer η σ` reads the exchanges off the import
events of these plays (`Thms.linkServer_eq`). It is finer than the composite strategy
`Wasi.link η σ = η.comp σ`, which hides the import events; equality of composites is **not**
assumed to give equal HTTP readings, and no theorem here claims it.

* `hostLang Y X`: the context language (components, hosts, plays).
* `HostEquiv σ₁ σ₂`: the two components interact identically with every host of every host
  game `Y`; `HostEquivOn Hs` restricts to a set of hosts (for example the pure ones,
  `concrete impl`).
* `httpReading`: the HTTP behaviour of a component under a host, read as `wasmtime serve` runs
  the proxy world, a fresh instance per request (`Exchange.fresh`), as core traces after a
  successful initialization (`Beh.ofModel`; the Lean component model has no instantiation phase,
  so initialization failures are observed only at runtime, `tests/servers/policies`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.WasiContext

open Silmaril.Servers.Exchange
open Silmaril.Games Silmaril.Wasi Silmaril.Servers.Calls Silmaril.Servers.WasiHttp
open Silmaril.Servers.Observe Silmaril.Servers.Context

variable {Y : Silmaril.Games.Sig.{0}} {X : Set FnName}

/-- **What the host `η` observes of the component `σ`**: the plays of `σ`, with their import
events, that interact with a play of `η`. -/
def interacts (η : Host Y proxyImports) (σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) :
    Set (List (Move (nsig proxyImports) (nsig X))) :=
  {u | u ∈ σ ∧ ∃ s ∈ η, ∃ p, Zip s u p}

/-- **The context language**: components, hosts of the host game `Y`, plays. -/
def hostLang (Y : Silmaril.Games.Sig.{0}) (X : Set FnName) : Lang :=
  ⟨Silmaril.Games.Strategy (nsig proxyImports) (nsig X), Host Y proxyImports,
    List (Move (nsig proxyImports) (nsig X)), interacts⟩

/-- **Host equivalence over the hosts `Hs`**: the components interact identically with each. -/
def HostEquivOn (Hs : Set (Host Y proxyImports))
    (σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) : Prop :=
  ∀ η ∈ Hs, interacts η σ₁ = interacts η σ₂

/-- **Host equivalence**: the same interactions with every host of every host game. -/
def HostEquiv (σ₁ σ₂ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) : Prop :=
  ∀ (Y : Silmaril.Games.Sig.{0}) (η : Host Y proxyImports), interacts η σ₁ = interacts η σ₂

/-- The HTTP exchanges read off a set of component plays. -/
def readExch (U : Set (List (Move (nsig proxyImports) (nsig X)))) : Exchange.Model httpIface :=
  {t | ∃ u ∈ U, List.Forall₂ Obs ((calls (wtrace u)).filter answered) t}

/-- **The HTTP reading**: under the host `η`, the per-request-instance core traces of the
exchanges read off the plays `η` observes. -/
def httpReading (Y : Silmaril.Games.Sig.{0}) (X : Set FnName) :
    Reading (hostLang Y X) (Host Y proxyImports) httpIface :=
  ⟨id, fun U => Beh.ofModel (fresh (readExch U))⟩

end Silmaril.Servers.WasiContext
