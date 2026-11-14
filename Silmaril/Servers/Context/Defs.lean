module

public import Silmaril.Servers.Hosts.Defs

/-!
# Contextual equivalence and the observations read through it

A component language has **contexts** (hosts, linkers, client harnesses) and an observation of
each **closed program** (a context filled with a component): `Lang.run K c`. **Contextual
equivalence** (`CtxEquivOn Ks`) and **contextual refinement** (`CtxRefinesOn Ks`) compare two
components in every context of a class `Ks` (`CtxEquiv`, `CtxRefines`: all contexts).

An HTTP observation of a component is **read through contexts** (`Reading`): for each
environment `x : X` (a host strategy) it fixes a context `ctx x` and a map `read` from the
observations of that closed program to an HTTP behaviour. These two fields are the exact
assumptions under which contextual equivalence implies HTTP observational equivalence
(`Thms.Reading.equivAt_of_ctxEquivOn`): the HTTP behaviour must be a function of what one
context in the class observes. Refinement needs, in addition, that `read` is monotone
(`Thms.Reading.refinesAt_of_ctxRefinesOn`).

What does **not** follow, and is refuted by small examples in `Thms`:

* an arbitrary projection of components (one that reads the component itself, not a closed
  program in the class) is not preserved by contextual equivalence
  (`Thms.ctxEquiv_not_preserves_projection`);
* a reading through a context outside the class is not preserved
  (`Thms.ctxEquivOn_not_preserves_outside`);
* HTTP equivalence does not reflect to contextual equivalence
  (`Thms.reading_not_reflects`); it does when every context of the class is itself read off
  the HTTP behaviour (`Thms.Reading.ctxEquivOn_of_equivAt`, full abstraction, an assumption).

The `wasi:http` instance, with hosts as contexts, is `Silmaril.Servers.WasiContext`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Context

open Silmaril.Servers Silmaril.Servers.Observe Silmaril.Servers.Hosts

/-- **A language with contexts**: components, contexts, and the observations of a closed
program. -/
structure Lang where
  /-- Components. -/
  Comp : Type
  /-- Contexts. -/
  Ctx : Type
  /-- Observations of closed programs. -/
  Obs : Type
  /-- The observations of the context `K` filled with the component `c`. -/
  run : Ctx → Comp → Set Obs

variable {L : Lang}

/-- **Contextual equivalence** over the contexts of `Ks`. -/
def CtxEquivOn (Ks : Set L.Ctx) (c₁ c₂ : L.Comp) : Prop := ∀ K ∈ Ks, L.run K c₁ = L.run K c₂

/-- **Contextual refinement** over the contexts of `Ks`, `c₁` refining `c₂`. -/
def CtxRefinesOn (Ks : Set L.Ctx) (c₁ c₂ : L.Comp) : Prop := ∀ K ∈ Ks, L.run K c₁ ⊆ L.run K c₂

/-- Contextual equivalence over all contexts. -/
def CtxEquiv (c₁ c₂ : L.Comp) : Prop := CtxEquivOn (L := L) Set.univ c₁ c₂

/-- Contextual refinement over all contexts. -/
def CtxRefines (c₁ c₂ : L.Comp) : Prop := CtxRefinesOn (L := L) Set.univ c₁ c₂

/-- **A reading of HTTP behaviours through contexts**: for each environment `x`, the context
`ctx x` and the map `read` from its observations to an HTTP behaviour. -/
structure Reading (L : Lang) (X : Type) (A : Sig) where
  /-- The context that observes the component in the environment `x`. -/
  ctx : X → L.Ctx
  /-- The HTTP behaviour read from the observations of that closed program. -/
  read : Set L.Obs → Beh A

/-- The HTTP behaviour of a component, per environment: an open server. -/
def Reading.beh {X : Type} {A : Sig} (ρ : Reading L X A) (c : L.Comp) : Open X A :=
  fun x => ρ.read (L.run (ρ.ctx x) c)

/-- The contexts a reading uses. -/
def Reading.ctxs {X : Type} {A : Sig} (ρ : Reading L X A) : Set L.Ctx := Set.range ρ.ctx

/-- A reading whose map is the image of a map on observations (always monotone). -/
def Reading.image {X : Type} {A : Sig} (ctx : X → L.Ctx) (f : L.Obs → Obs A) : Reading L X A :=
  ⟨ctx, fun S => f '' S⟩

end Silmaril.Servers.Context
