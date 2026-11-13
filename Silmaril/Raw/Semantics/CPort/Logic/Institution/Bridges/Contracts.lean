module

public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# An institution of contracts on call relations

For a fixed type of logical inputs, a signature chooses the observations visible
at one abstraction level. Models are input/output relations, and sentences are
pre/postconditions. Satisfaction requires a nonempty set of outcomes on every
permitted input and correctness of every represented outcome. Thus a relation
with no executions cannot satisfy a contract on a permitted input.

A signature morphism maps concrete observations to abstract observations. It
reduces models by direct image and translates sentences by pulling back their
postconditions. `sat_pullback` proves the satisfaction condition, and
`institution` packages the identity and composition laws as an actual functor
into the existing category of rooms. `transport` combines this satisfaction
condition with a semantic refinement that also preserves outcome existence.

An Ail, Core, manual model, IR or machine-code semantics can instantiate a model
by providing its own call relation and observation map. The representation and
refinement proofs remain obligations of that instantiation. In a deterministic
interpreter's finite-success relation, existence proves termination; for a
nondeterministic semantics this alone is only existence of a successful run.
Failures or divergent runs must be represented as observations if the contract
is intended to constrain them. This file does not assume determinism or supply
a correctness theorem for any translation or linker.
-/

@[expose] public section

namespace Silmaril.Logic.Institution.Bridges.Contracts

open CategoryTheory

universe u

/-- A pre/postcondition over logical inputs and observations at one level. -/
@[ext]
structure Contract (Input Observation : Type u) where
  pre : Input → Prop
  post : Input → Observation → Prop

/-- A call relation; its outcome set can be empty on inputs outside a contract. -/
abbrev Model (Input Observation : Type u) := Input → Set Observation

/-- Every permitted input has an outcome, and every outcome satisfies the post. -/
def Sat {Input Observation : Type u} (model : Model Input Observation)
    (spec : Contract Input Observation) : Prop :=
  ∀ input, spec.pre input → (model input).Nonempty ∧
    ∀ observation, observation ∈ model input → spec.post input observation

/-- Translate a contract by observing a concrete result at an abstract level. -/
def Contract.pullback {Input Abstract Concrete : Type u} (observe : Concrete → Abstract)
    (spec : Contract Input Abstract) : Contract Input Concrete where
  pre := spec.pre
  post input observation := spec.post input (observe observation)

/-- Reduce a concrete call relation to its abstract observations. -/
def reduct {Input Abstract Concrete : Type u} (observe : Concrete → Abstract)
    (model : Model Input Concrete) : Model Input Abstract :=
  fun input => observe '' model input

/-- The satisfaction condition: sentence translation and model reduction agree,
including the existence requirement. The observation map need not be injective. -/
theorem sat_pullback {Input Abstract Concrete : Type u} (observe : Concrete → Abstract)
    (model : Model Input Concrete) (spec : Contract Input Abstract) :
    Sat model (spec.pullback observe) ↔ Sat (reduct observe model) spec := by
  constructor
  · intro h input hp
    obtain ⟨⟨observation, ho⟩, hpost⟩ := h input hp
    refine ⟨⟨observe observation, observation, ho, rfl⟩, ?_⟩
    rintro abstract ⟨concrete, hc, rfl⟩
    exact hpost concrete hc
  · intro h input hp
    obtain ⟨⟨abstract, concrete, hc, _⟩, hpost⟩ := h input hp
    exact ⟨⟨concrete, hc⟩, fun observation ho => hpost _ ⟨observation, ho, rfl⟩⟩

@[simp] theorem reduct_id {Input Observation : Type u} (model : Model Input Observation) :
    reduct id model = model := by
  funext input
  exact Set.image_id _

theorem reduct_comp {Input A B C : Type u} (first : B → A) (second : C → B)
    (model : Model Input C) :
    reduct (first ∘ second) model = reduct first (reduct second model) := by
  funext input
  exact (Set.image_image first second (model input)).symm

/-- A signature records the observation type exposed by one representation. -/
structure Signature where
  Observation : Type u

/-- Signature maps point from abstract to concrete interfaces; their observation
maps run backwards, from concrete observations to abstract observations. -/
instance : Category Signature.{u} where
  Hom source target := target.Observation → source.Observation
  id _ := id
  comp first second := first ∘ second
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Contracts and call relations over one observation signature. -/
def room (Input : Type u) (signature : Signature.{u}) : Room.{u, u, u} where
  Sen := Contract Input signature.Observation
  Mod := Cat.of (Discrete (Model Input signature.Observation))
  Sat model spec := Sat model.as spec

/-- The corridor induced by an observation map. Models form a discrete category:
semantic refinement is supplied separately, rather than confused with exact
satisfaction-preserving change of signature. -/
def corridor (Input : Type u) {source target : Signature.{u}} (observe : source ⟶ target) :
    room Input source ⟶ room Input target where
  sen := Contract.pullback observe
  mod := Discrete.functor fun model => Discrete.mk (reduct observe model)
  sat model spec := sat_pullback observe model.as spec

/-- The contract institution, with genuine sentence/model translation and the
satisfaction condition of the existing institution framework. -/
def institution (Input : Type u) : Signature.{u} ⥤ Room.{u, u, u} where
  obj := room Input
  map observe := corridor Input observe
  map_id _ := Room.hom_ext rfl
    (Functor.ext (fun model => congrArg Discrete.mk (reduct_id model.as))
      (fun _ _ _ => Discrete.hom_eq))
  map_comp first second := Room.hom_ext rfl
    (Functor.ext (fun model => congrArg Discrete.mk (reduct_comp first second model.as))
      (fun _ _ _ => Discrete.hom_eq))

/-- A refinement removes possible outcomes while preserving their existence.
The second condition prevents an empty implementation from refining a usable
specification merely by having a subset of its outcomes. -/
structure Refines {Input Observation : Type u}
    (abstract concrete : Model Input Observation) : Prop where
  outcomes : ∀ input, concrete input ⊆ abstract input
  progress : ∀ input, (abstract input).Nonempty → (concrete input).Nonempty

theorem Refines.refl {Input Observation : Type u} (model : Model Input Observation) :
    Refines model model :=
  ⟨fun _ => Set.Subset.refl _, fun _ => id⟩

theorem Refines.trans {Input Observation : Type u} {first second third : Model Input Observation}
    (hfirst : Refines first second) (hsecond : Refines second third) : Refines first third :=
  ⟨fun input => (hsecond.outcomes input).trans (hfirst.outcomes input),
    fun input h => hsecond.progress input (hfirst.progress input h)⟩

/-- Correctness transfers to a refinement, including existence of an outcome. -/
theorem sat_of_refines {Input Observation : Type u} {abstract concrete : Model Input Observation}
    {spec : Contract Input Observation} (refinement : Refines abstract concrete)
    (correct : Sat abstract spec) : Sat concrete spec := by
  intro input hp
  obtain ⟨hexists, hpost⟩ := correct input hp
  exact ⟨refinement.progress input hexists,
    fun observation ho => hpost observation (refinement.outcomes input ho)⟩

/-- Observation reduction preserves semantic refinement. -/
theorem Refines.reduct {Input Abstract Concrete : Type u} (observe : Concrete → Abstract)
    {first second : Model Input Concrete} (h : Refines first second) :
    Refines (reduct observe first) (reduct observe second) := by
  constructor
  · rintro input abstract ⟨concrete, hc, rfl⟩
    exact ⟨concrete, h.outcomes input hc, rfl⟩
  · rintro input ⟨abstract, concrete, hc, _⟩
    obtain ⟨next, hn⟩ := h.progress input ⟨concrete, hc⟩
    exact ⟨observe next, next, hn, rfl⟩

/-- Transport a high-level contract to concrete executions using a semantic
refinement of the reduced concrete model. This is the institution satisfaction
condition followed by correctness preservation under refinement. -/
theorem transport {Input Abstract Concrete : Type u} (observe : Concrete → Abstract)
    {abstract : Model Input Abstract} {concrete : Model Input Concrete}
    {spec : Contract Input Abstract} (refinement : Refines abstract (reduct observe concrete))
    (correct : Sat abstract spec) : Sat concrete (spec.pullback observe) :=
  (sat_pullback observe concrete spec).2 (sat_of_refines refinement correct)

/-- Refinement obligations restricted to the inputs admitted by a contract.
Nothing about malformed arguments or unavailable ownership is assumed here. -/
structure RefinesOn {Input Observation : Type u} (domain : Input → Prop)
    (abstract concrete : Model Input Observation) : Prop where
  outcomes : ∀ input, domain input → concrete input ⊆ abstract input
  progress : ∀ input, domain input → (abstract input).Nonempty → (concrete input).Nonempty

theorem RefinesOn.trans {Input Observation : Type u} {domain : Input → Prop}
    {first second third : Model Input Observation}
    (hfirst : RefinesOn domain first second) (hsecond : RefinesOn domain second third) :
    RefinesOn domain first third :=
  ⟨fun input hp => (hsecond.outcomes input hp).trans (hfirst.outcomes input hp),
    fun input hp h => hsecond.progress input hp (hfirst.progress input hp h)⟩

/-- A contract needs refinement only on its own precondition. -/
theorem sat_of_refines_on {Input Observation : Type u}
    {abstract concrete : Model Input Observation} {spec : Contract Input Observation}
    (refinement : RefinesOn spec.pre abstract concrete) (correct : Sat abstract spec) :
    Sat concrete spec := by
  intro input hp
  obtain ⟨hexists, hpost⟩ := correct input hp
  exact ⟨refinement.progress input hp hexists,
    fun observation ho => hpost observation (refinement.outcomes input hp ho)⟩

/-- Transport with refinement obligations confined to the high-level
contract's precondition, convenient for C calls with validity/ownership premises. -/
theorem transport_on {Input Abstract Concrete : Type u} (observe : Concrete → Abstract)
    {abstract : Model Input Abstract} {concrete : Model Input Concrete}
    {spec : Contract Input Abstract}
    (refinement : RefinesOn spec.pre abstract (reduct observe concrete))
    (correct : Sat abstract spec) : Sat concrete (spec.pullback observe) :=
  (sat_pullback observe concrete spec).2 (sat_of_refines_on refinement correct)

/-- Proofs through two abstraction layers compose without relating their syntax.
Each layer supplies its own relation and observation/refinement proof; the final
postcondition observes the concrete result through the composed maps. -/
theorem transport_comp {Input A B C : Type u} (firstObserve : B → A) (secondObserve : C → B)
    {first : Model Input A} {second : Model Input B} {third : Model Input C}
    {spec : Contract Input A}
    (firstRefinement : RefinesOn spec.pre first (reduct firstObserve second))
    (secondRefinement : RefinesOn spec.pre second (reduct secondObserve third))
    (correct : Sat first spec) : Sat third (spec.pullback (firstObserve ∘ secondObserve)) :=
  transport_on secondObserve secondRefinement (transport_on firstObserve firstRefinement correct)

end Silmaril.Logic.Institution.Bridges.Contracts
