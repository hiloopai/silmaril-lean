module

public import Silmaril.Servers.Observe.Defs
import Silmaril.Proofs.Servers.Observe.Basic

/-!
# Observations after initialization: theorems

* **Refinement is a preorder and equivalence is its kernel**: `Beh.Refines` is reflexive and
  transitive, `Beh.Equiv` is equality, and equality is refinement both ways
  (`Beh.equiv_iff_eq`, `Beh.eq_iff_refines`).
* **Universal properties go down, existential ones go up**: a refinement satisfies every
  `Must` property of its specification (`Beh.must_of_refines`, so `InitSafe` and `NoStop`
  too), and a specification has every `May` property of its refinements
  (`Beh.may_of_refines`). The converse directions fail: the empty behaviour refines every
  behaviour (`Beh.empty_refines`) and cannot initialize (`Beh.not_canInit_empty`).
* **The core model is the running part**: `traces (ofModel M) = M`, refinement of `ofModel`s is
  core refinement (`Beh.ofModel_refines_iff`), and on healthy behaviours a trace sentence holds
  of all observations iff the core model satisfies it (`Beh.must_sen_iff`). A model whose
  initialization cannot fail is `InitSafe` (`Beh.initSafe_withInit`); for the behaviour of a
  core model, the universal reading is satisfaction (`Beh.must_ofModel_iff`).
* **The quotient**: implementations are related by `implPreorder d` exactly when their
  denotations are; two are identified in the quotient iff their behaviours are equal
  (`mk_eq_iff`); the normalized behaviour is injective on the quotient (`norm_injective`), so
  the quotient, ordered by refinement (`Norm.partialOrder`), is the set of trace languages
  realized by implementations, ordered by inclusion (`norm_le_iff`).
-/

@[expose] public section

namespace Silmaril.Servers.Observe

open Silmaril.Servers

namespace Beh

variable {A : Sig}

theorem Refines.refl (B : Beh A) : B.Refines B := subset_rfl

theorem Refines.trans {I M S : Beh A} (h₁ : I.Refines M) (h₂ : M.Refines S) : I.Refines S :=
  subset_trans h₁ h₂

/-- Observational equivalence is equality of behaviours. -/
theorem equiv_iff_eq {I S : Beh A} : I.Equiv S ↔ I = S := Set.ext_iff.symm

/-- **Equality is refinement both ways** (antisymmetry). -/
theorem eq_iff_refines {I S : Beh A} : I = S ↔ I.Refines S ∧ S.Refines I :=
  Set.Subset.antisymm_iff

/-- A refinement satisfies every universal property of its specification. -/
theorem must_of_refines {I S : Beh A} (h : I.Refines S) {φ : Obs A → Prop} (hS : S.Must φ) :
    I.Must φ := fun o ho => hS o (h ho)

/-- A specification has every existential property of its refinements. -/
theorem may_of_refines {I S : Beh A} (h : I.Refines S) {φ : Obs A → Prop} (hI : I.May φ) :
    S.May φ := let ⟨o, ho, hφ⟩ := hI; ⟨o, h ho, hφ⟩

theorem initSafe_of_refines {I S : Beh A} (h : I.Refines S) (hS : S.InitSafe) : I.InitSafe :=
  must_of_refines h hS

theorem noStop_of_refines {I S : Beh A} (h : I.Refines S) (hS : S.NoStop) : I.NoStop :=
  must_of_refines h hS

/-- **The empty behaviour refines every behaviour**: refinement alone is a safety relation. -/
theorem empty_refines (S : Beh A) : (∅ : Beh A).Refines S := Set.empty_subset S

/-- The empty behaviour cannot initialize: `CanInit` is not preserved by refinement. -/
theorem not_canInit_empty : ¬ (∅ : Beh A).CanInit := fun ⟨_, h, _⟩ => h

theorem traces_mono {I S : Beh A} (h : I.Refines S) : I.traces ≤ S.traces := fun _ ht => h ht

theorem traces_ofModel (M : Model A) : (ofModel M).traces = M := by
  apply Model.ext; funext t; apply propext
  exact ⟨fun ⟨_, he, ht⟩ => by cases he; exact ht, fun ht => ⟨t, rfl, ht⟩⟩

/-- Refinement of the behaviours of core models is core refinement. -/
theorem ofModel_refines_iff {M N : Model A} : (ofModel M).Refines (ofModel N) ↔ M.Refines N :=
  ⟨fun h t ht => (traces_ofModel N) ▸ h ⟨t, rfl, ht⟩,
    fun h _ ⟨t, he, ht⟩ => ⟨t, he, h t ht⟩⟩

theorem healthy_ofModel {M : Model A} (hp : ∀ t t', M.Tr (t ++ t') → M.Tr t) :
    (ofModel M).Healthy :=
  ⟨fun t t' ⟨_, he, ht⟩ => by cases he; exact ⟨t, rfl, hp t t' ht⟩,
    fun t ⟨_, he, _⟩ => by cases he⟩

/-- A model whose initialization cannot fail never fails to initialize. -/
theorem initSafe_withInit (M : Model A) : (withInit False M).InitSafe :=
  Proofs.Servers.Observe.initSafe_withInit M

/-- **On healthy behaviours, a trace sentence holds of every observation iff the core model of
the running traces satisfies it.** -/
theorem must_sen_iff {B : Beh A} (hB : B.Healthy) (φ : Sen A) :
    B.Must (Obs.sen φ) ↔ B.traces.Sat φ :=
  Proofs.Servers.Observe.must_sen_iff hB φ

/-- A trace sentence holds of every observation of a core model's behaviour iff the model
satisfies it. -/
theorem must_ofModel_iff (M : Model A) (φ : Sen A) : (ofModel M).Must (Obs.sen φ) ↔ M.Sat φ :=
  ⟨fun h t ht => h _ ⟨t, rfl, ht⟩, fun h _ ⟨t, he, ht⟩ => he ▸ h t ht⟩

end Beh

/-! ## The quotient -/

section Impl

variable {A : Sig} {ι : Type} (d : ι → Beh A)

theorem implPreorder_le_iff (i j : ι) : (implPreorder d).le i j ↔ (d i).Refines (d j) := Iff.rfl

/-- Two implementations are identified in the quotient iff their behaviours are equal. -/
theorem mk_eq_iff (i j : ι) :
    (Quotient.mk (obsSetoid d) i = Quotient.mk (obsSetoid d) j) ↔ d i = d j :=
  Quotient.eq (r := obsSetoid d)

theorem norm_mk (i : ι) : norm d (Quotient.mk (obsSetoid d) i) = d i := rfl

/-- **The normalized behaviour is injective**: a class is its trace language. -/
theorem norm_injective : Function.Injective (norm d) := Setoid.kerLift_injective d

/-- **The antisymmetric quotient**, ordered by refinement of normalized behaviours. -/
@[instance_reducible]
def Norm.partialOrder : PartialOrder (Quotient (obsSetoid d)) :=
  PartialOrder.lift (norm d) (norm_injective d)

theorem norm_le_iff (i j : ι) :
    (Norm.partialOrder d).le (Quotient.mk _ i) (Quotient.mk _ j) ↔ (d i).Refines (d j) :=
  Iff.rfl

end Impl

end Silmaril.Servers.Observe
