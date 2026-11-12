module

public import Silmaril.Raw.SSA.Isotope.Institution.Refinement.Signature
public import Silmaril.Logic.Institution.Morphism

@[expose] public section

/-!
# The refinement institution

Over a presented signature `P` (`PSig`):

* a *typed inequation* `a ⊑ b` is a pair of syntax elements of one sort (`Pair P`);
* a *sentence* is a finite conjunction of typed inequations (`Sentence P := List (Pair P)`);
* a *model* is an ordered algebra (`TheoryModel.OrderedAlgebra`): partially ordered carriers
  with monotone operations, and monotone homomorphisms;
* `M ⊨ a ⊑ b` when the unique folds satisfy `⟦a⟧ ≤ ⟦b⟧`, and a conjunction holds when each
  conjunct does.

Sentences translate by the syntax translation of `PSig.translate`, and models restrict by the
ordered reduct `TheoryModel.OrderedAlgebra.reduct`, the functor that underlies the Isotope model
restrictions `OrderedModels.reindex`. The satisfaction condition is `Pair.holds_map`, from
`TheoryModel.reindex_fold_map`.

Sentences are *conjunctions* rather than single inequations because the institution core
(`Silmaril.Logic.Institution`) translates one sentence to one sentence along a comorphism, and
the comparison with the equational institution sends an equation `a = b` to the pair
`a ⊑ b ∧ b ⊑ a` (`Comorphism.lean`).

## Main definitions

* `Pair`, `Pair.map`, `Pair.swap`, `Pair.Holds`; `Sentence`, `Sentence.map`, `Sentence.Holds`.
* `room`, `corridor`, `institution : PSig ⥤ Room`, the bundled `inst`.

## Main results

* `Pair.holds_map`, `Sentence.holds_map`: the satisfaction condition.
-/

namespace Silmaril.Isotope.Institution.Refinement

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel Silmaril.Logic.Metatheory.TheoryModel
open PSig

universe u v w

variable {P Q R : PSig.{u, v, w}}

/-- Two syntax elements of one sort: read as the inequation `a ⊑ b` in the refinement
institution and as the equation `a = b` in the equational institution. -/
abbrev Pair (P : PSig.{u, v, w}) : Type (max u w) :=
  Σ i : P.Index, P.syn.Carrier i × P.syn.Carrier i

namespace Pair

/-- Translate both sides along a signature morphism. -/
def map (f : P ⟶ Q) (φ : Pair P) : Pair Q :=
  ⟨(toSig f).sort φ.1, (translate f).map φ.2.1, (translate f).map φ.2.2⟩

/-- Exchange the two sides. -/
def swap (φ : Pair P) : Pair P := ⟨φ.1, φ.2.2, φ.2.1⟩

theorem map_id (φ : Pair P) : φ.map (𝟙 P) = φ := by
  have h : translate (𝟙 P) = 𝟙 P.syn := P.isInitial.hom_ext _ _
  unfold map
  rw [h]
  rfl

theorem map_comp (f : P ⟶ Q) (g : Q ⟶ R) (φ : Pair P) : φ.map (f ≫ g) = (φ.map f).map g := by
  obtain ⟨i, a, b⟩ := φ
  show (⟨(toSig (f ≫ g)).sort i, (translate (f ≫ g)).map a, (translate (f ≫ g)).map b⟩ :
      Pair R) =
    ⟨(toSig g).sort ((toSig f).sort i), (translate g).map ((translate f).map a),
      (translate g).map ((translate f).map b)⟩
  rw [translate_comp_map, translate_comp_map]
  rfl

theorem swap_map (f : P ⟶ Q) (φ : Pair P) : (φ.map f).swap = φ.swap.map f := rfl

/-- An ordered algebra validates `a ⊑ b` when `⟦a⟧ ≤ ⟦b⟧`. -/
def Holds (M : OrderedAlgebra.{u, v, w} P.sig) (φ : Pair P) : Prop :=
  P.eval M.toAlgebra φ.2.1 ≤ P.eval M.toAlgebra φ.2.2

/-- The satisfaction condition for typed inequations. -/
theorem holds_map (f : P ⟶ Q) (M : OrderedAlgebra.{u, v, w} Q.sig) (φ : Pair P) :
    (φ.map f).Holds M ↔ φ.Holds ((OrderedAlgebra.reduct (toSig f)).obj M) := by
  obtain ⟨i, a, b⟩ := φ
  show Q.eval M.toAlgebra ((translate f).map a) ≤ Q.eval M.toAlgebra ((translate f).map b) ↔
    P.eval ((OrderedAlgebra.reduct (toSig f)).obj M).toAlgebra a ≤
      P.eval ((OrderedAlgebra.reduct (toSig f)).obj M).toAlgebra b
  rw [eval_orderedReduct, eval_orderedReduct]
  exact Iff.rfl

end Pair

/-- Sentences of the refinement institution: finite conjunctions of typed inequations. -/
abbrev Sentence (P : PSig.{u, v, w}) : Type (max u w) := List (Pair P)

namespace Sentence

/-- Translate every conjunct. -/
def map (f : P ⟶ Q) (s : Sentence P) : Sentence Q := List.map (Pair.map f) s

/-- A conjunction holds when every conjunct holds. -/
def Holds (M : OrderedAlgebra.{u, v, w} P.sig) (s : Sentence P) : Prop := ∀ φ ∈ s, φ.Holds M

theorem map_id (s : Sentence P) : Sentence.map (𝟙 P) s = s := by
  induction s with
  | nil => rfl
  | cons φ s ih => exact congrArg₂ List.cons (Pair.map_id φ) ih

theorem map_comp (f : P ⟶ Q) (g : Q ⟶ R) (s : Sentence P) :
    Sentence.map (f ≫ g) s = Sentence.map g (Sentence.map f s) := by
  induction s with
  | nil => rfl
  | cons φ s ih => exact congrArg₂ List.cons (Pair.map_comp f g φ) ih

/-- The satisfaction condition for conjunctions. -/
theorem holds_map (f : P ⟶ Q) (M : OrderedAlgebra.{u, v, w} Q.sig) (s : Sentence P) :
    Sentence.Holds M (Sentence.map f s) ↔
      Sentence.Holds ((OrderedAlgebra.reduct (toSig f)).obj M) s := by
  constructor
  · intro h φ hφ
    exact (Pair.holds_map f M φ).1 (h _ (List.mem_map.2 ⟨φ, hφ, rfl⟩))
  · intro h ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
    exact (Pair.holds_map f M φ).2 (h φ hφ)

end Sentence

/-- The room of a presented signature: conjunctions of inequations, ordered algebras, and
ordered satisfaction. -/
def room (P : PSig.{u, v, w}) : Room.{max u w, max u w, max u v (w + 1)} :=
  ⟨Sentence P, Cat.of (OrderedAlgebra.{u, v, w} P.sig),
    fun (M : OrderedAlgebra.{u, v, w} P.sig) s => Sentence.Holds M s⟩

/-- The corridor of a signature morphism: translate sentences, restrict ordered models. -/
def corridor (f : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Sentence.map f, OrderedAlgebra.reduct (toSig f),
    fun (M : OrderedAlgebra.{u, v, w} Q.sig) s => Sentence.holds_map f M s⟩

theorem corridor_id (P : PSig.{u, v, w}) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Sentence.map_id) rfl

theorem corridor_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    corridor (f ≫ g) = corridor f ≫ corridor g :=
  Room.hom_ext (funext (Sentence.map_comp f g)) (orderedReduct_comp f g)

/-- The refinement institution of presented signatures: typed refinement inequations, ordered
models, and restriction of ordered models as reduct. -/
def institution : PSig.{u, v, w} ⥤ Room.{max u w, max u w, max u v (w + 1)} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

set_option linter.checkUnivs false in
/-- The refinement institution, bundled. (The signature, sentence and model universes are
`max`-expressions in `u`, `v`, `w` by construction.) -/
def inst : Inst.{max (u + 1) (v + 1) (w + 1), max u v, max u w, max u w, max u v (w + 1)} :=
  ⟨PSig.{u, v, w}, institution⟩

end Silmaril.Isotope.Institution.Refinement
