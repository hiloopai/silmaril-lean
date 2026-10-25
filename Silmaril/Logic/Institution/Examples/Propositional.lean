module

public import Silmaril.Logic.Institution.Morphism

@[expose] public section

/-!
# The institution of classical propositional logic

Signatures are sets of propositional variables and signature morphisms are functions (the
category `Type`). `Σ`-sentences are propositional formulas over `Σ` built from variables, `⊥`,
`→`, `∧` and `∨`; a signature morphism renames variables. `Σ`-models are valuations `Σ → Prop`,
with a (unique) morphism `v ⟶ v'` when every variable true under `v` is true under `v'`; the
reduct of a valuation along `σ` is precomposition with `σ`. Satisfaction is the truth-table
semantics, and the satisfaction condition is `Formula.eval_rename`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3
(the room CPL, with model morphisms as in footnote 8) and §4 (the institution CPL: "The
category of signatures is just the category of sets and functions … sentence translation replaces
propositional variables … reduced to M₂ ∘ σ").

Universes: everything is fixed so that propositional logic, many-sorted equational logic and
first-order logic are institutions over the same rooms `Room.{0, 0, 1}`, which lets them be
related by comorphisms.
-/

namespace Silmaril.Logic.Institution.Examples.PL

open CategoryTheory

/-- Propositional formulas over the variables `P`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3
(sentences of CPL "built by Boolean connectives") and §4. -/
inductive Formula (P : Type) : Type
  | var : P → Formula P
  | bot : Formula P
  | imp : Formula P → Formula P → Formula P
  | and : Formula P → Formula P → Formula P
  | or : Formula P → Formula P → Formula P

namespace Formula

variable {P Q R : Type}

/-- Renaming of propositional variables (sentence translation along a signature morphism).

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4
("sentence translation replaces propositional variables in the sentences according to σ"). -/
def rename (f : P → Q) : Formula P → Formula Q
  | var p => var (f p)
  | bot => bot
  | imp φ ψ => imp (rename f φ) (rename f ψ)
  | and φ ψ => and (rename f φ) (rename f ψ)
  | or φ ψ => or (rename f φ) (rename f ψ)

/-- Truth-table semantics under a valuation. -/
def eval (v : P → Prop) : Formula P → Prop
  | var p => v p
  | bot => False
  | imp φ ψ => eval v φ → eval v ψ
  | and φ ψ => eval v φ ∧ eval v ψ
  | or φ ψ => eval v φ ∨ eval v ψ

theorem rename_id : rename (id : P → P) = id := by
  (funext φ; induction φ <;> simp_all [rename])

theorem rename_comp (f : P → Q) (g : Q → R) : rename (g ∘ f) = rename g ∘ rename f := by
  (funext φ; induction φ <;> simp_all [rename])

/-- The satisfaction condition for propositional logic: evaluating a renamed formula is
evaluating the formula under the reduct valuation.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.2 (satisfaction condition), for the institution CPL described after it. -/
theorem eval_rename (f : P → Q) (v : Q → Prop) (φ : Formula P) :
    eval v (rename f φ) ↔ eval (v ∘ f) φ := by
  (induction φ <;> simp_all [rename, eval])

end Formula

/-- A propositional model (valuation). It is lifted to `Type 1` so that its category of models
lives in the same universe as algebras and first-order structures. -/
def Model (P : Type) : Type 1 := ULift.{1} (P → Prop)

/-- The valuation underlying a model. -/
def Model.val {P : Type} (v : Model P) : P → Prop := ULift.down v

/-- A model morphism `v ⟶ v'` exists (uniquely) when every variable true under `v` is true
under `v'`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
footnote 8. -/
instance (P : Type) : Category.{0} (Model P) where
  Hom v v' := PLift (∀ p, v.val p → v'.val p)
  id _ := ⟨fun _ h => h⟩
  comp f g := ⟨fun p h => g.down p (f.down p h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The reduct functor `Mod(σ)` of a renaming: precomposition.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4
("A Σ₂-model … is reduced to M₂|σ = M₂ ∘ σ"). -/
def Model.reduct {P Q : Type} (f : P → Q) : Model Q ⥤ Model P where
  obj v := ULift.up (v.val ∘ f)
  map h := ⟨fun p => h.down (f p)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The room of propositional logic over the variables `P`. -/
def room (P : Type) : Room.{0, 0, 1} :=
  ⟨Formula P, Cat.of (Model P), fun v φ => Formula.eval (Model.val v) φ⟩

/-- The corridor of a renaming `σ : P → Q`. -/
def corridor {P Q : Type} (σ : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Formula.rename σ, Model.reduct σ, fun v φ => Formula.eval_rename σ (Model.val v) φ⟩

theorem corridor_id (P : Type) : corridor (𝟙 P) = 𝟙 (room P) := by
  exact Room.hom_ext Formula.rename_id rfl

theorem corridor_comp {P Q R : Type} (σ : P ⟶ Q) (τ : Q ⟶ R) :
    corridor (σ ≫ τ) = corridor σ ≫ corridor τ := by
  exact Room.hom_ext (Formula.rename_comp σ τ) rfl

/-- The institution of classical propositional logic, as a functor `Set ⥤ Room`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.2 and the paragraph after it (CPL). -/
def institution : Type ⥤ Room.{0, 0, 1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

/-- Propositional logic as a bundled institution. -/
def inst : Inst.{1, 0, 0, 0, 1} := ⟨Type, institution⟩

end Silmaril.Logic.Institution.Examples.PL
