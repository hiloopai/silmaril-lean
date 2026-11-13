module

public import Silmaril.Automata.Spec.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# The machine institution

An institution (`Silmaril.Logic.Institution`: a functor `Sig ⥤ Room`) whose models are actual
machines and whose sentences are machine problems:

| institution | here |
| --- | --- |
| signatures | `Sig`: a type of state **names** `St` and a type of labels `Lb` |
| signature morphisms | `Sig.Hom`: maps of names and of labels (renaming, identification, extension) |
| sentences | `Sen Σ`: Boolean combinations of `step a l b` and `reach ls a b` |
| sentence translation | `Sen.map σ`: rename names and labels |
| models | `Model Σ`: a CSLib LTS over some state type `S`, labelled by `Σ.Lb`, with an interpretation `ι : Σ.St → S` of the names |
| model reduct | `Model.reduct σ`: keep states, relabel transitions along `σ.lb`, interpret names through `σ.st` |
| satisfaction | `Sat M φ` |

The models of a signature form a discrete category (machines are compared by the problem
shapes and the decision procedures, not by model morphisms).

**Sentences.** `step a l b`: one `l`-step from the state named `a` to the state named `b`;
`reach ls a b`: `b` is reachable from `a` using only labels in the list `ls` (zero or more
steps); negation and conjunction. Set reachability (`b` in a finite set) is a disjunction.

**The satisfaction condition** (`sat_map_iff` in `Thms`) holds for exactly this choice: a
reduct sees only the transitions whose labels are in the image of `σ.lb`, so *unrestricted*
reachability, deadlock freedom ("some label is enabled") and other sentences quantifying over
all labels are **not** invariant under reducts and are deliberately not sentences here. They
remain problems over single machines (`Silmaril.Automata.Shapes`), as do simulation and
bisimulation, which relate two models rather than state a property of one.
-/

namespace Silmaril.Automata.Inst

open CategoryTheory Silmaril.Logic.Institution

/-- A signature: state names and labels. -/
structure Sig where
  St : Type
  Lb : Type

/-- A signature morphism: maps of names and labels. -/
@[ext] structure Sig.Hom (A B : Sig) where
  st : A.St → B.St
  lb : A.Lb → B.Lb

instance : Category Sig where
  Hom := Sig.Hom
  id _ := ⟨id, id⟩
  comp σ τ := ⟨τ.st ∘ σ.st, τ.lb ∘ σ.lb⟩

/-- Sentences: machine problems over a signature. -/
inductive Sen (A : Sig) : Type where
  | step (a : A.St) (l : A.Lb) (b : A.St)
  | reach (ls : List A.Lb) (a b : A.St)
  | neg (φ : Sen A)
  | conj (φ ψ : Sen A)

/-- Sentence translation. -/
def Sen.map {A B : Sig} (σ : Sig.Hom A B) : Sen A → Sen B
  | .step a l b => .step (σ.st a) (σ.lb l) (σ.st b)
  | .reach ls a b => .reach (ls.map σ.lb) (σ.st a) (σ.st b)
  | .neg φ => .neg (φ.map σ)
  | .conj φ ψ => .conj (φ.map σ) (ψ.map σ)

/-- A model: a machine with an interpretation of the state names. -/
structure Model (A : Sig) : Type 1 where
  S : Type
  lts : Cslib.LTS S A.Lb
  ι : A.St → S

/-- Satisfaction. -/
def Sat {A : Sig} (M : Model A) : Sen A → Prop
  | .step a l b => M.lts.Tr (M.ι a) l (M.ι b)
  | .reach ls a b => ReachVia M.lts (· ∈ ls) (M.ι a) (M.ι b)
  | .neg φ => ¬ Sat M φ
  | .conj φ ψ => Sat M φ ∧ Sat M ψ

/-- The reduct of a model along a signature morphism. -/
def Model.reduct {A B : Sig} (σ : Sig.Hom A B) (M : Model B) : Model A :=
  ⟨M.S, ⟨fun s l s' => M.lts.Tr s (σ.lb l) s'⟩, M.ι ∘ σ.st⟩

/-- The signature of a typed machine: its states name themselves. -/
abbrev sigOf (S L : Type) : Sig := ⟨S, L⟩

/-- A typed machine as a model of its own signature. -/
def DMachine.model {S L : Type} (M : DMachine S L) : Model (sigOf S L) := ⟨S, M.toLTS, id⟩

/-- The model of a JSON spec: names are states. -/
def specModel (sp : Spec) : Model ⟨String, String⟩ := ⟨String, sp.toLTS, id⟩

/-- Naming, as a signature morphism from a typed machine's signature. -/
def nameHom (S L : Type) [FinNamed S] [FinNamed L] : Sig.Hom (sigOf S L) ⟨String, String⟩ :=
  ⟨FinNamed.name, FinNamed.name⟩

end Silmaril.Automata.Inst
