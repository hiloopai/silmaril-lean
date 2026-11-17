module

public import Silmaril.Logic.Consequence.Semantic.Defs
public import Silmaril.Logic.Consequence.Translation.Defs
public import Silmaril.Logic.Consequence.Institution.Defs
public import Silmaril.Logic.Concrete.Codec.Defs

/-!
# Interpretation, soundness and consistency

Four notions, kept apart. None is a property of a logic as a whole: each is about a system *and*
a context (a theory), relative to Lean's own consistency and to the stated models.

* **Satisfiability of a theory**: some model satisfies it (`Satisfaction.Satisfiable`,
  `Room.Satisfiable`).
* **Soundness of a system for an interpretation**: what it derives holds in every model of the
  premises, `S ≤ I.entails` (`System.SoundFor`).
* **Syntactic consistency** relative to a chosen falsity `ff`: the context does not derive `ff`
  (`System.ConsistentWrt`, existing). **Nontriviality**: some conclusion is not derived
  (`System.ContextConsistent`, existing). For an entailment relation (a closure on sets of
  sentences, the π-institution reading) the same two notions are `ER.ConsistentWrt` and
  `ER.Nontrivial`.
* **The bridge** (`Thms`): a system sound for an interpretation is consistent at every context
  that has a model in which `ff` fails (`consistentWrt_of_sound`). Consistency transports
  backwards along translations (`consistentWrt_of_translation`), and a system read over a concrete
  presentation (`viaCodec`) is consistent exactly when the abstract system is.

Consistency is never asserted for arbitrary added axioms: every theorem names its context and its
model.
-/

@[expose] public section

namespace Silmaril.Consequence

open Silmaril.Logic Silmaril.Logic.Institution Silmaril.Logic.Concrete

universe u v w

variable {Ax : Type u} {C : Type v}

/-- A context has a model. -/
def Satisfaction.Satisfiable (I : Satisfaction.{u, v, w} Ax C) (a : Ax) : Prop := ∃ m, I.satAx m a

/-- **Soundness for an interpretation**: every derived consequence holds in every model of the
premises. -/
def System.SoundFor (S : System Ax C) (I : Satisfaction.{u, v, w} Ax C) : Prop := S ≤ I.entails

/-- A set of sentences of a room has a model. -/
def Room.Satisfiable (R : Room) (Γ : Set R.Sen) : Prop := ∃ M : R.Mod, ∀ φ ∈ Γ, R.Sat M φ

/-- An entailment relation (π-institution closure) does not derive `ff` from `Γ`. -/
def ER.ConsistentWrt (E : Metatheory.ER.{w}) (ff : E.Sen) (Γ : Set E.Sen) : Prop :=
  ¬ E.Derives Γ ff

/-- An entailment relation's closure of `Γ` is not everything. -/
def ER.Nontrivial (E : Metatheory.ER.{w}) (Γ : Set E.Sen) : Prop := ∃ φ, ¬ E.Derives Γ φ

/-- **A system read over a concrete presentation**: premises and conclusion are the
S-expressions of the presentation `c`, and the system is the abstract one on what they present. -/
noncomputable def System.viaCodec {A : Type u} (S : System (List A) A) (c : SExpCodec A) :
    System (List c.Sen) c.Sen :=
  S.pullback (List.map SExpCodec.Sen.toAbs) SExpCodec.Sen.toAbs

end Silmaril.Consequence
