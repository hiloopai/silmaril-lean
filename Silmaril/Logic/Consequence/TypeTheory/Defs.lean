module

public import Silmaril.Logic.Consequence.Theory.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.Defs
public import Silmaril.Logic.TypeTheory.LambdaPi.Institution.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Defs

/-!
# Martin-Löf type theories as consequence systems

Three of the type theories in `Silmaril.Logic.TypeTheory`, each with its derivability relation
on judgments read as `J₁, …, Jₙ ⊢ J`, and, where the library has one, a semantic consequence:

| theory | sentences | derivability | semantic consequence |
|---|---|---|---|
| extensional MLTT (cumulative universes, `Π`, `Σ`, `ℕ`, `Id` with reflection) | judgments `Γ ⊢ a ≡ b : A` (`EJdg`, lifted by `ULift.up` into the room's sentences) | `extensionalDerives` (`ECtx.JEqH`) | `extensionalEntails`: validity in set hierarchies |
| intensional MLTT (Martin-Löf's original rules with `J`), at a universe stage | scoped typings `Γ ⊢ t : A` | `intensionalDerives stage` (proof trees within the stage) | `intensionalEntails stage`: realizability at a capacity |
| `λΠ` modulo rewriting, per calculus `C` | typings `Γ ⊢ t : A` | `lambdaPiDerives C` | none here (see below) |

**Contexts.** An MLTT context `Γ` is part of each judgment: in `Γ ⊢ J` the context is not a list
of premises. The premises of these consequence systems are *judgment hypotheses*. `[J₁, …, Jₙ] ⊢ J`
says that `J` has a derivation in which the `Jᵢ` may be used as leaves (hypothetical
derivability, the rule-level consequence of the calculus). Identity, weakening and cut hold for
these premises, because each relation is a logical system's derivability (`Thms`). Weakening and
substitution *of the context `Γ` of a judgment* are different: they are admissible rules of the
type theory, stated over judgments (for example `IntensionalMLTT.Substitution`), not laws of this
consequence relation.

**Soundness, never completeness.** Each semantic consequence above receives the derivability
relation by a soundness theorem of its logic (`Thms`). For `λΠ`, the library's logic is paired
with the *syntactic* model class of closed theories (`Institution.Syntactic.room`), whose
consequence coincides with derivability by construction. That is no semantics of `λΠ`, so it is
not offered as one here.
-/

@[expose] public section

namespace Silmaril.Consequence.TypeTheory

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution Silmaril.Logic.TypeTheory

universe u

/-! ## Extensional MLTT -/

/-- **Extensional MLTT derivability**: `J` has a derivation with the `Jᵢ` as hypotheses. The
logic's sentences are judgments lifted to the universe of its room; this is its derivability
on the judgments themselves (`ULift.up`). -/
def extensionalDerives : System (List ExtensionalMLTT.EJdg) ExtensionalMLTT.EJdg :=
  (LogicalSystem.listSys ExtensionalMLTT.Institution.logic.{0} ⟨⟨⟩⟩).pullback
    (List.map ULift.up) ULift.up

/-- **Extensional MLTT semantic consequence**: validity in every set hierarchy (in universe
`u`), read on the judgments themselves. -/
def extensionalEntails : System (List ExtensionalMLTT.EJdg) ExtensionalMLTT.EJdg :=
  (roomSeq ExtensionalMLTT.Institution.room.{u}).pullback (List.map ULift.up) ULift.up

/-- **Extensional MLTT with `levels` universe levels**: the bounded rules (`ECtx.JEqB`, every
universe index below `levels`), with judgment hypotheses, on the bounded judgments. -/
def boundedDerives (levels : ℕ) :=
  LogicalSystem.listSys (ExtensionalMLTT.Finite.logic.{u} levels) ⟨⟨⟩⟩

/-! ## Intensional MLTT (original rules) -/

/-- Scoped typings of intensional MLTT within a universe stage. -/
abbrev IntensionalJudgment (stage : IntensionalMLTT.OriginalInstitution.Stage) : Type :=
  IntensionalMLTT.OriginalInstitution.Sentence stage

/-- **Intensional MLTT derivability** at a stage: a proof tree of the original rules within
the stage, with the `Jᵢ` as leaves. -/
noncomputable def intensionalDerives (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    System (List (IntensionalJudgment stage)) (IntensionalJudgment stage) :=
  LogicalSystem.listSys (IntensionalMLTT.OriginalInstitution.logic stage) ⟨⟨⟩⟩

/-- **Intensional MLTT semantic consequence** at a stage: realizability at every capacity that
supplies the stage. -/
noncomputable def intensionalEntails (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    System (List (IntensionalJudgment stage)) (IntensionalJudgment stage) :=
  roomSeq (IntensionalMLTT.OriginalInstitution.room stage)

/-! ## `λΠ` modulo rewriting -/

/-- **`λΠ` derivability** in a calculus `C` (a signature with rewrite rules). -/
noncomputable def lambdaPiDerives (C : LambdaPi.Calculus) :
    System (List LambdaPi.Judgment) LambdaPi.Judgment :=
  LogicalSystem.listSys C.logic ⟨⟨⟩⟩

end Silmaril.Consequence.TypeTheory
