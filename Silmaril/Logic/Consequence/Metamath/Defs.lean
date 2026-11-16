module

public import Silmaril.Logic.Consequence.Theory.Defs
public import Silmaril.Logic.Institution.Metatheory.Metamath
public import Silmaril.Logic.Metamath.Peano.Axioms
public import Silmaril.Logic.Metamath.Peano.ZFC

/-!
# Metamath as consequence systems: the logic, PA, ZF and ZFC

Metamath's own proof system read as consequence systems over a grammar `X`
(`Metatheory.MMSig`: rule labels, constants, infinitely many variables and a grammar).

**Sentences** are well-formed tree *assertions* (`Grammar.TWFAssertion X.G`): frames with
disjoint-variable (DV) conditions, floating and essential hypotheses and a conclusion. A DV condition
is part of the sentence it constrains. It is not a premise and not a side condition of the
consequence system: a derivation may apply an assertion only under a substitution that is
*DV-safe* for it (`Grammar.TDerivation`, `Metamath.Derivation.app`), and that is how the conditions
restrict consequence.

**Derivability** (`derives X`): `[A₁, …, Aₙ] ⊢ A` when `A` is tree-derivable
(`Grammar.TDerivable`) with the `Aᵢ` as axioms. That is Metamath's checking of a `$p` statement
against the `$a` statements it uses, at the level of parse trees. The relation is Tarskian
(`Metatheory.Metamath.er`). Its cut rule is cut admissibility, which needs infinitely many
variables, hence `MMSig`.

**Semantic consequence** (`entails X`): Carneiro's models of a grammar
(`Metamath.Model`, `Model.Satisfies`), through the room `Metatheory.Metamath.room X`. Soundness is
`Metamath.Model.sound` (Carneiro, *Models for Metamath*, Theorem 1). Completeness is not claimed.

**Theories** (`theory X T`, `theoryEntails X T`): `Γ ⊢_T A` when `T ∪ Γ ⊢ A`, by
`Consequence.theoryOf`. The theories here are the axiom sets transcribed from Metamath databases:

* `PA`: the 30 axioms of `peano.mm` over its grammar `pa` (`Metamath.Peano.PA`);
* `ZF0` and `ZFC`: the axioms of set.mm's ZF and ZFC over the grammar `zf` of its set-theory
  fragment (`Metamath.Peano.ZF.ZF0`, `.ZFC`; `ZF0` omits `ax-ac`);
* `setMMZFC`: set.mm's ZFC over set.mm's grammar (`Metatheory.Metamath.setMM`, `.zfc`).

The arithmetic soundness of ZF and ZFC (`Metamath.Peano.ToZF.arithSound_ZFC`, `arithSound_ZF`) is
a fact about one translation of arithmetic *sentences*. It does not translate PA derivations into
ZF or ZFC derivations, so it is not a map between these consequence systems.
-/

@[expose] public section

namespace Silmaril.Consequence.Metamath

open Silmaril.Logic Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Metatheory (MMSig)
open Silmaril.Logic.Metamath.Grammar (TWFAssertion TAssertion)

universe u w

/-- The sentences of a Metamath signature: its well-formed tree assertions. -/
abbrev Sen (X : MMSig.{u}) : Type u := TWFAssertion X.G

/-- **Metamath derivability**: `[A₁, …, Aₙ] ⊢ A` when `A` is tree-derivable from the `Aᵢ`. -/
def derives (X : MMSig.{u}) : System (List (Sen X)) (Sen X) :=
  ER.listSys (Metatheory.Metamath.er X)

/-- **Semantic consequence** in Carneiro's models (domains in universe `w`). -/
def entails (X : MMSig.{u}) : System (List (Sen X)) (Sen X) :=
  roomSeq (Metatheory.Metamath.room.{u, w} X)

/-- **Derivability from a theory**: `A` is tree-derivable from `T` and the `Aᵢ`. -/
def theory (X : MMSig.{u}) (T : Set (Sen X)) : System (List (Sen X)) (Sen X) :=
  ER.theorySys (Metatheory.Metamath.er X) T

/-- **Semantic consequence over the models of a theory.** -/
def theoryEntails (X : MMSig.{u}) (T : Set (Sen X)) : System (List (Sen X)) (Sen X) :=
  roomTheorySeq (Metatheory.Metamath.room.{u, w} X) T

/-- The well-formed members of a set of tree assertions, as sentences. -/
def axiomsOf (X : MMSig.{u}) (A : Set (TAssertion X.L X.C X.V)) : Set (Sen X) := {B | B.1 ∈ A}

/-! ## Databases -/

/-- The grammar of `peano.mm`. -/
def pa : MMSig.{0} := ⟨Logic.Metamath.Peano.L, Logic.Metamath.Peano.C, Logic.Metamath.Peano.V,
  Logic.Metamath.Peano.grammar⟩

/-- The grammar of set.mm's set-theory fragment (wff and setvar syntax, `=` and `∈`). -/
def zf : MMSig.{0} := ⟨Logic.Metamath.Peano.ZF.L, Logic.Metamath.Peano.ZF.C,
  Logic.Metamath.Peano.ZF.V, Logic.Metamath.Peano.ZF.grammar⟩

/-- The axioms of `peano.mm`. -/
def PA : Set (Sen pa) := axiomsOf pa Logic.Metamath.Peano.PA

/-- set.mm's ZF axioms (ZFC without `ax-ac`). -/
def ZF0 : Set (Sen zf) := axiomsOf zf Logic.Metamath.Peano.ZF.ZF0

/-- set.mm's ZFC axioms. -/
def ZFC : Set (Sen zf) := axiomsOf zf Logic.Metamath.Peano.ZF.ZFC

/-- **Peano arithmetic**, as derivability from `PA` over the grammar of `peano.mm`. -/
def paTheory : System (List (Sen pa)) (Sen pa) := theory pa PA

/-- **ZF**, as derivability from `ZF0`. -/
def zfTheory : System (List (Sen zf)) (Sen zf) := theory zf ZF0

/-- **ZFC**, as derivability from `ZFC`. -/
def zfcTheory : System (List (Sen zf)) (Sen zf) := theory zf ZFC

/-- **set.mm's ZFC**, over the grammar of all of set.mm. -/
def setMMZFCTheory : System (List (Sen Metatheory.Metamath.setMM))
    (Sen Metatheory.Metamath.setMM) :=
  theory Metatheory.Metamath.setMM Metatheory.Metamath.zfc

end Silmaril.Consequence.Metamath
