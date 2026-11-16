module

public import Silmaril.Logic.Consequence.HOL.Defs
public import Silmaril.Logic.Consequence.TypeTheory.Defs
public import Silmaril.Logic.HOLLight.SExp.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Defs
public import Silmaril.Logic.Institution.Morphism

/-!
# Institutions and consequence systems over concrete (S-expression) syntax

HOL and extensional MLTT over their S-expression syntaxes (`Silmaril.Logic.HOLLight.SExp`,
`Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp`), related to the abstract syntax.

**Sentences.** A concrete sentence is an S-expression that denotes an abstract one:
* `HOLSen S`: the concrete form of a HOL proposition over `S`, a term of type `bool`;
* `HOLSequent S`: `(sequent (h₁ … hₙ) c)` with concrete propositions `hᵢ` and `c`;
* `MLTTSen`: the concrete form of an extensional MLTT judgment, `(jdg Γ A a b)`.

**The relation to the abstract syntax.** `HOLSen.toProp` and `MLTTSen.toJdg` send a concrete
sentence to what it denotes. They are bijections, with inverses `HOLSen.ofProp` and
`MLTTSen.ofJdg` (`Thms`). The decoders compute them (`Thms`: `decodeTm_toProp`,
`decodeJdg_toJdg`). A concrete sequent lists its hypotheses, so `HOLSequent.toSeq`, onto the
sequents of the HOL institution (hypotheses are a finite set), forgets their order and
repetitions: many concrete sequents denote one sentence.

**Consequence systems** are the abstract ones read through the relation, `System.pullback`:
* `holKernel S Δ`, `holSeq S`: the HOL kernel from axioms `Δ` and the sequent semantics;
* `mlttDerives`, `mlttEntails`: extensional MLTT derivability and validity in set hierarchies.

**Institutions.** `holRoom S` and `mlttRoom` have the concrete sentences and the abstract models,
and satisfaction through the relation. The corridors `holCorridor S : holRoom S ⟶ HOL.room S` and
`mlttCorridor : mlttRoom ⟶ ExtensionalMLTT.Institution.room` send each concrete sentence to what
it denotes and keep the models. `holInst S`, `mlttInst` are the one-signature institutions, and
`holToAbstract S`, `mlttToAbstract` the comorphisms into the abstract institutions.
-/

@[expose] public section

namespace Silmaril.Consequence.Concrete

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution
open Silmaril.Logic.Smt (SE)

universe u

/-! ## HOL -/

section HOL

open Silmaril.Logic.HOLLight Silmaril.Consequence.HOL
open Silmaril.Logic.Institution.Metatheory (HolSig)

/-- **A concrete HOL proposition** over `S`: the concrete form of a term of type `bool`. -/
def HOLSen (S : HolSig) : Type := {e : SE // ∃ p : HOLProp S, SExp.encodeTm p.1 = e}

variable {S : HolSig}

/-- The concrete form of a proposition. -/
def HOLSen.ofProp (p : HOLProp S) : HOLSen S := ⟨SExp.encodeTm p.1, p, rfl⟩

/-- The proposition a concrete proposition denotes. -/
noncomputable def HOLSen.toProp (e : HOLSen S) : HOLProp S := Classical.choose e.2

/-- **The HOL kernel over concrete propositions**, from the axioms `Δ`. -/
noncomputable def holKernel (S : HolSig) (Δ : Theory) : System (List (HOLSen S)) (HOLSen S) :=
  (HOL.kernelFrom S Δ).pullback (List.map HOLSen.toProp) HOLSen.toProp

/-- **HOL's sequent semantics over concrete propositions.** -/
noncomputable def holSeq (S : HolSig) : System (List (HOLSen S)) (HOLSen S) :=
  (HOL.seq.{u} S).pullback (List.map HOLSen.toProp) HOLSen.toProp

/-- The concrete form of the sequent `Γ ⊢ p`: `(sequent (h₁ … hₙ) c)`. -/
def encodeSequent (Γ : List (HOLProp S)) (p : HOLProp S) : SE :=
  .list [.atom "sequent", .list (Γ.map fun q => SExp.encodeTm q.1), SExp.encodeTm p.1]

/-- **A concrete HOL sequent** over `S`. -/
def HOLSequent (S : HolSig) : Type :=
  {e : SE // ∃ (Γ : List (HOLProp S)) (p : HOLProp S), encodeSequent Γ p = e}

/-- The sentence of the HOL institution a concrete sequent denotes. -/
noncomputable def HOLSequent.toSeq (e : HOLSequent S) : Metatheory.HOL.Seq S :=
  HOL.toSeq (Classical.choose e.2) (Classical.choose (Classical.choose_spec e.2))

/-- **The concrete HOL room** at `S`: concrete sequents, HOL's models. -/
noncomputable def holRoom (S : HolSig) : Room.{0, u + 1, u + 1} where
  Sen := HOLSequent S
  Mod := (Metatheory.HOL.room.{u} S).Mod
  Sat M e := (Metatheory.HOL.room.{u} S).Sat M e.toSeq

/-- Each concrete sequent goes to the sentence it denotes; models are kept. -/
noncomputable def holCorridor (S : HolSig) : holRoom.{u} S ⟶ Metatheory.HOL.room.{u} S where
  sen := HOLSequent.toSeq
  mod := 𝟭 _
  sat _ _ := Iff.rfl

/-- **The concrete HOL institution** at `S` (one signature). -/
noncomputable def holInst (S : HolSig) : Inst.{0, 0, 0, u + 1, u + 1} :=
  ⟨Discrete Unit, Discrete.functor fun _ => holRoom.{u} S⟩

/-- The abstract HOL institution. -/
def holAbstract : Inst.{0, 0, 0, u + 1, u + 1} := ⟨HolSig, Metatheory.HOL.inst.{u}⟩

/-- **The comorphism from concrete to abstract HOL** at `S`. -/
noncomputable def holToAbstract (S : HolSig) : Inst.CoHom (holInst.{u} S) holAbstract.{u} where
  Φ := Discrete.functor fun _ => S
  ρ := Discrete.natTrans fun _ => holCorridor.{u} S

end HOL

/-! ## Extensional MLTT -/

section MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- **A concrete extensional MLTT judgment**: the concrete form of a judgment. -/
def MLTTSen : Type := {e : SE // ∃ J : EJdg, SExp.encodeJdg J = e}

/-- The concrete form of a judgment. -/
def MLTTSen.ofJdg (J : EJdg) : MLTTSen := ⟨SExp.encodeJdg J, J, rfl⟩

/-- The judgment a concrete judgment denotes. -/
noncomputable def MLTTSen.toJdg (e : MLTTSen) : EJdg := Classical.choose e.2

/-- **Extensional MLTT derivability over concrete judgments.** -/
noncomputable def mlttDerives : System (List MLTTSen) MLTTSen :=
  TypeTheory.extensionalDerives.pullback (List.map MLTTSen.toJdg) MLTTSen.toJdg

/-- **Validity in set hierarchies over concrete judgments.** -/
noncomputable def mlttEntails : System (List MLTTSen) MLTTSen :=
  TypeTheory.extensionalEntails.{u}.pullback (List.map MLTTSen.toJdg) MLTTSen.toJdg

/-- **The concrete extensional MLTT room**: concrete judgments (lifted to the room's universe),
set hierarchies. -/
noncomputable def mlttRoom : Room.{u + 1, u + 1, u + 1} where
  Sen := ULift.{u + 1} MLTTSen
  Mod := Institution.room.{u}.Mod
  Sat T e := Institution.room.{u}.Sat T (ULift.up e.down.toJdg)

/-- Each concrete judgment goes to the judgment it denotes; models are kept. -/
noncomputable def mlttCorridor : mlttRoom.{u} ⟶ Institution.room.{u} where
  sen e := ULift.up e.down.toJdg
  mod := 𝟭 _
  sat _ _ := Iff.rfl

/-- **The concrete extensional MLTT institution.** -/
noncomputable def mlttInst : Inst.{0, 0, u + 1, u + 1, u + 1} :=
  ⟨Discrete Unit, Discrete.functor fun _ => mlttRoom.{u}⟩

/-- **The comorphism from concrete to abstract extensional MLTT.** -/
noncomputable def mlttToAbstract : Inst.CoHom mlttInst.{u} Institution.bundled.{u} where
  Φ := 𝟭 _
  ρ := Discrete.natTrans fun _ => mlttCorridor.{u}

end MLTT

end Silmaril.Consequence.Concrete
