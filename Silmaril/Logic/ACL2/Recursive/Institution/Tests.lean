module

import Silmaril.Logic.ACL2.Consequence.Thms
import Silmaril.Logic.ACL2.OrdinalAdmission.Thms
import Silmaril.Logic.ACL2.Recursive.Institution.Thms
import Silmaril.Logic.ACL2.Standard.Objects.CdrSize

namespace Silmaril.Logic.ACL2.Recursive.Institution.Tests

open CategoryTheory Ordinals Standard

def trueListName : Name := ⟨"ACL2", "TRUE-LISTP"⟩
def members : Signature := Signature.empty.add trueListName 1
def trueList : members.Symbol 1 := Signature.empty.addSymbol trueListName 1

theorem member_arity {k : Nat} (f : members.Symbol k) : k = 1 := by
  have declared := f.property
  by_cases h : f.val = trueListName <;> simp_all [members, Signature.add, Signature.empty]

-- The logical TRUE-LISTP body from ACL2 8.7 axioms.lisp, with EQ expanded to EQUAL.
def trueListBody : Body World.initial.signature members 1 :=
  .ite (.consp (.var 0)) (.call trueList fun _ => .cdr (.var 0))
    (.base (.equal (.var 0) .nil))

def block : Block World.initial.signature where
  members := members
  fresh _ := rfl
  body f := member_arity f ▸ trueListBody

theorem namesFresh : block.TheoremNamesFresh World.initial := fun _ => rfl

def output : World := block.extendWorld World.initial namesFresh
def extension : World.initial.Extension output := block.worldExtension World.initial namesFresh

def standardModel : Model World.initial.signature :=
  ⟨objectPrimitives, fun f => nomatch f.property⟩

theorem inputModels : World.initial.Models standardModel :=
  World.valid_bare _ _ fun _ ⟨_, _, _, body, _⟩ => nomatch body

def argument : MeasureArgument members := fun f =>
  ⟨0, member_arity f ▸ (by decide : 0 < 1)⟩

def certificate : BlockCertificate block := fun _ => .ite (.cdr 0) .base

theorem accepted : certificate.Accepted block argument := by
  intro k f
  have hk := member_arity f
  subst k
  rfl

def ordinalMeasure : OrdinalAdmission.Measure block standardModel :=
  fun state => .natural (objectCdrSize.rank argument state)

theorem admitted : OrdinalAdmission.Terminates block standardModel ordinalMeasure where
  valid _ := rfl
  decreases state :=
    (certificate.terminates objectCdrSize argument accepted state).mono fun next lt => by
      change (compare (objectCdrSize.rank argument next) (objectCdrSize.rank argument state) ==
        .lt) = true
      exact beq_iff_eq.mpr (Nat.compare_eq_lt.mpr lt)

theorem outputModels : output.Models admitted.model :=
  block.modelBy_models admitted.wellFounded admitted.decreases inputModels

example : (inst.I.map block.inclusion).mod.obj admitted.model = standardModel :=
  admitted.model_reduct

def presentedModel : (presentedInst.I.obj output.presentation).Mod :=
  ⟨admitted.model, fun _ hp => hp admitted.model fun q hq => outputModels q (Or.inl hq)⟩

example : ((presentedInst.I.map extension.presentation).mod.obj presentedModel).obj =
    standardModel := admitted.model_reduct

example : (forgetDefinitions.η.app output.presentation).mod.obj presentedModel = admitted.model := rfl

example : (block.equation trueList).Holds admitted.model :=
  outputModels _ (Or.inl (block.equation_mem trueList))

def isTrueList (x : Object) : Object :=
  admitted.model.interpret (block.symbol trueList) (fun _ => x)

theorem trueListEquation (x : Object) :
    isTrueList x = if x.consp then isTrueList x.cdr else x.equal Object.nil := by
  have h := (Sentence.holds_eq admitted.model _ _).mp (admitted.equation_holds trueList) (fun _ => x)
  change isTrueList x = objectPrimitives.ite (objectPrimitives.ofBool x.consp)
    (isTrueList x.cdr) (x.equal Object.nil) at h
  cases hc : x.consp <;>
    simpa [hc, objectPrimitives, Primitives.ite, Primitives.ofBool] using h

theorem singletonIsTrueList : isTrueList (.cons (.integer 4) .nil) = Object.truth := by
  rw (config := { transparency := .default }) [trueListEquation]
  change isTrueList Object.nil = Object.truth
  rw (config := { transparency := .default }) [trueListEquation]
  rfl

-- Ordinary and π signature changes use the same inclusion. The equation is a π hypothesis.
example (p : Sentence World.initial.signature) :
    (p.map extension.presentation.signature).Holds admitted.model ↔ p.Holds standardModel := by
  change (p.map block.inclusion).Holds admitted.model ↔ p.Holds standardModel
  rw [Sentence.holds_map, admitted.model_reduct]

theorem equationDerives : output.presentation.Derives ∅ (block.equation trueList) :=
  .hyp (Or.inl (block.equation_mem trueList))

example (p : Sentence World.initial.signature) (h : World.initial.presentation.Derives ∅ p) :
    output.presentation.Derives (Sentence.map block.inclusion '' ∅) (p.map block.inclusion) :=
  (pi.I.map extension.presentation).map_derives h

example : Consequence.presentationEntails output.presentation [] (block.equation trueList) :=
  Consequence.presentationSound output.presentation [] _ (.hyp (Or.inl (block.equation_mem trueList)))

def theoremName : Name := ⟨"ACL2", "SILMARIL-TRUE-LISTP-EQUATION"⟩
theorem equationProof : output.Provable (block.equation trueList) :=
  .hyp (Or.inl (block.equation_mem trueList))
def bookOutput : World := output.addTheorem theoremName ⟨rfl, rfl⟩ _ equationProof
def book : Book output bookOutput := .cons (.defthm ⟨rfl, rfl⟩ _ equationProof) (.nil _)

example : World.initial.Extension bookOutput := extension.comp book.extension
example : bookOutput.Checked := book.checked (block.extendWorld_checked (World.checked_bare _))

example : output.signature.resolve ⟨"OTHER", "TRUE-LISTP"⟩ 1 = none := by decide
example : output.signature.resolve trueListName 2 = none := by decide

def occupiedWorld : World := World.initial.addTheorem trueListName ⟨rfl, rfl⟩ ⟨0, .truth⟩ .truth

example : ¬ block.TheoremNamesFresh occupiedWorld := by
  intro fresh
  have collision := fresh trueList.property
  contradiction

#print axioms Block.presentationHom
#print axioms Block.worldExtension
#print axioms Block.equation_mem
#print axioms Block.extendPresentation_equations
#print axioms Block.extendWorld_checked
#print axioms Block.modelBy_models
#print axioms Block.entails_iff
#print axioms equationDerives
#print axioms outputModels
#print axioms singletonIsTrueList

end Silmaril.Logic.ACL2.Recursive.Institution.Tests
