module

public import Silmaril.Logic.HOLLight.CSLib.Substitution
public import Silmaril.Logic.HOLLight.Propositional
public import Silmaril.Logic.HOLLight.Propositional.Category
public import Silmaril.Logic.HOLLight.Context
public import Silmaril.Logic.Metatheory.InferenceSystemCat
public meta import Silmaril.Logic.HOLLight.CSLib.Substitution
public meta import Silmaril.Logic.HOLLight.Term
public meta import Silmaril.Logic.HOLLight.Type
public meta import Silmaril.Logic.HOLLight.Substitution
public meta import Silmaril.Logic.HOLLight.Context

@[expose] public section

/-!
# CSLib integration regressions

The substitution tests distinguish simultaneous replacement from sequential
replacement and exercise typed names and binders. The inference examples
translate actual CSLib proof trees, including a noninjective atom assignment,
and compose fixed-context morphisms with finite-context deduction.
-/

namespace Silmaril.Logic.HOLLight.CSLibExamples

open Cslib.Logic Cslib.Logic.InferenceSystem
open scoped Cslib.Logic.InferenceSystem

-- Parallel replacement swaps both original variables without reprocessing an insertion.
#guard (Tm.equal .bool (.fvar 0 .bool) (.fvar 1 .bool))[
    ({(0, .bool), (1, .bool)} : Finset (Nat × Ty)) :=
      fun (n : Nat) (A : Ty) => Tm.fvar (if n = 0 then 1 else 0) A] =
  Tm.equal .bool (.fvar 1 .bool) (.fvar 0 .bool)

#guard (Tm.equal .bool (.fvar 0 .bool) (.fvar 1 .bool))[
    ({(0, .bool), (1, .bool)} : Finset (Nat × Ty)) :=
      fun (n : Nat) (A : Ty) => Tm.fvar (if n = 0 then 1 else 0) A] ≠
  ((Tm.equal .bool (.fvar 0 .bool) (.fvar 1 .bool))[(0, Ty.bool) := Tm.fvar 1 .bool])[
    (1, Ty.bool) := Tm.fvar 0 .bool]

-- The finite domain includes the type, not only the numeric free name.
#guard (Tm.fvar 0 .bool)[({(0, .ind)} : Finset (Nat × Ty)) :=
    fun (_ : Nat) (A : Ty) => Tm.fvar 7 A] = .fvar 0 .bool

-- An open replacement is weakened when inserted under a binder.
#guard (Tm.lam .bool (.fvar 0 .bool))[({(0, .bool)} : Finset (Nat × Ty)) :=
    fun (_ : Nat) (_ : Ty) => Tm.bvar 0] = .lam .bool (.bvar 1)

#guard (Ty.arr (.var 0) (.var 1))[({0, 1} : Finset Nat) :=
    fun n => Ty.var (if n = 0 then 1 else 0)] = .arr (.var 1) (.var 0)

#guard (Const.user 0 [.var 0, .var 1])[({0, 1} : Finset Nat) :=
    fun n => Ty.var (if n = 0 then 1 else 0)] = .user 0 [.var 1, .var 0]

-- Context filling uses the hole's scope, unlike capture-avoiding substitution.
#guard (Tm.Context.lam .bool .hole)<[Tm.bvar 0] = Tm.lam .bool (.bvar 0)

example (sig : Signature) :
    HasType sig [] ((Tm.Context.lam .bool .hole)<[Tm.bvar 0]) (.arr .bool .bool) :=
  (Tm.Context.HasType.lam (by trivial) Tm.Context.HasType.hole).fill
    (HasType.bvar rfl (by trivial))

example (t : Tm) (σ : Nat → Ty → Tm) : t[t.freeVars.toFinset := σ] = t.freeSubst σ :=
  Tm.cslib_free_parallel_support t σ

example (t : Tm) (σ : Nat → Ty) : t[t.typeVars := σ] = t.tySubst σ :=
  Tm.cslib_type_parallel_support t σ

example (sig : Signature) (theory : Theory) :
    Derives sig theory ∅ (Tm.equal .bool (.fvar 1 .bool) (.fvar 1 .bool)) := by
  have original : Derives sig theory ∅ (Tm.equal .bool (.fvar 0 .bool) (.fvar 0 .bool)) :=
    .refl (.fvar 0 (by trivial))
  have instantiated := original.cslib_free_parallel ({(0, .bool)} : Finset (Nat × Ty))
    (fun _ A => Tm.fvar 1 A) (fun _ _ _ hA => HasType.fvar 1 hA)
  simpa [Tm.cslib_free_parallel_def, Tm.restrictFreeSubst, Tm.freeSubst, Tm.equal] using instantiated

-- Both checked-formula and raw-sequent notation use the existing kernel judgment.
example (sig : Signature) (theory : Theory) (p : Formula sig) :
    (HOLLight.ContextSystem sig theory {p.term})⇓p := Derives.assume p.typing

example (sig : Signature) (theory : Theory) (p : Formula sig) :
    (KernelSystem sig theory)⇓(Sequent.mk {p.term} p.term) := Derives.assume p.typing

/-- Compose two actual inference-system morphisms, then use CSLib's derivability. -/
example (sig : Signature) (theory : Theory) (p : Formula sig) :
    DerivableIn (HOLLight.ContextSystem sig theory ∅)
      (Tm.imp (Tm.andAll {p.term, Tm.truth}) p.term) := by
  have typed : TypedHyps sig [] {p.term, Tm.truth} := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact p.typing
    · exact HasType.truth
  let weaken := HOLLight.ContextSystem.weaken (theory := theory) typed
    (show ({p.term} : Hyps) ⊆ {p.term, Tm.truth} from by simp)
  let discharge := HOLLight.ContextSystem.discharge (theory := theory) typed
  exact (discharge.comp weaken).preserves ⟨Derives.assume p.typing⟩

example (sig : Signature) (theory : Theory) (p : Formula sig) :
    DerivableIn (HOLLight.ContextSystem sig theory ∅) (Tm.imp Tm.truth p.term) ↔
      DerivableIn (HOLLight.ContextSystem sig theory ∅) p := by
  have typed : TypedHyps sig [] ∅ := by intro q hq; simp at hq
  simpa using HOLLight.ContextSystem.deduction_iff (theory := theory) typed p

private def swapConjunction {Atom : Type} [DecidableEq Atom] (p q : PL.Proposition Atom) :
    (PL.Theory.MPL Atom).Derivation ∅ (.imp (.and p q) (.and q p)) :=
  .implI ∅ (.andI (.andE₂ (.ass (Finset.mem_insert_self _ _)))
    (.andE₁ (.ass (Finset.mem_insert_self _ _))))

example (sig : Signature) (theory : Theory) (p q : Formula sig) :
    Derives sig theory ∅ (Tm.imp (Tm.conj p.term q.term) (Tm.conj q.term p.term)) := by
  exact Propositional.minimal id (swapConjunction (.atom p) (.atom q))

-- Distinct source atoms may collapse, even across implication discharge.
example (sig : Signature) (theory : Theory) (p : Formula sig) :
    Derives sig theory ∅ (Tm.imp p.term (Tm.imp p.term (Tm.conj p.term p.term))) := by
  have source : (PL.Theory.MPL Bool).Derivation ∅
      (.imp (.atom false) (.imp (.atom true) (.and (.atom false) (.atom true)))) :=
    .implI ∅ (.implI _ (.andI (.ass (by simp)) (.ass (by simp))))
  exact Propositional.minimal (fun _ : Bool => p) source

-- The canonical classical bridge discharges CSLib's double-negation axiom in HOL.
example (sig : Signature) (p : Formula sig) :
    DerivableIn (HOLLight.ContextSystem sig classicalTheory ∅)
      (Tm.imp (Tm.neg (Tm.neg p.term)) p.term) := by
  let sourceFormula : PL.Proposition (Formula sig) := .imp (PL.Proposition.atom p).neg.neg (.atom p)
  have source : (PL.Theory.CPL (Formula sig)).Derivation ∅ sourceFormula :=
    .ax ⟨.atom p, rfl⟩
  have mapped := (Propositional.classicalContextMorphism sig ∅).preserves ⟨source⟩
  have mapped' : DerivableIn
      (HOLLight.ContextSystem sig classicalTheory (Propositional.translateCtx id ∅))
      (Propositional.interpret id sourceFormula) := mapped
  simpa [sourceFormula, Propositional.translate, Propositional.interpret,
    PL.Proposition.neg, Tm.neg] using mapped'

section Category

open Silmaril.Logic.Metatheory CategoryTheory CategoryTheory.Limits

/-- A single conclusion with two different proof objects. -/
def twoProofs : InferenceSystemCat.{0, 0} where
  Conclusion := PUnit
  Derivation _ := Bool

def alwaysFalse : twoProofs ⟶ twoProofs where
  map := id
  mapDerivation _ := false

def alwaysTrue : twoProofs ⟶ twoProofs where
  map := id
  mapDerivation _ := true

example : alwaysFalse.map = alwaysTrue.map := rfl

/-- Agreement on conclusions does not identify proof-relevant morphisms. -/
example : alwaysFalse ≠ alwaysTrue := by
  intro equal
  have impossible := congrArg (fun f : twoProofs ⟶ twoProofs =>
    f.mapDerivation (a := PUnit.unit) false) equal
  cases impossible

example : IsInitial (InferenceSystemCat.empty : InferenceSystemCat.{0, 0}) :=
  InferenceSystemCat.emptyIsInitial

example : IsTerminal (InferenceSystemCat.trivial : InferenceSystemCat.{0, 0}) :=
  InferenceSystemCat.trivialIsTerminal

example : IsInitial (InferenceSystemCat.empty : InferenceSystemCat.{1, 1}) :=
  InferenceSystemCat.emptyIsInitial

example : IsTerminal (InferenceSystemCat.trivial : InferenceSystemCat.{1, 1}) :=
  InferenceSystemCat.trivialIsTerminal

/-- A native CSLib system whose proofs live in `Type`, not `Prop`. -/
structure NativeTreeSystem where

instance : InferenceSystem NativeTreeSystem Nat where
  derivation _ := Bool

example : Nonempty ((InferenceSystemCat.of.{0, 0, 1, 0} NativeTreeSystem Nat).Derivation (7 : Nat)) :=
  ⟨⟨⟨true⟩⟩⟩

example (sig : Signature) (theory : Theory) :
    Nonempty ((InferenceSystemCat.of.{0, 0, 0, 1}
      (HOLLight.ContextSystem sig theory ∅) Tm).Derivation Tm.truth) :=
  ⟨⟨⟨Derives.truth⟩⟩⟩

/-- Packaging a Prop-to-Type proof map aligns its two proof universes. -/
def toNative (sig : Signature) (theory : Theory) :
    InferenceMorphism (HOLLight.ContextSystem sig theory ∅) NativeTreeSystem Tm Nat where
  map _ := 7
  mapDerivation _ := true

example (sig : Signature) (theory : Theory) :
    ((InferenceSystemCat.ofMorphism (toNative sig theory)).mapDerivation
      (a := Tm.truth) ⟨⟨Derives.truth⟩⟩).down.down = true := rfl

-- An actual CSLib tree passes through the categorical arrow to a kernel derivation.
example (sig : Signature) (p : Formula sig) :
    Derives sig classicalTheory ∅ (Tm.imp p.term p.term) := by
  let sourceFormula : PL.Proposition (Formula sig) := .imp (.atom p) (.atom p)
  have source : (PL.Theory.CPL (Formula sig)).Derivation ∅ sourceFormula :=
    .implI ∅ (.ass (Finset.mem_insert_self _ _))
  have packaged : Nonempty ((Propositional.classicalSource sig ∅).Derivation sourceFormula) :=
    ⟨⟨⟨source⟩⟩⟩
  exact Propositional.classicalContextArrow_derives sig ∅ sourceFormula packaged

end Category

end Silmaril.Logic.HOLLight.CSLibExamples
