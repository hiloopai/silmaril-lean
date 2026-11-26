module

import Silmaril.SSA.Isotope.LetParIter.Uniformity.Thms

import Silmaril.SSA.Isotope.LetParIter.QuotientBridge.Thms
import Silmaril.Semantics.Elgot.Thms

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Parallel (Derivation)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (TypeModel TyDen InstructionModel CtxDen BoundDen)

namespace LetParIterTests

open scoped LetParIter

abbrev Obj := Ty Empty

inductive Instr where
  | tick

instance : HasTy Instr Obj := ⟨fun _ => unit, fun _ => unit⟩
instance : HasEff Instr (Bool × Bool) := ⟨fun _ => (true, false)⟩

abbrev Γ : Ctx Empty Obj := .nil
abbrev U : Obj := unit

example (s : LetSeq.LocallyNameless.Tm Empty Instr 0) :
    LetParIter.embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed s)) =
      LetParIter.ofLetPar (LetPar.embed s) :=
  LetParIter.embed_seqIter s

example : Function.Injective (LetParIter.ofLetParCase :
    LetParCase.Tm Empty Instr 0 → LetParIter.Tm Empty Instr 0) :=
  LetParIter.ofLetParCase_injective

example : Function.Injective (LetParIter.ofLetPar :
    LetPar.Tm Empty Instr 0 → LetParIter.Tm Empty Instr 0) :=
  LetParIter.ofLetPar_injective

def native : LetIter.LocallyNameless.Tm Empty Instr 0 := .iter .unit (.inl (.bv 0))

def nativeTyped : LetIter.LocallyNameless.Derivation Instr Γ .nil native U :=
  .iter .unit (.inl .bv)

example : LetParIter.toLetIter? (LetParIter.embed native) = some native :=
  LetParIter.toLetIter?_embed native

example : Derivation Instr Γ .nil (LetParIter.embed native) U :=
  LetParIter.derivation nativeTyped

def nativeWithEta : LetIter.LocallyNameless.Derivation Instr Γ .nil
    (.let₁ native (.bv 0)) U :=
  .let₁ nativeTyped .bv

-- A native equation survives at its original exact typing endpoints.
example : LetParIter.Equiv (⊥ : Bool × Bool) Γ
    (LetParIter.derivation nativeWithEta) (LetParIter.derivation nativeTyped) :=
  LetParIter.embed_related nativeWithEta nativeTyped ⟨.letEta (LetParIter.nativeTyping nativeTyped)⟩

def unitBranch : Derivation Instr Γ (.snoc .nil U) (.bv 0 : LetParIter.Tm Empty Instr 1) U :=
  .bv

def tickBranch : Derivation Instr Γ (.snoc .nil U) (.op .tick .unit : LetParIter.Tm Empty Instr 1) U :=
  .op .unit

def branches := (.bv 0 : LetParIter.Tm Empty Instr 1) || .op .tick .unit

example : Derivation Instr Γ (.snoc .nil U) branches (product U U) :=
  .par unitBranch tickBranch

example : LetParIter.toLetIter? branches = none := rfl

theorem loopSwap :
    LetParIter.Equiv (⊥ : Bool × Bool) Γ
      (.iter (h := rfl) .unit
        (.inl (h := LetParIter.hasCase) (LetParIter.Typing.swap (.par unitBranch tickBranch))))
      (.iter (h := rfl) .unit (.inl (h := LetParIter.hasCase) (.par tickBranch unitBranch))) :=
  .iter (.refl .unit) (.inl (.swap unitBranch tickBranch))

-- Renaming and simultaneous substitution reach under the loop binder and both branches.
example := LetParIter.Equiv.rename (BoundCtx.Renaming.succ .nil U) loopSwap

theorem swapOpen :
    LetParIter.Equiv (⊥ : Bool × Bool) Γ (LetParIter.Typing.swap (.par unitBranch tickBranch))
      (.par tickBranch unitBranch) :=
  .swap unitBranch tickBranch

private def stepL : Derivation Instr Γ (.snoc .nil U)
    (.inl LetParIter.hasCase (Parallel.Tm.swap branches)) (coprod (product U U) U) :=
  .inl (LetParIter.Typing.swap (.par unitBranch tickBranch))

private def stepR : Derivation Instr Γ (.snoc .nil U)
    (.inl LetParIter.hasCase (.par (.op .tick .unit) (.bv 0))) (coprod (product U U) U) :=
  .inl (.par tickBranch unitBranch)

-- The recursive square is an instance of parallel swap inside the body.
-- Opening the transported body at the original state retains its exact typing.
private theorem uniformitySquare :
    LetParIter.Equiv (⊥ : Bool × Bool) Γ
      (LetParIter.Typing.uniformityLeft stepL unitBranch)
      (LetParIter.Typing.uniformityRight
        (LetParIter.Typing.uniformityLeft stepR unitBranch) unitBranch) := by
  change LetParIter.Equiv (⊥ : Bool × Bool) Γ
    (LetParIter.Typing.uniformityLeft stepL unitBranch)
    (LetParIter.Typing.uniformityLeft stepR unitBranch)
  exact .case (.inl swapOpen) (.refl _) (.refl _)

theorem uniformityWithParallel : LetParIter.Equiv (⊥ : Bool × Bool) Γ
    (.iter (h := rfl) .unit stepL)
    (.iter (h := rfl) (.let₁ .unit unitBranch) (LetParIter.Typing.uniformityLeft stepR unitBranch)) :=
  .iterUniformity .unit unitBranch .bv stepL
    (LetParIter.Typing.uniformityLeft stepR unitBranch) uniformitySquare

def substituteUnit :
    LetParIter.Subst (Γ := Γ) (.snoc .nil U) .nil (fun _ => (.unit : LetParIter.Tm Empty Instr 0)) :=
  fun i => Fin.cases .unit (fun j => Fin.elim0 j) i

example := LetParIter.Equiv.bsubst substituteUnit (fun _ => .unit) swapOpen

def openLoop : LetParIter.Tm Empty Instr 2 :=
  .iter rfl (.bv 0) (.inl LetParIter.hasCase (.par (.bv 0) (.par (.bv 1) (.bv 2))))

def replaceAmbient : Fin 2 → LetParIter.Tm Empty Instr 1 :=
  Fin.cases .unit (fun _ => .bv 0)

-- The loop variable stays at zero, while the replacement mentioning an ambient
-- variable is lifted past the binder.
example : openLoop.bsubst replaceAmbient =
    .iter rfl .unit (.inl LetParIter.hasCase (.par (.bv 0) (.par .unit (.bv 1)))) := rfl

variable [TypeModel.{0, 0} Obj]
variable {m : Type → Type} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
variable [InstructionModel Instr Obj (Bool × Bool) m]

example (P : Elgot.ParallelPairing m) (γ : CtxDen Γ) (ρ : BoundDen (.nil : BoundCtx Obj 0)) :=
  LetParIter.interpret_sound P loopSwap γ ρ

example (P : Elgot.ParallelPairing m) (γ : CtxDen Γ) (ρ : BoundDen (.nil : BoundCtx Obj 0)) :=
  LetParIter.interpret_sound P uniformityWithParallel γ ρ

end LetParIterTests

namespace LetParIterQuotientBridgeTests

noncomputable section

-- The same type code can have two product decompositions. The tag chooses
-- their product comparisons while leaving the underlying carrier fixed.
private abbrev Tag := Ty Unit × Bool

local instance : TypeFormers Tag where
  product a b := (.product a.1 b.1, false)
  unit := (.unit, false)
  coprod a b := (.coprod a.1 b.1, false)
  empty := (.empty, false)

local instance : Subtyping Tag where
  Subty a b := Ty.Subty a.1 b.1
  refl a := .refl a.1
  trans := .trans
  product := .product
  coprod := .coprod
  empty a := .empty a.1
  unit a := .unit a.1

private def interp : Ty Unit → Type
  | .base _ => Bool
  | .product a b => interp a × interp b
  | .unit => Unit
  | .coprod a b => interp a ⊕ interp b
  | .empty => Empty

private def coerce {a b : Ty Unit} (d : Ty.Subty a b) : interp a → interp b :=
  match d with
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => Prod.map (coerce f) (coerce g)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => Empty.elim
  | .unit _ => fun _ => ()

private def productView (a b : Tag) : interp (product a b).1 ≃ interp a.1 × interp b.1 :=
  if h : a.1 = b.1 then
    if b.2 then
      (Equiv.prodComm _ _).trans
        (Equiv.prodCongr (Equiv.cast (congrArg interp h.symm)) (Equiv.cast (congrArg interp h)))
    else Equiv.refl _
  else Equiv.refl _

local instance : TypeModel Tag where
  interp a := interp a.1
  productEquiv := productView
  unitEquiv := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := Equiv.refl _
  coe := coerce

local instance : HasTy Empty Tag := ⟨Empty.elim, Empty.elim⟩
local instance : HasEff Empty Bool := ⟨Empty.elim⟩

local instance : InstructionModel Empty Tag Bool Part where
  denote f := f.elim
  denotePure f := f.elim
  denote_pure f := f.elim

private def pairing : Elgot.ParallelPairing Part where
  pair x y := ⟨x.Dom ∧ y.Dom, fun h => (x.get h.1, y.get h.2)⟩
  natural _ _ _ _ := Part.ext' Iff.rfl (fun _ _ => rfl)
  swap _ _ := Part.ext' and_comm (fun _ _ => rfl)
  assoc _ _ _ := Part.ext' and_assoc (fun _ _ => rfl)
  rightUnit _ := Part.ext' (and_iff_left trivial) (fun _ _ => rfl)

private abbrev A : Tag := (.base (), false)
private abbrev B : Tag := (.base (), true)
private abbrev Γ : Ctx Empty Tag := .nil
private abbrev β : BoundCtx Tag 1 := .snoc .nil (product A A)

private abbrev term : LetIter.LocallyNameless.Tm Empty Empty 1 := .let₂ (.bv 0) (.bv 1)

private def ordinary : LetIter.LocallyNameless.Derivation Empty Γ β term A :=
  .let₂ (A := A) (B := A) .bv .bv

private def swapped : LetIter.LocallyNameless.Derivation Empty Γ β term A :=
  .let₂ (A := A) (B := B) .bv .bv

private abbrev UpperTerm := Σ t : LetParIter.Tm Empty Empty 1, Derivation Empty Γ β t A

private def upperSetoid : Setoid UpperTerm where
  r a b := LetParIter.Equiv false Γ a.2 b.2
  iseqv := ⟨fun a => .refl a.2, .symm, .trans⟩

private def upperClass {t : LetParIter.Tm Empty Empty 1} (d : Derivation Empty Γ β t A) :
    Quotient upperSetoid :=
  Quotient.mk _ ⟨t, d⟩

private theorem upperClassesDiffer :
    upperClass (LetParIter.derivation ordinary) ≠ upperClass (LetParIter.derivation swapped) := by
  intro classes
  have h : LetParIter.Equiv false Γ (LetParIter.derivation ordinary) (LetParIter.derivation swapped) :=
    Quotient.exact classes
  have eq := LetParIter.sound pairing h PUnit.unit (PUnit.unit, (false, true))
  simp [ordinary, swapped, LetParIter.derivation, LetParIter.denote,
    TypeModel.productEquiv, productView] at eq
  change (Part.some _).bind _ = (Part.some _).bind _ at eq
  erw [Part.bind_some, Part.bind_some] at eq
  change Part.some false = Part.some true at eq
  exact Bool.noConfusion (Part.some_injective eq)

private abbrev NativeTerm :=
  { t : LetIter.LocallyNameless.Tm Empty Empty 1 // LetIter.LocallyNameless.HasType Empty Γ β t A }

private def nativeSetoid : Setoid NativeTerm where
  r a b := LetIter.LocallyNameless.Equiv false Γ β a.val b.val A
  iseqv := ⟨fun a => .refl a.property, .symm, .trans⟩

private def nativeClass {t : LetIter.LocallyNameless.Tm Empty Empty 1}
    (d : LetIter.LocallyNameless.Derivation Empty Γ β t A) : Quotient nativeSetoid :=
  Quotient.mk _ ⟨t, d.toHasType⟩

/-- Native exact inclusion cannot descend along the raw equation quotient
while preserving the class of every supplied derivation. -/
theorem noNativeQuotientMap :
    ¬ ∃ f : Quotient nativeSetoid → Quotient upperSetoid,
      ∀ {t : LetIter.LocallyNameless.Tm Empty Empty 1}
        (d : LetIter.LocallyNameless.Derivation Empty Γ β t A),
        f (nativeClass d) = upperClass (LetParIter.derivation d) := by
  rintro ⟨f, commutes⟩
  have rawClasses : nativeClass ordinary = nativeClass swapped :=
    Quotient.sound (LetIter.LocallyNameless.Equiv.refl ordinary.toHasType)
  exact upperClassesDiffer
    ((commutes ordinary).symm.trans ((congrArg f rawClasses).trans (commutes swapped)))

private abbrev caseTerm : LetParCase.Tm Empty Empty 1 := .let₂ (.bv 0) (.bv 1)

private def caseOrdinary : Derivation Empty Γ β caseTerm A :=
  .let₂ (A := A) (B := A) .bv .bv

private def caseSwapped : Derivation Empty Γ β caseTerm A :=
  .let₂ (A := A) (B := B) .bv .bv

private abbrev CaseTerm := { t : LetParCase.Tm Empty Empty 1 // Parallel.HasType Empty Γ β t A }

private def caseSetoid : Setoid CaseTerm where
  r a b := LetParCase.Equiv false Γ β a.val b.val A
  iseqv := ⟨fun a => .refl a.property, .symm, .trans⟩

private def caseClass {t : LetParCase.Tm Empty Empty 1} (d : Derivation Empty Γ β t A) :
    Quotient caseSetoid :=
  Quotient.mk _ ⟨t, ⟨d⟩⟩

/-- Widening exact case-tier evidence likewise cannot descend while preserving
the class of every supplied derivation. -/
theorem noCaseQuotientMap :
    ¬ ∃ f : Quotient caseSetoid → Quotient upperSetoid,
      ∀ {t : LetParCase.Tm Empty Empty 1} (d : Derivation Empty Γ β t A),
        f (caseClass d) = upperClass (LetParIter.ofLetParCaseDerivation d) := by
  rintro ⟨f, commutes⟩
  have rawClasses : caseClass caseOrdinary = caseClass caseSwapped :=
    Quotient.sound (Parallel.Equiv.refl ⟨caseOrdinary⟩)
  apply upperClassesDiffer
  exact (commutes caseOrdinary).symm.trans ((congrArg f rawClasses).trans (commutes caseSwapped))

#print axioms noNativeQuotientMap
#print axioms noCaseQuotientMap

end

end LetParIterQuotientBridgeTests

#print axioms LetParIter.QuotientBridge.native_witness
#print axioms LetParIter.QuotientBridge.case_witness
#print axioms LetParIter.QuotientBridge.denote_eq_of_witness
