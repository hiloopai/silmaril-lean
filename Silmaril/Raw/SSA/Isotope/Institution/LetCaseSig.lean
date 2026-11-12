module

public import Silmaril.Raw.SSA.Isotope.Institution.InstrSig
public import Silmaril.Raw.SSA.Isotope.Institution.SigHomExt
public import Silmaril.Raw.SSA.Isotope.Theory.Models.Theories
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetCase

@[expose] public section

/-!
# Instruction maps as signature morphisms of exact LetCase syntax

The operation relabelling `sigHom Γ g` of `Models.signature P.Instr Γ` along an instruction
map `g`, and its functoriality (`sigHom_id`, `sigHom_comp`). These are the data and laws of
the functor `Silmaril.Isotope.Institution.LetCase.pres`.
-/

namespace Silmaril.Isotope.Institution.LetCase

open CategoryTheory
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory
open Silmaril.Isotope.Theory
open Silmaril.Isotope.LetCase.LocallyNameless

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν] (Γ : Ctx ν τ)

/-! ### Operation maps -/

section OpMap

variable {P Q : InstrSig τ ε}

/-- Relabel the operation symbols of the exact LetCase syntax along an instruction map. -/
def opMap (g : InstrSig.Hom P Q) :
    {i : TypingIndex τ} → Models.Operation (Φ := P.Instr) Γ i → Models.Operation (Φ := Q.Instr) Γ i
  | _, .fv h => .fv h
  | _, .bv i => .bv i
  | _, .op (β := β) f =>
      castOp (Models.signature Q.Instr Γ)
        (congrArg (fun A => (⟨_, β, A⟩ : TypingIndex τ)) (g.target f))
        (Models.Operation.op (β := β) (g.instr f))
  | _, .let₁ A B => .let₁ A B
  | _, .unit => .unit
  | _, .pair A B => .pair A B
  | _, .let₂ A B C => .let₂ A B C
  | _, .inl A B => .inl A B
  | _, .inr A B => .inr A B
  | _, .case A B C => .case A B C
  | _, .abort C => .abort C

/-- Argument positions are unchanged. -/
def argMap (g : InstrSig.Hom P Q) :
    {i : TypingIndex τ} → (o : Models.Operation (Φ := P.Instr) Γ i) →
      Fin ((Models.signature Q.Instr Γ).arity (opMap Γ g o)) ≃
        Fin ((Models.signature P.Instr Γ).arity o)
  | _, .fv _ => Equiv.refl _
  | _, .bv _ => Equiv.refl _
  | _, .op _ => finCongr (arity_castOp _ _ _)
  | _, .let₁ _ _ => Equiv.refl _
  | _, .unit => Equiv.refl _
  | _, .pair _ _ => Equiv.refl _
  | _, .let₂ _ _ _ => Equiv.refl _
  | _, .inl _ _ => Equiv.refl _
  | _, .inr _ _ => Equiv.refl _
  | _, .case _ _ _ => Equiv.refl _
  | _, .abort _ => Equiv.refl _

theorem argSortMap (g : InstrSig.Hom P Q) :
    ∀ {i : TypingIndex τ} (o : Models.Operation (Φ := P.Instr) Γ i)
      (j : Fin ((Models.signature Q.Instr Γ).arity (opMap Γ g o))),
      (Models.signature P.Instr Γ).argSort o (argMap Γ g o j) =
        (Models.signature Q.Instr Γ).argSort (opMap Γ g o) j
  | _, .fv _, j => Fin.elim0 j
  | _, .bv _, j => Fin.elim0 j
  | _, .op (β := β) f, j =>
      (congrArg (fun A => (⟨_, β, A⟩ : TypingIndex τ)) (g.source f).symm).trans
        (argSort_castOp _ _ _ j).symm
  | _, .let₁ _ _, _ => rfl
  | _, .unit, j => Fin.elim0 j
  | _, .pair _ _, _ => rfl
  | _, .let₂ _ _ _, _ => rfl
  | _, .inl _ _, _ => rfl
  | _, .inr _ _, _ => rfl
  | _, .case _ _ _, _ => rfl
  | _, .abort _, _ => rfl

/-- The signature morphism of exact LetCase syntax induced by an instruction map. Sorts (typing
indices) are unchanged. -/
def sigHom (g : InstrSig.Hom P Q) :
    TheoryModel.Signature.Hom (Models.signature P.Instr Γ) (Models.signature Q.Instr Γ) where
  sort i := i
  op o := opMap Γ g o
  arg o := argMap Γ g o
  argSort o j := argSortMap Γ g o j

end OpMap

/-! ### Operation-level functoriality -/

section OpMapLaws

variable {P Q R : InstrSig τ ε}

/-- Argument positions are unchanged, as underlying numbers. -/
theorem argMap_val (g : InstrSig.Hom P Q) :
    ∀ {i : TypingIndex τ} (o : Models.Operation (Φ := P.Instr) Γ i)
      (j : Fin ((Models.signature Q.Instr Γ).arity (opMap Γ g o))),
      (argMap Γ g o j).val = j.val := by
  intro i o j
  cases o <;> rfl

theorem sigHom_argVal (g : InstrSig.Hom P Q) : SigHomArgVal (sigHom Γ g) :=
  fun o j => argMap_val Γ g o j

/-- Relabelling an instruction operation casts the relabelled instruction to the old type. -/
theorem opMap_op (g : InstrSig.Hom P Q) {n : Nat} {β : BoundCtx τ n} (x : P.Instr) :
    opMap Γ g (Models.Operation.op (Γ := Γ) (β := β) x) =
      castOp (Models.signature Q.Instr Γ)
        (congrArg (fun A => (⟨_, β, A⟩ : TypingIndex τ)) (g.target x))
        (Models.Operation.op (β := β) (g.instr x)) :=
  rfl

theorem opMap_op_heq (g : InstrSig.Hom P Q) {n : Nat} {β : BoundCtx τ n} (x : P.Instr) :
    HEq (opMap Γ g (Models.Operation.op (Γ := Γ) (β := β) x))
      (Models.Operation.op (Γ := Γ) (β := β) (g.instr x)) := by
  rw [opMap_op]
  exact castOp_heq _ _

theorem opMap_castOp_heq (g : InstrSig.Hom P Q) {i j : TypingIndex τ} (h : i = j)
    (o : Models.Operation (Φ := P.Instr) Γ i) :
    HEq (opMap Γ g (castOp (Models.signature P.Instr Γ) h o)) (opMap Γ g o) := by
  subst h
  rfl

/-- Relabelling an operation along the identity is the identity, up to the result-type cast. -/
theorem opMap_id :
    ∀ {i : TypingIndex τ} (o : Models.Operation (Φ := P.Instr) Γ i),
      HEq (opMap Γ (𝟙 P) o) o := by
  intro i o
  cases o <;> exact HEq.rfl

/-- Relabelling an operation along a composite, up to the result-type casts. -/
theorem opMap_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    ∀ {i : TypingIndex τ} (o : Models.Operation (Φ := P.Instr) Γ i),
      HEq (opMap Γ (f ≫ g) o) (opMap Γ g (opMap Γ f o)) := by
  intro i o
  cases o with
  | @op n β x =>
      rw [opMap_op, opMap_op]
      refine (castOp_heq _ _).trans ?_
      refine HEq.symm ((opMap_castOp_heq Γ g _ _).trans ?_)
      exact opMap_op_heq Γ g (f.instr x)
  | _ => exact HEq.rfl

end OpMapLaws

/-! ### Functoriality -/

/-- Relabelling along the identity instruction map is the identity signature morphism. -/
theorem sigHom_id (P : InstrSig τ ε) :
    sigHom Γ (𝟙 P) = TheoryModel.Signature.Hom.id (Models.signature P.Instr Γ) :=
  sigHom_ext_of_argVal rfl (fun o => opMap_id Γ o) (sigHom_argVal Γ _) (sigHomArgVal_id _)

/-- Relabelling along a composite is the composite of relabellings. -/
theorem sigHom_comp {P Q R : InstrSig τ ε} (f : P ⟶ Q) (g : Q ⟶ R) :
    sigHom Γ (f ≫ g) = (sigHom Γ g).comp (sigHom Γ f) :=
  sigHom_ext_of_argVal rfl (fun o => opMap_comp Γ f g o) (sigHom_argVal Γ _)
    (sigHomArgVal_comp (sigHom_argVal Γ g) (sigHom_argVal Γ f))

end Silmaril.Isotope.Institution.LetCase
