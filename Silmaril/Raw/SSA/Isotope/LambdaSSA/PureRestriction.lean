module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.PureEmbedding

/-! # Checking every primitive before embedding a pure expression

`checkPure` retains the complete syntax tree and attaches each primitive's
existing purity proof. Its erasure is the original expression. Instruction
adapters can therefore require a purity certificate in their constructor,
without admitting unchecked effects or replacing a calculation by its result.
Typing and execution transport reuse the general signature embedding API.
-/

@[expose] public section
universe u v w a b s t e
namespace Silmaril.Isotope.LambdaSSA

/-- A primitive together with its checked effect equality. -/
abbrev PureInstruction (Φ : Type u) {ε : Type e} [HasEff Φ ε] (pureEff : ε) :=
  {i : Φ // IsPure pureEff i}

namespace PureInstruction
variable {Φ : Type u} {ε : Type e} [HasEff Φ ε] {pureEff : ε}

instance {τ : Type v} [HasTy Φ τ] : HasTy (PureInstruction Φ pureEff) τ where
  src i := instrSrc i.val
  trg i := instrTrg i.val

instance : HasEff (PureInstruction Φ pureEff) ε where
  eff i := instrEff i.val

instance {τ : Type v} [HasTy Φ τ] : Signature (PureInstruction Φ pureEff) τ ε where

@[simp] theorem effect (i : PureInstruction Φ pureEff) : instrEff i = pureEff := i.property

end PureInstruction

namespace Tm
variable {Φ : Type u} {ε : Type e} [HasEff Φ ε] {pureEff : ε}

/-- Retain each node and attach the purity certificate at each primitive. -/
def checkPure (term : Tm Φ) (pure : term.Pure pureEff) : Tm (PureInstruction Φ pureEff) :=
  match term with
  | .var i => .var i
  | .op i x => .op ⟨i, by cases pure; assumption⟩ (x.checkPure (by cases pure; assumption))
  | .let₁ x body => .let₁ (x.checkPure (by cases pure; assumption)) (body.checkPure (by cases pure; assumption))
  | .pair x y => .pair (x.checkPure (by cases pure; assumption)) (y.checkPure (by cases pure; assumption))
  | .unit => .unit
  | .let₂ x body => .let₂ (x.checkPure (by cases pure; assumption)) (body.checkPure (by cases pure; assumption))
  | .inl x => .inl (x.checkPure (by cases pure; assumption))
  | .inr x => .inr (x.checkPure (by cases pure; assumption))
  | .case x left right => .case (x.checkPure (by cases pure; assumption))
      (left.checkPure (by cases pure; assumption)) (right.checkPure (by cases pure; assumption))
  | .abort x => .abort (x.checkPure (by cases pure; assumption))

@[simp] theorem checkPure_erase {term : Tm Φ} (pure : term.Pure pureEff) :
    (term.checkPure pure).mapInstr Subtype.val = term := by
  induction pure <;> simp_all [checkPure, mapInstr]

theorem checkPure_rename {term : Tm Φ} (pure : term.Pure pureEff) (ρ : Nat → Nat) :
    (term.rename ρ).checkPure (pure.rename ρ) = (term.checkPure pure).rename ρ := by
  induction pure generalizing ρ <;> simp_all [checkPure, rename]

@[simp] theorem usesVar_checkPure {term : Tm Φ} (pure : term.Pure pureEff) (i : Nat) :
    (term.checkPure pure).UsesVar i ↔ term.UsesVar i := by
  simpa only [checkPure_erase] using (usesVar_mapInstr Subtype.val (term.checkPure pure) i).symm

theorem checkPure_pure {term : Tm Φ} (pure : term.Pure pureEff) :
    (term.checkPure pure).Pure pureEff := by
  induction pure <;> constructor <;> assumption

section Typing
variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem HasType.checkPure {Γ : VCtx τ} {term : Tm Φ} {A : τ} (typed : HasType Γ term A)
    (pure : term.Pure pureEff) : HasType Γ (term.checkPure pure) A := by
  induction typed with
  | var h => exact .var h
  | op _ ih => cases pure with | op _ hp => exact .op (ih hp)
  | let₁ _ _ ih₁ ih₂ => cases pure with | let₁ h₁ h₂ => exact .let₁ (ih₁ h₁) (ih₂ h₂)
  | pair _ _ ih₁ ih₂ => cases pure with | pair h₁ h₂ => exact .pair (ih₁ h₁) (ih₂ h₂)
  | unit => exact .unit
  | let₂ _ _ ih₁ ih₂ => cases pure with | let₂ h₁ h₂ => exact .let₂ (ih₁ h₁) (ih₂ h₂)
  | inl _ ih => cases pure with | inl hp => exact .inl (ih hp)
  | inr _ ih => cases pure with | inr hp => exact .inr (ih hp)
  | case _ _ _ ih₁ ih₂ ih₃ => cases pure with | case h₁ h₂ h₃ => exact .case (ih₁ h₁) (ih₂ h₂) (ih₃ h₃)
  | abort _ ih => cases pure with | abort hp => exact .abort (ih hp)

theorem hasType_checkPure_iff {Γ : VCtx τ} {term : Tm Φ} {A : τ} (pure : term.Pure pureEff) :
    HasType Γ (term.checkPure pure) A ↔ HasType Γ term A := by
  constructor
  · intro typed
    simpa only [checkPure_erase] using typed.mapInstr Subtype.val ⟨fun _ => rfl, fun _ => rfl⟩
  · exact fun typed => typed.checkPure pure

end Typing
end Tm

namespace Semantics.Tm
variable {Φ : Type u} {Ψ : Type v} {ε : Type e} [HasEff Φ ε] {pureEff : ε}
variable {α : Type a} {β : Type b} {σ : Type s} {τ : Type t}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-- Restriction changes only the instruction tag, keeping every intermediate
state, environment, value and effectful evaluation constructor. -/
theorem Eval.checkPure {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (execution : Eval instr env term before value after) (pure : term.Pure pureEff) :
    Eval (fun i : PureInstruction Φ pureEff => instr i.val) env (term.checkPure pure) before value after := by
  induction execution with
  | var => exact .var
  | op _ step ih => cases pure with | op _ hp => exact .op (ih hp) step
  | let₁ _ _ ih₁ ih₂ => cases pure with | let₁ h₁ h₂ => exact .let₁ (ih₁ h₁) (ih₂ h₂)
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => cases pure with | pair h₁ h₂ => exact .pair (ih₁ h₁) (ih₂ h₂)
  | let₂ _ _ ih₁ ih₂ => cases pure with | let₂ h₁ h₂ => exact .let₂ (ih₁ h₁) (ih₂ h₂)
  | inl _ ih => cases pure with | inl hp => exact .inl (ih hp)
  | inr _ ih => cases pure with | inr hp => exact .inr (ih hp)
  | case_inl _ _ ih₁ ih₂ => cases pure with | case h₁ h₂ _ => exact .case_inl (ih₁ h₁) (ih₂ h₂)
  | case_inr _ _ ih₁ ih₂ => cases pure with | case h₁ _ h₂ => exact .case_inr (ih₁ h₁) (ih₂ h₂)

theorem eval_checkPure_iff {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (pure : term.Pure pureEff) :
    Eval (fun i : PureInstruction Φ pureEff => instr i.val) env (term.checkPure pure) before value after ↔
      Eval instr env term before value after := by
  constructor
  · intro execution
    simpa only [LambdaSSA.Tm.checkPure_erase] using
      execution.mapInstr Subtype.val (fun _ _ _ _ _ step => step)
  · exact fun execution => execution.checkPure pure

/-- Embed into a signature whose primitive constructor requires a purity proof. -/
theorem Eval.embed_checked {instr' : Ψ → Value β → τ → Value β → τ → Prop}
    (instruction : PureInstruction Φ pureEff → Ψ) (atom : α → β) (state : σ → τ)
    (step : ∀ (i : PureInstruction Φ pureEff) input before output after,
      instr i.val input before output after →
        instr' (instruction i) (input.map atom) (state before) (output.map atom) (state after))
    {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (execution : Eval instr env term before value after) (pure : term.Pure pureEff) :
    Eval instr' (mapEnv atom env) ((term.checkPure pure).mapInstr instruction)
      (state before) (value.map atom) (state after) :=
  (execution.checkPure pure).embed instruction atom state step

end Semantics.Tm
end Silmaril.Isotope.LambdaSSA
