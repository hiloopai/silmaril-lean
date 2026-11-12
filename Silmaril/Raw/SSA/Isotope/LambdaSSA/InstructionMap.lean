module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Relabeling primitive instructions in lambda-SSA

Relabeling preserves all value and label binders. Type preservation requires
source/target agreement, and execution preservation requires simulation of the
atomic transitions. Neither condition assumes purity of the instructions.
-/

@[expose] public section
universe u v w t a s
namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {Ψ : Type v} {Ω : Type w}

def Tm.mapInstr (f : Φ → Ψ) : Tm Φ → Tm Ψ
  | .var i => .var i
  | .op i x => .op (f i) (x.mapInstr f)
  | .let₁ x body => .let₁ (x.mapInstr f) (body.mapInstr f)
  | .pair x y => .pair (x.mapInstr f) (y.mapInstr f)
  | .unit => .unit
  | .let₂ x body => .let₂ (x.mapInstr f) (body.mapInstr f)
  | .inl x => .inl (x.mapInstr f)
  | .inr x => .inr (x.mapInstr f)
  | .case x left right => .case (x.mapInstr f) (left.mapInstr f) (right.mapInstr f)
  | .abort x => .abort (x.mapInstr f)

def Region.mapInstr (f : Φ → Ψ) : Region Φ → Region Ψ
  | .br label arg => .br label (arg.mapInstr f)
  | .case discr left right => .case (discr.mapInstr f) (left.mapInstr f) (right.mapInstr f)
  | .let₁ value body => .let₁ (value.mapInstr f) (body.mapInstr f)
  | .let₂ value body => .let₂ (value.mapInstr f) (body.mapInstr f)
  | .cfg entry n blocks => .cfg (entry.mapInstr f) n (fun i => (blocks i).mapInstr f)

@[simp] theorem Tm.mapInstr_id (term : Tm Φ) : term.mapInstr id = term := by
  induction term <;> simp_all [mapInstr]

@[simp] theorem Tm.mapInstr_comp (f : Φ → Ψ) (g : Ψ → Ω) (term : Tm Φ) :
    (term.mapInstr f).mapInstr g = term.mapInstr (g ∘ f) := by
  induction term <;> simp_all [mapInstr]

theorem Tm.mapInstr_rename (f : Φ → Ψ) (term : Tm Φ) (ρ : Nat → Nat) :
    (term.rename ρ).mapInstr f = (term.mapInstr f).rename ρ := by
  induction term generalizing ρ <;> simp_all [rename, mapInstr]

@[simp] theorem Region.mapInstr_id (region : Region Φ) : region.mapInstr id = region := by
  induction region <;> simp_all [mapInstr]

@[simp] theorem Region.mapInstr_comp (f : Φ → Ψ) (g : Ψ → Ω) (region : Region Φ) :
    (region.mapInstr f).mapInstr g = region.mapInstr (g ∘ f) := by
  induction region <;> simp_all [mapInstr]

theorem Region.mapInstr_renameVars (f : Φ → Ψ) (region : Region Φ) (ρ : Nat → Nat) :
    (region.renameVars ρ).mapInstr f = (region.mapInstr f).renameVars ρ := by
  induction region generalizing ρ <;> simp_all [renameVars, mapInstr, Tm.mapInstr_rename]

theorem Region.mapInstr_renameLabels (f : Φ → Ψ) (region : Region Φ) (ρ : Nat → Nat) :
    (region.renameLabels ρ).mapInstr f = (region.mapInstr f).renameLabels ρ := by
  induction region generalizing ρ <;> simp_all [renameLabels, mapInstr]

namespace InstructionMap

/-- The instruction map preserves the ambient value-type signature. -/
structure PreservesTypes {τ : Type t} [HasTy Φ τ] [HasTy Ψ τ] (f : Φ → Ψ) : Prop where
  source : ∀ i, (instrSrc (f i) : τ) = instrSrc i
  target : ∀ i, (instrTrg (f i) : τ) = instrTrg i

end InstructionMap

section Typing
variable {τ : Type t} [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]
variable (f : Φ → Ψ) (hf : InstructionMap.PreservesTypes (τ := τ) f)
include hf

theorem Tm.HasType.mapInstr {Γ : VCtx τ} {term : Tm Φ} {A : τ}
    (h : Tm.HasType Γ term A) : Tm.HasType Γ (term.mapInstr f) A := by
  induction h with
  | var h => exact .var h
  | @op Γ arg opcode _ ih =>
    change Tm.HasType Γ (.op (f opcode) (arg.mapInstr f)) _
    rw [← hf.target opcode]
    exact .op (by simpa only [hf.source] using ih)
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | unit => exact .unit
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih

theorem Region.HasType.mapInstr {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) : Region.HasType Γ (region.mapInstr f) L := by
  induction h with
  | br label arg => exact .br label (arg.mapInstr f hf)
  | case discr _ _ ih₁ ih₂ => exact .case (discr.mapInstr f hf) ih₁ ih₂
  | let₁ value _ ih => exact .let₁ (value.mapInstr f hf) ih
  | let₂ value _ ih => exact .let₂ (value.mapInstr f hf) ih
  | cfg R _ _ ihEntry ihBlocks => exact .cfg R ihEntry ihBlocks

end Typing

namespace Semantics
variable {α : Type a} {σ : Type s}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}
variable {instr' : Ψ → Value α → σ → Value α → σ → Prop}
variable (f : Φ → Ψ)
variable (step : ∀ i input before output after,
  instr i input before output after → instr' (f i) input before output after)
include step

theorem Tm.Eval.mapInstr {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Tm.Eval instr env term before value after) :
    Tm.Eval instr' env (term.mapInstr f) before value after := by
  induction h with
  | var => exact .var
  | op _ hi ih => exact .op ih (step _ _ _ _ _ hi)
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case_inl _ _ ih₁ ih₂ => exact .case_inl ih₁ ih₂
  | case_inr _ _ ih₁ ih₂ => exact .case_inr ih₁ ih₂

theorem Region.Eval.mapInstr {env : Env α} {region : LambdaSSA.Region Φ}
    {before after : σ} {label : Nat} {value : Value α}
    (h : Region.Eval instr env region before label value after) :
    Region.Eval instr' env (region.mapInstr f) before label value after := by
  induction h using Region.Eval.rec
      (motive_2 := fun env _ blocks first initial before label value after _ =>
        Region.Follow instr' env (fun i => (blocks i).mapInstr f)
          first initial before label value after) with
  | br arg => exact .br (arg.mapInstr f step)
  | let₁ arg _ ih => exact .let₁ (arg.mapInstr f step) ih
  | let₂ arg _ ih => exact .let₂ (arg.mapInstr f step) ih
  | case_inl arg _ ih => exact .case_inl (arg.mapInstr f step) ih
  | case_inr arg _ ih => exact .case_inr (arg.mapInstr f step) ih
  | cfg _ _ ihEntry ihFollow => exact .cfg ihEntry ihFollow
  | exit outside => exact .exit outside
  | step inside _ _ ihHead ihTail => exact .step inside ihHead ihTail

end Semantics
end Silmaril.Isotope.LambdaSSA
