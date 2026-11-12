module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionMap
public import Silmaril.Raw.SSA.Isotope.Semantics.Value.Map
public import Silmaril.SSA.Isotope.Types.Defs

/-! # Embedding SSA signatures, atomic values and states

The syntax map preserves binders. Typing commutes with a map on base types;
evaluation commutes with maps on atomic values and states under an explicit
simulation of each primitive instruction. No purity assumption is used.
-/

@[expose] public section
universe u v a b c d s t
namespace Silmaril.Isotope.LambdaSSA

namespace Embedding

structure Types {Φ : Type u} {Ψ : Type v} {α : Type a} {β : Type b}
    [HasTy Φ (Ty α)] [HasTy Ψ (Ty β)] (instruction : Φ → Ψ) (base : α → β) : Prop where
  source : ∀ i, instrSrc (instruction i) = Ty.map base (instrSrc i)
  target : ∀ i, instrTrg (instruction i) = Ty.map base (instrTrg i)

end Embedding

theorem Tm.HasType.embed {Φ : Type u} {Ψ : Type v} {α : Type a} {β : Type b}
    [HasTy Φ (Ty α)] [HasTy Ψ (Ty β)]
    (instruction : Φ → Ψ) (base : α → β) (types : Embedding.Types instruction base)
    {Γ : VCtx (Ty α)} {term : Tm Φ} {A : Ty α} (h : Tm.HasType Γ term A) :
    Tm.HasType (Γ.map (Ty.map base)) (term.mapInstr instruction) (A.map base) := by
  induction h with
  | var h =>
    refine Tm.HasType.var ?_
    simp only [SSA.At, List.getElem?_map, h, Option.map_some]
  | @op Γ arg opcode _ ih =>
    change Tm.HasType _ (.op (instruction opcode) (arg.mapInstr instruction)) _
    rw [← types.target opcode]
    exact .op (by simpa only [types.source] using ih)
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | unit => exact .unit
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | abort _ ih => exact .abort ih

namespace Semantics

def mapEnv {α : Type a} {β : Type b} (atom : α → β) (env : Env α) : Env β :=
  fun i => (env i).map atom

@[simp] theorem mapEnv_extend {α : Type a} {β : Type b} (atom : α → β)
    (env : Env α) (value : Value α) :
    mapEnv atom (extend env value) = extend (mapEnv atom env) (value.map atom) := by
  funext i
  cases i <;> rfl

theorem Tm.Eval.embed {Φ : Type u} {Ψ : Type v} {α : Type a} {β : Type b}
    {σ : Type s} {τ : Type t}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {instr' : Ψ → Value β → τ → Value β → τ → Prop}
    (instruction : Φ → Ψ) (atom : α → β) (state : σ → τ)
    (step : ∀ i input before output after, instr i input before output after →
      instr' (instruction i) (input.map atom) (state before) (output.map atom) (state after))
    {env : Env α} {term : LambdaSSA.Tm Φ} {before after : σ} {value : Value α}
    (h : Tm.Eval instr env term before value after) :
    Tm.Eval instr' (mapEnv atom env) (term.mapInstr instruction)
      (state before) (value.map atom) (state after) := by
  induction h with
  | var => exact .var
  | op _ hi ih => exact .op ih (step _ _ _ _ _ hi)
  | let₁ _ _ ih₁ ih₂ => exact .let₁ ih₁ (by simpa only [mapEnv_extend] using ih₂)
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let₂ _ _ ih₁ ih₂ => exact .let₂ ih₁ (by simpa only [mapEnv_extend] using ih₂)
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case_inl _ _ ih₁ ih₂ => exact .case_inl ih₁ (by simpa only [mapEnv_extend] using ih₂)
  | case_inr _ _ ih₁ ih₂ => exact .case_inr ih₁ (by simpa only [mapEnv_extend] using ih₂)

end Semantics
end Silmaril.Isotope.LambdaSSA
