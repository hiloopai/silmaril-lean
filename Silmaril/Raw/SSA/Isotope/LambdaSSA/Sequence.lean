module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Effect-preserving single-exit region sequencing

The first region transfers its result to a continuation block. Its branch
arguments retain their evaluation count even when they have effects. The
continuation receives that result before the original captured environment.
-/

@[expose] public section
universe u v w x
namespace Silmaril.Isotope.LambdaSSA
variable {Φ : Type u}

def Region.sequence (first next : Region Φ) : Region Φ :=
  .cfg first 1 (fun _ => next.renameLabels Nat.succ)

theorem Region.HasType.sequence {τ : Type v} [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]
    {Γ : VCtx τ} {L : LCtx τ} {A : τ} {first next : Region Φ}
    (hf : Region.HasType Γ first [A]) (hn : Region.HasType (A :: Γ) next L) :
    Region.HasType Γ (Region.sequence first next) L := by
  apply Region.HasType.cfg (fun _ => A)
  · have hren : Ren [A] (A :: L) id := by
      intro i B h
      cases i with
      | zero => exact h
      | succ i => simp [At] at h
    simpa using hf.renameLabels hren
  · intro i
    exact hn.renameLabels (SSA.Ren.wk L A)

theorem Semantics.Region.Eval.sequence {α : Type v} {σ : Type w}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {first next : Region Φ}
    {before middle after : σ} {value result : Value α} {label : Nat}
    (hf : Semantics.Region.Eval instr env first before 0 value middle)
    (hn : Semantics.Region.Eval instr (Semantics.extend env value) next middle label result after) :
    Semantics.Region.Eval instr env (Region.sequence first next) before label result after := by
  exact .cfg hf (.step (by decide) (hn.renameLabels Nat.succ)
    (by simpa using (Semantics.Region.Follow.exit
      (instr := instr) (env := env) (blocks := fun _ : Fin 1 => next.renameLabels Nat.succ)
      (value := result) (s := after) (show 1 ≤ label + 1 by omega))))

end Silmaril.Isotope.LambdaSSA
