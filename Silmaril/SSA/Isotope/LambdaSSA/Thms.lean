module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Silmaril.SSA.Isotope.Types.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Determinism

/-!
# Lambda-SSA: renaming and determinism of evaluation

Results about the narrow lambda-SSA interface (`Silmaril.SSA.Isotope.LambdaSSA.Defs`):
evaluation commutes with renaming of value variables and of labels, and is
deterministic when every primitive instruction is. This header also re-exports
lambda-SSA typing and its structural laws (`LambdaSSA.Typing.Thms`) and the
type-syntax comparisons (`Types.Thms`), so it is the full lambda-SSA interface.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}

theorem extend_rename {env env' : Env α} {ρ : Nat → Nat}
    (h : ∀ i, env' (ρ i) = env i) (value : Value α) :
    ∀ i, extend env' value (Silmaril.DeBruijn.lift ρ i) = extend env value i := by
  intro i
  cases i with
  | zero => rfl
  | succ i => exact h i

namespace Tm

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem Eval.rename {env : Env α} {a : LambdaSSA.Tm Φ} {s s' : σ} {v : Value α}
    (h : Eval instr env a s v s') {env' : Env α} {ρ : Nat → Nat}
    (hρ : ∀ i, env' (ρ i) = env i) : Eval instr env' (a.rename ρ) s v s' := by
  induction h generalizing env' ρ with
  | var => simpa only [LambdaSSA.Tm.rename, hρ] using
      (Eval.var (env := env') (i := ρ _) (s := _))
  | op _ step ih => exact .op (ih hρ) step
  | let₁ _ _ ih₁ ih₂ => exact .let₁ (ih₁ hρ) (ih₂ (extend_rename hρ _))
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ hρ) (ih₂ hρ)
  | let₂ _ _ ih₁ ih₂ =>
      exact .let₂ (ih₁ hρ) (ih₂ (extend_rename (extend_rename hρ _) _))
  | inl _ ih => exact .inl (ih hρ)
  | inr _ ih => exact .inr (ih hρ)
  | case_inl _ _ ih₁ ih₂ => exact .case_inl (ih₁ hρ) (ih₂ (extend_rename hρ _))
  | case_inr _ _ ih₁ ih₂ => exact .case_inr (ih₁ hρ) (ih₂ (extend_rename hρ _))

end Tm

namespace Region

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem Eval.renameVars {env : Env α} {r : LambdaSSA.Region Φ}
    {s s' : σ} {label : Nat} {value : Value α}
    (h : Eval instr env r s label value s') {env' : Env α} {ρ : Nat → Nat}
    (hρ : ∀ i, env' (ρ i) = env i) :
    Eval instr env' (r.renameVars ρ) s label value s' := by
  induction h using Eval.rec
      (motive_2 := fun env _ blocks first initial s label value s' _ =>
        ∀ {env' : Env α} {ρ : Nat → Nat}, (∀ i, env' (ρ i) = env i) →
        Follow instr env' (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift ρ))
          first initial s label value s') generalizing env' ρ with
  | br arg => exact .br (arg.rename hρ)
  | let₁ arg _ ih => exact .let₁ (arg.rename hρ) (ih (extend_rename hρ _))
  | let₂ arg _ ih =>
      exact .let₂ (arg.rename hρ) (ih (extend_rename (extend_rename hρ _) _))
  | case_inl arg _ ih => exact .case_inl (arg.rename hρ) (ih (extend_rename hρ _))
  | case_inr arg _ ih => exact .case_inr (arg.rename hρ) (ih (extend_rename hρ _))
  | cfg _ _ ihEntry ihFollow => exact .cfg (ihEntry hρ) (ihFollow hρ)
  | exit outside => exact .exit outside
  | step inside _ _ ihHead ihTail =>
      rename_i env' ρ hρ
      exact .step inside (ihHead (extend_rename hρ _)) (ihTail hρ)

/-- An exit from a CFG whose labels are renamed under `n` binders leaves at the renamed
external label. -/
theorem Follow.exit_renameLabels {env : Env α} {n label : Nat}
    {blocks : Fin n → LambdaSSA.Region Φ} {value : Value α} {s : σ}
    (outside : n ≤ label) (ρ : Nat → Nat) :
    Follow instr env (fun i => (blocks i).renameLabels (Silmaril.DeBruijn.liftN n ρ))
      (Silmaril.DeBruijn.liftN n ρ label) value s (ρ (label - n)) value s := by
  rw [Silmaril.DeBruijn.liftN_ge ρ outside]
  simpa only [Nat.add_sub_cancel_left] using
    (Follow.exit (instr := instr) (env := env)
      (blocks := fun i => (blocks i).renameLabels (Silmaril.DeBruijn.liftN n ρ))
      (value := value) (s := s) (Nat.le_add_right n (ρ (label - n))))

theorem Eval.renameLabels {env : Env α} {r : LambdaSSA.Region Φ}
    {s s' : σ} {label : Nat} {value : Value α}
    (h : Eval instr env r s label value s') (ρ : Nat → Nat) :
    Eval instr env (r.renameLabels ρ) s (ρ label) value s' := by
  induction h using Eval.rec
      (motive_2 := fun env n blocks first initial s label value s' _ =>
        ∀ ρ, Follow instr env (fun i => (blocks i).renameLabels (Silmaril.DeBruijn.liftN n ρ))
          (Silmaril.DeBruijn.liftN n ρ first) initial s (ρ label) value s') generalizing ρ with
  | br arg => exact .br arg
  | let₁ arg _ ih => exact .let₁ arg (ih ρ)
  | let₂ arg _ ih => exact .let₂ arg (ih ρ)
  | case_inl arg _ ih => exact .case_inl arg (ih ρ)
  | case_inr arg _ ih => exact .case_inr arg (ih ρ)
  | cfg _ _ ihEntry ihFollow => exact .cfg (ihEntry (Silmaril.DeBruijn.liftN _ ρ)) (ihFollow ρ)
  | exit outside => exact Follow.exit_renameLabels outside _
  | step inside _ _ ihHead ihTail =>
      rename_i ρ
      rw [Silmaril.DeBruijn.liftN_lt ρ inside]
      exact .step inside (ihHead (Silmaril.DeBruijn.liftN _ ρ)) (ihTail ρ)

end Region

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

/-! ## Determinism -/

/-- Term evaluation is deterministic when every instruction is. -/
theorem Tm.Eval.deterministic (hd : InstrDeterministic instr)
    {env : Env α} {t : LambdaSSA.Tm Φ} {s s₁ : σ} {v₁ : Value α}
    (h : Tm.Eval instr env t s v₁ s₁) :
    ∀ {v₂ s₂}, Tm.Eval instr env t s v₂ s₂ → v₁ = v₂ ∧ s₁ = s₂ :=
  fun h' => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.Tm.Eval.deterministic hd h h'

/-- Region evaluation is deterministic when every instruction is: the exit label, its
argument and the final state are unique. -/
theorem Region.Eval.deterministic (hd : InstrDeterministic instr)
    {env : Env α} {r : LambdaSSA.Region Φ} {s s₁ : σ} {l₁ : Nat} {v₁ : Value α}
    (h : Region.Eval instr env r s l₁ v₁ s₁) :
    ∀ {l₂ v₂ s₂}, Region.Eval instr env r s l₂ v₂ s₂ →
      l₁ = l₂ ∧ v₁ = v₂ ∧ s₁ = s₂ :=
  fun h' => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.Region.Eval.deterministic hd h h'

/-- Following the internal transfers of a CFG is deterministic when every instruction is. -/
theorem Region.Follow.deterministic (hd : InstrDeterministic instr)
    {env : Env α} {n first l₁ : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
    {initial v₁ : Value α} {s s₁ : σ}
    (h : Region.Follow instr env blocks first initial s l₁ v₁ s₁) :
    ∀ {l₂ v₂ s₂}, Region.Follow instr env blocks first initial s l₂ v₂ s₂ →
      l₁ = l₂ ∧ v₁ = v₂ ∧ s₁ = s₂ :=
  fun h' => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.Region.Follow.deterministic hd h h'

end Silmaril.Isotope.LambdaSSA.Semantics

end
