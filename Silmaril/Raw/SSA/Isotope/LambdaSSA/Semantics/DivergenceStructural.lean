module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Divergence

/-! # Divergence respects value and label renaming -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}

inductive Config.VarRenaming : Config α Φ σ → Config α Φ σ → Prop where
  | region {env env' : Env α} {r : LambdaSSA.Region Φ} {s : σ} {ρ : Nat → Nat} :
      (∀ i, env' (ρ i) = env i) →
      VarRenaming (.region env r s) (.region env' (r.renameVars ρ) s)
  | follow {env env' : Env α} {n : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
      {label : Nat} {value : Value α} {s : σ} {ρ : Nat → Nat} :
      (∀ i, env' (ρ i) = env i) →
      VarRenaming (.follow env blocks label value s)
        (.follow env' (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift ρ)) label value s)

theorem Diverges.of_varRenaming {c c' : Config α Φ σ}
    (h : Diverges instr c) (hr : Config.VarRenaming c c') : Diverges instr c' := by
  refine Diverges.coinduct
    (fun d => ∃ c, Diverges instr c ∧ Config.VarRenaming c d) ?_ ⟨c, h, hr⟩
  intro d hd
  obtain ⟨c, hc, hr⟩ := hd
  cases hr with
  | region hρ =>
      cases hc.unfold with
      | let₁ arg rest =>
          exact .let₁ (arg.rename hρ) ⟨_, rest, .region (extend_rename hρ _)⟩
      | let₂ arg rest =>
          exact .let₂ (arg.rename hρ)
            ⟨_, rest, .region (extend_rename (extend_rename hρ _) _)⟩
      | case_inl arg rest =>
          exact .case_inl (arg.rename hρ) ⟨_, rest, .region (extend_rename hρ _)⟩
      | case_inr arg rest =>
          exact .case_inr (arg.rename hρ) ⟨_, rest, .region (extend_rename hρ _)⟩
      | cfg_entry rest => exact .cfg_entry ⟨_, rest, .region hρ⟩
      | cfg_follow entry rest =>
          exact .cfg_follow (entry.renameVars hρ) ⟨_, rest, .follow hρ⟩
  | follow hρ =>
      cases hc.unfold with
      | follow_body inside rest =>
          exact .follow_body inside ⟨_, rest, .region (extend_rename hρ _)⟩
      | follow_next inside head rest =>
          exact .follow_next inside (head.renameVars (extend_rename hρ _))
            ⟨_, rest, .follow hρ⟩

theorem Diverges.renameVars {env env' : Env α} {r : LambdaSSA.Region Φ}
    {s : σ} {ρ : Nat → Nat} (h : Diverges instr (.region env r s))
    (hρ : ∀ i, env' (ρ i) = env i) : Diverges instr (.region env' (r.renameVars ρ) s) :=
  h.of_varRenaming (.region hρ)

theorem Diverges.renameVars_follow {env env' : Env α} {n : Nat}
    {blocks : Fin n → LambdaSSA.Region Φ} {label : Nat} {value : Value α} {s : σ}
    {ρ : Nat → Nat} (h : Diverges instr (.follow env blocks label value s))
    (hρ : ∀ i, env' (ρ i) = env i) :
    Diverges instr (.follow env'
      (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift ρ)) label value s) :=
  h.of_varRenaming (.follow hρ)

inductive Config.LabelRenaming : Config α Φ σ → Config α Φ σ → Prop where
  | region {env : Env α} {r : LambdaSSA.Region Φ} {s : σ} (ρ : Nat → Nat) :
      LabelRenaming (.region env r s) (.region env (r.renameLabels ρ) s)
  | follow {env : Env α} {n : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
      {label : Nat} {value : Value α} {s : σ} (ρ : Nat → Nat) :
      LabelRenaming (.follow env blocks label value s)
        (.follow env (fun i => (blocks i).renameLabels (Silmaril.DeBruijn.liftN n ρ))
          (Silmaril.DeBruijn.liftN n ρ label) value s)

theorem Diverges.of_labelRenaming {c c' : Config α Φ σ}
    (h : Diverges instr c) (hr : Config.LabelRenaming c c') : Diverges instr c' := by
  refine Diverges.coinduct
    (fun d => ∃ c, Diverges instr c ∧ Config.LabelRenaming c d) ?_ ⟨c, h, hr⟩
  intro d hd
  obtain ⟨c, hc, hr⟩ := hd
  cases hr with
  | region ρ =>
      cases hc.unfold with
      | let₁ arg rest => exact .let₁ arg ⟨_, rest, .region ρ⟩
      | let₂ arg rest => exact .let₂ arg ⟨_, rest, .region ρ⟩
      | case_inl arg rest => exact .case_inl arg ⟨_, rest, .region ρ⟩
      | case_inr arg rest => exact .case_inr arg ⟨_, rest, .region ρ⟩
      | cfg_entry rest => exact .cfg_entry ⟨_, rest, .region (Silmaril.DeBruijn.liftN _ ρ)⟩
      | cfg_follow entry rest =>
          exact .cfg_follow (entry.renameLabels (Silmaril.DeBruijn.liftN _ ρ)) ⟨_, rest, .follow ρ⟩
  | follow ρ =>
      cases hc.unfold with
      | follow_body inside rest =>
          simp only [Silmaril.DeBruijn.liftN_lt ρ inside]
          exact .follow_body inside ⟨_, rest, .region (Silmaril.DeBruijn.liftN _ ρ)⟩
      | follow_next inside head rest =>
          simp only [Silmaril.DeBruijn.liftN_lt ρ inside]
          exact .follow_next inside (head.renameLabels (Silmaril.DeBruijn.liftN _ ρ))
            ⟨_, rest, .follow ρ⟩

theorem Diverges.renameLabels {env : Env α} {r : LambdaSSA.Region Φ}
    {s : σ} (h : Diverges instr (.region env r s)) (ρ : Nat → Nat) :
    Diverges instr (.region env (r.renameLabels ρ) s) := h.of_labelRenaming (.region ρ)

theorem Diverges.renameLabels_follow {env : Env α} {n : Nat}
    {blocks : Fin n → LambdaSSA.Region Φ} {label : Nat} {value : Value α} {s : σ}
    (h : Diverges instr (.follow env blocks label value s)) (ρ : Nat → Nat) :
    Diverges instr (.follow env (fun i => (blocks i).renameLabels (Silmaril.DeBruijn.liftN n ρ))
      (Silmaril.DeBruijn.liftN n ρ label) value s) := h.of_labelRenaming (.follow ρ)

end Silmaril.Isotope.LambdaSSA.Semantics
