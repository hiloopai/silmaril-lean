module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSASemantics
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External.Structural

/-! Scoped expression conversion preserves and reflects externally divergent primitives. -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.CaseSSA

open LetCase.LocallyNameless

variable {α : Type u} {Φ : Type v} {σ : Type w} {n : Nat}
    {instr : Φ → Value α → σ → Value α → σ → Prop} {prim : Φ → Value α → σ → Prop}
    {free : LetIter.Semantics.FreeEnv Empty α}

theorem erase_external_iff {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s : σ} (agree : EnvAgrees env bound) :
    LambdaSSA.Semantics.Tm.ExternalDiverges instr prim env (erase t) s ↔
      LetIter.Semantics.External.Diverges instr free prim (.term bound (CaseIter.embed t) s) := by
  induction t generalizing env s with
  | fv x => exact x.elim
  | bv i | unit =>
    constructor
    · intro h; cases h
    · intro h; cases h.unfold with | core h => cases h
  | op f a ih =>
    constructor
    · intro h; cases h with
      | op_arg arg => exact .fold_core (.op ((ih agree).mp arg))
      | primitive arg div => exact .primitive ((erase_eval_iff agree).mp arg) div
    · intro h; cases h.unfold with
      | core h => cases h with | op arg => exact .op_arg ((ih agree).mpr arg)
      | primitive arg div => exact .primitive ((erase_eval_iff agree).mpr arg) div
  | let₁ a b iha ihb =>
    constructor
    · intro h; cases h with
      | let₁_arg arg => exact .fold_core (.let₁_arg ((iha agree).mp arg))
      | let₁_body arg body =>
        exact .fold_core (.let₁_body ((erase_eval_iff agree).mp arg) ((ihb (agree.extend _)).mp body))
    · intro h; cases h.unfold with | core h => cases h with
      | let₁_arg arg => exact .let₁_arg ((iha agree).mpr arg)
      | let₁_body arg body =>
        exact .let₁_body ((erase_eval_iff agree).mpr arg) ((ihb (agree.extend _)).mpr body)
  | pair a b iha ihb =>
    constructor
    · intro h; cases h with
      | pair_left arg => exact .fold_core (.pair_left ((iha agree).mp arg))
      | pair_right arg body =>
        exact .fold_core (.pair_right ((erase_eval_iff agree).mp arg) ((ihb agree).mp body))
    · intro h; cases h.unfold with | core h => cases h with
      | pair_left arg => exact .pair_left ((iha agree).mpr arg)
      | pair_right arg body => exact .pair_right ((erase_eval_iff agree).mpr arg) ((ihb agree).mpr body)
  | let₂ a b iha ihb =>
    constructor
    · intro h; cases h with
      | let₂_arg arg => exact .fold_core (.let₂_arg ((iha agree).mp arg))
      | let₂_body arg body =>
        exact .fold_core (.let₂_body ((erase_eval_iff agree).mp arg)
          ((ihb ((agree.extend _).extend _)).mp body))
    · intro h; cases h.unfold with | core h => cases h with
      | let₂_arg arg => exact .let₂_arg ((iha agree).mpr arg)
      | let₂_body arg body =>
        exact .let₂_body ((erase_eval_iff agree).mpr arg) ((ihb ((agree.extend _).extend _)).mpr body)
  | inl a ih =>
    constructor
    · intro h; cases h with | inl arg => exact .fold_core (.inl ((ih agree).mp arg))
    · intro h; cases h.unfold with | core h => cases h with | inl arg => exact .inl ((ih agree).mpr arg)
  | inr a ih =>
    constructor
    · intro h; cases h with | inr arg => exact .fold_core (.inr ((ih agree).mp arg))
    · intro h; cases h.unfold with | core h => cases h with | inr arg => exact .inr ((ih agree).mpr arg)
  | case a l r iha ihl ihr =>
    constructor
    · intro h; cases h with
      | case_arg arg => exact .fold_core (.case_scrutinee ((iha agree).mp arg))
      | case_inl arg body =>
        exact .fold_core (.case_inl ((erase_eval_iff agree).mp arg) ((ihl (agree.extend _)).mp body))
      | case_inr arg body =>
        exact .fold_core (.case_inr ((erase_eval_iff agree).mp arg) ((ihr (agree.extend _)).mp body))
    · intro h; cases h.unfold with | core h => cases h with
      | case_scrutinee arg => exact .case_arg ((iha agree).mpr arg)
      | case_inl arg body =>
        exact .case_inl ((erase_eval_iff agree).mpr arg) ((ihl (agree.extend _)).mpr body)
      | case_inr arg body =>
        exact .case_inr ((erase_eval_iff agree).mpr arg) ((ihr (agree.extend _)).mpr body)
  | abort a ih =>
    constructor
    · intro h; cases h with | abort_arg arg => exact .fold_core (.abort ((ih agree).mp arg))
    · intro h; cases h.unfold with | core h => cases h with | abort arg => exact .abort_arg ((ih agree).mpr arg)

theorem ofScoped_external_iff {t : LambdaSSA.Tm Φ} (scope : t.Scoped n)
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s : σ} (agree : EnvAgrees env bound) :
    LetIter.Semantics.External.Diverges instr free prim
      (.term bound (CaseIter.embed (ofScoped t scope)) s) ↔
      LambdaSSA.Semantics.Tm.ExternalDiverges instr prim env t s := by
  rw [← erase_external_iff agree, erase_ofScoped]

end Silmaril.Isotope.Morphism.CaseSSA
