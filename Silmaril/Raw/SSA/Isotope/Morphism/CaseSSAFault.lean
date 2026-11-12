module

public import Silmaril.Raw.SSA.Isotope.Morphism.CaseSSASemantics
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault

/-! Explicit primitive faults agree across scoped SSA expression conversion. -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Morphism.CaseSSA

open LetCase.LocallyNameless

variable {α : Type u} {Φ : Type v} {σ : Type w} {n : Nat}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : LetIter.Semantics.FreeEnv Empty α}

theorem erase_fault_iff {t : Tm Empty Φ n}
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s s' : σ} (agree : EnvAgrees env bound) :
    LambdaSSA.Semantics.Tm.Fault instr faults env (erase t) s s' ↔
      LetIter.Semantics.Fault instr faults free bound (CaseIter.embed t) s s' := by
  induction t generalizing env s s' with
  | fv x => exact x.elim
  | bv i => constructor <;> intro h <;> cases h
  | unit => constructor <;> intro h <;> cases h
  | op f a ih =>
    constructor
    · intro h; cases h with
      | op_arg arg => exact .op_arg ((ih agree).mp arg)
      | op_fault arg fault => exact .op_fault ((erase_eval_iff agree).mp arg) fault
    · intro h; cases h with
      | op_arg arg => exact .op_arg ((ih agree).mpr arg)
      | op_fault arg fault => exact .op_fault ((erase_eval_iff agree).mpr arg) fault
  | let₁ a b iha ihb =>
    constructor
    · intro h; cases h with
      | let₁_arg arg => exact .let₁_arg ((iha agree).mp arg)
      | let₁_body arg body =>
        exact .let₁_body ((erase_eval_iff agree).mp arg) ((ihb (agree.extend _)).mp body)
    · intro h; cases h with
      | let₁_arg arg => exact .let₁_arg ((iha agree).mpr arg)
      | let₁_body arg body =>
        exact .let₁_body ((erase_eval_iff agree).mpr arg) ((ihb (agree.extend _)).mpr body)
  | pair a b iha ihb =>
    constructor
    · intro h; cases h with
      | pair_left arg => exact .pair_left ((iha agree).mp arg)
      | pair_right arg body => exact .pair_right ((erase_eval_iff agree).mp arg) ((ihb agree).mp body)
    · intro h; cases h with
      | pair_left arg => exact .pair_left ((iha agree).mpr arg)
      | pair_right arg body => exact .pair_right ((erase_eval_iff agree).mpr arg) ((ihb agree).mpr body)
  | let₂ a b iha ihb =>
    constructor
    · intro h; cases h with
      | let₂_arg arg => exact .let₂_arg ((iha agree).mp arg)
      | let₂_body arg body =>
        exact .let₂_body ((erase_eval_iff agree).mp arg) ((ihb ((agree.extend _).extend _)).mp body)
    · intro h; cases h with
      | let₂_arg arg => exact .let₂_arg ((iha agree).mpr arg)
      | let₂_body arg body =>
        exact .let₂_body ((erase_eval_iff agree).mpr arg) ((ihb ((agree.extend _).extend _)).mpr body)
  | inl a ih =>
    constructor
    · intro h; cases h with | inl arg => exact .inl ((ih agree).mp arg)
    · intro h; cases h with | inl arg => exact .inl ((ih agree).mpr arg)
  | inr a ih =>
    constructor
    · intro h; cases h with | inr arg => exact .inr ((ih agree).mp arg)
    · intro h; cases h with | inr arg => exact .inr ((ih agree).mpr arg)
  | case a l r iha ihl ihr =>
    constructor
    · intro h; cases h with
      | case_arg arg => exact .case_arg ((iha agree).mp arg)
      | case_inl arg body =>
        exact .case_inl ((erase_eval_iff agree).mp arg) ((ihl (agree.extend _)).mp body)
      | case_inr arg body =>
        exact .case_inr ((erase_eval_iff agree).mp arg) ((ihr (agree.extend _)).mp body)
    · intro h; cases h with
      | case_arg arg => exact .case_arg ((iha agree).mpr arg)
      | case_inl arg body =>
        exact .case_inl ((erase_eval_iff agree).mpr arg) ((ihl (agree.extend _)).mpr body)
      | case_inr arg body =>
        exact .case_inr ((erase_eval_iff agree).mpr arg) ((ihr (agree.extend _)).mpr body)
  | abort a ih =>
    constructor
    · intro h; cases h with | abort_arg arg => exact .abort_arg ((ih agree).mp arg)
    · intro h; cases h with | abort_arg arg => exact .abort_arg ((ih agree).mpr arg)

theorem ofScoped_fault_iff {t : LambdaSSA.Tm Φ} (scope : t.Scoped n)
    {env : LambdaSSA.Semantics.Env α} {bound : LetIter.Semantics.BoundEnv α n}
    {s s' : σ} (agree : EnvAgrees env bound) :
    LetIter.Semantics.Fault instr faults free bound (CaseIter.embed (ofScoped t scope)) s s' ↔
      LambdaSSA.Semantics.Tm.Fault instr faults env t s s' := by
  rw [← erase_fault_iff agree, erase_ofScoped]

end Silmaril.Isotope.Morphism.CaseSSA
