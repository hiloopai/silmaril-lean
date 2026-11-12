module

public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Abortive faults in SSA expressions and regions

Faults require an explicit primitive-failure witness after finite successful
prefixes. CFG traversal propagates the fault state through the selected blocks;
no missing transition or invalid label is treated as a fault.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}

inductive Tm.Fault (instr : Φ → Value α → σ → Value α → σ → Prop)
    (faults : Φ → Value α → σ → σ → Prop) :
    Env α → LambdaSSA.Tm Φ → σ → σ → Prop where
  | op_arg {env f a s s'} (arg : Fault instr faults env a s s') :
      Fault instr faults env (.op f a) s s'
  | op_fault {env f a s mid s' value}
      (arg : Tm.Eval instr env a s value mid) (fault : faults f value mid s') :
      Fault instr faults env (.op f a) s s'
  | let₁_arg {env a b s s'} (arg : Fault instr faults env a s s') :
      Fault instr faults env (.let₁ a b) s s'
  | let₁_body {env a b s mid s' value} (arg : Tm.Eval instr env a s value mid)
      (body : Fault instr faults (extend env value) b mid s') :
      Fault instr faults env (.let₁ a b) s s'
  | pair_left {env a b s s'} (left : Fault instr faults env a s s') :
      Fault instr faults env (.pair a b) s s'
  | pair_right {env a b s mid s' value} (left : Tm.Eval instr env a s value mid)
      (right : Fault instr faults env b mid s') : Fault instr faults env (.pair a b) s s'
  | let₂_arg {env a b s s'} (arg : Fault instr faults env a s s') :
      Fault instr faults env (.let₂ a b) s s'
  | let₂_body {env a b s mid s' left right}
      (arg : Tm.Eval instr env a s (.pair left right) mid)
      (body : Fault instr faults (extend (extend env left) right) b mid s') :
      Fault instr faults env (.let₂ a b) s s'
  | inl {env a s s'} (arg : Fault instr faults env a s s') :
      Fault instr faults env (.inl a) s s'
  | inr {env a s s'} (arg : Fault instr faults env a s s') :
      Fault instr faults env (.inr a) s s'
  | case_arg {env e l r s s'} (arg : Fault instr faults env e s s') :
      Fault instr faults env (.case e l r) s s'
  | case_inl {env e l r s mid s' value}
      (arg : Tm.Eval instr env e s (.inl value) mid)
      (branch : Fault instr faults (extend env value) l mid s') :
      Fault instr faults env (.case e l r) s s'
  | case_inr {env e l r s mid s' value}
      (arg : Tm.Eval instr env e s (.inr value) mid)
      (branch : Fault instr faults (extend env value) r mid s') :
      Fault instr faults env (.case e l r) s s'
  | abort_arg {env a s s'} (arg : Fault instr faults env a s s') :
      Fault instr faults env (.abort a) s s'

variable {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults other : Φ → Value α → σ → σ → Prop}

theorem Tm.Fault.false {env : Env α} {a : LambdaSSA.Tm Φ} {s s' : σ}
    (h : Tm.Fault instr (fun _ _ _ _ => False) env a s s') : False := by
  induction h <;> assumption

theorem Tm.Fault.mono (included : ∀ f a s s', faults f a s s' → other f a s s')
    {env : Env α} {a : LambdaSSA.Tm Φ} {s s' : σ}
    (h : Tm.Fault instr faults env a s s') : Tm.Fault instr other env a s s' := by
  induction h with
  | op_arg _ ih => exact .op_arg ih
  | op_fault arg fault => exact .op_fault arg (included _ _ _ _ fault)
  | let₁_arg _ ih => exact .let₁_arg ih
  | let₁_body arg _ ih => exact .let₁_body arg ih
  | pair_left _ ih => exact .pair_left ih
  | pair_right arg _ ih => exact .pair_right arg ih
  | let₂_arg _ ih => exact .let₂_arg ih
  | let₂_body arg _ ih => exact .let₂_body arg ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case_arg _ ih => exact .case_arg ih
  | case_inl arg _ ih => exact .case_inl arg ih
  | case_inr arg _ ih => exact .case_inr arg ih
  | abort_arg _ ih => exact .abort_arg ih

mutual

inductive Region.Fault (instr : Φ → Value α → σ → Value α → σ → Prop)
    (faults : Φ → Value α → σ → σ → Prop) :
    Env α → LambdaSSA.Region Φ → σ → σ → Prop where
  | br {env label a s s'} (arg : Tm.Fault instr faults env a s s') :
      Fault instr faults env (.br label a) s s'
  | let₁_arg {env a r s s'} (arg : Tm.Fault instr faults env a s s') :
      Fault instr faults env (.let₁ a r) s s'
  | let₁_body {env a r s mid s' value} (arg : Tm.Eval instr env a s value mid)
      (body : Fault instr faults (extend env value) r mid s') :
      Fault instr faults env (.let₁ a r) s s'
  | let₂_arg {env a r s s'} (arg : Tm.Fault instr faults env a s s') :
      Fault instr faults env (.let₂ a r) s s'
  | let₂_body {env a r s mid s' left right} (arg : Tm.Eval instr env a s (.pair left right) mid)
      (body : Fault instr faults (extend (extend env left) right) r mid s') :
      Fault instr faults env (.let₂ a r) s s'
  | case_arg {env a l r s s'} (arg : Tm.Fault instr faults env a s s') :
      Fault instr faults env (.case a l r) s s'
  | case_inl {env a l r s mid s' value} (arg : Tm.Eval instr env a s (.inl value) mid)
      (branch : Fault instr faults (extend env value) l mid s') :
      Fault instr faults env (.case a l r) s s'
  | case_inr {env a l r s mid s' value} (arg : Tm.Eval instr env a s (.inr value) mid)
      (branch : Fault instr faults (extend env value) r mid s') :
      Fault instr faults env (.case a l r) s s'
  | cfg_entry {env entry n} {blocks : Fin n → LambdaSSA.Region Φ} {s s'}
      (fault : Fault instr faults env entry s s') :
      Fault instr faults env (.cfg entry n blocks) s s'
  | cfg_follow {env entry n} {blocks : Fin n → LambdaSSA.Region Φ} {s mid s' label value}
      (run : Region.Eval instr env entry s label value mid)
      (fault : Region.FollowFault instr faults env blocks label value mid s') :
      Fault instr faults env (.cfg entry n blocks) s s'

inductive Region.FollowFault (instr : Φ → Value α → σ → Value α → σ → Prop)
    (faults : Φ → Value α → σ → σ → Prop) :
    Env α → {n : Nat} → (Fin n → LambdaSSA.Region Φ) → Nat → Value α → σ → σ → Prop where
  | body {env n label} {blocks : Fin n → LambdaSSA.Region Φ} {arg s s'} (inside : label < n)
      (fault : Region.Fault instr faults (extend env arg) (blocks ⟨label, inside⟩) s s') :
      FollowFault instr faults env blocks label arg s s'
  | step {env n label next} {blocks : Fin n → LambdaSSA.Region Φ} {arg value s mid s'}
      (inside : label < n)
      (run : Region.Eval instr (extend env arg) (blocks ⟨label, inside⟩) s next value mid)
      (tail : FollowFault instr faults env blocks next value mid s') :
      FollowFault instr faults env blocks label arg s s'

end

theorem Region.Fault.false {env : Env α} {r : LambdaSSA.Region Φ} {s s' : σ}
    (h : Region.Fault instr (fun _ _ _ _ => False) env r s s') : False := by
  induction h using Region.Fault.rec (motive_2 := fun _ _ _ _ _ _ _ _ => False) with
  | br arg | let₁_arg arg | let₂_arg arg | case_arg arg => exact arg.false
  | _ => assumption

theorem Region.Fault.mono (included : ∀ f a s s', faults f a s s' → other f a s s')
    {env : Env α} {r : LambdaSSA.Region Φ} {s s' : σ}
    (h : Region.Fault instr faults env r s s') : Region.Fault instr other env r s s' := by
  induction h using Region.Fault.rec
      (motive_2 := fun env _ blocks label arg s s' _ =>
        Region.FollowFault instr other env blocks label arg s s') with
  | br arg => exact .br (arg.mono included)
  | let₁_arg arg => exact .let₁_arg (arg.mono included)
  | let₁_body arg _ ih => exact .let₁_body arg ih
  | let₂_arg arg => exact .let₂_arg (arg.mono included)
  | let₂_body arg _ ih => exact .let₂_body arg ih
  | case_arg arg => exact .case_arg (arg.mono included)
  | case_inl arg _ ih => exact .case_inl arg ih
  | case_inr arg _ ih => exact .case_inr arg ih
  | cfg_entry _ ih => exact .cfg_entry ih
  | cfg_follow run _ ih => exact .cfg_follow run ih
  | body inside _ ih => exact .body inside ih
  | step inside run _ ih => exact .step inside run ih

end Silmaril.Isotope.LambdaSSA.Semantics
