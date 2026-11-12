module

public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Operational

/-! Abortive primitive faults, independently of successful evaluation and typing.
A fault executes only its successful left-to-right prefix; a missing transition
does not constitute a fault. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetCase.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

inductive Fault (instr : Φ → Value α → σ → Value α → σ → Prop)
    (faults : Φ → Value α → σ → σ → Prop) (free : FreeEnv ν α) :
    {n : Nat} → BoundEnv α n → Tm ν Φ n → σ → σ → Prop where
  | op_arg {n} {bound : BoundEnv α n} {f a s s'}
      (arg : Fault instr faults free bound a s s') : Fault instr faults free bound (.op f a) s s'
  | op_fault {n} {bound : BoundEnv α n} {f a s mid s' value}
      (arg : Eval instr free bound a s value mid) (fault : faults f value mid s') :
      Fault instr faults free bound (.op f a) s s'
  | let₁_arg {n} {bound : BoundEnv α n} {a b s s'}
      (arg : Fault instr faults free bound a s s') : Fault instr faults free bound (.let₁ a b) s s'
  | let₁_body {n} {bound : BoundEnv α n} {a b s mid s' value}
      (arg : Eval instr free bound a s value mid)
      (body : Fault instr faults free (extend bound value) b mid s') :
      Fault instr faults free bound (.let₁ a b) s s'
  | pair_left {n} {bound : BoundEnv α n} {a b s s'}
      (left : Fault instr faults free bound a s s') : Fault instr faults free bound (.pair a b) s s'
  | pair_right {n} {bound : BoundEnv α n} {a b s mid s' value}
      (left : Eval instr free bound a s value mid) (right : Fault instr faults free bound b mid s') :
      Fault instr faults free bound (.pair a b) s s'
  | let₂_arg {n} {bound : BoundEnv α n} {a b s s'}
      (arg : Fault instr faults free bound a s s') : Fault instr faults free bound (.let₂ a b) s s'
  | let₂_body {n} {bound : BoundEnv α n} {a b s mid s' left right}
      (arg : Eval instr free bound a s (.pair left right) mid)
      (body : Fault instr faults free (extend (extend bound left) right) b mid s') :
      Fault instr faults free bound (.let₂ a b) s s'
  | inl {n} {bound : BoundEnv α n} {a s s'} (arg : Fault instr faults free bound a s s') :
      Fault instr faults free bound (.inl a) s s'
  | inr {n} {bound : BoundEnv α n} {a s s'} (arg : Fault instr faults free bound a s s') :
      Fault instr faults free bound (.inr a) s s'
  | case_arg {n} {bound : BoundEnv α n} {e l r s s'}
      (arg : Fault instr faults free bound e s s') : Fault instr faults free bound (.case e l r) s s'
  | case_inl {n} {bound : BoundEnv α n} {e l r s mid s' value}
      (arg : Eval instr free bound e s (.inl value) mid)
      (branch : Fault instr faults free (extend bound value) l mid s') :
      Fault instr faults free bound (.case e l r) s s'
  | case_inr {n} {bound : BoundEnv α n} {e l r s mid s' value}
      (arg : Eval instr free bound e s (.inr value) mid)
      (branch : Fault instr faults free (extend bound value) r mid s') :
      Fault instr faults free bound (.case e l r) s s'
  | abort_arg {n} {bound : BoundEnv α n} {a s s'}
      (arg : Fault instr faults free bound a s s') : Fault instr faults free bound (.abort a) s s'

theorem Fault.false {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ}
    (h : Fault instr (fun _ _ _ _ => False) free bound t s s') : False := by
  induction h <;> assumption

end Silmaril.Isotope.LetCase.Semantics

