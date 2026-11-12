module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational

/-! # Abortive primitive faults

Successful prefixes use the ordinary `Eval` relation. A separate primitive
fault relation describes failures such as a Wasm trap; a missing successful
transition alone is not a fault. Faults propagate out of the term and iteration
without executing the remaining subterms. They are not sum values or exceptions
handled by the source case construct.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

mutual

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
  | iter_init {n} {bound : BoundEnv α n} {a b s s'}
      (arg : Fault instr faults free bound a s s') : Fault instr faults free bound (.iter a b) s s'
  | iter_loop {n} {bound : BoundEnv α n} {a b s mid s' value}
      (arg : Eval instr free bound a s value mid) (loop : LoopFault instr faults free bound b value mid s') :
      Fault instr faults free bound (.iter a b) s s'

inductive LoopFault (instr : Φ → Value α → σ → Value α → σ → Prop)
    (faults : Φ → Value α → σ → σ → Prop) (free : FreeEnv ν α) :
    {n : Nat} → BoundEnv α n → Tm ν Φ (n + 1) → Value α → σ → σ → Prop where
  | body {n} {bound : BoundEnv α n} {b current s s'}
      (fault : Fault instr faults free (extend bound current) b s s') :
      LoopFault instr faults free bound b current s s'
  | step {n} {bound : BoundEnv α n} {b current next s mid s'}
      (head : Eval instr free (extend bound current) b s (.inr next) mid)
      (tail : LoopFault instr faults free bound b next mid s') :
      LoopFault instr faults free bound b current s s'

end

theorem Fault.false {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ}
    (h : Fault instr (fun _ _ _ _ => False) free bound t s s') : False := by
  induction h using Fault.rec (motive_2 := fun _ _ _ _ _ _ => False) <;> assumption

theorem Fault.mono {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {faults other : Φ → Value α → σ → σ → Prop}
    (included : ∀ f a s s', faults f a s s' → other f a s s')
    {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s s' : σ}
    (h : Fault instr faults free bound t s s') : Fault instr other free bound t s s' := by
  induction h using Fault.rec
      (motive_2 := fun bound body current s s' _ => LoopFault instr other free bound body current s s') with
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
  | iter_init _ ih => exact .iter_init ih
  | iter_loop arg _ ih => exact .iter_loop arg ih
  | body _ ih => exact .body ih
  | step head _ ih => exact .step head ih

/-- Induction along the finite successful prefix before the fault, keeping the
loop body and environment fixed. -/
theorem LoopFault.induction_fixed {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : FreeEnv ν α}
    {n : Nat} {bound : BoundEnv α n} {b : Tm ν Φ (n + 1)}
    {motive : Value α → σ → σ → Prop}
    (body : ∀ {current s s'}, Fault instr faults free (extend bound current) b s s' → motive current s s')
    (step : ∀ {current next s mid s'}, Eval instr free (extend bound current) b s (.inr next) mid →
      LoopFault instr faults free bound b next mid s' → motive next mid s' → motive current s s')
    {current : Value α} {s s' : σ} (h : LoopFault instr faults free bound b current s s') :
    motive current s s' := by
  induction h using LoopFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | body h _ => exact body h
  | step h tail ih => exact step h tail (ih body step)
  | _ => trivial

end Silmaril.Isotope.LetIter.Semantics
