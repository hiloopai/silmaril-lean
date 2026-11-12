module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Structural

/-! Renaming preserves and reflects explicit faults, including their final state. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop} {free : FreeEnv ν α}

/-- A faulting loop respects simulations of both successful and faulting bodies. -/
theorem LoopFault.map_body {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {body : Tm ν Φ (n + 1)} {body' : Tm ν Φ (m + 1)}
    (eval : ∀ {current result : Value α} {s s' : σ},
      Eval instr free (extend bound current) body s result s' →
      Eval instr free (extend target current) body' s result s')
    (fault : ∀ {current : Value α} {s s' : σ},
      Fault instr faults free (extend bound current) body s s' →
      Fault instr faults free (extend target current) body' s s')
    {current : Value α} {s s' : σ} (h : LoopFault instr faults free bound body current s s') :
    LoopFault instr faults free target body' current s s' := by
  exact LoopFault.induction_fixed (fun h => .body (fault h))
    (fun h _ ih => .step (eval h) ih) h

theorem Fault.rename {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n}
    {s s' : σ} (h : Fault instr faults free bound t s s') :
    ∀ {m : Nat} (ρ : Fin n → Fin m) (target : BoundEnv α m),
      (∀ i, target (ρ i) = bound i) → Fault instr faults free target (t.rename ρ) s s' := by
  induction h using Fault.rec
      (motive_2 := fun {n} bound body current s s' _ =>
        ∀ {m : Nat} (ρ : Fin n → Fin m) (target : BoundEnv α m),
          (∀ i, target (ρ i) = bound i) →
          LoopFault instr faults free target (body.rename (Tm.up ρ)) current s s') with
  | op_arg _ ih => intro _ ρ target agree; exact .op_arg (ih ρ target agree)
  | op_fault arg fault => intro _ ρ target agree; exact .op_fault (arg.rename ρ target agree) fault
  | let₁_arg _ ih => intro _ ρ target agree; exact .let₁_arg (ih ρ target agree)
  | let₁_body arg _ ih =>
    intro _ ρ target agree
    exact .let₁_body (arg.rename ρ target agree) (ih (Tm.up ρ) _ (extend_rename agree _))
  | pair_left _ ih => intro _ ρ target agree; exact .pair_left (ih ρ target agree)
  | pair_right arg _ ih =>
    intro _ ρ target agree
    exact .pair_right (arg.rename ρ target agree) (ih ρ target agree)
  | let₂_arg _ ih => intro _ ρ target agree; exact .let₂_arg (ih ρ target agree)
  | let₂_body arg _ ih =>
    intro _ ρ target agree
    exact .let₂_body (arg.rename ρ target agree)
      (ih (Tm.up (Tm.up ρ)) _ (extend_rename (extend_rename agree _) _))
  | inl _ ih => intro _ ρ target agree; exact .inl (ih ρ target agree)
  | inr _ ih => intro _ ρ target agree; exact .inr (ih ρ target agree)
  | case_arg _ ih => intro _ ρ target agree; exact .case_arg (ih ρ target agree)
  | case_inl arg _ ih =>
    intro _ ρ target agree
    exact .case_inl (arg.rename ρ target agree) (ih (Tm.up ρ) _ (extend_rename agree _))
  | case_inr arg _ ih =>
    intro _ ρ target agree
    exact .case_inr (arg.rename ρ target agree) (ih (Tm.up ρ) _ (extend_rename agree _))
  | abort_arg _ ih => intro _ ρ target agree; exact .abort_arg (ih ρ target agree)
  | iter_init _ ih => intro _ ρ target agree; exact .iter_init (ih ρ target agree)
  | iter_loop arg _ ih =>
    intro _ ρ target agree
    exact .iter_loop (arg.rename ρ target agree) (ih ρ target agree)
  | body _ ih =>
    rename_i m ρ target agree
    exact .body (ih (Tm.up ρ) _ (extend_rename agree _))
  | step head _ ih =>
    rename_i m ρ target agree
    exact .step (head.rename (Tm.up ρ) _ (extend_rename agree _)) (ih ρ target agree)

theorem Fault.of_rename {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s s' : σ}
    (agree : ∀ i, target (ρ i) = bound i)
    (h : Fault instr faults free target (t.rename ρ) s s') :
    Fault instr faults free bound t s s' := by
  induction t generalizing m s s' with
  | fv _ => cases h
  | bv _ => cases h
  | unit => cases h
  | op f a ih =>
    cases h with
    | op_arg arg => exact .op_arg (ih agree arg)
    | op_fault arg fault => exact .op_fault (arg.of_rename agree) fault
  | let₁ a b iha ihb =>
    cases h with
    | let₁_arg arg => exact .let₁_arg (iha agree arg)
    | let₁_body arg body => exact .let₁_body (arg.of_rename agree) (ihb (extend_rename agree _) body)
  | pair a b iha ihb =>
    cases h with
    | pair_left arg => exact .pair_left (iha agree arg)
    | pair_right arg body => exact .pair_right (arg.of_rename agree) (ihb agree body)
  | let₂ a b iha ihb =>
    cases h with
    | let₂_arg arg => exact .let₂_arg (iha agree arg)
    | let₂_body arg body =>
      exact .let₂_body (arg.of_rename agree) (ihb (extend_rename (extend_rename agree _) _) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih agree arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih agree arg)
  | case a l r iha ihl ihr =>
    cases h with
    | case_arg arg => exact .case_arg (iha agree arg)
    | case_inl arg body => exact .case_inl (arg.of_rename agree) (ihl (extend_rename agree _) body)
    | case_inr arg body => exact .case_inr (arg.of_rename agree) (ihr (extend_rename agree _) body)
  | abort a ih => cases h with | abort_arg arg => exact .abort_arg (ih agree arg)
  | iter init body ihInit ihBody =>
    cases h with
    | iter_init arg => exact .iter_init (ihInit agree arg)
    | iter_loop arg loop =>
      exact .iter_loop (arg.of_rename agree)
        (loop.map_body (fun h => h.of_rename (extend_rename agree _))
          (fun h => ihBody (extend_rename agree _) h))

theorem Fault.rename_iff {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s s' : σ}
    (agree : ∀ i, target (ρ i) = bound i) :
    Fault instr faults free target (t.rename ρ) s s' ↔ Fault instr faults free bound t s s' :=
  ⟨of_rename agree, fun h => h.rename ρ target agree⟩

end Silmaril.Isotope.LetIter.Semantics
