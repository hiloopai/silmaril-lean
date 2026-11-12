module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational

/-! Structural compatibility of let-iter operational semantics. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

/-- Finite looping respects a simulation of each body evaluation. -/
theorem Loop.map_body {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {body : Tm ν Φ (n + 1)} {body' : Tm ν Φ (m + 1)}
    (hbody : ∀ {current result : Value α} {s s' : σ},
      Eval instr free (extend bound current) body s result s' →
      Eval instr free (extend target current) body' s result s')
    {current result : Value α} {s s' : σ}
    (h : Loop instr free bound body current s result s') :
    Loop instr free target body' current s result s' := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ => exact .done (hbody step)
  | step head _ _ ih => exact .step (hbody head) (ih hbody)
  | _ => trivial

/-- Renaming also reflects execution when the environments agree at each image. -/
theorem Eval.of_rename {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (agree : ∀ i, target (ρ i) = bound i)
    (h : Eval instr free target (t.rename ρ) s value s') :
    Eval instr free bound t s value s' := by
  induction t generalizing m s s' value with
  | fv x => cases h; exact .fv
  | bv i => cases h; exact agree i ▸ .bv
  | op f a ih =>
      cases h with | op arg step => exact .op (ih agree arg) step
  | let₁ a b iha ihb =>
      cases h with
      | let₁ arg body => exact .let₁ (iha agree arg) (ihb (extend_rename agree _) body)
  | unit => cases h; exact .unit
  | pair a b iha ihb =>
      cases h with | pair left right => exact .pair (iha agree left) (ihb agree right)
  | let₂ a b iha ihb =>
      cases h with
      | let₂ arg body =>
          exact .let₂ (iha agree arg) (ihb (extend_rename (extend_rename agree _) _) body)
  | inl a ih => cases h with | inl arg => exact .inl (ih agree arg)
  | inr a ih => cases h with | inr arg => exact .inr (ih agree arg)
  | case a l r iha ihl ihr =>
      cases h with
      | case_inl arg branch =>
          exact .case_inl (iha agree arg) (ihl (extend_rename agree _) branch)
      | case_inr arg branch =>
          exact .case_inr (iha agree arg) (ihr (extend_rename agree _) branch)
  | abort a _ => cases h
  | iter init body ihInit ihBody =>
      cases h with
      | iter init loop =>
          exact .iter (ihInit agree init)
            (loop.map_body (fun hbody => ihBody (extend_rename agree _) hbody))

theorem Eval.rename_iff {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {ρ : Fin n → Fin m} {t : Tm ν Φ n} {s s' : σ} {value : Value α}
    (agree : ∀ i, target (ρ i) = bound i) :
    Eval instr free target (t.rename ρ) s value s' ↔
      Eval instr free bound t s value s' :=
  ⟨of_rename agree, fun h => h.rename ρ target agree⟩

end Silmaril.Isotope.LetIter.Semantics
