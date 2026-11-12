module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Semantics.Divergence

/-! # SSA divergence with infinite primitive computations

Expressions have finite syntax: their divergence reaches an explicitly divergent
primitive after finite successful prefixes. Regions additionally admit infinite
CFG traversal, using the existing divergence rules as an open core. Neither a
missing instruction transition nor an invalid label establishes divergence.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}

inductive Tm.ExternalDiverges (instr : Φ → Value α → σ → Value α → σ → Prop)
    (prim : Φ → Value α → σ → Prop) : Env α → LambdaSSA.Tm Φ → σ → Prop where
  | op_arg {env f a s} (arg : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.op f a) s
  | primitive {env f a s mid value} (arg : Tm.Eval instr env a s value mid)
      (div : prim f value mid) : ExternalDiverges instr prim env (.op f a) s
  | let₁_arg {env a b s} (arg : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.let₁ a b) s
  | let₁_body {env a b s mid value} (arg : Tm.Eval instr env a s value mid)
      (body : ExternalDiverges instr prim (extend env value) b mid) :
      ExternalDiverges instr prim env (.let₁ a b) s
  | pair_left {env a b s} (left : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.pair a b) s
  | pair_right {env a b s mid value} (left : Tm.Eval instr env a s value mid)
      (right : ExternalDiverges instr prim env b mid) : ExternalDiverges instr prim env (.pair a b) s
  | let₂_arg {env a b s} (arg : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.let₂ a b) s
  | let₂_body {env a b s mid left right} (arg : Tm.Eval instr env a s (.pair left right) mid)
      (body : ExternalDiverges instr prim (extend (extend env left) right) b mid) :
      ExternalDiverges instr prim env (.let₂ a b) s
  | inl {env a s} (arg : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.inl a) s
  | inr {env a s} (arg : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.inr a) s
  | case_arg {env e l r s} (arg : ExternalDiverges instr prim env e s) :
      ExternalDiverges instr prim env (.case e l r) s
  | case_inl {env e l r s mid value} (arg : Tm.Eval instr env e s (.inl value) mid)
      (branch : ExternalDiverges instr prim (extend env value) l mid) :
      ExternalDiverges instr prim env (.case e l r) s
  | case_inr {env e l r s mid value} (arg : Tm.Eval instr env e s (.inr value) mid)
      (branch : ExternalDiverges instr prim (extend env value) r mid) :
      ExternalDiverges instr prim env (.case e l r) s
  | abort_arg {env a s} (arg : ExternalDiverges instr prim env a s) :
      ExternalDiverges instr prim env (.abort a) s

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {prim other : Φ → Value α → σ → Prop}

theorem Tm.ExternalDiverges.false {env : Env α} {a : LambdaSSA.Tm Φ} {s : σ}
    (h : Tm.ExternalDiverges instr (fun _ _ _ => False) env a s) : False := by
  induction h <;> assumption

theorem Tm.ExternalDiverges.mono (included : ∀ f a s, prim f a s → other f a s)
    {env : Env α} {a : LambdaSSA.Tm Φ} {s : σ} (h : Tm.ExternalDiverges instr prim env a s) :
    Tm.ExternalDiverges instr other env a s := by
  induction h with
  | op_arg _ ih => exact .op_arg ih
  | primitive arg div => exact .primitive arg (included _ _ _ div)
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

namespace External

inductive DivergenceStep (instr : Φ → Value α → σ → Value α → σ → Prop)
    (prim : Φ → Value α → σ → Prop) (continues : Config α Φ σ → Prop) : Config α Φ σ → Prop where
  | core {c} (h : Semantics.DivergenceStep instr continues c) : DivergenceStep instr prim continues c
  | br {env label arg s} (h : Tm.ExternalDiverges instr prim env arg s) :
      DivergenceStep instr prim continues (.region env (.br label arg) s)
  | let₁_arg {env arg body s} (h : Tm.ExternalDiverges instr prim env arg s) :
      DivergenceStep instr prim continues (.region env (.let₁ arg body) s)
  | let₂_arg {env arg body s} (h : Tm.ExternalDiverges instr prim env arg s) :
      DivergenceStep instr prim continues (.region env (.let₂ arg body) s)
  | case_arg {env arg left right s} (h : Tm.ExternalDiverges instr prim env arg s) :
      DivergenceStep instr prim continues (.region env (.case arg left right) s)

theorem DivergenceStep.mono {R S : Config α Φ σ → Prop} {c : Config α Φ σ}
    (h : DivergenceStep instr prim R c) (included : ∀ c, R c → S c) :
    DivergenceStep instr prim S c := by
  cases h with
  | core h => exact .core (h.mono included)
  | br h => exact .br h
  | let₁_arg h => exact .let₁_arg h
  | let₂_arg h => exact .let₂_arg h
  | case_arg h => exact .case_arg h

def Diverges (instr : Φ → Value α → σ → Value α → σ → Prop)
    (prim : Φ → Value α → σ → Prop) (c : Config α Φ σ) : Prop :=
  ∃ R : Config α Φ σ → Prop, R c ∧ ∀ c, R c → DivergenceStep instr prim R c

namespace Diverges

theorem coinduct (R : Config α Φ σ → Prop)
    (closed : ∀ c, R c → DivergenceStep instr prim R c) {c : Config α Φ σ}
    (hc : R c) : Diverges instr prim c := ⟨R, hc, closed⟩

theorem unfold {c : Config α Φ σ} (h : Diverges instr prim c) :
    DivergenceStep instr prim (Diverges instr prim) c := by
  obtain ⟨R, hc, closed⟩ := h
  exact (closed c hc).mono (fun _ hr => ⟨R, hr, closed⟩)

theorem fold {c : Config α Φ σ} (h : DivergenceStep instr prim (Diverges instr prim) c) :
    Diverges instr prim c := by
  refine ⟨fun c' => c' = c ∨ Diverges instr prim c', Or.inl rfl, ?_⟩
  intro c' hc'
  rcases hc' with rfl | hd
  · exact h.mono (fun _ hd => Or.inr hd)
  · exact hd.unfold.mono (fun _ hd => Or.inr hd)

theorem fold_core {c : Config α Φ σ}
    (h : Semantics.DivergenceStep instr (Diverges instr prim) c) :
    Diverges instr prim c := fold (.core h)

theorem of_internal {c : Config α Φ σ} (h : Semantics.Diverges instr c) :
    Diverges instr prim c := by
  obtain ⟨R, hc, closed⟩ := h
  exact ⟨R, hc, fun c h => .core (closed c h)⟩

/-- Removing externally divergent primitives recovers exactly internal CFG divergence. -/
theorem false_iff {c : Config α Φ σ} :
    Diverges instr (fun _ _ _ => False) c ↔ Semantics.Diverges instr c := by
  constructor
  · rintro ⟨R, hc, closed⟩
    refine ⟨R, hc, ?_⟩
    intro c h
    cases closed c h with
    | core h => exact h
    | br div | let₁_arg div | let₂_arg div | case_arg div => exact div.false.elim
  · exact of_internal

theorem mono (included : ∀ f a s, prim f a s → other f a s) {c : Config α Φ σ}
    (h : Diverges instr prim c) : Diverges instr other c := by
  obtain ⟨R, hc, closed⟩ := h
  refine ⟨R, hc, ?_⟩
  intro c h
  cases closed c h with
  | core h => exact .core h
  | br div => exact .br (div.mono included)
  | let₁_arg div => exact .let₁_arg (div.mono included)
  | let₂_arg div => exact .let₂_arg (div.mono included)
  | case_arg div => exact .case_arg (div.mono included)

end Diverges

end External

end Silmaril.Isotope.LambdaSSA.Semantics
