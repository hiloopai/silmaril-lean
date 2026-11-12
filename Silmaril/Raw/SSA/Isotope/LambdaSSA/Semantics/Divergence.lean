module

public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Divergence of SSA regions

Infinite execution follows CFG transfers or a divergent nested region. Finite
expression prefixes retain their instruction effects. Stuck expressions and
invalid eliminations do not create divergence.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics

variable {α : Type u} {Φ : Type v} {σ : Type w}

inductive Config (α : Type u) (Φ : Type v) (σ : Type w) where
  | region (env : Env α) (r : LambdaSSA.Region Φ) (state : σ)
  | follow (env : Env α) {n : Nat} (blocks : Fin n → LambdaSSA.Region Φ)
      (label : Nat) (arg : Value α) (state : σ)

inductive DivergenceStep (instr : Φ → Value α → σ → Value α → σ → Prop)
    (continues : Config α Φ σ → Prop) : Config α Φ σ → Prop where
  | let₁ {env : Env α} {a : LambdaSSA.Tm Φ} {r : LambdaSSA.Region Φ}
      {s s' : σ} {value : Value α} :
      Tm.Eval instr env a s value s' → continues (.region (extend env value) r s') →
      DivergenceStep instr continues (.region env (.let₁ a r) s)
  | let₂ {env : Env α} {a : LambdaSSA.Tm Φ} {r : LambdaSSA.Region Φ}
      {s s' : σ} {va vb : Value α} :
      Tm.Eval instr env a s (.pair va vb) s' →
      continues (.region (extend (extend env va) vb) r s') →
      DivergenceStep instr continues (.region env (.let₂ a r) s)
  | case_inl {env : Env α} {a : LambdaSSA.Tm Φ} {l r : LambdaSSA.Region Φ}
      {s s' : σ} {value : Value α} :
      Tm.Eval instr env a s (.inl value) s' → continues (.region (extend env value) l s') →
      DivergenceStep instr continues (.region env (.case a l r) s)
  | case_inr {env : Env α} {a : LambdaSSA.Tm Φ} {l r : LambdaSSA.Region Φ}
      {s s' : σ} {value : Value α} :
      Tm.Eval instr env a s (.inr value) s' → continues (.region (extend env value) r s') →
      DivergenceStep instr continues (.region env (.case a l r) s)
  | cfg_entry {env : Env α} {entry : LambdaSSA.Region Φ} {n : Nat}
      {blocks : Fin n → LambdaSSA.Region Φ} {s : σ} :
      continues (.region env entry s) →
      DivergenceStep instr continues (.region env (.cfg entry n blocks) s)
  | cfg_follow {env : Env α} {entry : LambdaSSA.Region Φ} {n : Nat}
      {blocks : Fin n → LambdaSSA.Region Φ} {s s' : σ} {label : Nat} {value : Value α} :
      Region.Eval instr env entry s label value s' →
      continues (.follow env blocks label value s') →
      DivergenceStep instr continues (.region env (.cfg entry n blocks) s)
  | follow_body {env : Env α} {n label : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
      {s : σ} {arg : Value α} (inside : label < n) :
      continues (.region (extend env arg) (blocks ⟨label, inside⟩) s) →
      DivergenceStep instr continues (.follow env blocks label arg s)
  | follow_next {env : Env α} {n label next : Nat} {blocks : Fin n → LambdaSSA.Region Φ}
      {s s' : σ} {arg value : Value α} (inside : label < n) :
      Region.Eval instr (extend env arg) (blocks ⟨label, inside⟩) s next value s' →
      continues (.follow env blocks next value s') →
      DivergenceStep instr continues (.follow env blocks label arg s)

variable {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem DivergenceStep.mono {R S : Config α Φ σ → Prop} {c : Config α Φ σ}
    (h : DivergenceStep instr R c) (hRS : ∀ c, R c → S c) : DivergenceStep instr S c := by
  cases h with
  | let₁ arg rest => exact .let₁ arg (hRS _ rest)
  | let₂ arg rest => exact .let₂ arg (hRS _ rest)
  | case_inl arg rest => exact .case_inl arg (hRS _ rest)
  | case_inr arg rest => exact .case_inr arg (hRS _ rest)
  | cfg_entry rest => exact .cfg_entry (hRS _ rest)
  | cfg_follow entry rest => exact .cfg_follow entry (hRS _ rest)
  | follow_body inside rest => exact .follow_body inside (hRS _ rest)
  | follow_next inside head rest => exact .follow_next inside head (hRS _ rest)

/-- Greatest-fixed-point divergence, witnessed by a relation closed under unfolding. -/
def Diverges (instr : Φ → Value α → σ → Value α → σ → Prop) (c : Config α Φ σ) : Prop :=
  ∃ R : Config α Φ σ → Prop, R c ∧ ∀ c, R c → DivergenceStep instr R c

namespace Diverges

theorem coinduct (R : Config α Φ σ → Prop)
    (closed : ∀ c, R c → DivergenceStep instr R c) {c : Config α Φ σ}
    (hc : R c) : Diverges instr c := ⟨R, hc, closed⟩

theorem unfold {c : Config α Φ σ} (h : Diverges instr c) :
    DivergenceStep instr (Diverges instr) c := by
  obtain ⟨R, hc, closed⟩ := h
  exact (closed c hc).mono (fun _ hr => ⟨R, hr, closed⟩)

theorem fold {c : Config α Φ σ} (h : DivergenceStep instr (Diverges instr) c) :
    Diverges instr c := by
  refine ⟨fun c' => c' = c ∨ Diverges instr c', Or.inl rfl, ?_⟩
  intro c' hc'
  rcases hc' with rfl | hd
  · exact h.mono (fun _ hd => Or.inr hd)
  · exact hd.unfold.mono (fun _ hd => Or.inr hd)

theorem iff_step {c : Config α Φ σ} :
    Diverges instr c ↔ DivergenceStep instr (Diverges instr) c := ⟨unfold, fold⟩

end Diverges

theorem Region.Eval.not_diverges (hd : InstrDeterministic instr)
    {env : Env α} {r : LambdaSSA.Region Φ} {s s' : σ} {label : Nat} {value : Value α}
    (h : Region.Eval instr env r s label value s') :
    ¬ Diverges instr (.region env r s) := by
  induction h using Region.Eval.rec
      (motive_2 := fun env _ blocks first initial s _ _ _ _ =>
        ¬ Diverges instr (.follow env blocks first initial s)) with
  | br _ => intro hdiv; cases hdiv.unfold
  | let₁ arg _ ih =>
      intro hdiv
      cases hdiv.unfold with
      | let₁ arg' rest =>
          obtain ⟨rfl, rfl⟩ := arg.deterministic hd arg'
          exact ih rest
  | let₂ arg _ ih =>
      intro hdiv
      cases hdiv.unfold with
      | let₂ arg' rest =>
          obtain ⟨hv, rfl⟩ := arg.deterministic hd arg'
          obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
          exact ih rest
  | case_inl arg _ ih =>
      intro hdiv
      cases hdiv.unfold with
      | case_inl arg' rest =>
          obtain ⟨hv, rfl⟩ := arg.deterministic hd arg'
          cases Value.inl.inj hv
          exact ih rest
      | case_inr arg' _ => obtain ⟨hv, _⟩ := arg.deterministic hd arg'; cases hv
  | case_inr arg _ ih =>
      intro hdiv
      cases hdiv.unfold with
      | case_inr arg' rest =>
          obtain ⟨hv, rfl⟩ := arg.deterministic hd arg'
          cases Value.inr.inj hv
          exact ih rest
      | case_inl arg' _ => obtain ⟨hv, _⟩ := arg.deterministic hd arg'; cases hv
  | cfg entry _ ihEntry ihFollow =>
      intro hdiv
      cases hdiv.unfold with
      | cfg_entry rest => exact ihEntry rest
      | cfg_follow entry' rest =>
          obtain ⟨rfl, rfl, rfl⟩ := entry.deterministic hd entry'
          exact ihFollow rest
  | exit outside =>
      intro hdiv
      cases hdiv.unfold with
      | follow_body inside _ | follow_next inside _ _ =>
          exact Nat.not_lt_of_ge outside inside
  | step inside head _ ihHead ihTail =>
      intro hdiv
      cases hdiv.unfold with
      | follow_body _ rest => exact ihHead rest
      | follow_next _ head' rest =>
          obtain ⟨rfl, rfl, rfl⟩ := head.deterministic hd head'
          exact ihTail rest

/-- An unconditional backedge has an infinite execution for every initial value. -/
theorem follow_self_loop (env : Env α) (arg : Value α) (s : σ) :
    Diverges instr (.follow env (fun _ : Fin 1 => .br 0 (.var 0)) 0 arg s) := by
  refine Diverges.coinduct
    (fun c => c = .follow env (fun _ : Fin 1 => .br 0 (.var 0)) 0 arg s) ?_ rfl
  intro c hc
  subst c
  exact .follow_next (by decide) (.br .var) rfl

/-- A CFG can initialize once and then take its backedge forever. -/
theorem cfg_self_loop (env : Env α) (s : σ) :
    Diverges instr (.region env (.cfg (.br 0 .unit) 1 (fun _ => .br 0 (.var 0))) s) :=
  .fold (.cfg_follow (.br .unit) (follow_self_loop env .unit s))

/-- A malformed elimination is stuck, without being an infinite computation. -/
theorem abort_unit_stuck (env : Env α) (s : σ) :
    (¬ ∃ label value s', Region.Eval instr env (.br 0 (.abort .unit)) s label value s') ∧
      ¬ Diverges instr (.region env (.br 0 (.abort .unit)) s) := by
  constructor
  · rintro ⟨_, _, _, h⟩
    cases h with
    | br harg => cases harg
  · intro hdiv
    cases hdiv.unfold

end Silmaril.Isotope.LambdaSSA.Semantics
