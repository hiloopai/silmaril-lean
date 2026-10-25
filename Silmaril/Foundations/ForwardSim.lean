module

public import Silmaril.Foundations.InfiniteTrace

/-! # A forward-simulation kit for step relations

A *forward simulation* from a source step relation `SStep` to a target step
relation `TStep`, over a matching relation `R`, is the one-step obligation: from
a related pair, every source step is matched by target steps. Two strengths are
offered.

* `LockstepSim` demands **at least one** target step per source step. This is
  the shape of every Wasm subset theorem (`Lime1 → Core 3.0`, `2.0 → Core 3.0`,
  `Lime1 → 2.0`, and the `2.0 → 3.0` bridge of the commuting triangle), each of
  which is stated as exactly this `∀`.
* `ForwardSim` additionally allows a source step to be matched by **no** target
  step, provided a `Nat` measure on source states strictly decreases, so that
  the target cannot stutter forever. This is what a compiler backend needs
  (a separate imperative-IR simulation development (not included in this package)), and `LockstepSim` is the degenerate
  case `measure := fun _ => 0`.

Derived once, for either strength: finite runs (`steps`), nonempty runs
(`LockstepSim.plus`), and divergence (`diverges`), the last via
`InfiniteTrace.of_sim`, which states the divergence transfer under a still
weaker hypothesis. `LockstepSim.ofFun` and `LockstepSim.ofMap` cover a
matching relation that is the graph of a function, so `LockstepSim.diverges`
subsumes `InfiniteTrace.map`; `LockstepSim.comp` and `ForwardSim.comp` compose
simulations, which is what a delegation wrapper such as
`Wasm 1.0 → Lime1 → Core 3.0` needs.

**Out of scope: result transport.** Concluding something about a *terminal*
configuration is deliberately not part of the kit, because it is not uniform.
`Lime1.Execution.Sim.result` and `Lime1.Execution.ToV2.Sim.result` conclude an
equation on the target code, whereas `V2.Execution.Sim.result` can only conclude
that the target *reaches* such a configuration in finitely many steps (2.0's
relation holds a Core configuration one `Step_read/ref.null` behind per null
reference). A common shape would have to be the weaker one, so each development
states its own.
-/

@[expose] public section

namespace Silmaril

variable {α β γ : Type*}

/-! ## Lock-step simulations -/

/-- A forward simulation in which every source step from a related pair is
matched by **at least one** target step. Nondeterminism is allowed on both
sides: the conclusion is that *some* target run matches. The single field is
literally the statement each Wasm subset theorem already proves, so such a
theorem builds one by `⟨·⟩`. -/
structure LockstepSim (SStep : α → α → Prop) (TStep : β → β → Prop)
    (R : α → β → Prop) : Prop where
  /-- Every source step from a related pair is matched by a nonempty target
  run. -/
  step : ∀ {a b : α} {c : β}, SStep a b → R a c → ∃ c', Relation.TransGen TStep c c' ∧ R b c'

/-! ## Simulations up to a measure -/

/-- A forward simulation that may stutter: a source step from a related pair is
matched by at least one target step, or by no target step and a strictly smaller
`measure`. The measure bounds the number of consecutive source steps the target
can ignore, which is what keeps divergence preserved. -/
structure ForwardSim (SStep : α → α → Prop) (TStep : β → β → Prop) (R : α → β → Prop) where
  /-- A bound on how long the target may stutter; `fun _ => 0` forbids
  stuttering altogether. -/
  measure : α → Nat := fun _ => 0
  /-- The one-step obligation. -/
  step : ∀ {a b : α} {c : β}, SStep a b → R a c →
    ∃ c', (Relation.TransGen TStep c c' ∨ (c' = c ∧ measure b < measure a)) ∧ R b c'

variable {SStep : α → α → Prop} {TStep : β → β → Prop} {UStep : γ → γ → Prop}
  {R : α → β → Prop}

/-- A lock-step simulation is the stuttering-free forward simulation. -/
def LockstepSim.toForwardSim (sim : LockstepSim SStep TStep R) : ForwardSim SStep TStep R where
  step hab hr := by
    obtain ⟨c', h, hr'⟩ := sim.step hab hr
    exact ⟨c', .inl h, hr'⟩

/-- Finite source runs are matched by finite target runs. -/
theorem ForwardSim.steps (sim : ForwardSim SStep TStep R) {a b : α} {c : β}
    (h : Relation.ReflTransGen SStep a b) (hr : R a c) :
    ∃ c', Relation.ReflTransGen TStep c c' ∧ R b c' := by
  induction h with
  | refl => exact ⟨c, .refl, hr⟩
  | tail _ hstep ih =>
    obtain ⟨c₁, h₁, hr₁⟩ := ih
    obtain ⟨c₂, prog, hr₂⟩ := sim.step hstep hr₁
    rcases prog with h₂ | ⟨rfl, -⟩
    · exact ⟨c₂, h₁.trans h₂.to_reflTransGen, hr₂⟩
    · exact ⟨c₂, h₁, hr₂⟩

/-- Divergence transfers under a weaker obligation than `ForwardSim`'s: the
one-step property is needed only for source steps *into* a state that itself
diverges, and the measure is supplied loose rather than packaged. The inner
`progress` is the heart of the argument — strong induction on the measure
absorbs the finitely many source steps the target ignores, leaving at least one
target step — after which `InfiniteTrace.coinduct` iterates it. -/
theorem InfiniteTrace.of_sim (measure : α → Nat)
    (step : ∀ {a b : α} {c : β}, SStep a b → InfiniteTrace SStep b → R a c →
      ∃ c', (Relation.TransGen TStep c c' ∨ (c' = c ∧ measure b < measure a)) ∧ R b c')
    {a : α} {c : β} (h : InfiniteTrace SStep a) (hr : R a c) : InfiniteTrace TStep c := by
  have progress : ∀ n : Nat, ∀ {a : α} {c : β}, measure a = n → InfiniteTrace SStep a → R a c →
      ∃ (b : α) (c' : β), Relation.TransGen TStep c c' ∧ R b c' ∧ InfiniteTrace SStep b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a c hn hd hr
      obtain ⟨a₁, h₁, d₁⟩ := hd.unfold
      obtain ⟨c₁, prog, hr₁⟩ := step h₁ d₁ hr
      rcases prog with h | ⟨rfl, lt⟩
      · exact ⟨a₁, c₁, h, hr₁, d₁⟩
      · exact ih _ (hn ▸ lt) rfl d₁ hr₁
  refine InfiniteTrace.coinduct
    (fun c => ∃ (a : α) (c₀ : β), InfiniteTrace SStep a ∧ R a c₀ ∧
      Relation.ReflTransGen TStep c c₀) ?_ ⟨a, c, h, hr, .refl⟩
  rintro c ⟨a, c₀, hd, hr₀, hp⟩
  rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨c₁, hstep, hp'⟩
  · obtain ⟨b, c', hc', hr', hb⟩ := progress _ rfl hd hr₀
    obtain ⟨c₁, hstep, hp'⟩ := Relation.TransGen.head'_iff.mp hc'
    exact ⟨c₁, hstep, b, c', hb, hr', hp'⟩
  · exact ⟨c₁, hstep, a, c₀, hd, hr₀, hp'⟩

/-- Divergence is preserved: an infinite source trace from a related pair forces
an infinite target trace. -/
theorem ForwardSim.diverges (sim : ForwardSim SStep TStep R) {a : α} {c : β}
    (h : InfiniteTrace SStep a) (hr : R a c) : InfiniteTrace TStep c :=
  InfiniteTrace.of_sim sim.measure (fun hab _ hc => sim.step hab hc) h hr

/-! ## Consequences of a lock-step simulation -/

/-- Finite source runs are matched by finite target runs. -/
theorem LockstepSim.steps (sim : LockstepSim SStep TStep R) {a b : α} {c : β}
    (h : Relation.ReflTransGen SStep a b) (hr : R a c) :
    ∃ c', Relation.ReflTransGen TStep c c' ∧ R b c' :=
  sim.toForwardSim.steps h hr

/-- Nonempty source runs are matched by **nonempty** target runs. This is the
strengthening of `LockstepSim.steps` that stuttering simulations do not admit,
and it is what lets lock-step simulations compose. -/
theorem LockstepSim.plus (sim : LockstepSim SStep TStep R) {a b : α} {c : β}
    (h : Relation.TransGen SStep a b) (hr : R a c) :
    ∃ c', Relation.TransGen TStep c c' ∧ R b c' := by
  induction h with
  | single hs => exact sim.step hs hr
  | tail _ hs ih =>
    obtain ⟨c₁, h₁, hr₁⟩ := ih
    obtain ⟨c₂, h₂, hr₂⟩ := sim.step hs hr₁
    exact ⟨c₂, h₁.trans h₂, hr₂⟩

/-- Divergence is preserved. This is why the one-step obligation produces a
`Relation.TransGen` and not a `Relation.ReflTransGen`: a source step making no
target progress would not give an infinite target trace. -/
theorem LockstepSim.diverges (sim : LockstepSim SStep TStep R) {a : α} {c : β}
    (h : InfiniteTrace SStep a) (hr : R a c) : InfiniteTrace TStep c :=
  sim.toForwardSim.diverges h hr

/-! ## Building and composing simulations -/

/-- The graph of a function is a lock-step simulation as soon as the function
maps each source step to a nonempty target run. `LockstepSim.diverges` at this
instance is `InfiniteTrace.map` (which is the special case of a single step). -/
theorem LockstepSim.ofFun (f : α → β)
    (map : ∀ {a b : α}, SStep a b → Relation.TransGen TStep (f a) (f b)) :
    LockstepSim SStep TStep (fun a c => c = f a) where
  step := by
    rintro a b c hab rfl
    exact ⟨f b, map hab, rfl⟩

/-- Precomposition of a simulation with a lock-step map on source states: the
fused `LockstepSim.ofFun` and `LockstepSim.comp`, in the form a delegation
wrapper such as `Wasm 1.0 → Lime1 → X` wants, since it keeps the matching
relation in the shape `R (f a) c` rather than an existential. -/
theorem LockstepSim.ofMap {R : β → γ → Prop} (f : α → β)
    (map : ∀ {a b : α}, SStep a b → TStep (f a) (f b)) (sim : LockstepSim TStep UStep R) :
    LockstepSim SStep UStep (fun a c => R (f a) c) :=
  ⟨fun hab hr => sim.step (map hab) hr⟩

/-- Lock-step simulations compose, the matching relations composing as
relations. `LockstepSim.plus` is what makes this work: the middle run is
nonempty, so the final run is too. -/
theorem LockstepSim.comp {R₁ : α → β → Prop} {R₂ : β → γ → Prop}
    (s₁ : LockstepSim SStep TStep R₁) (s₂ : LockstepSim TStep UStep R₂) :
    LockstepSim SStep UStep (fun a c => ∃ b, R₁ a b ∧ R₂ b c) where
  step := by
    rintro a b c hab ⟨m, h₁, h₂⟩
    obtain ⟨m', hm', h₁'⟩ := s₁.step hab h₁
    obtain ⟨c', hc', h₂'⟩ := s₂.plus hm' h₂
    exact ⟨c', hc', m', h₁', h₂'⟩

/-- A stuttering simulation composes with a lock-step one, keeping the first
factor's measure: the composite stutters exactly where the first factor does.
The other order has no uniform measure, because the second factor's measure
lives on intermediate states that the composite relation knows only
existentially. -/
def ForwardSim.comp {R₁ : α → β → Prop} {R₂ : β → γ → Prop}
    (s₁ : ForwardSim SStep TStep R₁) (s₂ : LockstepSim TStep UStep R₂) :
    ForwardSim SStep UStep (fun a c => ∃ b, R₁ a b ∧ R₂ b c) where
  measure := s₁.measure
  step := by
    rintro a b c hab ⟨m, h₁, h₂⟩
    obtain ⟨m', prog, h₁'⟩ := s₁.step hab h₁
    rcases prog with h | ⟨rfl, lt⟩
    · obtain ⟨c', hc', h₂'⟩ := s₂.plus h h₂
      exact ⟨c', .inl hc', m', h₁', h₂'⟩
    · exact ⟨c, .inr ⟨rfl, lt⟩, m', h₁', h₂⟩

end Silmaril
