module

public import Silmaril.Wasm.Game.Strategy.Defs
public import Silmaril.Games.LTS.Thms
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# The strategy of a scalar instance: proofs

* Determinism of the hidden-state transition system: the next state is a
  function of the state and the move (`Trans.functional`), and Proponent's
  move is unique (`Trans.player_unique`), from uniqueness of normal forms of
  host-free runs (`reach_normal_unique`).
* Legality: hidden states project to game positions (`HState.pos`) and every
  transition is a step of the game automaton.
* The traces of `I.lts P s` are the plays `I.plays P s`; they are legal,
  prefix closed and receptive, so `I.lts P s` denotes `I.strategy P s`.
* Persistence: after a complete activation ending in `s'` the plays continue
  as the plays from `s'`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : ScalarInstance}

open Silmaril.Wasm.Game.ScalarInstance

/-! ### Determinism of the transition system -/

/-- Proponent moves are made exactly from `running` states. -/
theorem Trans.isP_iff {P : Profile} {q q' : I.HState} {m : Move I.E I.F}
    (h : I.Trans P q m q') : m.IsP ↔ ∃ f s t, q = .running f s t := by
  cases h <;> simp [Move.IsP]

/-- The next state is a function of the state and the move. -/
theorem Trans.functional {o : GrowOracle} {q q₁ q₂ : I.HState} {m : Move I.E I.F}
    (h₁ : I.Trans (profile o) q m q₁) (h₂ : I.Trans (profile o) q m q₂) : q₁ = q₂ := by
  cases h₁ with
  | call => cases h₂; rfl
  | ucall run callout op =>
    cases h₂ with
    | ucall run' callout' op' =>
      have := reach_normal_unique run run' (calloutAt_no_internal callout)
        (calloutAt_no_internal callout')
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl
  | uret v => cases h₂; rfl
  | oret run final answer =>
    cases h₂ with
    | oret run' final' answer' =>
      have := reach_normal_unique run run' (resultAt_no_internal final)
        (resultAt_no_internal final')
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl

/-- Two host-free runs from the same thread to normal forms stop at the same store and
thread. -/
private theorem reach_normal_eq {o : GrowOracle} {s s₁ s₂ : Store Nat} {t t₁ t₂ : Thread}
    (run : Reach (profile o) (s, t) (s₁, t₁)) (run' : Reach (profile o) (s, t) (s₂, t₂))
    (h₁ : ∀ y, ¬ InternalP (profile o) (s₁, t₁) y)
    (h₂ : ∀ y, ¬ InternalP (profile o) (s₂, t₂) y) :
    s₁ = s₂ ∧ t₁ = t₂ :=
  Prod.mk.inj (reach_normal_unique run run' h₁ h₂)

/-- Proponent's move is unique. -/
theorem Trans.player_unique {o : GrowOracle} {q q₁ q₂ : I.HState} {m m' : Move I.E I.F}
    (h₁ : I.Trans (profile o) q m q₁) (h₂ : I.Trans (profile o) q m' q₂) (hm : m.IsP) :
    m = m' := by
  cases h₁ with
  | call => exact absurd hm (by simp [Move.IsP])
  | uret v => exact absurd hm (by simp [Move.IsP])
  | @ucall f s s₁ t t₁ h args e run callout op =>
    show (.inl (.ask e) : Move I.E I.F) = m'
    cases h₂ with
    | @ucall _ _ s₂ _ t₂ h' args' e' run' callout' op' =>
      obtain ⟨rfl, rfl⟩ : s₁ = s₂ ∧ t₁ = t₂ := reach_normal_eq run run'
        (calloutAt_no_internal callout) (calloutAt_no_internal callout')
      obtain ⟨rfl, rfl⟩ : h = h' ∧ args = args' := calloutAt_unique callout callout'
      obtain rfl : e = e' := Option.some.inj (op.symm.trans op')
      rfl
    | @oret _ _ s₂ _ t₂ r' v' run' final' answer' =>
      obtain ⟨rfl, rfl⟩ : s₁ = s₂ ∧ t₁ = t₂ := reach_normal_eq run run'
        (calloutAt_no_internal callout) (resultAt_no_internal final')
      exact absurd callout (resultAt_not_calloutAt final')
  | @oret f s s₁ t t₁ r v run final answer =>
    show (.inr (.ans f v) : Move I.E I.F) = m'
    cases h₂ with
    | @ucall _ _ s₂ _ t₂ h' args' e' run' callout' op' =>
      obtain ⟨rfl, rfl⟩ : s₁ = s₂ ∧ t₁ = t₂ := reach_normal_eq run run'
        (resultAt_no_internal final) (calloutAt_no_internal callout')
      exact absurd callout' (resultAt_not_calloutAt final)
    | @oret _ _ s₂ _ t₂ r' v' run' final' answer' =>
      obtain ⟨rfl, rfl⟩ : s₁ = s₂ ∧ t₁ = t₂ := reach_normal_eq run run'
        (resultAt_no_internal final) (resultAt_no_internal final')
      obtain rfl : r = r' := resultAt_unique final final'
      obtain rfl : v = v' := Option.some.inj (answer.symm.trans answer')
      rfl

/-! ### Paths -/

theorem Path.append_iff {P : Profile} {q q'' : I.HState} {p₁ p₂ : List (Move I.E I.F)} :
    I.Path P q (p₁ ++ p₂) q'' ↔ ∃ q', I.Path P q p₁ q' ∧ I.Path P q' p₂ q'' := by
  induction p₁ generalizing q with
  | nil =>
    refine ⟨fun h => ⟨q, .nil _, h⟩, ?_⟩
    rintro ⟨q', h1, h2⟩
    cases h1
    exact h2
  | cons m p ih =>
    constructor
    · intro h
      cases h with
      | cons ht hp =>
        obtain ⟨q', h1, h2⟩ := ih.mp hp
        exact ⟨q', .cons ht h1, h2⟩
    · rintro ⟨q', h1, h2⟩
      cases h1 with
      | cons ht hp => exact .cons ht (ih.mpr ⟨q', hp, h2⟩)

theorem Path.functional {o : GrowOracle} {q q₁ q₂ : I.HState} {p : List (Move I.E I.F)}
    (h₁ : I.Path (profile o) q p q₁) (h₂ : I.Path (profile o) q p q₂) : q₁ = q₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons ht _ ih =>
    cases h₂ with
    | cons ht' hp' =>
      obtain rfl := Trans.functional ht ht'
      exact ih hp'

theorem Path.snoc {P : Profile} {q q' q'' : I.HState} {p : List (Move I.E I.F)}
    {m : Move I.E I.F} (hp : I.Path P q p q') (ht : I.Trans P q' m q'') :
    I.Path P q (p ++ [m]) q'' :=
  Path.append_iff.mpr ⟨q', hp, .cons ht (.nil _)⟩

theorem Path.snoc_iff {P : Profile} {q q'' : I.HState} {p : List (Move I.E I.F)}
    {m : Move I.E I.F} :
    I.Path P q (p ++ [m]) q'' ↔ ∃ q', I.Path P q p q' ∧ I.Trans P q' m q'' := by
  rw [Path.append_iff]
  constructor
  · rintro ⟨q', h1, h2⟩
    cases h2 with
    | cons ht hn => cases hn; exact ⟨q', h1, ht⟩
  · rintro ⟨q', h1, ht⟩
    exact ⟨q', h1, .cons ht (.nil _)⟩

/-! ### Legality -/

theorem Trans.step {P : Profile} {q q' : I.HState} {m : Move I.E I.F}
    (h : I.Trans P q m q') : Step q.pos m q'.pos := by
  cases h with
  | call s f => exact .ask f
  | ucall => exact .call _ _
  | uret v => exact .reply _ _ v
  | oret => exact .ret _ _

theorem Path.legal {P : Profile} {q q' : I.HState} {p : List (Move I.E I.F)}
    (h : I.Path P q p q') : Silmaril.Games.Path q.pos p q'.pos := by
  induction h with
  | nil => exact .nil _
  | cons ht _ ih => exact .cons (Trans.step ht) ih

/-! ### Traces and the strategy -/

theorem run_iff_path {P : Profile} {s : Store Nat} {x y : (I.lts P s).State}
    {p : List (Move I.E I.F)} : (I.lts P s).Run x p y ↔ I.Path P x p y := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil _
    | tau hs _ _ => obtain ⟨m, hm, -⟩ := hs; cases hm
    | vis hs _ ih =>
      obtain ⟨m, hm, ht⟩ := hs
      cases hm
      exact .cons ht ih
  · intro h
    induction h with
    | nil => exact .nil _
    | cons ht _ ih => exact .vis ⟨_, rfl, ht⟩ ih

theorem traces_eq (P : Profile) (s : Store Nat) : (I.lts P s).Traces = I.plays P s := by
  ext p
  exact ⟨fun ⟨y, h⟩ => ⟨y, run_iff_path.1 h⟩, fun ⟨y, h⟩ => ⟨y, run_iff_path.2 h⟩⟩

theorem plays_legal {P : Profile} {s : Store Nat} {p : List (Move I.E I.F)}
    (h : p ∈ I.plays P s) : Legal p := by
  obtain ⟨q, hq⟩ := h
  exact ⟨_, Path.legal hq⟩

theorem plays_of_prefix {P : Profile} {s : Store Nat} {p p' : List (Move I.E I.F)}
    (hp' : p' ∈ I.plays P s) (h : p <+: p') : p ∈ I.plays P s := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨q, hq⟩ := hp'
  obtain ⟨q', hq', -⟩ := Path.append_iff.mp hq
  exact ⟨q', hq'⟩

theorem plays_receptive {P : Profile} {s : Store Nat} {p : List (Move I.E I.F)}
    {x y : Pos I.E I.F} {m : Move I.E I.F} (hp : p ∈ I.plays P s)
    (hx : Silmaril.Games.Path .idle p x) (hxy : Step x m y) (hm : m.IsO) :
    p ++ [m] ∈ I.plays P s := by
  obtain ⟨q, hq⟩ := hp
  have hpos : q.pos = x := Silmaril.Games.Path.det (Path.legal hq) hx
  cases q with
  | idle s' =>
    subst hpos
    cases hxy with
    | ask f => exact ⟨_, Path.snoc hq (.call s' f)⟩
  | running f s' t =>
    subst hpos
    cases hxy <;> simp [Move.IsO] at hm
  | waiting f s' t e =>
    subst hpos
    cases hxy with
    | reply _ _ n => exact ⟨_, Path.snoc hq (.uret n)⟩

theorem mem_strategy_iff {P : Profile} {s : Store Nat} {p : List (Move I.E I.F)} :
    p ∈ I.strategy P s ↔ p ∈ I.plays P s := by
  constructor
  · rintro ⟨hl, u, hu, hp⟩
    have hu' : u ∈ I.plays P s := by
      rcases hu with rfl | ⟨hu, -⟩
      · exact ⟨_, .nil _⟩
      · rwa [← traces_eq]
    rcases hp with hp | ⟨p₀, m, rfl, hp₀, hm⟩
    · exact plays_of_prefix hu' hp
    · obtain ⟨_, hpath⟩ := hl
      obtain ⟨x, hx, hxm⟩ := Silmaril.Games.Path.concat_iff.1 hpath
      exact plays_receptive (plays_of_prefix hu' hp₀) hx hxm hm
  · intro h
    exact Strategy.mem_ofLTS_of_mem_traces (by rwa [traces_eq]) (plays_legal h)

theorem denotes (P : Profile) (s : Store Nat) : (I.lts P s).Denotes (I.strategy P s) := by
  intro p
  rw [traces_eq, mem_strategy_iff]

/-! ### Determinism of the strategy -/

theorem strategy_deterministic {o : GrowOracle} {s : Store Nat} {p : List (Move I.E I.F)}
    {m m' : Move I.E I.F} (h : p ++ [m] ∈ I.strategy (profile o) s)
    (h' : p ++ [m'] ∈ I.strategy (profile o) s) (hm : m.IsP) : m = m' := by
  obtain ⟨q, hq⟩ := mem_strategy_iff.1 h
  obtain ⟨q', hq'⟩ := mem_strategy_iff.1 h'
  obtain ⟨a, ha, ht⟩ := Path.snoc_iff.1 hq
  obtain ⟨a', ha', ht'⟩ := Path.snoc_iff.1 hq'
  obtain rfl := Path.functional ha ha'
  exact Trans.player_unique ht ht' hm

/-! ### Persistence -/

theorem activation_functional {o : GrowOracle} {s s₁ s₂ : Store Nat}
    {c : List (Move I.E I.F)} (h₁ : I.Activation (profile o) s c s₁)
    (h₂ : I.Activation (profile o) s c s₂) : s₁ = s₂ := by
  have := Path.functional h₁ h₂
  cases this
  rfl

/-- After a complete activation `c` ending in `s'`, the plays from `s'` continue those from
`s` (every profile). -/
theorem append_mem_plays_of {P : Profile} {s s' : Store Nat}
    {c p : List (Move I.E I.F)} (hc : I.Activation P s c s') (hp : p ∈ I.plays P s') :
    c ++ p ∈ I.plays P s := by
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, Path.append_iff.mpr ⟨_, hc, hq⟩⟩

/-- **Persistence, every profile.** A play `c ++ p` from `s`, with `c` a complete
activation (ending idle), is `c` reaching *some* store `s'` followed by a play from `s'`.
Under a nondeterministic profile several stores `s'` may be reachable along `c`. -/
theorem append_mem_plays_iff_exists {P : Profile} {s : Store Nat}
    {c p : List (Move I.E I.F)} (hq : ∀ q', I.Path P (.idle s) c q' → ∃ s', q' = .idle s') :
    c ++ p ∈ I.plays P s ↔ ∃ s', I.Activation P s c s' ∧ p ∈ I.plays P s' := by
  constructor
  · rintro ⟨q₂, hq₂⟩
    obtain ⟨q', h1, h2⟩ := Path.append_iff.mp hq₂
    obtain ⟨s', rfl⟩ := hq q' h1
    exact ⟨s', h1, q₂, h2⟩
  · rintro ⟨s', hc', hp⟩
    exact append_mem_plays_of hc' hp

theorem append_mem_plays_iff {o : GrowOracle} {s s' : Store Nat}
    {c p : List (Move I.E I.F)} (hc : I.Activation (profile o) s c s') :
    c ++ p ∈ I.plays (profile o) s ↔ p ∈ I.plays (profile o) s' := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨q', h1, h2⟩ := Path.append_iff.mp hq
    cases Path.functional h1 hc
    exact ⟨q, h2⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, Path.append_iff.mpr ⟨_, hc, hq⟩⟩

/-! ### Monotonicity in the profile -/

/-- Host-free runs of a profile whose host-free steps are steps of another profile are runs of
the other profile. -/
theorem Reach.mono {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Det.noHost c c' → Step Q Det.noHost c c')
    {x y : Store Nat × Thread} (h : Reach P x y) : Reach Q x y := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨f', code', heq, hstep⟩ := hst
    exact ih.tail ⟨f', code', heq, hPQ _ _ hstep⟩

/-- Transitions are monotone in the profile. -/
theorem Trans.mono {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Det.noHost c c' → Step Q Det.noHost c c')
    {q q' : I.HState} {m : Move I.E I.F} (h : I.Trans P q m q') : I.Trans Q q m q' := by
  cases h with
  | call s f => exact .call s f
  | ucall run callout op => exact .ucall (Reach.mono hPQ run) callout op
  | uret v => exact .uret v
  | oret run final answer => exact .oret (Reach.mono hPQ run) final answer

/-- Paths are monotone in the profile. -/
theorem Path.mono {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Det.noHost c c' → Step Q Det.noHost c c')
    {q q' : I.HState} {p : List (Move I.E I.F)} (h : I.Path P q p q') : I.Path Q q p q' := by
  induction h with
  | nil => exact .nil _
  | cons ht _ ih => exact .cons (Trans.mono hPQ ht) ih

/-- The strategy is monotone in the profile. -/
theorem strategy_mono {P Q : Profile}
    (hPQ : ∀ c c' : Config Nat, Step P Det.noHost c c' → Step Q Det.noHost c c')
    (s : Store Nat) : I.strategy P s ≤ I.strategy Q s := by
  intro p hp
  obtain ⟨q, hq⟩ := mem_strategy_iff.1 hp
  exact mem_strategy_iff.2 ⟨q, Path.mono hPQ hq⟩

/-! ### Agreement with Core reduction -/

theorem ask_ans_iff {P : Profile} {s : Store Nat} {f : I.F.Op} {w : I.F.Ar f} :
    [.inr (.ask f), .inr (.ans f w)] ∈ I.strategy P s ↔
      ∃ d r, Steps P (Det.noHost : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1) d ∧
        d.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w := by
  rw [mem_strategy_iff]
  constructor
  · rintro ⟨q, hq⟩
    cases hq with
    | cons h₁ hq =>
      cases h₁
      cases hq with
      | cons h₂ hq =>
        cases h₂ with
        | oret run final answer =>
          obtain ⟨d, hd, hc⟩ := ret_iff_core.1 ⟨_, _, run, final⟩
          exact ⟨d, _, hd, hc, answer⟩
  · rintro ⟨d, r, hd, hc, hr⟩
    obtain ⟨s', t', run, final⟩ := (ret_iff_core (P := P) (s := s) (t := I.initThread f)).2 ⟨d, hd, hc⟩
    exact ⟨_, .cons (.call s f) (.cons (.oret run final hr) (.nil _))⟩

theorem ask_call_iff {P : Profile} {s : Store Nat} {f : I.F.Op} {e : I.E.Op} :
    [.inr (.ask f), .inl (.ask e)] ∈ I.strategy P s ↔
      ∃ d, Steps P (Det.noHost : HostSemantics Nat) (invoke s (I.addr f.1) f.2.1) d ∧
        ∃ E a h args, decompose? d.store d.code = some (E, a, h, args) ∧
          I.importOp? h args = some e := by
  rw [mem_strategy_iff]
  constructor
  · rintro ⟨q, hq⟩
    cases hq with
    | cons h₁ hq =>
      cases h₁
      cases hq with
      | cons h₂ hq =>
        cases h₂ with
        | ucall run callout op =>
          obtain ⟨d, hd, E, a, hdec⟩ := out_iff_core.1 ⟨_, _, run, callout⟩
          exact ⟨d, hd, E, a, _, _, hdec, op⟩
  · rintro ⟨d, hd, E, a, h, args, hdec, hop⟩
    obtain ⟨s', t', run, callout⟩ :=
      (out_iff_core (P := P) (s := s) (t := I.initThread f)).2 ⟨d, hd, E, a, hdec⟩
    exact ⟨_, .cons (.call s f) (.cons (.ucall run callout hop) (.nil _))⟩

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
