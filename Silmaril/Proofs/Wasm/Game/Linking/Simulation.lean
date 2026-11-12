module

public import Silmaril.Proofs.Wasm.Game.Adequacy.Termination
public import Silmaril.Wasm.Link.WholeSimulation
public import Silmaril.Wasm.Link.LinkObservation
public import Silmaril.Proofs.Wasm.Game.Linking.Callout

/-!
# Static linking: simulation of host-free runs

Original module documentation:

# #1936's simulation on the single-threaded machine (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. #1936 relates
the shared store (provider and consumer instantiated separately) and the linked store by
`StoreRelation.Related` and transports every host-free Core step forward
(`WholeSimulation.step`, any numerics profile). This file lifts it to the single-threaded
machine and adds what the game statement needs beyond #1936's forward simulation of
terminating runs:

* `internal_simulation`: lock-step forward simulation of `Internal` steps, typing supplying
  the scopes (`AdminScope`, `FunctionScopes`) that `WholeSimulation.step` asks for;
* `reach_reverse`: the **reverse** direction for runs to a result. Route: the typed source
  makes progress (or is stuck at a callout, which the matching target is too) and, if it did
  not finish, would diverge; divergence transfers forward, which contradicts the target
  finishing (`reach_normal_unique`, `reach_normal_not_infinite`);
* `diverges_transfer`: **divergence** transfers both ways;
* `step_hostOf_simulation`: the host contract for open programs: strategy-definable hosts
  (M2) are compatible with #1936's `Matching` relation (a host sees only the host function,
  which `StoreRelation.Function.same` keeps, and the arguments, and does not change the
  store).

**Profiles.** The forward simulations here (`internal_simulation`,
`reach_simulation`, `infinite_simulation`, `normal_transfer`,
`step_hostOf_simulation`) hold for an arbitrary profile `P`
(`WholeSimulation.step` is stated for every profile). The reverse direction
`reach_reverse` and `diverges_transfer` are stated for `profile o`; the general
form of the former is `ReachReverse P`, proved for every profile in
`Silmaril.Proofs.Wasm.Game.Linking.Reverse` (`reachReverse_all`). Original text on the grow oracle:
everything here holds for an arbitrary grow oracle `o`:
`WholeSimulation.step` is stated for every profile, and uniqueness of normal forms is
`reach_normal_unique` (`Internal.deterministic`), which is oracle-generic (#1936's
`LinkObservation.terminal_unique` is stated for `neverFail`, but its proof,
`nf_unique_of_join` with `Det.DStep.join'`, is not specific to it). In the M3 fragment the
oracle is moreover irrelevant: `inProfile` modules have no memories or tables and cannot
import them, so `memory.grow`/`table.grow` never execute.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC

namespace Linking

open Silmaril.Wasm.Link.GC.AdminRelation

/-- Typing of the configuration of a thread, read off as a `ThreadOk` with its store. -/
private theorem storeOk_of_typed {x : Store Nat × Thread} {ts : List CValType}
    (typed : ConfigOk (x.2.config x.1) ts) : StoreOk x.1 := by
  have h := ConfigOk.storeOk typed
  rwa [Thread.config_store] at h

private theorem reach_typed {P : Profile} {x y : Store Nat × Thread} {ts : List CValType}
    (run : Reach P x y) (typed : ConfigOk (x.2.config x.1) ts) :
    ConfigOk (y.2.config y.1) ts :=
  (reachableP_typed run (storeOk_of_typed typed) typed).2

/-- Lock-step forward simulation of host-free steps (`WholeSimulation.step`), with the
typing invariant supplying the scopes it needs. -/
theorem internal_simulation {P : Profile} {x y x' : Store Nat × Thread}
    {mode : AdminRelation.Mode} {ts : List CValType} (h : InternalP P x y)
    (typed : ConfigOk (x.2.config x.1) ts)
    (matching : Simulation.Matching mode (x.2.config x.1) (x'.2.config x'.1)) :
    ∃ y', InternalP P x' y' ∧ Simulation.Matching mode (y.2.config y.1) (y'.2.config y'.1) := by
  rcases x with ⟨s, t⟩
  rcases y with ⟨s₁, t₁⟩
  obtain ⟨f₁, code₁, rfl, hstep⟩ := h
  obtain ⟨target, tstep, paired⟩ := WholeSimulation.step hstep matching
    (AdminScope.config_scope typed) (Simulation.function_scopes typed.choose_spec.1.1)
  refine ⟨(target.store, .active target.frame target.code), ⟨_, _, rfl, ?_⟩, paired⟩
  exact tstep

/-- Forward simulation of host-free runs. -/
theorem reach_simulation {P : Profile} {x y x' : Store Nat × Thread}
    {mode : AdminRelation.Mode} {ts : List CValType} (run : Reach P x y)
    (typed : ConfigOk (x.2.config x.1) ts)
    (matching : Simulation.Matching mode (x.2.config x.1) (x'.2.config x'.1)) :
    ∃ y', Reach P x' y' ∧ Simulation.Matching mode (y.2.config y.1) (y'.2.config y'.1) := by
  induction run with
  | refl => exact ⟨x', .refl, matching⟩
  | @tail mid fin previous next ih =>
    obtain ⟨mid', run', paired⟩ := ih
    obtain ⟨fin', step', paired'⟩ :=
      internal_simulation next (reach_typed previous typed) paired
    exact ⟨fin', run'.tail step', paired'⟩

/-- Forward transfer of divergence. -/
theorem infinite_simulation {P : Profile} {x x' : Store Nat × Thread}
    {mode : AdminRelation.Mode} {ts : List CValType}
    (inf : InfiniteTrace (InternalP P) x) (typed : ConfigOk (x.2.config x.1) ts)
    (matching : Simulation.Matching mode (x.2.config x.1) (x'.2.config x'.1)) :
    InfiniteTrace (InternalP P) x' := by
  refine InfiniteTrace.coinduct (fun b => ∃ a, InfiniteTrace (InternalP P) a ∧
      ConfigOk (a.2.config a.1) ts ∧ Simulation.Matching mode (a.2.config a.1) (b.2.config b.1))
    ?_ ⟨x, inf, typed, matching⟩
  rintro b ⟨a, ha, ta, ma⟩
  obtain ⟨a₁, step, tail⟩ := ha.unfold
  obtain ⟨b₁, step', m₁⟩ := internal_simulation step ta ma
  exact ⟨b₁, step', a₁, tail, reach_typed (.single step) ta, m₁⟩

/-- Classically, a host-free run either reaches a normal form or diverges. -/
theorem normal_or_infinite (P : Profile) (x : Store Nat × Thread) :
    (∃ y, Reach P x y ∧ ∀ z, ¬ InternalP P y z) ∨ InfiniteTrace (InternalP P) x := by
  by_cases hn : ∃ y, Reach P x y ∧ ∀ z, ¬ InternalP P y z
  · exact .inl hn
  · refine .inr (InfiniteTrace.coinduct (fun y => Reach P x y) ?_ .refl)
    intro y hy
    by_contra hno
    exact hn ⟨y, hy, fun z hz => hno ⟨z, hz, hy.tail hz⟩⟩

/-- A typed normal form is matched by a normal form, and a result of the target is one of
the source. -/
theorem normal_transfer {P : Profile} {y y' : Store Nat × Thread}
    {mode : AdminRelation.Mode} {ts : List CValType}
    (typed : ConfigOk (y.2.config y.1) ts) (normal : ∀ z, ¬ InternalP P y z)
    (matching : Simulation.Matching mode (y.2.config y.1) (y'.2.config y'.1)) :
    (∀ z, ¬ InternalP P y' z) ∧ ∀ r, ResultAt y'.1 y'.2 r → ResultAt y.1 y.2 r := by
  rcases y with ⟨s, t⟩
  rcases y' with ⟨s', t'⟩
  rcases Config.progress (P := P) (host := divHost) divHost_ok typed with
    ⟨r₀, hr₀⟩ | ⟨c₁, hc₁⟩
  · show (∀ z, ¬ InternalP P (s', t') z) ∧ ∀ r, ResultAt s' t' r → ResultAt s t r
    have code : AdminRelation.Control mode (t.config s).frame.module (t'.config s').frame.module
        r₀.toAdmin (t'.config s').code := hr₀ ▸ matching.code
    have hr₀' : (t'.config s').code = r₀.toAdmin := by
      cases r₀ with
      | values vs => exact code.values_left
      | trap => exact code.trap_singleton
      | throw a => exact code.throwing_left
    refine ⟨toAdmin_no_internal hr₀', fun r hr => ?_⟩
    change (t.config s).code = r.toAdmin
    change (t'.config s').code = r.toAdmin at hr
    rw [hr₀, ← hr₀', hr]
  · show (∀ z, ¬ InternalP P (s', t') z) ∧ ∀ r, ResultAt s' t' r → ResultAt s t r
    rcases (stepP_iff P divHost s t c₁).mp hc₁ with ⟨s₁, f₁, code₁, -, hi⟩ |
      ⟨E, a, h, args, hd, -⟩
    · exact absurd hi (normal _)
    · have hstores : StoreRelation.Related s s' := by
        simpa only [Thread.config_store] using matching.stores
      obtain ⟨E', hd'', -⟩ := decompose?_transfer hstores matching.code hd
      refine ⟨decompose?_no_internal hd'', fun r hr => ?_⟩
      change (t'.config s').code = r.toAdmin at hr
      have hnone : decompose? s' (t'.config s').code = none := by
        rw [hr, decompose?_toAdmin]
      exact absurd (hnone.symm.trans hd'') (by simp)

/-- **Reverse simulation of host-free runs to a result under the profile `P`**: whenever a
typed source configuration matches a target one, every run of the target to a result is
matched by a run of the source to the same result. This is the backward direction that M3
needs beyond silmaril-lean's forward simulation. It holds in the deterministic profiles
(`reach_reverse`, from uniqueness of normal forms) and, by a backward simulation of the linker
relation that silmaril-lean does not provide (`Silmaril/Wasm/Link/LinkObservation.lean`,
"Nondeterministic profile"), in every profile (`reachReverse_all`). -/
def ReachReverse (P : Profile) : Prop :=
  ∀ {x x' y' : Store Nat × Thread} {ts : List CValType} {r : Result},
    ConfigOk (x.2.config x.1) ts →
    Simulation.Matching .same (x.2.config x.1) (x'.2.config x'.1) →
    Reach P x' y' → ResultAt y'.1 y'.2 r →
    ∃ y, Reach P x y ∧ ResultAt y.1 y.2 r ∧
      Simulation.Matching .same (y.2.config y.1) (y'.2.config y'.1)

/-- Reverse simulation of runs to a result: if the target finishes, so does the source, with
the same result and related final configurations. -/
theorem reach_reverse {o : GrowOracle} {x x' y' : Store Nat × Thread}
    {ts : List CValType} {r : Result} (typed : ConfigOk (x.2.config x.1) ts)
    (matching : Simulation.Matching .same (x.2.config x.1) (x'.2.config x'.1))
    (run : Reach (profile o) x' y') (final : ResultAt y'.1 y'.2 r) :
    ∃ y, Reach (profile o) x y ∧ ResultAt y.1 y.2 r ∧
      Simulation.Matching .same (y.2.config y.1) (y'.2.config y'.1) := by
  have normal' : ∀ z, ¬ InternalP (profile o) y' z := by
    rcases y' with ⟨s', t'⟩
    exact toAdmin_no_internal final
  rcases normal_or_infinite (profile o) x with ⟨y, hxy, hny⟩ | hinf
  · obtain ⟨y'', hx'y'', hm⟩ := reach_simulation hxy typed matching
    obtain ⟨hn'', hres⟩ := normal_transfer (reach_typed hxy typed) hny hm
    have heq : y'' = y' := reach_normal_unique hx'y'' run hn'' normal'
    subst heq
    exact ⟨y, hxy, hres r final, hm⟩
  · exact absurd (infinite_simulation hinf typed matching)
      (reach_normal_not_infinite run normal')

/-- Divergence transfers both ways between matching typed configurations. -/
theorem diverges_transfer {o : GrowOracle} {c c' : Config Nat} {ts : List CValType}
    (typed : ConfigOk c ts) (matching : Simulation.Matching .same c c') :
    InfiniteTrace (InternalP (profile o)) (c.store, .active c.frame c.code) ↔
      InfiniteTrace (InternalP (profile o)) (c'.store, .active c'.frame c'.code) := by
  constructor
  · intro h
    exact infinite_simulation (x := (c.store, .active c.frame c.code)) h typed matching
  · intro h'
    rcases normal_or_infinite (profile o) (c.store, .active c.frame c.code) with ⟨y, hxy, hny⟩ | hinf
    · obtain ⟨y'', hx'y'', hm⟩ := reach_simulation (x' := (c'.store, .active c'.frame c'.code))
        hxy typed matching
      obtain ⟨hn'', -⟩ := normal_transfer (reach_typed (ts := ts) hxy typed) hny hm
      exact absurd h' (reach_normal_not_infinite hx'y'' hn'')
    · exact hinf

/-- The reverse simulation holds in every deterministic profile. -/
theorem reachReverse_profile (o : GrowOracle) : ReachReverse (profile o) :=
  fun typed matching run final => reach_reverse typed matching run final

/-- Strategy-definable hosts are compatible with #1936's relation: a host step of the source
is matched by a host step of the target. -/
theorem step_hostOf_simulation {P : Silmaril.Wasm.Numerics.Profile} {ts : List FnType}
    {K : Silmaril.Wasm.Game.Env (ifaceSig ts)} {mode : AdminRelation.Mode} {c c₁ c' : Config Nat}
    (step : Step P (hostOf ts K) c c₁)
    (hd : ∃ E a h args, decompose? c.store c.code = some (E, a, h, args))
    (matching : Simulation.Matching mode c c') :
    ∃ c₁', Step P (hostOf ts K) c' c₁' ∧ Simulation.Matching mode c₁ c₁' := by
  obtain ⟨st, fr, code⟩ := c
  obtain ⟨st', fr', code'⟩ := c'
  rcases Step.split_host step with hfree | ⟨E, a, hh, args, hd, ⟨s₁, r, hr, hc₁⟩ | ⟨hdiv, hc₁⟩⟩
  · obtain ⟨E, a, h, args, hd⟩ := hd
    have hn : decompose? st code = none := decompose?_none_of_noRedex (Step.noRedex hfree)
    exact absurd (hn.symm.trans hd) (by simp)
  · show ∃ c₁', Step P (hostOf ts K) ⟨st', fr', code'⟩ c₁' ∧ Simulation.Matching mode c₁ c₁'
    obtain ⟨e, he, ⟨w, hw, heq⟩ | ⟨-, heq⟩⟩ := hr
    · show ∃ c₁', Step P (hostOf ts K) ⟨st', fr', code'⟩ c₁' ∧ Simulation.Matching mode c₁ c₁'
      obtain ⟨hs₁, hr'⟩ : s₁ = st ∧ r = Answer.toResult (ft := ts.get e.1) w := by
        simpa using heq
      obtain ⟨E', hd', mode₀, m₀, m₀', hfill⟩ :=
        decompose?_transfer matching.stores matching.code hd
      obtain ⟨fi, yy, ps, rs, hf, hc, hyy, hex, hn, hcode'⟩ := decompose?_sound hd'
      have hcode'' : code' = E'.fill (vals args ++ [.ref (.func a), yy]) := hcode'
      refine ⟨⟨st', fr', E'.fill (Result.toAdmin (Answer.toResult (ft := ts.get e.1) w))⟩,
        ?_, ?_⟩
      · rw [hcode'']
        exact E'.step_fill (fun g => Step.callRefHost hyy hf hex hn hc
          ⟨e, he, Or.inl ⟨w, hw, rfl⟩⟩) fr'
      · rw [hc₁, hs₁, hr']
        exact ⟨matching.stores, matching.frames, hfill _ _ (Control.result_refl _ _ _ _)⟩
    · exact absurd heq (by simp)
  · show ∃ c₁', Step P (hostOf ts K) ⟨st', fr', code'⟩ c₁' ∧ Simulation.Matching mode c₁ c₁'
    obtain ⟨E', hd', -⟩ := decompose?_transfer matching.stores matching.code hd
    obtain ⟨fi, yy, ps, rs, hf, hc, hyy, hex, hn, hcode'⟩ := decompose?_sound hd'
    have hcode'' : code' = E'.fill (vals args ++ [.ref (.func a), yy]) := hcode'
    have hdiv' : hostOf ts K hh st' args .diverged := by
      obtain ⟨e, he, ⟨w, hw, heq⟩ | ⟨hno, -⟩⟩ := hdiv
      · exact absurd heq (by simp)
      · exact ⟨e, he, Or.inr ⟨hno, rfl⟩⟩
    refine ⟨⟨st', fr', code'⟩, ?_, hc₁ ▸ matching⟩
    rw [hcode'']
    exact E'.step_fill (fun g => Step.callRefHostDiv hyy hf hex hn hc hdiv') fr'

end Linking

end Silmaril.Wasm.Game
