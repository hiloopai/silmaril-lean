module

public import Silmaril.Games.DivLTS.Defs

/-!
# Divergence-sensitive simulations: proofs

* `simulation_run`: a weak simulation matches runs (restated from
  `Silmaril.Proofs.Games.LTS.Basic`, which this topic may not import).
* `diverges_of_divSimulation`: a divergence-sensitive simulation maps a
  diverging source state to a diverging target state. Well-founded induction
  on the measure gives one target silent step at least
  (`progress`); `Silmaril.InfiniteTrace.coinduct` then builds the infinite
  silent run.
* `infRun_of_simulation`: a weak simulation maps an infinite run to an
  infinite run with the same traces (dependent choice through `choose`).
* `toLTSDivSimulation`: a divergence-sensitive simulation of reduction
  semantics is one of their transition systems.
* `run_ask_inv`, `diverges_run_iff`: the silent behaviour of `Reduction.toLTS`
  after a question.
-/

public section

namespace Silmaril.Proofs.Games.DivLTS

open Silmaril.Games

universe u

variable {E F : Sig.{u}}

theorem simulation_run {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) {x x' : L₁.State}
    {s : List (Move E F)} (h : L₁.Run x s x') : ∀ {y}, S.R x y → ∃ y', L₂.Run y s y' ∧ S.R x' y' := by
  induction h with
  | nil x => exact fun hxy => ⟨_, .nil _, hxy⟩
  | tau hst _ ih =>
    intro y hxy
    obtain ⟨y₁, hr₁, h₁⟩ := S.step hxy hst
    obtain ⟨y', hr, h'⟩ := ih h₁
    exact ⟨y', by simpa using hr₁.append hr, h'⟩
  | vis hst _ ih =>
    intro y hxy
    obtain ⟨y₁, hr₁, h₁⟩ := S.step hxy hst
    obtain ⟨y', hr, h'⟩ := ih h₁
    exact ⟨y', by simpa using hr₁.append hr, h'⟩

theorem progress {L₁ L₂ : LTS E F} (S : L₁.DivSimulation L₂) (x : L₁.State) :
    ∀ y, S.R x y → L₁.Diverges x →
      ∃ y', Relation.TransGen L₂.Silent y y' ∧ ∃ x', S.R x' y' ∧ L₁.Diverges x' := by
  induction x using S.wf.induction with
  | _ x ih =>
    intro y hxy hd
    obtain ⟨x₁, hst, hd₁⟩ := hd.unfold
    rcases S.tau hxy hst with ⟨y', ht, hr⟩ | ⟨hr, hlt⟩
    · exact ⟨y', ht, x₁, hr, hd₁⟩
    · exact ih x₁ hlt y hr hd₁

theorem diverges_of_divSimulation {L₁ L₂ : LTS E F} (S : L₁.DivSimulation L₂) {x : L₁.State}
    {y : L₂.State} (hxy : S.R x y) (hd : L₁.Diverges x) : L₂.Diverges y := by
  let P : L₂.State → Prop := fun z =>
    ∃ y', Relation.TransGen L₂.Silent z y' ∧ ∃ x', S.R x' y' ∧ L₁.Diverges x'
  refine Silmaril.InfiniteTrace.coinduct P ?_ (progress S x y hxy hd)
  rintro z ⟨y', ht, x', hr, hd'⟩
  obtain ⟨z₁, hz, hrt⟩ := Relation.TransGen.head'_iff.1 ht
  refine ⟨z₁, hz, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hrt with rfl | ht'
  · exact progress S x' _ hr hd'
  · exact ⟨y', ht', x', hr, hd'⟩

theorem infRun_of_simulation {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) (r : L₁.InfRun) :
    ∃ r' : L₂.InfRun, r'.tr = r.tr := by
  choose w hw hrun using r.step
  have key : ∀ n y, S.R (r.st n) y → ∃ y', L₂.Run y (w n) y' ∧ S.R (r.st (n + 1)) y' :=
    fun n _ h => simulation_run S (hrun n) h
  choose! nxt hnxt using key
  let g : ℕ → L₂.State := fun n => Nat.rec L₂.init (fun k y => nxt k y) n
  have hg : ∀ n, S.R (r.st n) (g n) := by
    intro n
    induction n with
    | zero => rw [r.st_zero]; exact S.init
    | succ n ih => exact (hnxt n (g n) ih).2
  exact ⟨⟨g, r.tr, rfl, r.tr_zero, fun n => ⟨w n, hw n, (hnxt n (g n) (hg n)).1⟩⟩, rfl⟩

/-! ## Reduction semantics -/

variable {R R₁ R₂ : Reduction E F}

theorem run_taus {q : F.Op} {d d' : R.Conf q} (h : Relation.ReflTransGen R.step d d') :
    R.toLTS.Run (.run q d) [] (.run q d') := by
  induction h with
  | refl => exact .nil _
  | tail _ hst ih => simpa using ih.append (LTS.Run.of_step (L := R.toLTS) (Reduction.Step.tau hst))

theorem transGen_taus {q : F.Op} {d d' : R.Conf q} (h : Relation.TransGen R.step d d') :
    Relation.TransGen R.toLTS.Silent (.run q d) (.run q d') := by
  induction h with
  | single hst => exact .single (Reduction.Step.tau hst)
  | tail _ hst ih => exact ih.tail (Reduction.Step.tau hst)

/-- Simulation of reduction states. -/
inductive SimRel (S : R₁.Simulation R₂) : R₁.State → R₂.State → Prop
  | idle : SimRel S .idle .idle
  | run {q : F.Op} {c : R₁.Conf q} {d : R₂.Conf q} : S.rel c d → SimRel S (.run q c) (.run q d)
  | wait {q : F.Op} {m : E.Op} {k : E.Ar m → R₁.Conf q} {k' : E.Ar m → R₂.Conf q} :
      (∀ n, S.rel (k n) (k' n)) → SimRel S (.wait q m k) (.wait q m k')

/-- The measure on reduction states: the measure of the running configuration. -/
inductive StLt (S : R₁.DivSimulation R₂) : R₁.State → R₁.State → Prop
  | run {q : F.Op} {c c' : R₁.Conf q} : S.lt c' c → StLt S (.run q c') (.run q c)

theorem stLt_wf (S : R₁.DivSimulation R₂) : WellFounded (StLt S) := by
  refine ⟨fun x => ?_⟩
  cases x with
  | idle => exact ⟨_, fun y h => by cases h⟩
  | wait q m k => exact ⟨_, fun y h => by cases h⟩
  | run q c =>
    induction c using (S.wf q).induction with
    | _ c ih =>
      exact ⟨_, fun y h => by cases h with | run hlt => exact ih _ hlt⟩

/-- A divergence-sensitive simulation of reduction semantics is one of their
transition systems. -/
def toLTSDivSimulation (S : R₁.DivSimulation R₂) : LTS.DivSimulation R₁.toLTS R₂.toLTS where
  R := SimRel S.toSimulation
  init := .idle
  step := by
    intro x x' y l hxy hst
    cases hst with
    | ask q =>
      cases hxy
      exact ⟨_, LTS.Run.of_step (L := R₂.toLTS) (Reduction.Step.ask q), .run (S.start q)⟩
    | tau hc =>
      cases hxy with
      | run hr =>
        obtain ⟨d', hd, hr'⟩ := S.step hr hc
        exact ⟨_, run_taus hd, .run hr'⟩
    | call hc =>
      cases hxy with
      | run hr =>
        obtain ⟨d', hd, k', hk', hkk⟩ := S.call hr hc
        have h₁ := (run_taus hd).append (LTS.Run.of_step (L := R₂.toLTS) (Reduction.Step.call hk'))
        exact ⟨_, by simpa using h₁, .wait hkk⟩
    | resume q m k n =>
      cases hxy with
      | wait hkk =>
        exact ⟨_, LTS.Run.of_step (L := R₂.toLTS) (Reduction.Step.resume q m _ n), .run (hkk n)⟩
    | ret hc =>
      cases hxy with
      | run hr =>
        obtain ⟨d', hd, hd'⟩ := S.done hr hc
        have h₁ := (run_taus hd).append (LTS.Run.of_step (L := R₂.toLTS) (Reduction.Step.ret hd'))
        exact ⟨_, by simpa using h₁, .idle⟩
  lt := StLt S
  wf := stLt_wf S
  tau := by
    intro x x' y hxy hst
    cases hst with
    | tau hc =>
      cases hxy with
      | run hr =>
        rcases S.tau hr hc with ⟨d', hd, hr'⟩ | ⟨hr', hlt⟩
        · exact .inl ⟨_, transGen_taus hd, .run hr'⟩
        · exact .inr ⟨.run hr', .run hlt⟩

theorem silent_run_stuck {L : LTS E F} {x y : L.State} (hx : ∀ z, ¬ L.step x none z)
    (h : L.Run x [] y) : y = x := by
  cases h with
  | nil => rfl
  | tau hst _ => exact (hx _ hst).elim

theorem silent_run_map {L : LTS E F} {A : Type u} (f : A → L.State) (r : A → A → Prop)
    (hf : ∀ a z, L.step (f a) none z → ∃ b, r a b ∧ z = f b) {a : A} {y : L.State}
    (h : L.Run (f a) [] y) : ∃ b, y = f b ∧ Relation.ReflTransGen r a b := by
  generalize hx : f a = x at h
  generalize hs : ([] : List (Move E F)) = s at h
  induction h generalizing a with
  | nil => subst hx; exact ⟨a, rfl, .refl⟩
  | tau hst _ ih =>
    subst hx
    obtain ⟨b, hab, rfl⟩ := hf a _ hst
    obtain ⟨c, rfl, hc⟩ := ih rfl hs
    exact ⟨c, rfl, Relation.ReflTransGen.head hab hc⟩
  | vis _ _ _ => cases hs

theorem silent_run_idle {y : R.State} (h : R.toLTS.Run .idle [] y) : y = .idle :=
  silent_run_stuck (L := R.toLTS) (fun _ h => by cases h) h

theorem silent_run_run {q : F.Op} {c : R.Conf q} {y : R.State} (h : R.toLTS.Run (.run q c) [] y) :
    ∃ c', y = .run q c' ∧ Relation.ReflTransGen R.step c c' :=
  silent_run_map (L := R.toLTS) (fun c => (Reduction.State.run q c : R.State)) R.step
    (fun _ _ h => by cases h with | tau hc => exact ⟨_, hc, rfl⟩) h

theorem diverges_run_iff {q : F.Op} {c : R.Conf q} :
    R.toLTS.Diverges (.run q c) ↔ Silmaril.InfiniteTrace (R.step (q := q)) c := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map (fun c => (Reduction.State.run q c : R.State))
      (fun _ => True) ?_ trivial h
    intro a b _ hab
    cases hab with
    | tau hc => exact ⟨_, hc, trivial, rfl⟩
  · intro h
    exact Silmaril.InfiniteTrace.map (fun c => (Reduction.State.run q c : R.State))
      (fun _ _ h => Reduction.Step.tau h) h

/-- Divergence right after a question is divergence of the question's initial
configuration. -/
theorem div_ask_iff {q : F.Op} :
    [.inr (.ask q)] ∈ (DStrategy.ofReduction R).div ↔
      Silmaril.InfiniteTrace (R.step (q := q)) (R.start q) := by
  constructor
  · rintro ⟨⟨y, hr, hd⟩, -⟩
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hr
    cases silent_run_idle h₁
    cases h₂
    obtain ⟨c', rfl, hc⟩ := silent_run_run h₃
    exact Silmaril.InfiniteTrace.of_steps hc (diverges_run_iff.1 hd)
  · intro h
    exact ⟨⟨_, LTS.Run.of_step (L := R.toLTS) (Reduction.Step.ask q), diverges_run_iff.2 h⟩,
      q, Path.single (.ask q)⟩

end Silmaril.Proofs.Games.DivLTS
