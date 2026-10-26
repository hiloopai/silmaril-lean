module

public import Silmaril.Process.LPS.Equivalence

/-!
# Changing the instruction step of an LPS machine

`isa.withStep st` is the user machine `isa` with its instruction step replaced
by `st`; the state type, the syscall interface, the memory views, the effect
application and the initial state are those of `isa`. This file shows that two
such machines, `isa.withStep a` and `isa.withStep b`, have the same LPS
judgments whenever their steps agree at every configuration reachable under
`a` that executes an instruction (`AgreesFrom`).

* `sstep_recast`, `star_recast`, `star_unrecast`: steps and executions carry
  over at agreeing configurations, in both directions.
* `obsTrace_iff`, `reachesError_iff`, `reachesUnmodeled_iff`,
  `allTracesError_iff`, `mustExitInAt_iff`: every observation of a `Behavior`
  (traces, errors, all-traces-error, unmodelled) and LPS `must_exit_in_at`
  are the same; `runWith_iff` packages the behaviour.
* `agreesFrom_of_errorFree`: the agreement holds automatically at every
  reachable instruction when the run under `a` never errors and `a` and `b`
  agree on every instruction step that `a` completes (`ok`). Every LPS
  correctness statement includes error freedom (`ErrorFree`), so this is the
  hypothesis under which those statements transfer.

This is the LPS half of the x86 configuration lattice
(`Silmaril.X86.Features.Lattice.LPS`), where `a` and `b` are the steps of
two configurations `c ≤ d`.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- `isa` with the instruction step `st`. -/
def UserIsa.withStep (isa : UserIsa)
    (st : List Segment → isa.State → MachineResult (AccessReport isa.State)) : UserIsa :=
  { isa with step := st }

namespace StepTransfer

variable {isa : UserIsa} {a b : List Segment → isa.State → MachineResult (AccessReport isa.State)}
  {segs : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}

/-- The same configuration, seen by the machine with the other step. -/
def recast (c : Config (isa.withStep a)) : Config (isa.withStep b) := ⟨c.ms, c.model⟩

def recastTo : StepTo (isa.withStep a) → StepTo (isa.withStep b)
  | .next c => .next (recast c)
  | .error => .error

@[simp] theorem recast_recast (c : Config (isa.withStep a)) :
    recast (b := a) (recast (b := b) c) = c := rfl

/-- The two steps agree at `c` whenever `c` executes an instruction. -/
def AgreesAt (a b : List Segment → isa.State → MachineResult (AccessReport isa.State))
    (segs : List Segment) (c : Config (isa.withStep a)) : Prop :=
  c.model.halted = none → isa.svcPending c.ms = none → b segs c.ms = a segs c.ms

theorem AgreesAt.symm {c : Config (isa.withStep a)} (h : AgreesAt a b segs c) :
    AgreesAt b a segs (recast c) := fun h1 h2 => (h h1 h2).symm

theorem accountStep_eq {c : Config (isa.withStep a)} (h : AgreesAt a b segs c)
    (h1 : c.model.halted = none) (h2 : isa.svcPending c.ms = none) :
    accountStep (isa.withStep b) segs c.ms c.model = accountStep (isa.withStep a) segs c.ms c.model := by
  unfold accountStep
  simp only [UserIsa.withStep]
  rw [h h1 h2]
  cases a segs c.ms <;> rfl

theorem sstep_recast {c : Config (isa.withStep a)} {evs : List Event}
    {st : StepTo (isa.withStep a)} (h : AgreesAt a b segs c)
    (s : SStep segs spec refused c evs st) :
    SStep segs spec refused (recast (b := b) c) evs (recastTo st) := by
  cases s with
  | instr h1 h2 h3 =>
    refine .instr h1 h2 ?_
    rw [accountStep_eq (c := ⟨_, _⟩) h h1 h2]; exact h3
  | instrFault h1 h2 h3 =>
    refine .instrFault h1 h2 ?_
    rw [accountStep_eq (c := ⟨_, _⟩) h h1 h2]; exact h3
  | instrUnmodeled h1 h2 h3 =>
    refine .instrUnmodeled h1 h2 ?_
    rw [accountStep_eq (c := ⟨_, _⟩) h h1 h2]; exact h3
  | syscall h1 h2 h3 h4 h5 h6 => exact .syscall h1 h2 h3 h4 h5 h6
  | syscallMaterializationFault h1 h2 h3 h4 h5 h6 =>
    exact .syscallMaterializationFault h1 h2 h3 h4 h5 h6
  | exit h1 h2 h3 h4 h5 => exact .exit h1 h2 h3 h4 h5
  | killed h1 h2 h3 h4 => exact .killed h1 h2 h3 h4
  | syscallUnmodeled h1 h2 h3 => exact .syscallUnmodeled h1 h2 h3

theorem sstep_recast_next {c c' : Config (isa.withStep a)} {evs : List Event}
    (h : AgreesAt a b segs c) (s : SStep segs spec refused c evs (.next c')) :
    SStep segs spec refused (recast (b := b) c) evs (.next (recast c')) :=
  sstep_recast h s

theorem sstep_recast_error {c : Config (isa.withStep a)} {evs : List Event}
    (h : AgreesAt a b segs c) (s : SStep segs spec refused c evs .error) :
    SStep segs spec refused (recast (b := b) c) evs .error :=
  sstep_recast h s

/-- Every configuration reachable under `a` from `c₀` agrees. -/
def AgreesFrom (a b : List Segment → isa.State → MachineResult (AccessReport isa.State))
    (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (c₀ : Config (isa.withStep a)) : Prop :=
  ∀ tr c, Star segs spec refused c₀ tr c → AgreesAt a b segs c

theorem AgreesFrom.here {c₀ : Config (isa.withStep a)} (h : AgreesFrom a b segs spec refused c₀) :
    AgreesAt a b segs c₀ := h [] c₀ (.refl c₀)

theorem AgreesFrom.next {c₀ c₁ : Config (isa.withStep a)} {evs : List Event}
    (h : AgreesFrom a b segs spec refused c₀) (s : SStep segs spec refused c₀ evs (.next c₁)) :
    AgreesFrom a b segs spec refused c₁ := fun tr c r => h (evs ++ tr) c (.step s r)

theorem star_recast {c₀ c : Config (isa.withStep a)} {tr : List Event}
    (h : AgreesFrom a b segs spec refused c₀) (s : Star segs spec refused c₀ tr c) :
    Star segs spec refused (recast (b := b) c₀) tr (recast c) := by
  induction s with
  | refl c => exact .refl _
  | step st _ ih => exact .step (sstep_recast_next h.here st) (ih (h.next st))

theorem star_unrecast {x y : Config (isa.withStep b)} {tr : List Event}
    (h : AgreesFrom a b segs spec refused (recast x)) (s : Star segs spec refused x tr y) :
    Star segs spec refused (recast (b := a) x) tr (recast y) := by
  induction s with
  | refl c => exact .refl _
  | step st _ ih =>
    have st' := sstep_recast_next (a := b) (b := a) h.here.symm st
    exact .step st' (ih (h.next st'))

/-- Agreement from `c₀` under `a` gives agreement from `c₀` under `b`. -/
theorem AgreesFrom.symm {c₀ : Config (isa.withStep a)} (h : AgreesFrom a b segs spec refused c₀) :
    AgreesFrom b a segs spec refused (recast c₀) := fun tr c s =>
  (h tr (recast c) (star_unrecast (a := a) (b := b) (x := recast c₀) h s)).symm

/-! ## The judgments -/

variable {c₀ : Config (isa.withStep a)}

theorem star_iff (h : AgreesFrom a b segs spec refused c₀) {tr : List Event}
    {c : Config (isa.withStep a)} :
    Star segs spec refused (recast (b := b) c₀) tr (recast c) ↔ Star segs spec refused c₀ tr c :=
  ⟨fun s => star_unrecast (a := a) (b := b) (x := recast c₀) h s, star_recast h⟩

theorem obsTrace_iff (h : AgreesFrom a b segs spec refused c₀) (tr : List Event) :
    ObsTrace segs spec refused (recast (b := b) c₀) tr ↔ ObsTrace segs spec refused c₀ tr := by
  constructor
  · rintro ⟨tr', c, s, pre⟩
    exact ⟨tr', recast c, star_unrecast (a := a) (b := b) (x := recast c₀) h s, pre⟩
  · rintro ⟨tr', c, s, pre⟩
    exact ⟨tr', recast c, star_recast h s, pre⟩

theorem reachesError_iff (h : AgreesFrom a b segs spec refused c₀) :
    ReachesError segs spec refused (recast (b := b) c₀) ↔ ReachesError segs spec refused c₀ := by
  constructor
  · rintro ⟨tr, c, evs, s, e⟩
    have s' := star_unrecast (a := a) (b := b) (x := recast c₀) h s
    exact ⟨tr, recast c, evs, s', sstep_recast_error (a := b) (b := a) (h.symm tr c s) e⟩
  · rintro ⟨tr, c, evs, s, e⟩
    exact ⟨tr, recast c, evs, star_recast h s, sstep_recast_error (h tr c s) e⟩

theorem unmodeledAt_iff {c : Config (isa.withStep a)} (h : AgreesAt a b segs c) :
    UnmodeledAt segs spec (recast (b := b) c) ↔ UnmodeledAt segs spec c := by
  unfold UnmodeledAt
  constructor
  · rintro ⟨h1, (⟨h2, h3⟩ | h3)⟩
    · refine ⟨h1, .inl ⟨h2, ?_⟩⟩
      rw [← accountStep_eq h h1 h2]; exact h3
    · exact ⟨h1, .inr h3⟩
  · rintro ⟨h1, (⟨h2, h3⟩ | h3)⟩
    · refine ⟨h1, .inl ⟨h2, ?_⟩⟩
      change accountStep (isa.withStep b) segs c.ms c.model = _
      rw [accountStep_eq h h1 h2]; exact h3
    · exact ⟨h1, .inr h3⟩

theorem reachesUnmodeled_iff (h : AgreesFrom a b segs spec refused c₀) :
    ReachesUnmodeled segs spec refused (recast (b := b) c₀) ↔
      ReachesUnmodeled segs spec refused c₀ := by
  constructor
  · rintro ⟨tr, c, s, u⟩
    have s' := star_unrecast (a := a) (b := b) (x := recast c₀) h s
    exact ⟨tr, recast c, s', (unmodeledAt_iff (h tr _ s')).mp u⟩
  · rintro ⟨tr, c, s, u⟩
    exact ⟨tr, recast c, star_recast h s, (unmodeledAt_iff (h tr c s)).mpr u⟩

private theorem allTracesError_recast {c₀ : Config (isa.withStep a)}
    (h : AgreesFrom a b segs spec refused c₀) (e : AllTracesError segs spec refused c₀) :
    AllTracesError segs spec refused (recast (b := b) c₀) := by
  induction e with
  | intro hex _ ih =>
    rename_i c
    refine .intro ?_ ?_
    · obtain ⟨evs, st, s⟩ := hex
      exact ⟨evs, recastTo st, sstep_recast h.here s⟩
    · intro evs c' s
      have s' := sstep_recast_next (a := b) (b := a) h.here.symm s
      exact ih evs (recast c') s' (h.next s')

theorem allTracesError_iff (h : AgreesFrom a b segs spec refused c₀) :
    AllTracesError segs spec refused (recast (b := b) c₀) ↔ AllTracesError segs spec refused c₀ :=
  ⟨fun e => allTracesError_recast (a := b) (b := a) h.symm e, allTracesError_recast h⟩

private theorem mustExitInAt_recast {S : List Word} {c₀ : Config (isa.withStep a)}
    (h : AgreesFrom a b segs spec refused c₀) (e : MustExitInAt segs spec refused S c₀) :
    MustExitInAt segs spec refused S (recast (b := b) c₀) := by
  induction e with
  | halted h1 h2 h3 => exact .halted h1 h2 h3
  | running h1 hex hne _ ih =>
    refine .running h1 ?_ ?_ ?_
    · obtain ⟨evs, st, s⟩ := hex
      exact ⟨evs, recastTo st, sstep_recast h.here s⟩
    · intro evs s
      exact hne evs (sstep_recast_error (a := b) (b := a) h.here.symm s)
    · intro evs c' s
      have s' := sstep_recast_next (a := b) (b := a) h.here.symm s
      exact ih evs (recast c') s' (h.next s')

theorem mustExitInAt_iff (h : AgreesFrom a b segs spec refused c₀) (S : List Word) :
    MustExitInAt segs spec refused S (recast (b := b) c₀) ↔ MustExitInAt segs spec refused S c₀ :=
  ⟨fun e => mustExitInAt_recast (a := b) (b := a) h.symm e, mustExitInAt_recast h⟩

/-- The behaviour of one launch is the same. -/
theorem runWith_iff {spec : Sys SyscallEffect} {refused : RefusalFilter} {img : Image} {lim : Int}
    {en : ExecEntry} {inp : ProcInput}
    (h : AgreesFrom a b img.segments spec refused (initConfig (isa.withStep a) img en lim inp)) :
    (∀ tr, (runWith (isa.withStep b) spec refused img lim en inp).traces tr ↔
        (runWith (isa.withStep a) spec refused img lim en inp).traces tr) ∧
      ((runWith (isa.withStep b) spec refused img lim en inp).errors ↔
        (runWith (isa.withStep a) spec refused img lim en inp).errors) ∧
      ((runWith (isa.withStep b) spec refused img lim en inp).allErrors ↔
        (runWith (isa.withStep a) spec refused img lim en inp).allErrors) ∧
      ((runWith (isa.withStep b) spec refused img lim en inp).unmodeled ↔
        (runWith (isa.withStep a) spec refused img lim en inp).unmodeled) :=
  ⟨obsTrace_iff h, reachesError_iff h, allTracesError_iff h, reachesUnmodeled_iff h⟩

/-! ## Agreement from error freedom -/

/-- At a configuration that executes an instruction and does not error, the
instruction step completes. -/
theorem step_ok_of_not_error {c : Config (isa.withStep a)}
    (h1 : c.model.halted = none) (h2 : isa.svcPending c.ms = none)
    (hne : ∀ evs, ¬ SStep segs spec refused c evs .error) :
    ∃ r, a segs c.ms = .ok r := by
  cases hs : a segs c.ms with
  | ok r => exact ⟨r, rfl⟩
  | fault =>
    exfalso
    have : accountStep (isa.withStep a) segs c.ms c.model = .fault ∨
        accountStep (isa.withStep a) segs c.ms c.model = .unmodeled := by
      simp only [accountStep, UserIsa.withStep, hs]
      cases (!isa.reportsAccesses && !c.model.vmLazy.isEmpty) <;> simp
    rcases this with e | e
    · exact hne [] (.instrFault (isa := isa.withStep a) h1 h2 e)
    · exact hne [] (.instrUnmodeled (isa := isa.withStep a) h1 h2 e)
  | unmodeled =>
    exfalso
    have : accountStep (isa.withStep a) segs c.ms c.model = .unmodeled := by
      simp only [accountStep, UserIsa.withStep, hs]
      cases (!isa.reportsAccesses && !c.model.vmLazy.isEmpty) <;> simp
    exact hne [] (.instrUnmodeled (isa := isa.withStep a) h1 h2 this)

/-- **Agreement from error freedom**: if no execution from `c₀` under `a`
errors, and `b` agrees with `a` at every state where `a`'s instruction step
completes, the steps agree at every reachable instruction. -/
theorem agreesFrom_of_errorFree (hne : ¬ ReachesError segs spec refused c₀)
    (hok : ∀ ms r, a segs ms = .ok r → b segs ms = a segs ms) :
    AgreesFrom a b segs spec refused c₀ := by
  intro tr c s h1 h2
  obtain ⟨r, hr⟩ := step_ok_of_not_error (segs := segs) (spec := spec) (refused := refused)
    (c := c) h1 h2 (fun evs e => hne ⟨tr, c, evs, s, e⟩)
  exact hok c.ms r hr

end StepTransfer

end Silmaril.Process.LPS
