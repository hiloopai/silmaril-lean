module

public import Silmaril.Process.LPS.RunExt
public import Silmaril.Process.LPS.Equivalence

/-!
# LPS in Lean: run outcomes, raw syscall histories and the final file system

LPS `Run.v` observes a run through four propositions (`behavior`): its finite trace
prefixes, whether some execution errors, whether every execution errors, and whether the
model gives up. The statements (`MustExit.v`, `Equivalence.v`) read further facts off the same
relations: how an execution ends, the exit status, the final file system carried by the last
event. This file names those readings over the translated relations, without changing them:

* **Outcomes.** A maximal execution ends in one of six ways (`RunOutcome`): a normal exit
  with a status and the final file system, death by a signal with the final file system, an
  error that is a *fault* (the program died: an instruction fault, or an access the budget
  refuses at first touch), an error that is *unmodeled* (the model gave up), a *stuck*
  configuration (running, with no transition at all: possible only when the spec admits no
  outcome for the pending syscall, or the refusal filter refuses every outcome it admits that
  does not halt; the `spuriousRefusalCfg` filters never do the latter, by their non-refusal
  witness), or *divergence* (an infinite sequence of successful steps). `Ends c₀ o` says that
  some execution from `c₀` ends in `o`; nondeterminism stays quantified, so several outcomes
  can hold of one configuration. The outcomes are pairwise distinguished on the configuration
  or step that witnesses them (`exitedAt_not_killedAt`, `ErrorStep.not_halted`,
  `Stuck.not_error`, `Diverges.not_halted`, …).
* **Universal termination.** `MustExitInAt` (LPS `must_exit_in_at`) excludes every other
  outcome: no reachable kill, error, stuck configuration or divergence
  (`MustExitInAt.not_diverges`, `.no_errorStep`, `.no_stuck`, `.no_kill`).
* **Raw syscall history.** `LStep` is `SStep` with a label (`StepRecord`) recording each
  successful step: an instruction, or a syscall's number, argument registers, chosen effect
  (return value or errno included; for an exit or kill step, the effect the spec chose before
  halting) and emitted events, with batching kept. Only successful steps are recorded: a
  syscall whose step is an error (a materialization fault or `unmodeled`) has no record, and
  is read off the history's last configuration by `ErrorStep` instead. `HStar` is its star; `byteTrace` flattens a history into
  the byte-granular event trace of `Star`, and the two views reach the same configurations
  (`HStar.toStar`, `Star.toHStar`). The trace prefixes of a run are exactly the prefixes of
  flattened histories (`obsTrace_iff_history`), and a raw prefix flattens to a trace prefix
  (`byteTrace_prefix`); the converse fails, since a byte prefix can end inside a batch.
* **Final file system.** A halted configuration reached from a running one was reached by an
  exit or kill step, whose event is the last of the trace and carries the configuration's file
  system (`Star.final`, `Star.finalFs`).
* **Budget.** The first-touch and copy-in/out clauses of `BudgetRefusedAt` are errors of the
  plain run; only the grant clause is not (`BudgetRefusedAt.error_or_grant`), so a run that
  must exit is never refused at first touch (`MustExitInAt.no_touch_refusal`).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-! ## Terminal configurations -/

/-- LPS `State.v:3464` `m_killed` reads through `m_halted`: a killed model is halted. -/
theorem Model.halted_of_killedBy {m : Model} {sig : Word} (h : m.killedBy = some sig) :
    m.halted = some sig := by
  unfold Model.killedBy at h
  split at h
  · exact h
  · cases h

section Outcomes

variable {isa : UserIsa} (segs : List Segment) (spec : Sys SyscallEffect)
  (refused : RefusalFilter)

/-- The process has exited normally with `code`. -/
def ExitedAt (c : Config isa) (code : Word) : Prop :=
  c.model.halted = some code ∧ c.model.killedBy = none

/-- The process was killed by `sig`. -/
def KilledAt (c : Config isa) (sig : Word) : Prop := c.model.killedBy = some sig

/-- The kind of an error transition: the program died, or the model gave up. -/
inductive ErrorKind where
  | fault
  | unmodeled
  deriving DecidableEq, Repr

/-- The error transitions of `SStep`, by kind (LPS `Run.v:409-466`, the four constructors that
go to `SError`). -/
inductive ErrorStep : Config isa → ErrorKind → Prop where
  | instrFault {ms model} : model.halted = none → isa.svcPending ms = none →
      accountStep isa segs ms model = .fault → ErrorStep ⟨ms, model⟩ .fault
  | instrUnmodeled {ms model} : model.halted = none → isa.svcPending ms = none →
      accountStep isa segs ms model = .unmodeled → ErrorStep ⟨ms, model⟩ .unmodeled
  | materializationFault {ms model x8 eff model' evs} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      ¬ refused (sysInput isa segs ms x8) model eff → model'.halted = none →
      materializeModelAccesses model' (syscallEffectAccesses eff) = none →
      ErrorStep ⟨ms, model⟩ .fault
  | syscallUnmodeled {ms model x8} : model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model .unmodeled → ErrorStep ⟨ms, model⟩ .unmodeled

/-- Running, with no transition at all. -/
def Stuck (c : Config isa) : Prop :=
  c.model.halted = none ∧ ¬ ∃ evs st, SStep segs spec refused c evs st

/-- An infinite execution of successful steps from `c`. -/
def Diverges (c : Config isa) : Prop :=
  ∃ f : Nat → Config isa, f 0 = c ∧ ∀ n, ∃ evs, SStep segs spec refused (f n) evs (.next (f (n + 1)))

/-- How a maximal execution ends. -/
inductive RunOutcome where
  | exited (code : Word) (fs : Fs.FileSystem)
  | killed (sig : Word) (fs : Fs.FileSystem)
  | error (kind : ErrorKind)
  | stuck
  | diverges

/-- Some execution from `c₀` ends in the outcome. -/
def Ends (c₀ : Config isa) : RunOutcome → Prop
  | .exited code fs => ∃ tr c, Star segs spec refused c₀ tr c ∧ ExitedAt c code ∧ c.model.fs = fs
  | .killed sig fs => ∃ tr c, Star segs spec refused c₀ tr c ∧ KilledAt c sig ∧ c.model.fs = fs
  | .error k => ∃ tr c, Star segs spec refused c₀ tr c ∧ ErrorStep segs spec refused c k
  | .stuck => ∃ tr c, Star segs spec refused c₀ tr c ∧ Stuck segs spec refused c
  | .diverges => Diverges segs spec refused c₀

variable {segs spec refused}

/-- An error transition is exactly an `ErrorStep` of some kind, and emits nothing. -/
theorem sstep_error_iff {c : Config isa} :
    (∃ evs, SStep segs spec refused c evs .error) ↔ ∃ k, ErrorStep segs spec refused c k := by
  constructor
  · rintro ⟨evs, s⟩
    cases s with
    | instrFault a b c => exact ⟨_, .instrFault a b c⟩
    | instrUnmodeled a b c => exact ⟨_, .instrUnmodeled a b c⟩
    | syscallMaterializationFault a b c d e f => exact ⟨_, .materializationFault a b c d e f⟩
    | syscallUnmodeled a b c => exact ⟨_, .syscallUnmodeled a b c⟩
  · rintro ⟨k, e⟩
    cases e with
    | instrFault a b c => exact ⟨_, .instrFault a b c⟩
    | instrUnmodeled a b c => exact ⟨_, .instrUnmodeled a b c⟩
    | materializationFault a b c d e f => exact ⟨_, .syscallMaterializationFault a b c d e f⟩
    | syscallUnmodeled a b c => exact ⟨_, .syscallUnmodeled a b c⟩

theorem ErrorStep.sstep {c : Config isa} {k : ErrorKind} (e : ErrorStep segs spec refused c k) :
    SStep segs spec refused c [] .error := by
  cases e with
  | instrFault a b c => exact .instrFault a b c
  | instrUnmodeled a b c => exact .instrUnmodeled a b c
  | materializationFault a b c d e f => exact .syscallMaterializationFault a b c d e f
  | syscallUnmodeled a b c => exact .syscallUnmodeled a b c

theorem SStep.error_evs {c : Config isa} {evs : List Event} (s : SStep segs spec refused c evs .error) :
    evs = [] := by
  cases s <;> rfl

/-- The unmodeled errors are exactly LPS's `unmodeled_at` (`Run.v:805`). -/
theorem errorStep_unmodeled_iff {c : Config isa} :
    ErrorStep segs spec refused c .unmodeled ↔ UnmodeledAt segs spec c := by
  constructor
  · intro e
    cases e with
    | instrUnmodeled a b c => exact ⟨a, .inl ⟨b, c⟩⟩
    | syscallUnmodeled a b c => exact ⟨a, .inr ⟨_, b, c⟩⟩
  · intro h
    cases c with
    | mk ms model =>
      obtain ⟨hh, ⟨hsvc, hstep⟩ | ⟨x8, hsvc, hspec⟩⟩ := h
      · exact .instrUnmodeled hh hsvc hstep
      · exact .syscallUnmodeled hh hsvc hspec

/-- `ReachesError` is reaching an error of some kind. -/
theorem reachesError_iff {c₀ : Config isa} :
    ReachesError segs spec refused c₀ ↔ ∃ k, Ends segs spec refused c₀ (.error k) := by
  constructor
  · rintro ⟨tr, c, evs, s, e⟩
    obtain ⟨k, e⟩ := sstep_error_iff.1 ⟨evs, e⟩
    exact ⟨k, tr, c, s, e⟩
  · rintro ⟨k, tr, c, s, e⟩
    exact ⟨tr, c, [], s, e.sstep⟩

/-- `ReachesUnmodeled` is reaching an unmodeled error. -/
theorem reachesUnmodeled_iff {c₀ : Config isa} :
    ReachesUnmodeled segs spec refused c₀ ↔ Ends segs spec refused c₀ (.error .unmodeled) := by
  constructor
  · rintro ⟨tr, c, s, u⟩; exact ⟨tr, c, s, errorStep_unmodeled_iff.2 u⟩
  · rintro ⟨tr, c, s, e⟩; exact ⟨tr, c, s, errorStep_unmodeled_iff.1 e⟩

/-! ### The outcomes are distinguished -/

theorem exitedAt_not_killedAt {c : Config isa} {code sig : Word} (h : ExitedAt c code) :
    ¬ KilledAt c sig := by
  intro hk; unfold KilledAt at hk; rw [h.2] at hk; cases hk

theorem halted_not_step {c : Config isa} {evs : List Event} {st : StepTo isa}
    (h : c.model.halted ≠ none) : ¬ SStep segs spec refused c evs st :=
  fun s => h s.halted_none

theorem ErrorStep.not_halted {c : Config isa} {k : ErrorKind}
    (e : ErrorStep segs spec refused c k) : c.model.halted = none :=
  e.sstep.halted_none

theorem ExitedAt.not_error {c : Config isa} {code : Word} {k : ErrorKind} (h : ExitedAt c code) :
    ¬ ErrorStep segs spec refused c k :=
  fun e => by have := e.not_halted; rw [h.1] at this; cases this

theorem KilledAt.not_error {c : Config isa} {sig : Word} {k : ErrorKind} (h : KilledAt c sig) :
    ¬ ErrorStep segs spec refused c k :=
  fun e => by have := e.not_halted; rw [Model.halted_of_killedBy h] at this; cases this

theorem ExitedAt.not_stuck {c : Config isa} {code : Word} (h : ExitedAt c code) :
    ¬ Stuck segs spec refused c :=
  fun ⟨hh, _⟩ => by rw [h.1] at hh; cases hh

theorem KilledAt.not_stuck {c : Config isa} {sig : Word} (h : KilledAt c sig) :
    ¬ Stuck segs spec refused c :=
  fun ⟨hh, _⟩ => by rw [Model.halted_of_killedBy h] at hh; cases hh

theorem Stuck.not_error {c : Config isa} {k : ErrorKind} (h : Stuck segs spec refused c) :
    ¬ ErrorStep segs spec refused c k :=
  fun e => h.2 ⟨_, _, e.sstep⟩

theorem Stuck.not_diverges {c : Config isa} (h : Stuck segs spec refused c) :
    ¬ Diverges segs spec refused c := by
  rintro ⟨f, h₀, hf⟩
  obtain ⟨evs, s⟩ := hf 0
  rw [h₀] at s
  exact h.2 ⟨_, _, s⟩

/-- Divergence is not halting: every configuration of a diverging execution is running. -/
theorem Diverges.not_halted {c : Config isa} (h : Diverges segs spec refused c) :
    c.model.halted = none := by
  obtain ⟨f, h₀, hf⟩ := h
  obtain ⟨evs, s⟩ := hf 0
  rw [h₀] at s
  exact s.halted_none

/-- Every configuration along a diverging execution is running. -/
theorem diverging_all_running {f : Nat → Config isa}
    (hf : ∀ n, ∃ evs, SStep segs spec refused (f n) evs (.next (f (n + 1)))) (n : Nat) :
    (f n).model.halted = none :=
  let ⟨_, s⟩ := hf n
  s.halted_none

theorem Diverges.not_exited {c : Config isa} {code : Word} (h : Diverges segs spec refused c) :
    ¬ ExitedAt c code :=
  fun he => by have := h.not_halted; rw [he.1] at this; cases this

theorem Diverges.not_killed {c : Config isa} {sig : Word} (h : Diverges segs spec refused c) :
    ¬ KilledAt c sig :=
  fun hk => by have := h.not_halted; rw [Model.halted_of_killedBy hk] at this; cases this

/-- A diverging execution never errors on the way: universal error excludes divergence. -/
theorem AllTracesError.not_diverges {c : Config isa} (h : AllTracesError segs spec refused c) :
    ¬ Diverges segs spec refused c := by
  induction h with
  | intro _ _ ih =>
    rintro ⟨f, h₀, hf⟩
    obtain ⟨evs, s⟩ := hf 0
    rw [h₀] at s
    exact ih _ _ s ⟨fun n => f (n + 1), rfl, fun n => hf (n + 1)⟩

/-! ## Universal termination (LPS `MustExit.v:929` `must_exit_in_at`) -/

theorem MustExitInAt.star {S : List Word} {c c' : Config isa} {tr : List Event}
    (h : MustExitInAt segs spec refused S c) (s : Star segs spec refused c tr c') :
    MustExitInAt segs spec refused S c' := by
  revert h
  induction s with
  | refl => exact id
  | step st _ ih =>
    intro h
    cases h with
    | halted hh _ _ => exact absurd st.halted_none (by simp [hh])
    | running _ _ _ hnext => exact ih (hnext _ _ st)

/-- Universal termination excludes divergence. -/
theorem MustExitInAt.not_diverges {S : List Word} {c : Config isa}
    (h : MustExitInAt segs spec refused S c) : ¬ Diverges segs spec refused c := by
  induction h with
  | halted hh _ _ =>
    rintro ⟨f, h₀, hf⟩
    obtain ⟨evs, s⟩ := hf 0
    rw [h₀] at s
    exact absurd s.halted_none (by simp [hh])
  | running _ _ _ _ ih =>
    rintro ⟨f, h₀, hf⟩
    obtain ⟨evs, s⟩ := hf 0
    rw [h₀] at s
    exact ih _ _ s ⟨fun n => f (n + 1), rfl, fun n => hf (n + 1)⟩

theorem MustExitInAt.here_no_error {S : List Word} {c : Config isa} {k : ErrorKind}
    (h : MustExitInAt segs spec refused S c) : ¬ ErrorStep segs spec refused c k := by
  cases h with
  | halted hh _ _ => exact fun e => absurd e.not_halted (by simp [hh])
  | running _ _ hnoerr _ => exact fun e => hnoerr _ e.sstep

/-- Universal termination excludes a reachable error of either kind. -/
theorem MustExitInAt.no_errorStep {S : List Word} {c₀ c : Config isa} {tr : List Event}
    {k : ErrorKind} (h : MustExitInAt segs spec refused S c₀)
    (s : Star segs spec refused c₀ tr c) : ¬ ErrorStep segs spec refused c k :=
  (h.star s).here_no_error

theorem MustExitInAt.not_reachesError {S : List Word} {c₀ : Config isa}
    (h : MustExitInAt segs spec refused S c₀) : ¬ ReachesError segs spec refused c₀ := by
  rintro ⟨tr, c, evs, s, e⟩
  obtain ⟨k, e⟩ := sstep_error_iff.1 ⟨evs, e⟩
  exact h.no_errorStep s e

/-- Universal termination excludes a reachable stuck configuration. -/
theorem MustExitInAt.no_stuck {S : List Word} {c₀ c : Config isa} {tr : List Event}
    (h : MustExitInAt segs spec refused S c₀) (s : Star segs spec refused c₀ tr c) :
    ¬ Stuck segs spec refused c := by
  rintro ⟨hh, hno⟩
  cases h.star s with
  | halted hh' _ _ => rw [hh'] at hh; cases hh
  | running _ hprog _ _ => exact hno hprog

/-- Universal termination excludes a reachable kill. -/
theorem MustExitInAt.no_kill {S : List Word} {c₀ c : Config isa} {tr : List Event} {sig : Word}
    (h : MustExitInAt segs spec refused S c₀) (s : Star segs spec refused c₀ tr c) :
    ¬ KilledAt c sig := by
  intro hk
  cases h.star s with
  | halted _ _ hnk => unfold KilledAt at hk; rw [hnk] at hk; cases hk
  | running hh _ _ _ => rw [Model.halted_of_killedBy hk] at hh; cases hh

/-- Every halted reachable configuration of a must-exit run has exited with an allowed
status. -/
theorem MustExitInAt.exited {S : List Word} {c₀ c : Config isa} {tr : List Event}
    (h : MustExitInAt segs spec refused S c₀) (s : Star segs spec refused c₀ tr c)
    (hh : c.model.halted ≠ none) : ∃ code ∈ S, ExitedAt c code := by
  cases h.star s with
  | halted hc hS hk => exact ⟨_, hS, hc, hk⟩
  | running hr _ _ _ => exact absurd hr hh

/-! ## Raw syscall histories -/

/-- One labelled step: an instruction, or a syscall with its number, argument registers,
the effect the spec chose (its return value is the errno, if negative) and the events it
emitted, batched as the call emitted them. -/
inductive StepRecord where
  | instr
  | syscall (sysno : Word) (args : List Word) (eff : SyscallEffect) (evs : List Event)
  | exit (sysno : Word) (args : List Word) (eff : SyscallEffect) (code : Word) (evs : List Event)
  | killed (sysno : Word) (args : List Word) (eff : SyscallEffect) (sig : Word) (evs : List Event)

/-- The events a record emitted. -/
def StepRecord.events : StepRecord → List Event
  | .instr => []
  | .syscall _ _ _ evs => evs
  | .exit _ _ _ _ evs => evs
  | .killed _ _ _ _ evs => evs

/-- The syscall request of a record: number and argument registers. -/
def StepRecord.request? : StepRecord → Option (Word × List Word)
  | .instr => none
  | .syscall no args _ _ => some (no, args)
  | .exit no args _ _ _ => some (no, args)
  | .killed no args _ _ _ => some (no, args)

/-- The value returned to the program, if the call returned. -/
def StepRecord.ret? : StepRecord → Option Word
  | .syscall _ _ eff _ => some eff.ret
  | _ => none

variable (segs spec refused) in
/-- `SStep`'s successful transitions, labelled by their raw record. -/
inductive LStep : Config isa → StepRecord → Config isa → Prop where
  | instr {ms model ms' model'} : model.halted = none → isa.svcPending ms = none →
      accountStep isa segs ms model = .ok (ms', model') →
      LStep ⟨ms, model⟩ .instr ⟨ms', model'⟩
  | syscall {ms model x8 eff model' model'' evs} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      ¬ refused (sysInput isa segs ms x8) model eff → model'.halted = none →
      materializeModelAccesses model' (syscallEffectAccesses eff) = some model'' →
      LStep ⟨ms, model⟩ (.syscall x8 (isa.syscallArgs ms) eff evs)
        ⟨isa.advancePastSvc (isa.applyEffect ms eff), model''⟩
  | exit {ms model x8 eff model' evs code} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      model'.halted = some code → model'.killedBy = none →
      LStep ⟨ms, model⟩ (.exit x8 (isa.syscallArgs ms) eff code (evs ++ [.exitEv code model'.fs]))
        ⟨ms, model'⟩
  | killed {ms model x8 eff model' evs sig} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      model'.killedBy = some sig →
      LStep ⟨ms, model⟩ (.killed x8 (isa.syscallArgs ms) eff sig (evs ++ [.killEv sig model'.fs]))
        ⟨ms, model'⟩

variable (segs spec refused) in
/-- The raw history of a finite execution. -/
inductive HStar : Config isa → List StepRecord → Config isa → Prop where
  | refl (c) : HStar c [] c
  | step {c₁ r c₂ h c₃} : LStep segs spec refused c₁ r c₂ → HStar c₂ h c₃ → HStar c₁ (r :: h) c₃

/-- The byte-granular trace of a raw history: its events, batches flattened. -/
def byteTrace (h : List StepRecord) : List Event := h.flatMap StepRecord.events

theorem LStep.toSStep {c c' : Config isa} {r : StepRecord} (s : LStep segs spec refused c r c') :
    SStep segs spec refused c r.events (.next c') := by
  cases s with
  | instr a b c => exact .instr a b c
  | syscall a b c d e f => exact .syscall a b c d e f
  | exit a b c d e => exact .exit a b c d e
  | killed a b c d => exact .killed a b c d

theorem SStep.toLStep {c c' : Config isa} {evs : List Event}
    (s : SStep segs spec refused c evs (.next c')) :
    ∃ r, LStep segs spec refused c r c' ∧ r.events = evs := by
  cases s with
  | instr a b c => exact ⟨_, .instr a b c, rfl⟩
  | syscall a b c d e f => exact ⟨_, .syscall a b c d e f, rfl⟩
  | exit a b c d e => exact ⟨_, .exit a b c d e, rfl⟩
  | killed a b c d => exact ⟨_, .killed a b c d, rfl⟩

theorem HStar.toStar {c c' : Config isa} {h : List StepRecord}
    (s : HStar segs spec refused c h c') : Star segs spec refused c (byteTrace h) c' := by
  induction s with
  | refl c => exact .refl c
  | step st _ ih => exact .step st.toSStep ih

theorem Star.toHStar {c c' : Config isa} {tr : List Event} (s : Star segs spec refused c tr c') :
    ∃ h, HStar segs spec refused c h c' ∧ byteTrace h = tr := by
  induction s with
  | refl c => exact ⟨[], .refl c, rfl⟩
  | step st _ ih =>
    obtain ⟨r, l, hr⟩ := st.toLStep
    obtain ⟨h, hs, ht⟩ := ih
    subst hr ht
    exact ⟨r :: h, .step l hs, by simp [byteTrace]⟩

/-- The trace prefixes of a run are the prefixes of the byte traces of its raw histories. -/
theorem obsTrace_iff_history {c₀ : Config isa} {tr : List Event} :
    ObsTrace segs spec refused c₀ tr ↔
      ∃ h c, HStar segs spec refused c₀ h c ∧ tr <+: byteTrace h := by
  constructor
  · rintro ⟨tr', c, s, p⟩
    obtain ⟨h, hs, ht⟩ := s.toHStar
    exact ⟨h, c, hs, ht ▸ p⟩
  · rintro ⟨h, c, hs, p⟩
    exact ⟨_, c, hs.toStar, p⟩

/-- A raw-history prefix flattens to a trace prefix. -/
theorem byteTrace_prefix {h₁ h₂ : List StepRecord} (p : h₁ <+: h₂) :
    byteTrace h₁ <+: byteTrace h₂ := by
  obtain ⟨t, rfl⟩ := p
  exact ⟨byteTrace t, by simp [byteTrace]⟩

/-- A raw history of a prefix-closed set of executions: every prefix of a history is a
history. -/
theorem HStar.prefix {c₀ c : Config isa} {h : List StepRecord} (s : HStar segs spec refused c₀ h c)
    {h' : List StepRecord} (p : h' <+: h) : ∃ c', HStar segs spec refused c₀ h' c' := by
  induction s generalizing h' with
  | refl c =>
    rw [List.prefix_nil.1 p]
    exact ⟨c, .refl c⟩
  | step st _ ih =>
    cases h' with
    | nil => exact ⟨_, .refl _⟩
    | cons r' h' =>
      obtain ⟨hr, p'⟩ := List.cons_prefix_cons.1 p
      obtain ⟨c', hc'⟩ := ih p'
      subst hr
      exact ⟨c', .step st hc'⟩

/-! ## Final file system -/

/-- The file system an ending event carries. -/
def Event.finalFs? : Event → Option Fs.FileSystem
  | .exitEv _ fs => some fs
  | .killEv _ fs => some fs
  | _ => none

/-- The file system observed at the end of a trace, if it ends. -/
def traceFinalFs (tr : List Event) : Option Fs.FileSystem := tr.getLast?.bind Event.finalFs?

/-- A step into a halted configuration is an exit or a kill, whose last event carries the
final file system. -/
theorem SStep.ends {c c' : Config isa} {evs : List Event}
    (s : SStep segs spec refused c evs (.next c')) (h : c'.model.halted ≠ none) :
    (∃ code pre, ExitedAt c' code ∧ evs = pre ++ [.exitEv code c'.model.fs]) ∨
      (∃ sig pre, KilledAt c' sig ∧ evs = pre ++ [.killEv sig c'.model.fs]) := by
  cases s with
  | @instr ms model ms' model' hh _ hacc =>
    exact absurd (show model'.halted = none by
      show model'.proc.halted = none; rw [accountStep_proc hacc]; exact hh) h
  | @syscall ms model x8 eff model' model'' evs _ _ _ _ hh' hmat =>
    exact absurd (show model''.halted = none by
      show model''.proc.halted = none; rw [materializeModelAccesses_proc hmat]; exact hh') h
  | exit _ _ _ hc hk => exact .inl ⟨_, _, ⟨hc, hk⟩, rfl⟩
  | killed _ _ _ hk => exact .inr ⟨_, _, hk, rfl⟩

/-- A run from a running configuration to a halted one ends with the exit or kill event,
carrying the final file system. -/
theorem Star.final {c₀ c : Config isa} {tr : List Event} (s : Star segs spec refused c₀ tr c)
    (h₀ : c₀.model.halted = none) (h : c.model.halted ≠ none) :
    (∃ code pre, ExitedAt c code ∧ tr = pre ++ [.exitEv code c.model.fs]) ∨
      (∃ sig pre, KilledAt c sig ∧ tr = pre ++ [.killEv sig c.model.fs]) := by
  revert h₀ h
  induction s with
  | refl c => intro h₀ h; exact absurd h₀ h
  | @step c₁ evs c₂ tr c₃ st rest ih =>
    intro _ h
    by_cases h₂ : c₂.model.halted = none
    · rcases ih h₂ h with ⟨code, pre, he, rfl⟩ | ⟨sig, pre, hk, rfl⟩
      · exact .inl ⟨code, evs ++ pre, he, by simp⟩
      · exact .inr ⟨sig, evs ++ pre, hk, by simp⟩
    · obtain ⟨rfl, rfl⟩ := Star.from_halted h₂ rest
      rcases st.ends h₂ with ⟨code, pre, he, rfl⟩ | ⟨sig, pre, hk, rfl⟩
      · exact .inl ⟨code, pre, he, by simp⟩
      · exact .inr ⟨sig, pre, hk, by simp⟩

/-- The final file system observation: the trace of a run that halts shows the halted
configuration's file system. -/
theorem Star.finalFs {c₀ c : Config isa} {tr : List Event}
    (s : Star segs spec refused c₀ tr c) (h₀ : c₀.model.halted = none)
    (h : c.model.halted ≠ none) : traceFinalFs tr = some c.model.fs := by
  rcases s.final h₀ h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    simp [LPS.traceFinalFs, Event.finalFs?]

/-! ## Budget refusal is not success -/

/-- The clauses of `BudgetRefusedAt` (LPS `Run.v:2086`): the first-touch and copy clauses are
errors of the plain run; the grant clause is the only one that is not. -/
theorem BudgetRefusedAt.error_or_grant {c : Config isa} (h : BudgetRefusedAt isa segs spec c) :
    (∃ evs, SStep segs spec noFilter c evs .error) ∨
      ∃ x8, isa.svcPending c.ms = some x8 ∧
        allocBudgetRefusedB (sysInput isa segs c.ms x8) c.model = true := by
  cases c with
  | mk ms model =>
    obtain ⟨hh, ⟨hsvc, report, hstep, hmat⟩ | ⟨x8, hsvc, hgrant | ⟨eff, model', evs, hspec, hh', hmat⟩⟩⟩ :=
      h
    · exact .inl (budgetFault_instr_sstep_error hh hsvc hstep hmat)
    · exact .inr ⟨x8, hsvc, hgrant⟩
    · exact .inl ⟨[], .syscallMaterializationFault hh hsvc hspec (fun h => h) hh' hmat⟩

/-- A run that must exit is never refused for budget at a first touch or a copy: wherever it
is budget-refused, the refusal is a grant the program is answered for. -/
theorem MustExitInAt.no_touch_refusal {S : List Word} {c₀ c : Config isa} {tr : List Event}
    (h : MustExitInAt segs spec noFilter S c₀) (s : Star segs spec noFilter c₀ tr c)
    (hb : BudgetRefusedAt isa segs spec c) :
    ∃ x8, isa.svcPending c.ms = some x8 ∧
      allocBudgetRefusedB (sysInput isa segs c.ms x8) c.model = true := by
  rcases hb.error_or_grant with ⟨evs, e⟩ | g
  · obtain ⟨k, e⟩ := sstep_error_iff.1 ⟨evs, e⟩
    exact absurd e (h.no_errorStep s)
  · exact g

end Outcomes

end Silmaril.Process.LPS
