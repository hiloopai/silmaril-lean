module

public import Silmaril.Process.LPS.Machines.RiscVLPSFpu
public import Silmaril.Process.LPS.Run

/-!
# FPU refinement lifted to runs and behaviours

`riscvLpsWith_refines` (`Machines/RiscVLPSFpu`) is a statement about one step. This file
lifts it to LPS's run semantics (`Silmaril.Process.LPS.Run`, LPS `Run.v`): if `fine` refines
`coarse` and the run of the coarse machine never reaches an unmodeled configuration, the two
machines have the same behaviour (`runWith_behaviorEquiv_of_modeled`): the same observable
traces, the same `errors`, the same `allErrors`, and neither reaches `unmodeled`.

The proof transfers configurations between the two machines (their state types are both
`RiscV.LPS.MachineState`, `cfg`) and shows, by induction on `Star` and on
`AllTracesError`, that every run of either machine is a run of the other as long as the
coarse machine is modeled along it.

Instances (`riscvLps_behaviorEquiv_agreed`, `riscvLpsIeee_behaviorEquiv_agreed`): every run
of `riscvLpsAgreed` that is modeled has the behaviour of the literal LPS machine
`riscvLps` and of `riscvLpsIeee`. So a theorem.dev-style statement that needs only
`Modeled` runs (LPS `Equivalence.v` `modeled`) and is proved for `riscvLpsAgreed` holds for
both kernels.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Machines

open Silmaril.RiscV.LPS (FpuOps)

namespace FpuRun

variable {a b : FpuOps}

theorem star_trans {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {c₁ c₂ c₃ : Config isa} {tr₁ tr₂ : List Event}
    (s₁ : Star segs spec refused c₁ tr₁ c₂) (s₂ : Star segs spec refused c₂ tr₂ c₃) :
    Star segs spec refused c₁ (tr₁ ++ tr₂) c₃ := by
  induction s₁ with
  | refl => exact s₂
  | step s _ ih => rw [List.append_assoc]; exact .step s (ih s₂)

/-- A configuration of `riscvLpsWith a` read as one of `riscvLpsWith b`: the state types
coincide. -/
def cfg (c : Config (riscvLpsWith a)) : Config (riscvLpsWith b) := ⟨c.ms, c.model⟩

/-- `cfg` on step targets. -/
def stepTo : StepTo (riscvLpsWith a) → StepTo (riscvLpsWith b)
  | .next c => .next (cfg c)
  | .error => .error

/-- The two machines' accounted steps at a configuration agree whenever an instruction
step is possible there. -/
def AccAgree (a b : FpuOps) (segs : List Segment) (c : Config (riscvLpsWith a)) : Prop :=
  c.model.halted = none → c.ms.svcPending = none →
    accountStep (riscvLpsWith a) segs c.ms c.model =
      accountStep (riscvLpsWith b) segs c.ms c.model

/-- One step transfers between machines whose accounted steps agree. -/
theorem sstep_transfer {segs : List Segment} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {c : Config (riscvLpsWith a)} {evs : List Event}
    {st : StepTo (riscvLpsWith a)} (hacc : AccAgree a b segs c)
    (s : SStep segs spec refused c evs st) :
    SStep segs spec refused (cfg (b := b) c) evs (stepTo st) := by
  cases s with
  | instr h1 h2 h3 => exact .instr h1 h2 (by rw [← hacc h1 h2]; exact h3)
  | instrFault h1 h2 h3 => exact .instrFault h1 h2 (by rw [← hacc h1 h2]; exact h3)
  | instrUnmodeled h1 h2 h3 => exact .instrUnmodeled h1 h2 (by rw [← hacc h1 h2]; exact h3)
  | syscall h1 h2 h3 h4 h5 h6 => exact .syscall h1 h2 h3 h4 h5 h6
  | syscallMaterializationFault h1 h2 h3 h4 h5 h6 =>
    exact .syscallMaterializationFault h1 h2 h3 h4 h5 h6
  | exit h1 h2 h3 h4 h5 => exact .exit h1 h2 h3 h4 h5
  | killed h1 h2 h3 h4 => exact .killed h1 h2 h3 h4
  | syscallUnmodeled h1 h2 h3 => exact .syscallUnmodeled h1 h2 h3

/-- If the coarse machine's accounted step is modeled, the fine machine's is the same. -/
theorem accountStep_eq (h : FpuOps.Refines a b) (segs : List Segment)
    (ms : RiscV.LPS.MachineState) (model : Model)
    (hu : accountStep (riscvLpsWith b) segs ms model ≠ .unmodeled) :
    accountStep (riscvLpsWith a) segs ms model = accountStep (riscvLpsWith b) segs ms model := by
  by_cases hs : (riscvLpsWith b).step segs ms = .unmodeled
  · exfalso
    apply hu
    unfold accountStep
    simp only [show (riscvLpsWith b).reportsAccesses = true from rfl, Bool.not_true,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hs]
  · unfold accountStep
    rw [riscvLpsWith_refines h segs ms hs,
      show (riscvLpsWith a).reportsAccesses = true from rfl,
      show (riscvLpsWith b).reportsAccesses = true from rfl]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    generalize (riscvLpsWith b).step segs ms = r
    cases r with
    | ok r => simp only; cases materializeModelAccesses model r.accessed <;> rfl
    | fault => rfl
    | unmodeled => rfl

/-- Where the coarse machine is not unmodeled, the accounted steps agree (both ways). -/
theorem accAgree_of_not_unmodeledAt (h : FpuOps.Refines a b) {segs : List Segment}
    {spec : Sys SyscallEffect} {d : Config (riscvLpsWith b)}
    (hn : ¬ UnmodeledAt segs spec d) :
    AccAgree b a segs d ∧ AccAgree a b segs (cfg d) := by
  have key : d.model.halted = none → d.ms.svcPending = none →
      accountStep (riscvLpsWith a) segs d.ms d.model =
        accountStep (riscvLpsWith b) segs d.ms d.model := fun h1 h2 =>
    accountStep_eq h segs d.ms d.model fun hu => hn ⟨h1, .inl ⟨h2, hu⟩⟩
  exact ⟨fun h1 h2 => (key h1 h2).symm, key⟩

/-- The coarse machine never reaches an unmodeled configuration from `d`. -/
abbrev NoUnmod (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (d : Config (riscvLpsWith b)) : Prop :=
  ¬ ReachesUnmodeled segs spec refused d

theorem NoUnmod.here {segs : List Segment} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {d : Config (riscvLpsWith b)} (hn : NoUnmod segs spec refused d) :
    ¬ UnmodeledAt segs spec d := fun hu => hn ⟨[], d, .refl d, hu⟩

theorem NoUnmod.next {segs : List Segment} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {d d' : Config (riscvLpsWith b)} {evs : List Event}
    (hn : NoUnmod segs spec refused d) (s : SStep segs spec refused d evs (.next d')) :
    NoUnmod segs spec refused d' := fun ⟨tr, e, hs, hu⟩ => hn ⟨evs ++ tr, e, .step s hs, hu⟩

/-- A run of the fine machine is a run of the coarse one while the coarse one is modeled. -/
theorem star_fine_coarse (h : FpuOps.Refines a b) {segs : List Segment}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {c c' : Config (riscvLpsWith a)}
    {tr : List Event} (s : Star segs spec refused c tr c') :
    NoUnmod segs spec refused (cfg (b := b) c) →
      Star segs spec refused (cfg (b := b) c) tr (cfg c') := by
  induction s with
  | refl => intro _; exact .refl _
  | step s₁ _ ih =>
    intro hn
    have s₁' := sstep_transfer (b := b) (accAgree_of_not_unmodeledAt h hn.here).2 s₁
    exact .step s₁' (ih (hn.next s₁'))

/-- A run of the coarse machine is a run of the fine one while the coarse one is modeled. -/
theorem star_coarse_fine (h : FpuOps.Refines a b) {segs : List Segment}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {d d' : Config (riscvLpsWith b)}
    {tr : List Event} (s : Star segs spec refused d tr d') :
    NoUnmod segs spec refused d → Star segs spec refused (cfg (b := a) d) tr (cfg d') := by
  induction s with
  | refl => intro _; exact .refl _
  | step s₁ _ ih =>
    intro hn
    exact .step (sstep_transfer (accAgree_of_not_unmodeledAt h hn.here).1 s₁) (ih (hn.next s₁))

theorem allTracesError_fine_coarse (h : FpuOps.Refines a b) {segs : List Segment}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {c : Config (riscvLpsWith a)}
    (e : AllTracesError segs spec refused c) :
    NoUnmod segs spec refused (cfg (b := b) c) →
      AllTracesError segs spec refused (cfg (b := b) c) := by
  induction e with
  | intro hex _ ih =>
    intro hn
    have ag := accAgree_of_not_unmodeledAt h hn.here
    obtain ⟨evs, st, s⟩ := hex
    refine .intro ⟨evs, stepTo st, sstep_transfer ag.2 s⟩ fun evs' c' s' => ?_
    exact ih evs' (cfg c') (sstep_transfer ag.1 s') (hn.next s')

theorem allTracesError_coarse_fine (h : FpuOps.Refines a b) {segs : List Segment}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {d : Config (riscvLpsWith b)}
    (e : AllTracesError segs spec refused d) :
    NoUnmod segs spec refused d → AllTracesError segs spec refused (cfg (b := a) d) := by
  induction e with
  | intro hex _ ih =>
    intro hn
    have ag := accAgree_of_not_unmodeledAt h hn.here
    obtain ⟨evs, st, s⟩ := hex
    refine .intro ⟨evs, stepTo st, sstep_transfer ag.1 s⟩ fun evs' c' s' => ?_
    have s'' := sstep_transfer (b := b) ag.2 s'
    exact ih evs' (cfg c') s'' (hn.next s'')

end FpuRun

open FpuRun

/-- **FPU refinement on runs.** If `fine` refines `coarse` and the coarse machine's run never
reaches an unmodeled configuration, the two machines have the same behaviour. -/
theorem runWith_behaviorEquiv_of_modeled {fine coarse : FpuOps} (h : FpuOps.Refines fine coarse)
    (spec : Sys SyscallEffect) (refused : RefusalFilter) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (hm : ¬ (runWith (riscvLpsWith coarse) spec refused img lim en inp).unmodeled) :
    BehaviorEquiv (runWith (riscvLpsWith fine) spec refused img lim en inp)
      (runWith (riscvLpsWith coarse) spec refused img lim en inp) := by
  have hc : (initConfig (riscvLpsWith fine) img en lim inp : Config _) =
      cfg (initConfig (riscvLpsWith coarse) img en lim inp) := rfl
  have hn : NoUnmod img.segments spec refused (initConfig (riscvLpsWith coarse) img en lim inp) :=
    hm
  refine ⟨fun tr => ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, fun hu => absurd hu hm⟩⟩
  · rintro ⟨tr', c, s, hp⟩
    exact ⟨tr', cfg c, star_fine_coarse h s (by rw [hc] at *; exact hn), hp⟩
  · rintro ⟨tr', c, s, hp⟩
    exact ⟨tr', cfg c, star_coarse_fine h s hn, hp⟩
  · rintro ⟨tr, c, evs, s, se⟩
    have s' := star_fine_coarse (b := coarse) h s (by rw [hc] at *; exact hn)
    exact ⟨tr, cfg c, evs, s',
      sstep_transfer (st := .error) (accAgree_of_not_unmodeledAt h
        (NoUnmod.here fun hr => hn (by
          obtain ⟨tr₂, e, hs, hu⟩ := hr
          exact ⟨tr ++ tr₂, e, star_trans s' hs, hu⟩))).2 se⟩
  · rintro ⟨tr, c, evs, s, se⟩
    have hnc : NoUnmod img.segments spec refused c := fun ⟨tr₂, e, hs, hu⟩ =>
      hn ⟨tr ++ tr₂, e, star_trans s hs, hu⟩
    exact ⟨tr, cfg c, evs, star_coarse_fine h s hn,
      sstep_transfer (st := .error) (accAgree_of_not_unmodeledAt h hnc.here).1 se⟩
  · intro e
    exact allTracesError_fine_coarse h e (by rw [hc] at *; exact hn)
  · intro e
    exact allTracesError_coarse_fine h e hn
  · rintro ⟨tr, c, s, hu⟩
    have s' := star_fine_coarse (b := coarse) h s (by rw [hc] at *; exact hn)
    have hnc : NoUnmod img.segments spec refused (cfg (b := coarse) c) :=
      fun ⟨tr₂, e, hs, hu'⟩ => hn ⟨tr ++ tr₂, e, star_trans s' hs, hu'⟩
    obtain ⟨h1, hu⟩ := hu
    rcases hu with ⟨h2, hacc⟩ | ⟨x8, h2, hsys⟩
    · exact (hnc.here ⟨h1, .inl ⟨h2, (accAgree_of_not_unmodeledAt h hnc.here).2 h1 h2 ▸ hacc⟩⟩).elim
    · exact (hnc.here ⟨h1, .inr ⟨x8, h2, hsys⟩⟩).elim

/-- Every modeled run of `riscvLpsAgreed` has the behaviour of the literal LPS machine. -/
theorem riscvLps_behaviorEquiv_agreed (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hm : ¬ (runWith riscvLpsAgreed spec refused img lim en inp).unmodeled) :
    BehaviorEquiv (runWith riscvLps spec refused img lim en inp)
      (runWith riscvLpsAgreed spec refused img lim en inp) := by
  rw [← riscvLpsWith_lps]
  exact runWith_behaviorEquiv_of_modeled FpuOps.lps_refines_agreed spec refused img lim en inp hm

/-- Every modeled run of `riscvLpsAgreed` has the behaviour of `riscvLpsIeee`. -/
theorem riscvLpsIeee_behaviorEquiv_agreed (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hm : ¬ (runWith riscvLpsAgreed spec refused img lim en inp).unmodeled) :
    BehaviorEquiv (runWith riscvLpsIeee spec refused img lim en inp)
      (runWith riscvLpsAgreed spec refused img lim en inp) :=
  runWith_behaviorEquiv_of_modeled FpuOps.ieee_refines_agreed spec refused img lim en inp hm

end Silmaril.Process.LPS.Machines
