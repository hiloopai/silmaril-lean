module

public import Silmaril.Process.LPS.Equivalence
public import Silmaril.Process.LPS.OmniRun

/-!
# Compatibility names for the entry-inhabitation and omni lemmas

The anti-vacuity lemmas of LPS `Equivalence.v:558-659` (`image_brk_satisfiable_entry` and its
supporting facts) are translated in `Equivalence.lean`, and the omni judgments of LPS
`OmniRun.v` in `OmniRun.lean`. This module keeps the names an earlier partial port exported
(used by the x86 launch controls) as aliases of those translations, adds `imageWf_entry`,
`mustExitInAt_iff_exec` and the `Progress` rules, and nothing else. They concern the legacy
`ValidEntry`/`ValidInput` predicates, not the native x86 launch policy.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS

/-- Alias of `uns_zw`. -/
theorem uns_zw_of_bounds {z : Int} (nonneg : 0 ≤ z) (bound : z < 2 ^ 64) :
    uns (zw z) = z :=
  uns_zw nonneg bound

theorem imageWf_entry (isa : UserIsa) (img : Image) (wf : ImageWf isa img)
    (inp : ProcInput) (valid : ValidInput inp) : ∃ en, ValidEntry img en inp :=
  imageBrkSatisfiable_entry img inp valid wf.2.2

theorem imageBrkSatisfiable_empty : imageBrkSatisfiable [] = true := by decide

/-- The may-fail reading switches no family off. -/
theorem injectedFamilyOff_mayFail (i : SyscallInput) :
    injectedFamilyOff mayFailCfg i = false := by
  have all (family : SpuriousFamily) : familyMayFail mayFailCfg family = true := by
    cases family <;> rfl
  unfold injectedFamilyOff
  split
  · simp only [all, Bool.not_true]
  · rfl

theorem runScfg_mayFail_eq_run (isa : UserIsa) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    runScfg isa mayFailCfg img lim en inp = run isa img lim en inp := by
  rw [runScfg_mayFail]

theorem runScfgBudgetRefused_mayFail_iff (isa : UserIsa) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    RunScfgBudgetRefused isa mayFailCfg img lim en inp ↔
      RunBudgetRefused isa img lim en inp := by
  rw [runScfgBudgetRefused_mayFail]

namespace Omni

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- Alias of `MExec` (LPS `OmniRun.v:177` `mexec`). -/
abbrev FiniteExec (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter) :
    Config isa → List Event → Outcome isa → Prop :=
  MExec segs spec refused

theorem step_from_running {c : Config isa} {evs : List Event} {target : StepTo isa}
    (step : SStep segs spec refused c evs target) : c.model.halted = none :=
  sstep_from_running step

theorem star_finiteExec {c c' : Config isa} {trace suffix : List Event} {outcome : Outcome isa}
    (tracePrefix : Star segs spec refused c trace c')
    (tail : FiniteExec segs spec refused c' suffix outcome) :
    FiniteExec segs spec refused c (trace ++ suffix) outcome :=
  star_mexec tracePrefix tail

theorem finiteExec_error_star {c final : Config isa} {trace : List Event}
    (run : FiniteExec segs spec refused c trace (.error final)) :
    ∃ tracePrefix evs, trace = tracePrefix ++ evs ∧ Star segs spec refused c tracePrefix final ∧
      SStep segs spec refused final evs .error :=
  mexec_error_star run

theorem reachesError_iff_finiteExec (c : Config isa) :
    ReachesError segs spec refused c ↔
      ∃ trace final, FiniteExec segs spec refused c trace (.error final) := by
  constructor
  · rintro ⟨tracePrefix, final, evs, star, step⟩
    exact ⟨tracePrefix ++ evs, final, star_finiteExec star (.error step)⟩
  · rintro ⟨trace, final, run⟩
    obtain ⟨tracePrefix, evs, _, star, step⟩ := finiteExec_error_star run
    exact ⟨tracePrefix, final, evs, star, step⟩

theorem Exec.consequence {c : Config isa} {post post' : Post isa}
    (run : Exec segs spec refused c post)
    (weaken : ∀ trace outcome, post trace outcome → post' trace outcome) :
    Exec segs spec refused c post' :=
  exec_conseq run weaken

theorem Exec.realizes {c : Config isa} {post : Post isa} (run : Exec segs spec refused c post) :
    ∃ trace outcome, FiniteExec segs spec refused c trace outcome ∧ post trace outcome :=
  exec_realizes run

theorem Exec.sound {c : Config isa} {post : Post isa} {trace : List Event}
    {outcome : Outcome isa} (run : Exec segs spec refused c post)
    (finite : FiniteExec segs spec refused c trace outcome) : post trace outcome :=
  exec_sound run finite

/-- Normal exit with an allowed code; a signal death is excluded explicitly. -/
def ExitsIn (allowed : List Word) : Post isa := fun _ outcome =>
  match outcome with
  | .halt final =>
    ∃ code, final.model.halted = some code ∧ code ∈ allowed ∧ final.model.killedBy = none
  | .error _ => False

/-- The existing must-exit proposition is the corresponding terminating omni proof. -/
theorem mustExitInAt_iff_exec (allowed : List Word) (c : Config isa) :
    MustExitInAt segs spec refused allowed c ↔ Exec segs spec refused c (ExitsIn allowed) := by
  constructor
  · intro must
    induction must with
    | halted halted member unkilled =>
      exact .halt (by rw [halted]; exact Option.some_ne_none _)
        ⟨_, halted, member, unkilled⟩
    | running running progress noError _ ih =>
      exact .step running progress (fun evs error => (noError evs error).elim)
        (fun evs next step => (ih evs next step).consequence (fun _ _ h => h))
  · intro run
    generalize postEq : ExitsIn allowed = post at run
    induction run with
    | halt _ satisfied =>
      rw [← postEq] at satisfied
      obtain ⟨code, halted, member, unkilled⟩ := satisfied
      exact .halted halted member unkilled
    | step running progress errors _ ih =>
      refine .running running progress ?_ ?_
      · intro evs error
        have contradiction := errors evs error
        rw [← postEq] at contradiction
        exact contradiction
      · intro evs next step
        apply ih evs next step
        rw [← postEq]
        rfl

end Omni

/-! A concrete terminating path refutes the universal "all traces error"
observation. These reusable rules need the actual process transition relation,
not merely the existence of a syntactic exit instruction. -/

namespace Progress

variable {isa : UserIsa} {segments : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter} {initial final : Config isa}

/-- With no lazy mappings, reporting an access does not change the model or
consume additional backing, independently of the access list's size. -/
theorem materializeModelAccesses_noLazy (model : Model) (accesses : List (Word × Nat))
    (noLazy : model.vmLazy = []) :
    materializeModelAccesses model accesses = some model := by
  rcases model with ⟨fd, ⟨maps, lazy, pages⟩, io, fsys, proc, lim, time, profile⟩
  change lazy = [] at noLazy
  subst lazy
  simp [materializeModelAccesses, materializeAccesses, newlyMaterializedPages,
    pageInRanges, Model.vmLazy, Model.vmMaterialized, Model.withVmBacking]

theorem accountStep_of_noLazy (state next : isa.State) (model : Model)
    (accesses : List (Word × Nat)) (noLazy : model.vmLazy = [])
    (step : isa.step segments state = .ok ⟨next, accesses⟩) :
    accountStep isa segments state model = .ok (next, model) := by
  simp [accountStep, noLazy, step, materializeModelAccesses_noLazy model accesses noLazy]

theorem allTracesError_next {events : List Event}
    (errors : AllTracesError segments spec refused initial)
    (step : SStep segments spec refused initial events (.next final)) :
    AllTracesError segments spec refused final := by
  cases errors with
  | intro _ every => exact every events final step

theorem allTracesError_star {trace : List Event}
    (errors : AllTracesError segments spec refused initial)
    (path : Star segments spec refused initial trace final) :
    AllTracesError segments spec refused final := by
  induction path with
  | refl => exact errors
  | step step _ ih => exact ih (allTracesError_next errors step)

theorem halted_not_allTracesError (halted : final.model.halted ≠ none) :
    ¬ AllTracesError segments spec refused final := by
  intro errors
  cases errors with
  | intro progress _ =>
    obtain ⟨_, _, step⟩ := progress
    exact halted (Omni.step_from_running step)

theorem halting_path_not_allTracesError {trace : List Event}
    (path : Star segments spec refused initial trace final)
    (halted : final.model.halted ≠ none) :
    ¬ AllTracesError segments spec refused initial := by
  intro errors
  exact halted_not_allTracesError halted (allTracesError_star errors path)

end Progress

end Silmaril.Process.LPS
