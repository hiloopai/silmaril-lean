module

public import Silmaril.Process.LPS.Run

/-!
# LPS in Lean: omni-big-step judgments over the one-step relation

Translation of LPS `LinuxProcessSem/OmniRun.v` (upstream commit `f1006fe8`, 798 lines). The
file adds three judgments over `SStep` and proves each observable of a run (`Behavior`)
equivalent to one of them, so an obligation may be stated in either form:

* `Exec c Q` (inductive): every maximal execution from `c` is finite and its trace and
  outcome satisfy `Q` (LPS `exec`). It generalises `AllTracesError` and `MustExitInAt` to an
  arbitrary postcondition, and keeps the progress premise, so a stuck configuration satisfies
  no `Exec` (`stuck_no_exec`).
* `Coexec c Q` (coinductive, no progress premise): every maximal execution that ends satisfies
  `Q` (LPS `coexec`). Negated `ReachesError` and `ReachesUnmodeled` are `Coexec` judgments
  (`never_errors_iff`, `covered_iff`). A stuck configuration satisfies every `Coexec`
  (`stuck_coexec_any`), the reading LPS's `reaches_error` and `obs_trace` already take.
* `Cosafe c P` (coinductive): every finite prefix of every execution satisfies `P` (LPS
  `cosafe`). Trace equivalence is agreement on all prefix-closed `Cosafe` postconditions
  (`obs_equiv_iff_cosafe`); `Exec`/`Coexec` agreement is strictly weaker (a run that writes a
  byte and then diverges against one that only diverges), so they carry the exit-code, error
  and coverage facts and `Cosafe` carries the traces.

LPS states the judgments over its one relation `sstep`. Here, as everywhere in this
translation, the step relation is `SStep segs spec refused` for a syscall table `spec` and a
refusal filter `refused` (`noFilter` is LPS's `sstep`, `spuriousRefusalCfg spec cfg` its
`sstep_cfg cfg`), and the configuration is over any `UserIsa`. LPS's coinductive types are
Lean `coinductive` predicates (greatest fixed points); LPS's `cofix` proofs are proofs by the
generated `coinduct` principle.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Omni

open Silmaril.Process.LPS

variable {isa : UserIsa}

/-- LPS `OmniRun.v:113` `outcome`: how a maximal finite execution ends, halted, or erroring
from the carried configuration. -/
inductive Outcome (isa : UserIsa) where
  | halt (c : Config isa)
  | error (c : Config isa)

/-- LPS `OmniRun.v:117` `post`. -/
abbrev Post (isa : UserIsa) := List Event → Outcome isa → Prop

/-- LPS `OmniRun.v:119` `is_error`. -/
def IsError : Outcome isa → Prop
  | .halt _ => False
  | .error _ => True

section WithSegs

variable (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)

/-- LPS `OmniRun.v:123` `errors`. -/
def errors : Post isa := fun _ o => IsError o

/-- LPS `OmniRun.v:125` `never_errors`. -/
def neverErrors : Post isa := fun _ o => ¬ IsError o

/-- LPS `OmniRun.v:129` `covered`: `Equivalence.modeled`'s postcondition, an error is allowed
but not one taken from a configuration the model declines to interpret. -/
def covered : Post isa := fun _ o =>
  match o with
  | .halt _ => True
  | .error c => ¬ UnmodeledAt segs spec c

/-- LPS `OmniRun.v:136` `uncovered`. -/
def uncovered : Post isa := fun _ o =>
  match o with
  | .halt _ => False
  | .error c => UnmodeledAt segs spec c

/-- LPS `OmniRun.v:150` `exits_with`: a death by signal is not an exit. -/
def exitsWith (code : Word) : Post isa := fun _ o =>
  match o with
  | .halt c => c.model.halted = some code ∧ c.model.killedBy = none
  | .error _ => False

/-- LPS `OmniRun.v:157` `never_errors_covered`. -/
theorem neverErrors_covered (tr : List Event) (o : Outcome isa) (h : neverErrors tr o) :
    covered segs spec tr o := by
  cases o with
  | halt c => trivial
  | error c => exact absurd trivial h

/-- LPS `OmniRun.v:160` `exits_with_never_errors`. -/
theorem exitsWith_neverErrors (code : Word) (tr : List Event) (o : Outcome isa)
    (h : exitsWith code tr o) : neverErrors tr o := by
  cases o with
  | halt c => exact id
  | error c => exact h.elim

variable {segs spec refused}

/-- LPS `OmniRun.v:168` `sstep_from_running`: every step leaves a non-halted configuration. -/
theorem sstep_from_running {c : Config isa} {evs : List Event} {st : StepTo isa}
    (h : SStep segs spec refused c evs st) : c.model.halted = none := by
  cases h <;> assumption

/-- LPS `Run.v:821` `unmodeled_at_sstep_error`: an unmodelled configuration takes the error
transition. -/
theorem unmodeledAt_sstep_error {c : Config isa} (h : UnmodeledAt segs spec c) :
    ∃ evs, SStep segs spec refused c evs .error := by
  obtain ⟨ms, model⟩ := c
  obtain ⟨hh, ⟨hsvc, hacc⟩ | ⟨x8, hsvc, hspec⟩⟩ := h
  · exact ⟨[], .instrUnmodeled hh hsvc hacc⟩
  · exact ⟨[], .syscallUnmodeled hh hsvc hspec⟩

/-! ## Maximal executions: the "may" side -/

variable (segs spec refused) in
/-- LPS `OmniRun.v:177` `mexec`: one maximal finite execution, its trace and how it ended. -/
inductive MExec : Config isa → List Event → Outcome isa → Prop where
  | halt {c} : c.model.halted ≠ none → MExec c [] (.halt c)
  | error {c evs} : SStep segs spec refused c evs .error → MExec c evs (.error c)
  | next {c evs c' tr o} : SStep segs spec refused c evs (.next c') → MExec c' tr o →
      MExec c (evs ++ tr) o

/-- LPS `OmniRun.v:189` `star_mexec`. -/
theorem star_mexec {c c' : Config isa} {tr tr' : List Event} {o : Outcome isa}
    (hs : Star segs spec refused c tr c') (hm : MExec segs spec refused c' tr' o) :
    MExec segs spec refused c (tr ++ tr') o := by
  induction hs with
  | refl => exact hm
  | step hss _ ih => rw [List.append_assoc]; exact .next hss (ih hm)

/-- LPS `OmniRun.v:198` `mexec_halt_star`. -/
theorem mexec_halt_star {c c' : Config isa} {tr : List Event}
    (hm : MExec segs spec refused c tr (.halt c')) :
    Star segs spec refused c tr c' ∧ c'.model.halted ≠ none := by
  generalize ho : (Outcome.halt c' : Outcome isa) = o at hm
  induction hm with
  | halt hh => cases ho; exact ⟨.refl _, hh⟩
  | error => cases ho
  | next hss _ ih => obtain ⟨hs, hh⟩ := ih ho; exact ⟨.step hss hs, hh⟩

/-- LPS `OmniRun.v:210` `mexec_error_star`. -/
theorem mexec_error_star {c c' : Config isa} {tr : List Event}
    (hm : MExec segs spec refused c tr (.error c')) :
    ∃ tr₁ evs, tr = tr₁ ++ evs ∧ Star segs spec refused c tr₁ c' ∧
      SStep segs spec refused c' evs .error := by
  generalize ho : (Outcome.error c' : Outcome isa) = o at hm
  induction hm with
  | halt => cases ho
  | error hss => cases ho; exact ⟨[], _, rfl, .refl _, hss⟩
  | next hss _ ih =>
    obtain ⟨tr₁, evs', rfl, hs, hss'⟩ := ih ho
    exact ⟨_ ++ tr₁, evs', (List.append_assoc _ _ _).symm, .step hss hs, hss'⟩

/-- LPS `OmniRun.v:226` `reaches_error_iff_may`: some maximal execution errors. -/
theorem reachesError_iff_may (c : Config isa) :
    ReachesError segs spec refused c ↔ ∃ tr o, MExec segs spec refused c tr o ∧ errors tr o := by
  constructor
  · rintro ⟨tr, c₂, evs, hs, hss⟩
    exact ⟨tr ++ evs, .error c₂, star_mexec hs (.error hss), trivial⟩
  · rintro ⟨tr, o, hm, he⟩
    cases o with
    | halt => exact he.elim
    | error c' =>
      obtain ⟨tr₁, evs, -, hs, hss⟩ := mexec_error_star hm
      exact ⟨tr₁, c', evs, hs, hss⟩

/-- LPS `OmniRun.v:240` `reaches_unmodeled_iff_may`. -/
theorem reachesUnmodeled_iff_may (c : Config isa) :
    ReachesUnmodeled segs spec refused c ↔
      ∃ tr o, MExec segs spec refused c tr o ∧ uncovered segs spec tr o := by
  constructor
  · rintro ⟨tr, c', hs, hun⟩
    obtain ⟨evs, hss⟩ := unmodeledAt_sstep_error (refused := refused) hun
    exact ⟨tr ++ evs, .error c', star_mexec hs (.error hss), hun⟩
  · rintro ⟨tr, o, hm, hun⟩
    cases o with
    | halt => exact hun.elim
    | error c' =>
      obtain ⟨tr₁, evs, -, hs, -⟩ := mexec_error_star hm
      exact ⟨tr₁, c', hs, hun⟩

/-! ## Terminating omni-exec (inductive) -/

variable (segs spec refused) in
/-- LPS `OmniRun.v:257` `exec`: every maximal execution is finite and satisfies `Q`. -/
inductive Exec : Config isa → Post isa → Prop where
  | halt {c Q} : c.model.halted ≠ none → Q [] (.halt c) → Exec c Q
  | step {c Q} : c.model.halted = none → (∃ evs st, SStep segs spec refused c evs st) →
      (∀ evs, SStep segs spec refused c evs .error → Q evs (.error c)) →
      (∀ evs c', SStep segs spec refused c evs (.next c') →
        Exec c' (fun tr o => Q (evs ++ tr) o)) →
      Exec c Q

/-- LPS `OmniRun.v:271` `exec_conseq`: the postcondition may be weakened. -/
theorem exec_conseq {c : Config isa} {Q Q' : Post isa} (h : Exec segs spec refused c Q)
    (himp : ∀ tr o, Q tr o → Q' tr o) : Exec segs spec refused c Q' := by
  induction h generalizing Q' with
  | halt hh hq => exact .halt hh (himp _ _ hq)
  | step hh hprog herr _ ih =>
    exact .step hh hprog (fun evs hs => himp _ _ (herr evs hs))
      fun evs c' hs => ih evs c' hs fun tr o => himp _ _

/-- LPS `OmniRun.v:282` `exec_halted`. -/
theorem exec_halted {c : Config isa} {Q : Post isa} (hh : c.model.halted ≠ none)
    (hq : Q [] (.halt c)) : Exec segs spec refused c Q :=
  .halt hh hq

/-- LPS `OmniRun.v:288` `exec_step_only`: a configuration with exactly one transition. -/
theorem exec_step_only {c c₁ : Config isa} {Q : Post isa} {evs₁ : List Event}
    (hs : SStep segs spec refused c evs₁ (.next c₁))
    (honly : ∀ evs st, SStep segs spec refused c evs st → evs = evs₁ ∧ st = .next c₁)
    (hex : Exec segs spec refused c₁ (fun tr o => Q (evs₁ ++ tr) o)) :
    Exec segs spec refused c Q := by
  refine .step (sstep_from_running hs) ⟨_, _, hs⟩ (fun evs he => ?_) (fun evs c' hs' => ?_)
  · cases (honly _ _ he).2
  · obtain ⟨rfl, h⟩ := honly _ _ hs'
    cases h
    exact hex

/-- LPS `OmniRun.v:305` `exec_star`: an omni judgment survives any `Star` prefix. -/
theorem exec_star {c c' : Config isa} {Q : Post isa} {tr : List Event}
    (hex : Exec segs spec refused c Q) (hs : Star segs spec refused c tr c') :
    Exec segs spec refused c' (fun tr' o => Q (tr ++ tr') o) := by
  induction hs generalizing Q with
  | refl => exact exec_conseq hex fun tr o h => by simpa using h
  | step hss _ ih =>
    cases hex with
    | halt hh _ => exact absurd (sstep_from_running hss) hh
    | step _ _ _ hnext =>
      exact exec_conseq (ih (hnext _ _ hss)) fun tr' o h => by simpa [List.append_assoc] using h

/-- LPS `OmniRun.v:320` `exec_sound`: every maximal execution satisfies the postcondition. -/
theorem exec_sound {c : Config isa} {Q : Post isa} (h : Exec segs spec refused c Q)
    {tr : List Event} {o : Outcome isa} (hm : MExec segs spec refused c tr o) : Q tr o := by
  induction h generalizing tr o with
  | halt hh hq =>
    cases hm with
    | halt => exact hq
    | error hss => exact absurd (sstep_from_running hss) hh
    | next hss => exact absurd (sstep_from_running hss) hh
  | step hh _ herr _ ih =>
    cases hm with
    | halt hh' => exact absurd hh hh'
    | error hss => exact herr _ hss
    | next hss hm' => exact ih _ _ hss hm'

/-- LPS `OmniRun.v:336` `exec_realizes`: at least one maximal execution exists, so `Exec` never
holds vacuously. -/
theorem exec_realizes {c : Config isa} {Q : Post isa} (h : Exec segs spec refused c Q) :
    ∃ tr o, MExec segs spec refused c tr o ∧ Q tr o := by
  induction h with
  | halt hh hq => exact ⟨[], _, .halt hh, hq⟩
  | step _ hprog herr _ ih =>
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | next c' =>
      obtain ⟨tr, o, hm, hq⟩ := ih evs c' hss
      exact ⟨evs ++ tr, o, .next hss hm, hq⟩
    | error => exact ⟨evs, _, .error hss, herr _ hss⟩

/-- LPS `OmniRun.v:352` `stuck_no_exec`: a stuck non-halted configuration satisfies no `Exec`. -/
theorem stuck_no_exec {c : Config isa} (hh : c.model.halted = none)
    (hstuck : ∀ evs st, ¬ SStep segs spec refused c evs st) (Q : Post isa) :
    ¬ Exec segs spec refused c Q := by
  intro h
  cases h with
  | halt hh' => exact hh' hh
  | step _ hprog => obtain ⟨evs, st, hs⟩ := hprog; exact hstuck _ _ hs

/-- LPS `OmniRun.v:367` `exec_errors_all_traces_error`. -/
theorem exec_errors_allTracesError {c : Config isa} {Q : Post isa}
    (h : Exec segs spec refused c Q) (himp : ∀ tr o, Q tr o → IsError o) :
    AllTracesError segs spec refused c := by
  induction h with
  | halt _ hq => exact (himp _ _ hq).elim
  | step _ hprog _ _ ih =>
    exact .intro hprog fun evs c' hs => ih evs c' hs fun tr o hq => himp _ _ hq

/-- LPS `OmniRun.v:377` `all_traces_error_iff`. -/
theorem allTracesError_iff (c : Config isa) :
    AllTracesError segs spec refused c ↔ Exec segs spec refused c errors := by
  constructor
  · intro h
    induction h with
    | intro hprog _ ih =>
      obtain ⟨evs, st, hs⟩ := hprog
      exact .step (sstep_from_running hs) ⟨evs, st, hs⟩ (fun _ _ => trivial) ih
  · intro h
    exact exec_errors_allTracesError h fun _ _ h => h

/-- LPS `OmniRun.v:392` `exec_no_error`. -/
theorem exec_no_error {c : Config isa} (hex : Exec segs spec refused c neverErrors) :
    ¬ ReachesError segs spec refused c := by
  rintro ⟨tr, c₂, evs, hs, hss⟩
  exact exec_sound hex (star_mexec hs (.error hss)) trivial

/-- LPS `OmniRun.v:403` `exec_obs_iff`: an exact trace postcondition characterises the whole
trace set. -/
theorem exec_obs_iff {c : Config isa} {full : List Event}
    (hex : Exec segs spec refused c (fun tr o => tr = full ∧ ¬ IsError o)) (tr : List Event) :
    ObsTrace segs spec refused c tr ↔ tr <+: full := by
  constructor
  · rintro ⟨tr', c', hs, hp⟩
    obtain ⟨tr'', o, -, heq, -⟩ := exec_realizes (exec_star hex hs)
    rw [← heq]
    exact hp.trans (List.prefix_append _ _)
  · intro hp
    obtain ⟨tr', o, hm, rfl, hno⟩ := exec_realizes hex
    cases o with
    | error => exact (hno trivial).elim
    | halt c' => exact ⟨tr', c', (mexec_halt_star hm).1, hp⟩

/-! ## Possibly-diverging omni-exec (coinductive), no progress premise -/

variable (segs spec refused) in
/-- LPS `OmniRun.v:424` `coexec`: every maximal execution that ends satisfies `Q`. -/
coinductive Coexec : Config isa → Post isa → Prop where
  | halt {c : Config isa} {Q : Post isa} : c.model.halted ≠ none → Q [] (.halt c) → Coexec c Q
  | step {c : Config isa} {Q : Post isa} : c.model.halted = none →
      (∀ evs, SStep segs spec refused c evs .error → Q evs (.error c)) →
      (∀ evs c', SStep segs spec refused c evs (.next c') →
        Coexec c' (fun tr o => Q (evs ++ tr) o)) →
      Coexec c Q

/-- LPS `OmniRun.v:436` `exec_coexec`. -/
theorem exec_coexec {c : Config isa} {Q : Post isa} (h : Exec segs spec refused c Q) :
    Coexec segs spec refused c Q := by
  induction h with
  | halt hh hq => exact .halt _ _ _ hh hq
  | step hh _ herr _ ih => exact .step _ _ _ hh herr ih

/-- LPS `OmniRun.v:445` `coexec_conseq`. -/
theorem coexec_conseq {c : Config isa} {Q Q' : Post isa} (h : Coexec segs spec refused c Q)
    (himp : ∀ tr o, Q tr o → Q' tr o) : Coexec segs spec refused c Q' := by
  refine Coexec.coinduct segs spec refused
    (fun c Q' => ∃ Q, Coexec segs spec refused c Q ∧ ∀ tr o, Q tr o → Q' tr o) ?_ c Q'
    ⟨Q, h, himp⟩
  rintro c Q' ⟨Q, h, himp⟩
  cases h with
  | halt hh hq => exact .inl ⟨hh, himp _ _ hq⟩
  | step hh herr hnext =>
    exact .inr ⟨hh, fun evs he => himp _ _ (herr evs he),
      fun evs c' hs => ⟨_, hnext evs c' hs, fun tr o => himp _ _⟩⟩

/-- LPS `OmniRun.v:456` `coexec_step_only`. -/
theorem coexec_step_only {c c₁ : Config isa} {Q : Post isa} {evs₁ : List Event}
    (hs : SStep segs spec refused c evs₁ (.next c₁))
    (honly : ∀ evs st, SStep segs spec refused c evs st → evs = evs₁ ∧ st = .next c₁)
    (hco : Coexec segs spec refused c₁ (fun tr o => Q (evs₁ ++ tr) o)) :
    Coexec segs spec refused c Q := by
  refine .step _ _ _ (sstep_from_running hs) (fun evs he => ?_) (fun evs c' hs' => ?_)
  · cases (honly _ _ he).2
  · obtain ⟨rfl, h⟩ := honly _ _ hs'
    cases h
    exact hco

/-- LPS `OmniRun.v:470` `coexec_star`. -/
theorem coexec_star {c c' : Config isa} {Q : Post isa} {tr : List Event}
    (hex : Coexec segs spec refused c Q) (hs : Star segs spec refused c tr c') :
    Coexec segs spec refused c' (fun tr' o => Q (tr ++ tr') o) := by
  induction hs generalizing Q with
  | refl => exact coexec_conseq hex fun tr o h => by simpa using h
  | step hss _ ih =>
    cases hex with
    | halt hh _ => exact absurd (sstep_from_running hss) hh
    | step _ _ hnext =>
      exact coexec_conseq (ih (hnext _ _ hss)) fun tr' o h => by simpa [List.append_assoc] using h

/-- LPS `OmniRun.v:486` `coexec_sound`: every maximal execution that ends satisfies the
postcondition. -/
theorem coexec_sound {c : Config isa} {tr : List Event} {o : Outcome isa}
    (hm : MExec segs spec refused c tr o) {Q : Post isa} (hco : Coexec segs spec refused c Q) :
    Q tr o := by
  induction hm generalizing Q with
  | halt hh =>
    cases hco with
    | halt _ hq => exact hq
    | step hh' => exact absurd hh' hh
  | error hss =>
    cases hco with
    | halt hh => exact absurd (sstep_from_running hss) hh
    | step _ herr => exact herr _ hss
  | next hss _ ih =>
    cases hco with
    | halt hh => exact absurd (sstep_from_running hss) hh
    | step _ _ hnext => exact ih (hnext _ _ hss)

/-- LPS `OmniRun.v:502` `stuck_coexec_any`: a stuck configuration satisfies every `Coexec`. -/
theorem stuck_coexec_any {c : Config isa} (hh : c.model.halted = none)
    (hstuck : ∀ evs st, ¬ SStep segs spec refused c evs st) (Q : Post isa) :
    Coexec segs spec refused c Q :=
  .step _ _ _ hh (fun _ hs => (hstuck _ _ hs).elim) fun _ _ hs => (hstuck _ _ hs).elim

/-- LPS `OmniRun.v:514` `coexec_no_error`. -/
theorem coexec_no_error {c : Config isa} (hco : Coexec segs spec refused c neverErrors) :
    ¬ ReachesError segs spec refused c := by
  rintro ⟨tr, c₂, evs, hs, hss⟩
  exact coexec_sound (star_mexec hs (.error hss)) hco trivial

/-- LPS `OmniRun.v:524` `no_error_coexec`. -/
theorem no_error_coexec {c : Config isa} (h : ¬ ReachesError segs spec refused c) :
    Coexec segs spec refused c neverErrors := by
  refine Coexec.coinduct segs spec refused
    (fun c Q => Q = neverErrors ∧ ¬ ReachesError segs spec refused c) ?_ c _ ⟨rfl, h⟩
  rintro c Q ⟨rfl, h⟩
  cases hh : c.model.halted with
  | some code => exact .inl ⟨by simp, fun h => h⟩
  | none =>
    refine .inr ⟨rfl, fun evs hs _ => h ⟨[], c, evs, .refl _, hs⟩, fun evs c' hs => ⟨rfl, ?_⟩⟩
    rintro ⟨tr, c₂, evs₂, hs₂, hss₂⟩
    exact h ⟨evs ++ tr, c₂, evs₂, .step hs hs₂, hss₂⟩

/-- LPS `OmniRun.v:539` `never_errors_iff`. -/
theorem neverErrors_iff (c : Config isa) :
    ¬ ReachesError segs spec refused c ↔ Coexec segs spec refused c neverErrors :=
  ⟨no_error_coexec, coexec_no_error⟩

/-- LPS `OmniRun.v:545` `coexec_covered`. -/
theorem coexec_covered {c : Config isa} (hco : Coexec segs spec refused c (covered segs spec)) :
    ¬ ReachesUnmodeled segs spec refused c := by
  rintro ⟨tr, c', hs, hun⟩
  obtain ⟨evs, hss⟩ := unmodeledAt_sstep_error (refused := refused) hun
  exact coexec_sound (star_mexec hs (.error hss)) hco hun

/-- LPS `OmniRun.v:554` `no_unmodeled_coexec`. -/
theorem no_unmodeled_coexec {c : Config isa} (h : ¬ ReachesUnmodeled segs spec refused c) :
    Coexec segs spec refused c (covered segs spec) := by
  refine Coexec.coinduct segs spec refused
    (fun c Q => Q = covered segs spec ∧ ¬ ReachesUnmodeled segs spec refused c) ?_ c _ ⟨rfl, h⟩
  rintro c Q ⟨rfl, h⟩
  cases hh : c.model.halted with
  | some code => exact .inl ⟨by simp, trivial⟩
  | none =>
    refine .inr ⟨rfl, fun evs _ hun => h ⟨[], c, .refl _, hun⟩, fun evs c' hs => ⟨rfl, ?_⟩⟩
    rintro ⟨tr, c₂, hs₂, hun⟩
    exact h ⟨evs ++ tr, c₂, .step hs hs₂, hun⟩

/-- LPS `OmniRun.v:569` `covered_iff`. -/
theorem covered_iff (c : Config isa) :
    ¬ ReachesUnmodeled segs spec refused c ↔ Coexec segs spec refused c (covered segs spec) :=
  ⟨no_unmodeled_coexec, coexec_covered⟩

/-! ## The progress-carrying alternative, kept for a local reversal -/

variable (segs spec refused) in
/-- LPS `OmniRun.v:580` `coexec_progress`: `Coexec` with `Exec`'s progress premise, so a stuck
configuration refutes it. -/
coinductive CoexecProgress : Config isa → Post isa → Prop where
  | halt {c : Config isa} {Q : Post isa} : c.model.halted ≠ none → Q [] (.halt c) →
      CoexecProgress c Q
  | step {c : Config isa} {Q : Post isa} : c.model.halted = none →
      (∃ evs st, SStep segs spec refused c evs st) →
      (∀ evs, SStep segs spec refused c evs .error → Q evs (.error c)) →
      (∀ evs c', SStep segs spec refused c evs (.next c') →
        CoexecProgress c' (fun tr o => Q (evs ++ tr) o)) →
      CoexecProgress c Q

/-- LPS `OmniRun.v:593` `coexec_progress_implies`. -/
theorem coexecProgress_implies {c : Config isa} {Q : Post isa}
    (h : CoexecProgress segs spec refused c Q) : Coexec segs spec refused c Q := by
  refine Coexec.coinduct segs spec refused (fun c Q => CoexecProgress segs spec refused c Q)
    ?_ c Q h
  rintro c Q h
  cases h with
  | halt hh hq => exact .inl ⟨hh, hq⟩
  | step hh _ herr hnext => exact .inr ⟨hh, herr, hnext⟩

/-- LPS `OmniRun.v:604` `stuck_not_coexec_progress`. -/
theorem stuck_not_coexecProgress {c : Config isa} (hh : c.model.halted = none)
    (hstuck : ∀ evs st, ¬ SStep segs spec refused c evs st) (Q : Post isa) :
    ¬ CoexecProgress segs spec refused c Q := by
  intro h
  cases h with
  | halt hh' => exact hh' hh
  | step _ hprog => obtain ⟨evs, st, hs⟩ := hprog; exact hstuck _ _ hs

/-! ## Prefix safety (coinductive): what `ObsTrace` is -/

variable (segs spec refused) in
/-- LPS `OmniRun.v:622` `cosafe`: every finite prefix of every execution satisfies `P`. -/
coinductive Cosafe : Config isa → (List Event → Prop) → Prop where
  | intro {c : Config isa} {P : List Event → Prop} : P [] →
      (∀ evs c', SStep segs spec refused c evs (.next c') → Cosafe c' (fun tr => P (evs ++ tr))) →
      Cosafe c P

/-- LPS `OmniRun.v:629` `cosafe_star`. -/
theorem cosafe_star {c c' : Config isa} {P : List Event → Prop} {tr : List Event}
    (hsafe : Cosafe segs spec refused c P) (hs : Star segs spec refused c tr c') : P tr := by
  induction hs generalizing P with
  | refl => cases hsafe with | intro hnil _ => exact hnil
  | step hss _ ih => cases hsafe with | intro _ hnext => exact ih (hnext _ _ hss)

/-- LPS `OmniRun.v:639` `star_cosafe`. -/
theorem star_cosafe {c : Config isa} {P : List Event → Prop}
    (hall : ∀ tr c', Star segs spec refused c tr c' → P tr) : Cosafe segs spec refused c P := by
  refine Cosafe.coinduct segs spec refused
    (fun c P => ∀ tr c', Star segs spec refused c tr c' → P tr) ?_ c P hall
  intro c P hall
  exact ⟨hall [] c (.refl _), fun evs c' hs tr c'' hs' => hall _ _ (.step hs hs')⟩

/-- LPS `OmniRun.v:649` `prefix_closed`. -/
def PrefixClosed (P : List Event → Prop) : Prop := ∀ tr tr', P tr → tr' <+: tr → P tr'

/-- LPS `Run.v:504` `obs_trace_prefix_closed`. -/
theorem obsTrace_prefixClosed (c : Config isa) : PrefixClosed (ObsTrace segs spec refused c) :=
  fun _ _ ⟨tr', c', hs, hp⟩ hp' => ⟨tr', c', hs, hp'.trans hp⟩

/-- LPS `OmniRun.v:657` `cosafe_obs_iff`: on a prefix-closed `P`, "every observable trace
satisfies `P`" is `Cosafe`. -/
theorem cosafe_obs_iff (c : Config isa) {P : List Event → Prop} (hpc : PrefixClosed P) :
    Cosafe segs spec refused c P ↔ ∀ tr, ObsTrace segs spec refused c tr → P tr := by
  constructor
  · rintro hsafe tr ⟨tr', c', hs, hp⟩
    exact hpc _ _ (cosafe_star hsafe hs) hp
  · intro hall
    exact star_cosafe fun tr c' hs => hall tr ⟨tr, c', hs, List.prefix_refl _⟩

end WithSegs

section TwoImages

variable {spec : Sys SyscallEffect} {refused : RefusalFilter}

/-- LPS `OmniRun.v:673` `obs_equiv_iff_refinement`: each side's trace set is a prefix
postcondition the other side satisfies. -/
theorem obs_equiv_iff_refinement (segs₁ : List Segment) (c₁ : Config isa) (segs₂ : List Segment)
    (c₂ : Config isa) :
    (∀ tr, ObsTrace segs₁ spec refused c₁ tr ↔ ObsTrace segs₂ spec refused c₂ tr) ↔
      Cosafe segs₁ spec refused c₁ (ObsTrace segs₂ spec refused c₂) ∧
        Cosafe segs₂ spec refused c₂ (ObsTrace segs₁ spec refused c₁) := by
  have h₂ := obsTrace_prefixClosed (segs := segs₂) (spec := spec) (refused := refused) c₂
  have h₁ := obsTrace_prefixClosed (segs := segs₁) (spec := spec) (refused := refused) c₁
  rw [cosafe_obs_iff (segs := segs₁) c₁ h₂, cosafe_obs_iff (segs := segs₂) c₂ h₁]
  exact ⟨fun h => ⟨fun tr ht => (h tr).1 ht, fun tr ht => (h tr).2 ht⟩,
    fun ⟨h₁₂, h₂₁⟩ tr => ⟨h₁₂ tr, h₂₁ tr⟩⟩

/-- LPS `OmniRun.v:689` `obs_equiv_iff_cosafe`: trace-set equality is "the two configurations
satisfy the same prefix-closed postconditions". -/
theorem obs_equiv_iff_cosafe (segs₁ : List Segment) (c₁ : Config isa) (segs₂ : List Segment)
    (c₂ : Config isa) :
    (∀ tr, ObsTrace segs₁ spec refused c₁ tr ↔ ObsTrace segs₂ spec refused c₂ tr) ↔
      ∀ P, PrefixClosed P →
        (Cosafe segs₁ spec refused c₁ P ↔ Cosafe segs₂ spec refused c₂ P) := by
  constructor
  · intro heq P hpc
    rw [cosafe_obs_iff (segs := segs₁) (spec := spec) (refused := refused) c₁ hpc,
      cosafe_obs_iff (segs := segs₂) (spec := spec) (refused := refused) c₂ hpc]
    exact ⟨fun h tr ho => h tr ((heq tr).2 ho), fun h tr ho => h tr ((heq tr).1 ho)⟩
  · intro hall
    refine (obs_equiv_iff_refinement segs₁ c₁ segs₂ c₂).2 ⟨?_, ?_⟩
    · refine (hall _ (obsTrace_prefixClosed (segs := segs₂) (spec := spec)
        (refused := refused) c₂)).2 ?_
      exact star_cosafe fun tr c' hs => ⟨tr, c', hs, List.prefix_refl _⟩
    · refine (hall _ (obsTrace_prefixClosed (segs := segs₁) (spec := spec)
        (refused := refused) c₁)).1 ?_
      exact star_cosafe fun tr c' hs => ⟨tr, c', hs, List.prefix_refl _⟩

end TwoImages

/-! ## Run-level judgments

LPS writes these as a `match` on the image and the entry so that `cbn` exposes
`init_config`; here they are stated directly over `initConfig`, which is the same
configuration `runWith` uses. -/

section RunLevel

variable (isa) (spec : Sys SyscallEffect) (refused : RefusalFilter)

/-- LPS `OmniRun.v:716` `omni_run`. -/
def omniRun (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : Post isa) : Prop :=
  Exec img.segments spec refused (initConfig isa img en lim inp) Q

/-- LPS `OmniRun.v:723` `omni_corun`. -/
def omniCorun (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : Post isa) :
    Prop :=
  Coexec img.segments spec refused (initConfig isa img en lim inp) Q

/-- LPS `OmniRun.v:730` `omni_cosafe`. -/
def omniCosafe (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (P : List Event → Prop) : Prop :=
  Cosafe img.segments spec refused (initConfig isa img en lim inp) P

/-- LPS `OmniRun.v:738` `omni_may`: some maximal execution satisfies `Q`. -/
def omniMay (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : Post isa) : Prop :=
  ∃ tr o, MExec img.segments spec refused (initConfig isa img en lim inp) tr o ∧ Q tr o

/-! ### Compat: the four fields of `runWith`, each unconditional -/

/-- LPS `OmniRun.v:750` `bh_all_errors_iff`. -/
theorem bh_allErrors_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (runWith isa spec refused img lim en inp).allErrors ↔
      omniRun isa spec refused img lim en inp errors :=
  allTracesError_iff _

/-- LPS `OmniRun.v:757` `bh_errors_iff`. -/
theorem bh_errors_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ (runWith isa spec refused img lim en inp).errors ↔
      omniCorun isa spec refused img lim en inp neverErrors :=
  neverErrors_iff _

/-- LPS `OmniRun.v:764` `bh_errors_may_iff`. -/
theorem bh_errors_may_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (runWith isa spec refused img lim en inp).errors ↔
      omniMay isa spec refused img lim en inp errors :=
  reachesError_iff_may _

/-- LPS `OmniRun.v:771` `bh_unmodeled_iff`. -/
theorem bh_unmodeled_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ (runWith isa spec refused img lim en inp).unmodeled ↔
      omniCorun isa spec refused img lim en inp (covered img.segments spec) :=
  covered_iff _

/-- LPS `OmniRun.v:779` `bh_unmodeled_may_iff`. -/
theorem bh_unmodeled_may_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (runWith isa spec refused img lim en inp).unmodeled ↔
      omniMay isa spec refused img lim en inp (uncovered img.segments spec) :=
  reachesUnmodeled_iff_may _

/-- LPS `OmniRun.v:790` `bh_traces_iff`: trace-set equality of two runs is agreement on every
prefix-closed postcondition. -/
theorem bh_traces_iff (img₁ : Image) (lim₁ : Int) (en₁ : ExecEntry) (img₂ : Image) (lim₂ : Int)
    (en₂ : ExecEntry) (inp : ProcInput) :
    (∀ tr, (runWith isa spec refused img₁ lim₁ en₁ inp).traces tr ↔
        (runWith isa spec refused img₂ lim₂ en₂ inp).traces tr) ↔
      ∀ P, PrefixClosed P →
        (omniCosafe isa spec refused img₁ lim₁ en₁ inp P ↔
          omniCosafe isa spec refused img₂ lim₂ en₂ inp P) :=
  obs_equiv_iff_cosafe _ _ _ _

end RunLevel

end Silmaril.Process.LPS.Omni
