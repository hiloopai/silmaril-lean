module

public import Silmaril.X86.SegVC
public import Silmaril.Apps.Sha256sum.X86Sys.Silent
public import Silmaril.Apps.Sha256sum.X86Sys8

/-!
# The segment VC generator on the `X86Sys` process machine

`Isa.sys r11Of` is the `SegVC.Isa` whose machine is the internal (`tau`) steps of
`X86Sys.x86Machine r11Of`: the extended instruction set, executed by the Linux process
model, with system calls and exits excluded (a `syscall` site is a *stop* of a segment, not
a step). A `ret` is an ordinary step here: the process has no designated exit.

* `Isa.sys` and its law (`step_of`), from `Ext.step_of_loaded` and
  `X86Sys.step_of_ext_retired`;
* `tauRun_of_reaches`: a `SegVC` run is an `X86Sys.TauRun`, hence (`TauRun.reach`,
  `TauRun.exec_iff`) a `Sys.Reach` segment with the kernel unchanged, which composes with the
  system-call steps of the surrounding proof;
* **the call bridge as a VC rule** (`Call.ofReturns`): any callee with an `X86.Ext.Returns`
  contract (for every designated exit it is given, such as `Binary.compress_contract`)
  is a contracted call of the generator. Its body is never executed symbolically.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys

open Silmaril.Apps.Sha256sum.Sys
open Silmaril.X86 (State MState Word)
open Silmaril.X86.SegVC (Isa Call)
open Silmaril.Machine.Execution (run Reaches)

/-- The internal steps of the process machine, as a partial function. -/
def tauStep (r11Of : Core → Word) (s : XState) : Option XState :=
  match (x86Machine r11Of).step s with
  | .tau t => some t
  | _ => none

theorem tauStep_eq_some {r11Of : Core → Word} {s t : XState} :
    tauStep r11Of s = some t ↔ (x86Machine r11Of).step s = .tau t := by
  cases h : (x86Machine r11Of).step s with
  | tau u =>
    simp only [tauStep, h]
    exact ⟨fun e => by cases e; rfl, fun e => by cases e; rfl⟩
  | _ => simp [tauStep, h]

/-- An internal step keeps the process unfaulted. -/
theorem faulted_of_tau {r11Of : Core → Word} {s t : XState} (hs : s.faulted = false)
    (h : (x86Machine r11Of).step s = .tau t) : t.faulted = false := by
  simp only [x86Machine, step, hs, Bool.false_eq_true, ite_false] at h
  split at h
  · cases h; rfl
  · cases h
  · split at h
    · cases h
    · cases h
    · cases h
      unfold brkStep
      split
      · exact hs
      · split <;> exact hs
    · cases h

/-- The internal step at an instruction that **retires** (no system call, no `brk`): the
step of every segment between two system calls. It mentions no `r11`. -/
def rStep (s : XState) : Option XState :=
  if s.faulted then none else
  match Process.CLI.X86Linux.step s.core s.memory with
  | .retired c m => some { s with core := c, memory := m }
  | _ => none

theorem rStep_eq_some {s t : XState} :
    rStep s = some t ↔ s.faulted = false ∧ ∃ c m,
      Process.CLI.X86Linux.step s.core s.memory = .retired c m ∧
        t = { s with core := c, memory := m } := by
  unfold rStep
  cases hf : s.faulted
  · simp only [Bool.false_eq_true, ite_false, true_and]
    cases h : Process.CLI.X86Linux.step s.core s.memory with
    | retired c m =>
      simp only [Option.some.injEq, Process.CLI.Step.retired.injEq]
      exact ⟨fun e => ⟨c, m, ⟨rfl, rfl⟩, e.symm⟩,
        fun ⟨_, _, ⟨e1, e2⟩, e⟩ => by subst e1 e2; exact e.symm⟩
    | fault _ => simp
    | syscall _ => simp
  · simp

/-- A retiring step is an internal step of `x86Machine r11Of`, for every `r11Of`. -/
theorem tauStep_of_rStep {r11Of : Core → Word} {s t : XState} (h : rStep s = some t) :
    tauStep r11Of s = some t := by
  obtain ⟨hf, c, m, hs, rfl⟩ := rStep_eq_some.mp h
  rw [tauStep_eq_some]
  simp [x86Machine, step, hf, hs]

/-- A retiring `X86.Ext` step of an unfaulted process is an `rStep`. -/
theorem rStep_of_ext_retired {exit : Word} {s : XState} {final : MState}
    (running : s.faulted = false) (retired : X86.Ext.step exit (toExtState s) = .retired final) :
    rStep s = some (withExtState s final) :=
  rStep_eq_some.mpr ⟨running, _, _, Process.CLI.X86Linux.step_of_ext_retired retired, rfl⟩

theorem rStep_of_ext_returned {exit : Word} {s : XState} {final : MState}
    (running : s.faulted = false) (returned : X86.Ext.step exit (toExtState s) = .returned final) :
    rStep s = some (withExtState s final) :=
  rStep_eq_some.mpr ⟨running, _, _, Process.CLI.X86Linux.step_of_ext_returned returned, rfl⟩

/-- An `X86.Ext` call that returns is a run of retiring steps (no system call). -/
theorem rReaches_of_ext_run {exit : Word} {n : Nat} {s : XState} {final : MState}
    (running : s.faulted = false)
    (executed : run (X86.Ext.stepOpt exit) n (toExtState s) = some final) :
    Reaches rStep s (withExtState s final) := by
  induction n generalizing s with
  | zero =>
    simp only [Silmaril.Machine.Execution.run_zero, Option.some.injEq] at executed
    subst final
    simpa using (Reaches.refl _ s : Reaches rStep s s)
  | succ n ih =>
    simp only [Silmaril.Machine.Execution.run_succ] at executed
    cases head : X86.Ext.stepOpt exit (toExtState s) with
    | none => simp [head] at executed
    | some mid =>
      simp only [head, Option.bind_some] at executed
      have first := rStep_of_ext_retired running (X86.Ext.stepOpt_eq_some_iff.mp head)
      have rest := ih (s := withExtState s mid) running (by simpa using executed)
      have r1 : Reaches rStep s (withExtState s mid) := ⟨1, by simp [run, first]⟩
      simpa only [withExtState_withExtState] using r1.trans rest

theorem rReaches_of_ext_returns {exit : Word} {s : XState} {final : MState}
    (running : s.faulted = false) (returned : X86.Ext.Returns exit (toExtState s) final) :
    Reaches rStep s (withExtState s final) := by
  obtain ⟨n, mid, executed, last⟩ := returned
  have first := rReaches_of_ext_run running executed
  have lastStep := rStep_of_ext_returned (s := withExtState s mid) running (by simpa using last)
  simpa only [withExtState_withExtState] using first.trans ⟨1, by simp [run, lastStep]⟩

/-- The `X86Sys` process machine's retiring steps, as a `SegVC` instance. -/
@[reducible] def Isa.sys (_r11Of : Core → Word) : Isa XState :=
  Isa.ofExt XState.core XState.memory (fun s c m => { s with core := c, memory := m })
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => True)
    (fun s => s.faulted = false)
    rStep (fun hs h => by obtain ⟨_, _, _, _, rfl⟩ := rStep_eq_some.mp h; exact hs) (by
      intro s base code o l i c m hlv hl hrip hfit hdec hx _
      have hlen : l = i.length := (X86.Ext.decode_length hdec).1
      subst hlen
      have hstep : X86.Ext.step (c.rip + 1) (toExtState s) = .retired ⟨c, m⟩ := by
        rw [X86.Ext.step_of_loaded (m := toExtState s) hl hrip hfit hdec]
        change (match X86.Ext.exec i s.core s.memory with
          | .ok core memory =>
            if i = X86.Ext.Instr.ret ∧ core.rip = c.rip + 1 then
              X86.Ext.Outcome.returned ⟨core, memory⟩
            else .retired ⟨core, memory⟩
          | .dataFault => .dataFault i
          | .divideError => .divideFault
          | .undefinedCondition cc => .undefinedCondition cc
          | .trap => .trapped) = _
        rw [hx]
        have : ¬ (i = X86.Ext.Instr.ret ∧ c.rip = c.rip + 1) := fun h => by
          have := h.2; bv_omega
        simp only [this, ite_false]
      exact rStep_of_ext_retired hlv hstep)

/-- A `SegVC` run of the process machine is a silent segment. -/
theorem tauRun_of_reaches {r11Of : Core → Word} {s t : XState}
    (h : Reaches (Isa.sys r11Of).step s t) : ∃ n, TauRun r11Of n s t := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  induction n generalizing s with
  | zero => cases Option.some.inj hn; exact .refl
  | succ n ih =>
    simp only [Silmaril.Machine.Execution.run_succ] at hn
    cases hs : rStep s with
    | none => simp [hs] at hn
    | some mid =>
      simp only [hs, Option.bind_some] at hn
      exact .cons (tauStep_eq_some.mp (tauStep_of_rStep hs)) (ih hn)

/-- **The call bridge, as a VC rule.** A callee entered in a live state whose
`X86.Ext.Returns` run (to the exit address the contract names) ends in a final core and
memory satisfying `post` is a contracted call of the process machine: the run is a sequence
of internal steps (`ext_returns_tauRun`), with no system call. -/
def Call.ofReturns (r11Of : Core → Word) (pre : XState → Prop) (post : XState → XState → Prop)
    (contract : ∀ s, s.faulted = false → pre s →
      ∃ exit fin, X86.Ext.Returns exit (toExtState s) fin ∧ post s (withExtState s fin)) :
    Call (Isa.sys r11Of) where
  pre := pre
  post := post
  runs := by
    intro s hlv hpre
    obtain ⟨exit, fin, hret, hpost⟩ := contract s hlv hpre
    exact ⟨_, rReaches_of_ext_returns hlv hret, hpost⟩

/-- A segment proved by the generator, inside a completed process execution: the run up to
the stop may be dropped (the same calls, replies and exit status). -/
theorem exec_iff_of_reaches {r11Of : Core → Word} {s t : XState}
    (h : Reaches (Isa.sys r11Of).step s t) {E : Env} {k : KState}
    {events : List Event} {status : Nat} :
    Exec (x86Machine r11Of) E s k events status ↔ Exec (x86Machine r11Of) E t k events status := by
  obtain ⟨n, hn⟩ := tauRun_of_reaches h
  exact hn.exec_iff

/-! ## Transport to the `Ext8` machine

A segment proved over `Isa.sys` (instructions of `X86.Ext`) is a run of the 8-bit variant's
process machine `x86Machine8` too: every internal step of the original is one of the
variant (`step8_of_step`). Segments that contain the new 8-bit forms need an instance with
the variant's decoder (`X86.Ext8.decode`); its law is open. -/

/-- The internal steps of `x86Machine8`. -/
def tau8Step (r11Of : Core → Word) (s : XState) : Option XState :=
  match step8 r11Of s with
  | .tau t => some t
  | _ => none

theorem tau8Step_of_tauStep {r11Of : Core → Word} {s t : XState} (h : tauStep r11Of s = some t) :
    tau8Step r11Of s = some t := by
  have h' := tauStep_eq_some.mp h
  have h8 : step8 r11Of s = .tau t := step8_of_step h' (by intro e; cases e)
  simp [tau8Step, h8]

/-- The retiring step of the `Ext8` variant (`GnuSha256sum.retStep`, by definition). -/
def rStep8 (s : XState) : Option XState :=
  if s.faulted then none else
  match Process.CLI.X86Linux8.step s.core s.memory with
  | .retired c m => some { s with core := c, memory := m }
  | _ => none

theorem rStep8_of_rStep {s t : XState} (h : rStep s = some t) : rStep8 s = some t := by
  obtain ⟨hf, c, m, hs, rfl⟩ := rStep_eq_some.mp h
  have h8 : Process.CLI.X86Linux8.step s.core s.memory = .retired c m := by
    rcases Process.CLI.X86Linux8.step_eq_or_unmodeled s.core s.memory with e | e
    · rw [e, hs]
    · rw [hs] at e; cases e
  simp [rStep8, hf, h8]

/-- **A segment proved over `Isa.sys` is a run of the `Ext8` variant's retiring steps** (the
silent steps of `GStep`). -/
theorem reaches_rStep8 {s t : XState} (h : Reaches rStep s t) : Reaches rStep8 s t := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  exact Silmaril.Machine.Execution.run_simulates rStep rStep8 (· = ·)
    (fun a b a' hab ha => ⟨a', by subst hab; exact rStep8_of_rStep ha, rfl⟩) n rfl hn
    |>.elim fun t' ⟨ht, he⟩ => he ▸ ht

/-- A `SegVC` run over `Isa.sys` is a run of the `Ext8` process machine. -/
theorem reaches8_of_reaches {r11Of : Core → Word} {s t : XState}
    (h : Reaches (tauStep r11Of) s t) : Reaches (tau8Step r11Of) s t := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  exact Silmaril.Machine.Execution.run_simulates (tauStep r11Of) (tau8Step r11Of) (· = ·)
    (fun a b a' hab ha => ⟨a', by subst hab; exact tau8Step_of_tauStep ha, rfl⟩) n rfl hn
    |>.elim fun t' ⟨ht, he⟩ => he ▸ ht

end Silmaril.Apps.Sha256sum.X86Sys
