module

public import Silmaril.Process.LPS.Probes.Kit

/-! # Probe kit: syscalls with one deterministic return

`Kit.lean` steps the syscalls whose result is chosen by the environment (a
channel `write`, any nonempty prefix) or that halt (`exit`). Error paths and
bookkeeping calls instead have exactly one outcome: a return value `ret`, no
memory effect and no events, possibly with a changed model (`close` removes the
descriptor). `Probe.sstep_ret_iff` characterizes every successor of such a call,
and `Probe.exec_ret` / `Probe.run_ret` are its `Omni.Exec` and `Run` rules.

The outcome lemmas below are the reference arms on the paths the I/O probes
take, each a reading of one branch of LPS `Sys/Fs/ReadWrite.v` or
`Sys/Fs/Open.v`:

* `close_ok_iff`, `close_badf_iff`: `close_spec` of an open and of a closed
  descriptor (`Open.v:1387`);
* `write_badf_iff`, `write_efault_iff`, `write_zero_iff`: `write_spec` of a
  closed descriptor, of a channel whose source buffer has no readable first byte
  (`-EFAULT`), and of a channel with count 0 (`ReadWrite.v:909`);
* `read_badf_iff`, `read_eof_iff`: `read_spec` of a closed descriptor and of
  stdin at end of file (`ReadWrite.v:345`).

The tactic `probe_ret lemma` applies the rule with the outcome lemma and
discharges the side conditions by evaluation.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Machines.X86Launch

namespace Probe

variable (P : Probe) {refused : RefusalFilter}

theorem resume_plain (core : Silmaril.X86.State) (n : Word) (other : n ≠ 158) (ret : Word) :
    x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, P.mem0⟩, some n⟩ (mkEffect ret [] [])) =
      ⟨⟨resume core ret, P.mem0⟩, none⟩ :=
  P.resume_effect core n other ret []

/-- A pending call with exactly one outcome: it returns `ret` and leaves the
model `model'`, with no memory effect and no events. -/
theorem sstep_ret_iff {core : Silmaril.X86.State} {n : Word} {model model' : Model} {ret : Word}
    (other : n ≠ 158) (running : model.halted = none) (running' : model'.halted = none)
    (lazy' : model'.vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔ outcome = .ok (mkEffect ret [] []) model' [])
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core (some n) model) evs target ↔
      ¬ refused (P.sysIn core n) model (mkEffect ret [] []) ∧ evs = [] ∧
        target = .next (P.cfg (resume core ret) none model') := by
  have materialized := Progress.materializeModelAccesses_noLazy model'
    (syscallEffectAccesses (mkEffect ret [] [])) lazy'
  have unkilled : model'.killedBy = none := by
    simp [Model.killedBy, Model.halted] at running' ⊢
    simp [running']
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s notRefused _ m =>
      cases p
      cases (outcomes _).mp s
      rw [materialized] at m
      cases m
      refine ⟨notRefused, rfl, ?_⟩
      rw [P.resume_plain core n other]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      cases (outcomes _).mp s
      rw [materialized] at m
      cases m
    | exit _ p s h _ =>
      cases p
      cases (outcomes _).mp s
      rw [running'] at h
      cases h
    | killed _ p s k =>
      cases p
      cases (outcomes _).mp s
      rw [unkilled] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      cases (outcomes _).mp s
  · rintro ⟨notRefused, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := n)
      (ms := (⟨⟨core, P.mem0⟩, some n⟩ : X86State)) running rfl ((outcomes _).mpr rfl)
      notRefused running' materialized
    rwa [P.resume_plain core n other] at step

theorem exec_ret {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model model' : Model} {ret : Word}
    (other : n ≠ 158) (running : model.halted = none) (running' : model'.halted = none)
    (lazy' : model'.vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔ outcome = .ok (mkEffect ret [] []) model' [])
    (rest : Omni.Exec P.segs spec noFilter (P.cfg (resume core ret) none model') post) :
    Omni.Exec P.segs spec noFilter (P.cfg core (some n) model) post :=
  Omni.exec_of_unique (events := []) running
    (fun evs target => (P.sstep_ret_iff other running running' lazy' outcomes evs target).trans
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun refusal => refusal, h⟩⟩) rest

theorem run_ret {core : Silmaril.X86.State} {n : Word} {model model' : Model} {ret : Word}
    {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (other : n ≠ 158) (running : model.halted = none) (running' : model'.halted = none)
    (lazy' : model'.vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔ outcome = .ok (mkEffect ret [] []) model' [])
    (accepted : ¬ refused (P.sysIn core n) model (mkEffect ret [] []))
    (rest : Run P.segs spec refused (P.cfg (resume core ret) none model') calls trace outcome) :
    Run P.segs spec refused (P.cfg core (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, P.mem0⟩, some n⟩ : X86State), some ret⟩ :: calls)
      trace outcome := by
  have run := Run.sys (c' := P.cfg (resume core ret) none model') rfl
    ((P.sstep_ret_iff other running running' lazy' outcomes _ _).mpr ⟨accepted, rfl, rfl⟩) rest
  rw [P.returned_resume ret running'] at run
  exact run

end Probe

/-! ## Reference arms with one outcome -/

section Arms

variable (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)

theorem close_ok_iff (number : input.sysno = 3)
    (clear : NativeX86.All.boundarySuspect 3 input = false) {entry : FdEntry}
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some entry) :
    spec input model outcome ↔
      outcome = .ok (mkEffect 0 [] []) (model.withFds (fdRemove model.fds (fd32 (input.arg 0)))) [] := by
  rw [dispatches_close.spec_iff (by rw [number]; rfl) clear model outcome]
  cases outcome <;> simp [closeSpec, bind, Sys.bind, Sys.getModel, Sys.modify, lookup, retOnly, Sys.pure]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨c, a, b⟩, fun ⟨c, a, b⟩ => ⟨⟨a, b⟩, c⟩⟩

theorem close_badf_iff (number : input.sysno = 3)
    (clear : NativeX86.All.boundarySuspect 3 input = false)
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = none) :
    spec input model outcome ↔ outcome = .ok (mkEffect (errnoRet EBADF) [] []) model [] := by
  rw [dispatches_close.spec_iff (by rw [number]; rfl) clear model outcome]
  cases outcome <;> simp [closeSpec, bind, Sys.bind, Sys.getModel, lookup, errRet, retOnly, Sys.pure]

theorem write_badf_iff (number : input.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 input = false)
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = none) :
    spec input model outcome ↔ outcome = .ok (mkEffect (errnoRet EBADF) [] []) model [] := by
  rw [dispatches_write.spec_iff (by rw [number]; rfl) clear model outcome]
  cases outcome <;> simp [writeSpecX86, writeSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, errRet, retOnly,
    Sys.pure]

/-- A channel write whose source buffer has no readable first byte is `-EFAULT`. -/
theorem write_efault_iff (number : input.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 input = false) {ch : Word}
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (modeled : modeledRwRangeWith accessOkbX86 (input.arg 1) (input.arg 2) = true) (count : input.arg 2 ≠ 0)
    (unreadable : writeSource input.mem (input.arg 1) (input.arg 2) = []) :
    spec input model outcome ↔ outcome = .ok (mkEffect (errnoRet EFAULT) [] []) model [] := by
  have zeroCh : wIs0 ch = false := by simpa [wIs0] using nonzero
  have zeroCount : wIs0 (input.arg 2) = false := by simpa [wIs0] using count
  rw [dispatches_write.spec_iff (by rw [number]; rfl) clear model outcome]
  change writeSpecX86 (fd32 (input.arg 0)) (input.arg 1) (input.arg 2) _ model outcome ↔ _
  cases outcome <;> simp [writeSpecX86, writeSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, zeroCh, modeled,
    zeroCount, unreadable, errRet, retOnly, Sys.pure]

/-- A channel write of count 0 returns 0 when the (empty) range is accessible. -/
theorem write_zero_iff (number : input.sysno = 1)
    (clear : NativeX86.All.boundarySuspect 1 input = false) {ch : Word}
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (modeled : modeledRwRangeWith accessOkbX86 (input.arg 1) (input.arg 2) = true) (count : input.arg 2 = 0)
    (accessible : accessOkbX86 (input.arg 1) (uns (input.arg 2)) = true) :
    spec input model outcome ↔ outcome = .ok (mkEffect 0 [] []) model [] := by
  have zeroCh : wIs0 ch = false := by simpa [wIs0] using nonzero
  have zeroCount : wIs0 (input.arg 2) = true := by simpa [wIs0] using count
  rw [dispatches_write.spec_iff (by rw [number]; rfl) clear model outcome]
  change writeSpecX86 (fd32 (input.arg 0)) (input.arg 1) (input.arg 2) _ model outcome ↔ _
  cases outcome <;> simp [writeSpecX86, writeSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, zeroCh, modeled,
    zeroCount, accessible, accessOkZeroWith, retOnly, Sys.pure]

theorem read_badf_iff (number : input.sysno = 0)
    (clear : NativeX86.All.boundarySuspect 0 input = false)
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = none) :
    spec input model outcome ↔ outcome = .ok (mkEffect (errnoRet EBADF) [] []) model [] := by
  rw [dispatches_read.spec_iff (by rw [number]; rfl) clear model outcome]
  cases outcome <;> simp [readSpecX86, readSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, errRet, retOnly,
    Sys.pure]

/-- A read of stdin at end of file returns 0 (whatever the count: a count of 0
also returns 0). -/
theorem read_eof_iff (number : input.sysno = 0)
    (clear : NativeX86.All.boundarySuspect 0 input = false)
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some (.channel 0))
    (accessible : accessOkbX86 (input.arg 1) (uns (input.arg 2)) = true)
    (eof : model.stdin.atEof = true) :
    spec input model outcome ↔ outcome = .ok (mkEffect 0 [] []) model [] := by
  rw [dispatches_read.spec_iff (by rw [number]; rfl) clear model outcome]
  cases outcome <;> simp [readSpecX86, readSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, wIs0, accessible,
    eof, retOnly, Sys.pure]

end Arms

/-- `probe_ret lemma`: the pending syscall has the single outcome `lemma`
describes (one of the `…_iff` arms above); its side conditions are evaluated. -/
macro "probe_ret " outcomes:term:max : tactic =>
  `(tactic| ((first
    | apply Probe.exec_ret
    | apply Probe.run_ret) <;> (try (intro _; apply $outcomes)) <;> probe_sides))

end Silmaril.Process.LPS.Probes
