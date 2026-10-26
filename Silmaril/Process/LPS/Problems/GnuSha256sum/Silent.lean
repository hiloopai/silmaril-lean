module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysModel
public import Silmaril.Machine.Execution

/-! # Silent segments are independent of `r11` (the `r11` bridge)

The VC and lift tracks prove segments over the internal (`tau`) steps of
`X86Sys.x86Machine8 r11Of`, for every function `r11Of : Core → Word`; the middle model `GStep`
lets `r11` be *any* value at each system-call return (LPS fills it from RFLAGS with oracle
flags, which depend on a counter, not on the core). A function cannot reproduce such a choice in
general: two returns from equal cores may get different `r11` values.

The mismatch only concerns returns, and a segment between two system calls contains none.
This file makes that precise.

* `retStep`: the internal step at an instruction that retires. It mentions no `r11`.
* `step8_of_retStep` (`∀ r11Of`) and `retStep_of_step8` (off a `syscall`): `retStep` is the
  internal step of `x86Machine8 r11Of` on every non-`syscall` instruction, for every `r11Of`.
  The only other internal step is `brk`, which `GStep` does not have.
* `run_ret_of_run8`: an `n`-step internal run of `x86Machine8 r11Of`, for any one `r11Of`,
  that visits no `syscall` before its last state is a `retStep` run, and the converse
  `run8_of_run_ret` holds for every `r11Of`. So a segment result proved `∀ r11Of` (or for one
  `r11Of`) whose stops include every `syscall` site holds over `retStep` unchanged.
* `gstep_of_retStep`, `gstep_retStep_cases`: `GStep`'s silent steps are exactly `retStep`, with
  the kernel and exit status unchanged; at a retiring instruction no other step exists.
* `leads_of_run`: a `retStep` run from an `Ok` state to a state at cut `Post` is a `Leads`
  segment of `GStep` (`Ok` is kept by silent steps: it constrains only the history, the exit
  status and the fault flag).

So the silent parts of the `sys-total` proof can be taken from `∀ r11Of` results as they are;
`r11` enters only at the system-call steps, which the glue handles with `GStep.call` for an
arbitrary `r11` (the segment after a return must not assume anything about `r11`).

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.X86Sys (XState Core)
open Silmaril.Machine.Execution (Reaches run_succ)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-! ## The `r11`-free internal step -/

/-- The internal step at a retiring instruction (no system call, so no `r11`). -/
def retStep (s : XState) : Option XState :=
  if s.faulted then none else
  match CLI.X86Linux8.step s.core s.memory with
  | .retired c m => some { s with core := c, memory := m }
  | _ => none

/-- The internal steps of `x86Machine8 r11Of`, as a partial function (the VC track's
`tau8Step`). -/
def tau8 (r11Of : Core → Silmaril.X86.Word) (s : XState) : Option XState :=
  match Silmaril.Apps.Sha256sum.X86Sys.step8 r11Of s with
  | .tau t => some t
  | _ => none

/-- The state is at a `syscall` instruction. -/
def Trap (s : XState) : Prop := s.memory.fetchBytes s.core.rip.toNat 2 = some [0x0f, 0x05]

theorem retStep_eq_some {s t : XState} :
    retStep s = some t ↔ s.faulted = false ∧ ∃ c m,
      CLI.X86Linux8.step s.core s.memory = .retired c m ∧
        t = { s with core := c, memory := m } := by
  unfold retStep
  cases hf : s.faulted
  · simp only [Bool.false_eq_true, ite_false, true_and]
    cases h : CLI.X86Linux8.step s.core s.memory with
    | retired c m =>
      simp only [Option.some.injEq, CLI.Step.retired.injEq]
      exact ⟨fun e => ⟨c, m, ⟨rfl, rfl⟩, e.symm⟩,
        fun ⟨_, _, ⟨e1, e2⟩, e⟩ => by subst e1 e2; exact e.symm⟩
    | fault _ => simp
    | syscall _ => simp
  · simp

theorem trap_iff_syscall {s : XState} :
    Trap s ↔ ∃ c, CLI.X86Linux8.step s.core s.memory = .syscall c := by
  constructor
  · intro trap
    refine ⟨{ s.core with rip := s.core.rip + 2 }, ?_⟩
    unfold CLI.X86Linux8.step
    rw [ite_eq_left (by simpa [Trap, CLI.X86Linux.syscallBytes] using trap)]
  · rintro ⟨c, h⟩
    unfold CLI.X86Linux8.step at h
    split at h
    · rename_i trap; simpa [Trap, CLI.X86Linux.syscallBytes] using trap
    · split at h
      · cases h
      · cases h
      · revert h
        cases Silmaril.X86.Ext.exec _ _ _ _ <;> simp [CLI.X86Linux.execResult]
      · revert h
        cases Silmaril.X86.Ext8.execNew _ _ _ _ <;> simp [CLI.X86Linux.execResult]

/-- **`r11` independence.** At a retiring instruction the internal step of `x86Machine8 r11Of`
is `retStep`, whatever `r11Of` is. -/
theorem step8_of_retStep {s t : XState} (h : retStep s = some t)
    (r11Of : Core → Silmaril.X86.Word) :
    Silmaril.Apps.Sha256sum.X86Sys.step8 r11Of s = .tau t := by
  obtain ⟨hf, c, m, hs, rfl⟩ := retStep_eq_some.mp h
  simp [Silmaril.Apps.Sha256sum.X86Sys.step8, Silmaril.Apps.Sha256sum.X86Sys.stepWith, hf, hs]

theorem tau8_of_retStep {s t : XState} (h : retStep s = some t)
    (r11Of : Core → Silmaril.X86.Word) : tau8 r11Of s = some t := by
  simp [tau8, step8_of_retStep h r11Of]

/-- Off a `syscall`, an internal step of `x86Machine8 r11Of` is `retStep`. -/
theorem retStep_of_tau8 {r11Of : Core → Silmaril.X86.Word} {s t : XState}
    (h : tau8 r11Of s = some t) (notTrap : ¬ Trap s) : retStep s = some t := by
  unfold tau8 at h
  split at h
  · rename_i u step
    cases h
    unfold Silmaril.Apps.Sha256sum.X86Sys.step8 Silmaril.Apps.Sha256sum.X86Sys.stepWith at step
    cases hf : s.faulted
    · rw [hf] at step
      simp only [Bool.false_eq_true, ite_false] at step
      cases hs : CLI.X86Linux8.step s.core s.memory with
      | retired c m =>
        rw [hs] at step
        cases step
        exact retStep_eq_some.mpr ⟨hf, c, m, hs, by rw [hf]⟩
      | fault _ => rw [hs] at step; cases step
      | syscall c => exact absurd (trap_iff_syscall.mpr ⟨c, hs⟩) notTrap
    · rw [hf] at step; cases step
  · cases h

/-- **Runs transfer** (one `r11Of` suffices): an internal run of `x86Machine8 r11Of` that
visits no `syscall` before its last state is a `retStep` run. -/
theorem run_ret_of_run8 {r11Of : Core → Silmaril.X86.Word} :
    ∀ (n : Nat) (s t : XState), Silmaril.Machine.Execution.run (tau8 r11Of) n s = some t →
      (∀ k < n, ∀ u, Silmaril.Machine.Execution.run (tau8 r11Of) k s = some u → ¬ Trap u) →
      Silmaril.Machine.Execution.run retStep n s = some t
  | 0, _, _, h, _ => h
  | n + 1, s, t, h, noTrap => by
    simp only [run_succ] at h ⊢
    cases hs : tau8 r11Of s with
    | none => rw [hs] at h; cases h
    | some mid =>
      rw [hs, Option.bind_some] at h
      rw [retStep_of_tau8 hs (noTrap 0 (by omega) s rfl), Option.bind_some]
      refine run_ret_of_run8 n mid t h fun k hk u hu => noTrap (k + 1) (by omega) u ?_
      simp [run_succ, hs, hu]

/-- The converse, for every `r11Of`. -/
theorem run8_of_run_ret (r11Of : Core → Silmaril.X86.Word) :
    ∀ (n : Nat) (s t : XState), Silmaril.Machine.Execution.run retStep n s = some t →
      Silmaril.Machine.Execution.run (tau8 r11Of) n s = some t
  | 0, _, _, h => h
  | n + 1, s, t, h => by
    simp only [run_succ] at h ⊢
    cases hs : retStep s with
    | none => rw [hs] at h; cases h
    | some mid =>
      rw [hs, Option.bind_some] at h
      rw [tau8_of_retStep hs, Option.bind_some]
      exact run8_of_run_ret r11Of n mid t h

theorem reaches8_of_reaches_ret (r11Of : Core → Silmaril.X86.Word) {s t : XState}
    (h : Reaches retStep s t) : Reaches (tau8 r11Of) s t :=
  let ⟨n, hn⟩ := h
  ⟨n, run8_of_run_ret r11Of n s t hn⟩

/-! ## `GStep`'s silent steps are `retStep` -/

variable {w : Silmaril.Apps.Sha256sum.World}

theorem gstep_of_retStep {g : GS} {t : XState} (running : g.exited = none)
    (h : retStep g.x = some t) : GStep w g [] { g with x := t } := by
  obtain ⟨hf, c, m, hs, rfl⟩ := retStep_eq_some.mp h
  exact .retire running hf hs

/-- From a retiring instruction, the only `GStep` is the `retStep`. -/
theorem gstep_retStep_cases {g g' : GS} {t : XState} {es : List Ev}
    (h : retStep g.x = some t) (s : GStep w g es g') : es = [] ∧ g' = { g with x := t } := by
  obtain ⟨-, c, m, hs, rfl⟩ := retStep_eq_some.mp h
  cases s with
  | retire _ _ step => rw [hs] at step; cases step; exact ⟨rfl, rfl⟩
  | call _ _ _ step => rw [hs] at step; cases step
  | exit _ _ step => rw [hs] at step; cases step

/-- A silent `GStep` is a `retStep`, with the kernel and the exit status unchanged. -/
theorem retStep_of_gstep_nil {g g' : GS} (s : GStep w g [] g') :
    retStep g.x = some g'.x ∧ g'.k = g.k ∧ g'.exited = g.exited := by
  cases s with
  | retire _ hf step => exact ⟨retStep_eq_some.mpr ⟨hf, _, _, step, rfl⟩, rfl, rfl⟩

/-- Silent steps keep `Ok`. -/
theorem ok_of_retStep {message : List Byte} {g : GS} {t : XState} {h : List Ev}
    (ok : Ok message g h) (step : retStep g.x = some t) : Ok message { g with x := t } h := by
  obtain ⟨-, -, -, -, rfl⟩ := retStep_eq_some.mp step
  exact ok

/-- **Silent segments are `Leads` segments.** A `retStep` run from an `Ok` state to a state
satisfying `Post` gives `Leads` (every `GStep` execution follows the run). -/
theorem leads_of_run {message : List Byte} {Post : GS → List Ev → Prop} :
    ∀ (n : Nat) (g : GS) (t : XState) (h : List Ev),
      Silmaril.Machine.Execution.run retStep n g.x = some t → g.exited = none → Ok message g h → Post { g with x := t } h →
      Leads (GStep w) (Ok message) Post g h
  | 0, g, t, h, run0, _, _, post => by
    cases run0
    exact .done post
  | n + 1, g, t, h, runN, running, ok, post => by
    simp only [run_succ] at runN
    cases hs : retStep g.x with
    | none => rw [hs] at runN; cases runN
    | some mid =>
      rw [hs, Option.bind_some] at runN
      refine .step ok ⟨[], _, gstep_of_retStep running hs⟩ fun es g' s => ?_
      obtain ⟨rfl, rfl⟩ := gstep_retStep_cases hs s
      rw [List.append_nil]
      exact leads_of_run n { g with x := mid } t h runN running (ok_of_retStep ok hs) post

/-- The same from a `Reaches` witness. -/
theorem leads_of_reaches {message : List Byte} {Post : GS → List Ev → Prop} {g : GS}
    {t : XState} {h : List Ev} (r : Reaches retStep g.x t) (running : g.exited = none)
    (ok : Ok message g h) (post : Post { g with x := t } h) :
    Leads (GStep w) (Ok message) Post g h :=
  let ⟨n, hn⟩ := r
  leads_of_run n g t h hn running ok post

end Silmaril.Process.LPS.Problems.GnuSha256sum
