module

public import Silmaril.Process.LPS.NativeX86AllLattice

/-! # Small x86-64 parity gaps, closed as more-defined variants of the native table

`NativeX86.All.nativeTable` (the hub) leaves a few x86-64 entry points `unmodeled` although
their Linux implementation is, on the modelled paths, a call of an already modelled
specification, or an architectural value the machine holds. This module defines

* `gapTable`: the hub's table with five more-defined arms in front of it, and
* `gapTable_restricts : Restricts (dispatch nativeTable) (dispatch gapTable)`: at every input
  the hub is the variant, or the hub only declines. By `Lattice.obsTrace_mono` the variant has
  no fewer observable traces than the hub, and by `Lattice.obsTrace_eq_of_errorFree` a program
  that never errors against the hub has the same traces against the variant.

The kernel sources cited are Linux v6.8 (`/usr/src/linux-source-6.8.0`); the paths quoted
are unchanged in substance through the hub's kernel profile (v6.13 to v6.18), except
`do_epoll_wait`'s order, which changed in v6.15 (below).

## The arms

* **`arch_prctl` (158)**, `arch/x86/kernel/process_64.c:818-890` `do_arch_prctl_64`:
  `ARCH_SET_FS` is the hub's arm (`NativeX86.archPrctlSpec`). `ARCH_SET_GS` has the same
  check (`arg2 >= TASK_SIZE_MAX` is `-EPERM`, else 0); its effect, the inactive GS base and a
  zero GS selector, is invisible to `X86.Ext`, which decodes no GS-relative access and no
  segment-register move. `ARCH_GET_FS`/`ARCH_GET_GS` are `put_user(base, (unsigned long
  __user *)arg2)`: a single 8-byte store, which faults as a whole, so a range `access_ok`
  refuses is `-EFAULT`, a writable range receives the base and returns 0, and the rest (a
  range the writable view does not cover) declines. The range check before the store is
  base-only (`arch/x86/lib/putuser.S`, `check_range`), but in the band below `TASK_SIZE_MAX`
  the store reaches the never-mapped guard page and faults before writing anything, so the
  whole-range `accessOkbX86` gives the right answer there too (`-EFAULT`, nothing written),
  on v6.8 and on the hub's v6.13+ profile alike. The band is therefore **answered**, not
  declined: the guard deliberately adds no row for `arch_prctl`'s second register, which the
  hub audits as `.unread` because its only arm (`ARCH_SET_FS`) does not dereference it.
  The base is the task's, which the
  syscall input does not carry: the specification chooses **any** word (`getBaseSpec`), which
  is a sound over-approximation on every machine. The option is compared at full width, as the
  hub and `Machines.x86ApplyEffectNative` do, so an `int` option with high register bits stays
  `unmodeled`.
* **`setrlimit` (160)**, `kernel/sys.c:1764-1771`: `copy_from_user` of the LP64 `struct
  rlimit` (which is `struct rlimit64` on x86-64, `X86Legacy.getrlimit_layout_compatible`),
  then `do_prlimit(current, resource, &new, NULL)`. `prlimit64(0, resource, rlim, NULL)`
  (`kernel/sys.c:1699-1762`) takes the same path: the same `copy_from_user` first, `tsk =
  current` for pid 0, `check_prlimit_permission` returns 0 for `current` (`kernel/sys.c:1683`),
  `need_tasklist` is false, and `do_prlimit` is called with the same arguments. The one
  difference is a NULL `rlim`: `setrlimit` faults where `prlimit64` skips the copy. The arm is
  `prlimit64SpecX86 0 resource rlim 0`, which declines a NULL `rlim` (both pointers NULL).
* **`kill` (62)**, `kernel/signal.c:3826-3832`: `kill_something_info` sends to `pid > 0`
  through `kill_proc_info`, `kill_pid_info` and `group_send_sig_info(…, PIDTYPE_TGID)`
  (`kernel/signal.c:1451-1520, 1609-1614`): `check_kill_permission` (`-EINVAL` for an invalid
  signal, `kernel/signal.c:837`), then the shared-pending send. `tkill(pid, sig)`
  (`kernel/signal.c:4023-4030`, `do_tkill`, `do_send_specific`) runs the same
  `check_kill_permission` and sends with `PIDTYPE_PID`. The LPS model is single-threaded
  (`getpid` and `gettid` are the same pinned id, `Sys.Kernel.getpidSpec`), so the process's
  own pid names its only thread and the two deliveries are observably the same (the only
  modelled signal is SIGABRT: pending under a blocking mask, otherwise death by the signal).
  The `siginfo` differs (`SI_USER` against `SI_TKILL`), which no modelled call observes. The
  arm is `tkillSpec` for a positive `pid`, which itself declines every other target, and
  `unmodeled` for `pid <= 0` (process groups and broadcast).
* **`clock_nanosleep` (230)**, `kernel/time/posix-timers.c:1381-1405`: for
  `CLOCK_MONOTONIC` (`common_nsleep_timens`, which converts only absolute times) and
  `flags & TIMER_ABSTIME == 0`, the same `get_timespec64`, `timespec64_valid`, restart block and
  `hrtimer_nanosleep(…, HRTIMER_MODE_REL, CLOCK_MONOTONIC)` as `nanosleep`
  (`kernel/time/hrtimer.c:2159-2175`). The arm is `nanosleepSpec`; other clocks and absolute
  sleeps decline.
* **`epoll_pwait2` (441)**, `fs/eventpoll.c:2621-2637`: a non-NULL `timeout` is copied with
  `get_timespec64` (`-EFAULT`) and judged by `poll_select_set_timeout` (`-EINVAL` unless
  `timespec64_valid`, `fs/select.c:271-286`), then `do_epoll_pwait` runs, as for
  `epoll_pwait` (`fs/eventpoll.c:2610-2619`). The timeout is read as `pselect6`'s
  (`pselectTimeout`), and the rest is the hub's x86-64 `epoll_pwait` specification, which
  answers no outcome that depends on the timeout (`epollPwaitOutcomeWith`). That
  specification has the `do_epoll_wait` order of Linux up to v6.14 (`fs/eventpoll.c:2541-2552`
  in v6.8: the `maxevents` bounds, then `access_ok`, then `fdget(epfd)`); from v6.15 (commit
  `6b47d35d4d9e`) Linux looks `epfd` up first, as LPS does (`FdEventsAbi.epollFdFirst`). The
  profile spans both, so the installed arm is `All.epollOrderChaos` of it: it declines an
  unopened `epfd` with a bad `maxevents` or a bad `events` range, where the two kernels answer
  differently, and keeps the shared answer elsewhere (see "`do_epoll_wait`'s order" below).

Every new arm is guarded as the hub guards its arms (`guardGap`: the hub's
`boundarySuspect`, plus the constant-size pointers of the new numbers, the `rlimit` at
`setrlimit`'s second register, `epoll_pwait2`'s `timespec` and signal mask, and
`clock_nanosleep`'s two `timespec`s, as the hub audits `nanosleep`). The one deliberate
exception is `arch_prctl`'s `ARCH_GET_FS`/`ARCH_GET_GS` pointer, whose band is answered (see
above); a guard row there would also decline the hub's `ARCH_SET_FS` answers on the same
register and break `gapTable_restricts`.

## FS-base read-back

`Machines.x86ExtNativeFs` is `x86ExtNative` whose effect application writes, for a
successful `ARCH_GET_FS`, the machine's FS base at RSI in place of the bytes the effect
carries (`x86ApplyEffectNativeFs`). Under `gapTable` the effect the machine applies is then
the one the specification admits with the chosen base equal to the FS base
(`getFs_step_admitted`), and after `ARCH_SET_FS(base)` that base is `base`
(`Machines.x86ApplyEffectNativeFs_setFs`). On every other call the two machines apply effects
identically (`x86ApplyEffectNativeFs_other`), and the hub never answers a successful
`ARCH_GET_FS`, so the hub's behaviour does not change with the machine.

## `rt_sigprocmask`

`rtSigprocmaskSpecX86` now gates the `oset` copy-out with the whole-range
`accessGateX86`: `copy_to_user` is out of line on x86-64 (no `INLINE_COPY_TO_USER`), as for
the other constant-size copies. Its band answer (`-EFAULT`, nothing written) is that of the
hub's v6.13+ profile (`USER_PTR_MAX = TASK_SIZE_MAX`); v6.8's sign-test `access_ok` lets the
band through and copies partially before `-EFAULT` (`Sys/AccessGate.lean`), so probes on a
v6.8 host are outside the profile for that band. `rtSigprocmask_restricts` proves the former base-only reading
(`rtSigprocmaskSpecX86Small`) restricts it. In `nativeTable` the band where they differ is
declined by the boundary guard in both readings.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.GapSweep

open Silmaril.Process.LPS Silmaril.Process.LPS.NativeX86.All

/-! ## Restriction at one input -/

/-- At one input and model, `p` is `f`, or `p` only declines. `Restricts p f` is this at
every input. -/
def RestrictsAt (p f : Sys SyscallEffect) (i : SyscallInput) (m : Model) : Prop :=
  (∀ o, p i m o ↔ f i m o) ∨ (∀ o, p i m o ↔ o = .unmodeled)

theorem RestrictsAt.refl (p : Sys SyscallEffect) (i : SyscallInput) (m : Model) :
    RestrictsAt p p i m :=
  .inl fun _ => Iff.rfl

theorem RestrictsAt.unmodeled (f : Sys SyscallEffect) (i : SyscallInput) (m : Model) :
    RestrictsAt Sys.unmodeled f i m :=
  .inr fun _ => Iff.rfl

theorem RestrictsAt.ite (c : Prop) [Decidable c] {p₁ p₂ f₁ f₂ : Sys SyscallEffect}
    {i : SyscallInput} {m : Model} (h₁ : c → RestrictsAt p₁ f₁ i m)
    (h₂ : ¬ c → RestrictsAt p₂ f₂ i m) :
    RestrictsAt (if c then p₁ else p₂) (if c then f₁ else f₂) i m := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc, ite_eq_right hc]; exact h₂ hc

theorem RestrictsAt.bind_getModel {kp kf : Model → Sys SyscallEffect} {i : SyscallInput}
    {m : Model} (h : RestrictsAt (kp m) (kf m) i m) :
    RestrictsAt (Sys.getModel >>= kp) (Sys.getModel >>= kf) i m := by
  rcases h with h | h
  · exact .inl fun o => by rw [Sys.bind_getModel_iff, Sys.bind_getModel_iff]; exact h o
  · exact .inr fun o => by rw [Sys.bind_getModel_iff]; exact h o

theorem RestrictsAt.bind_input {kp kf : SyscallInput → Sys SyscallEffect} {i : SyscallInput}
    {m : Model} (h : RestrictsAt (kp i) (kf i) i m) :
    RestrictsAt (Sys.input >>= kp) (Sys.input >>= kf) i m := by
  rcases h with h | h
  · exact .inl fun o => by rw [Sys.bind_input_iff, Sys.bind_input_iff]; exact h o
  · exact .inr fun o => by rw [Sys.bind_input_iff]; exact h o

theorem bind_modify_iff {β : Type} (g : Model → Model) (k : Unit → Sys β) (i : SyscallInput)
    (m : Model) (o : Outcome β) : (Sys.modify g >>= k) i m o ↔ k () i (g m) o := by
  show Sys.bind (Sys.modify g) k i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁; simpa using h₂
    · intro h; exact ⟨(), g m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h₁ | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h₁
      · cases h₁; exact h₂
    · intro h; exact .inr ⟨(), g m, [], rfl, h⟩

theorem RestrictsAt.bind_modify {g : Model → Model} {kp kf : Unit → Sys SyscallEffect}
    {i : SyscallInput} {m : Model} (h : RestrictsAt (kp ()) (kf ()) i (g m)) :
    RestrictsAt (Sys.modify g >>= kp) (Sys.modify g >>= kf) i m := by
  rcases h with h | h
  · exact .inl fun o => by rw [bind_modify_iff, bind_modify_iff]; exact h o
  · exact .inr fun o => by rw [bind_modify_iff]; exact h o

/-- A computation followed by a common continuation keeps the restriction. -/
theorem RestrictsAt.bind_left {α : Type} {p f : Sys α} {k : α → Sys SyscallEffect}
    {i : SyscallInput} {m : Model}
    (h : (∀ o, p i m o ↔ f i m o) ∨ (∀ o, p i m o ↔ o = .unmodeled)) :
    RestrictsAt (Sys.bind p k) (Sys.bind f k) i m := by
  rcases h with h | h
  · refine .inl fun o => ?_
    show Sys.bind p k i m o ↔ Sys.bind f k i m o
    cases o with
    | ok y m₂ evs =>
      constructor
      · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, h₃⟩
        exact ⟨x, m₁, evs₁, evs₂, (h _).1 h₁, h₂, h₃⟩
      · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, h₃⟩
        exact ⟨x, m₁, evs₁, evs₂, (h _).2 h₁, h₂, h₃⟩
    | unmodeled =>
      constructor
      · rintro (h₁ | ⟨x, m₁, evs₁, h₁, h₂⟩)
        · exact .inl ((h _).1 h₁)
        · exact .inr ⟨x, m₁, evs₁, (h _).1 h₁, h₂⟩
      · rintro (h₁ | ⟨x, m₁, evs₁, h₁, h₂⟩)
        · exact .inl ((h _).2 h₁)
        · exact .inr ⟨x, m₁, evs₁, (h _).2 h₁, h₂⟩
  · refine .inr fun o => ?_
    show Sys.bind p k i m o ↔ _
    cases o with
    | ok y m₂ evs =>
      constructor
      · rintro ⟨x, m₁, evs₁, evs₂, h₁, -, -⟩
        cases (h _).1 h₁
      · intro e; cases e
    | unmodeled =>
      exact ⟨fun _ => rfl, fun _ => .inl ((h _).2 rfl)⟩

theorem RestrictsAt.recordCopyins {p f : Sys SyscallEffect} {i : SyscallInput} {m : Model}
    (reads : List (Word × Nat)) (h : RestrictsAt p f i m) :
    RestrictsAt (recordCopyins reads p) (recordCopyins reads f) i m :=
  RestrictsAt.bind_left h

/-! ## `rt_sigprocmask`: the whole-range `oset` gate -/

/-- The base-only gate restricts the whole-range gate: they differ only in the band, where the
base-only gate declines. -/
theorem gate_restrictsAt (base : Word) (len : Int) (k : Sys SyscallEffect) (i : SyscallInput)
    (m : Model) : RestrictsAt (accessGateSmallX86 base len k) (accessGateX86 base len k) i m := by
  cases h : accessOkbX86 base len
  · by_cases hb : uns base ≤ taskSizeMaxX86
    · have e : accessGateSmallX86 base len k = Sys.unmodeled := by
        simp [accessGateSmallX86, h, hb]
      rw [e]; exact RestrictsAt.unmodeled _ i m
    · have e : accessGateSmallX86 base len k = accessGateX86 base len k := by
        simp [accessGateSmallX86, accessGateX86, h, hb]
      rw [e]; exact RestrictsAt.refl _ i m
  · have e : accessGateSmallX86 base len k = accessGateX86 base len k := by
      simp [accessGateSmallX86, accessGateX86, h]
    rw [e]; exact RestrictsAt.refl _ i m

/-- **`rt_sigprocmask`**: the former base-only reading restricts the whole-range one. -/
theorem rtSigprocmask_restrictsAt (how nset oset ss : Word) (i : SyscallInput) (m : Model) :
    RestrictsAt (rtSigprocmaskSpecX86Small how nset oset ss)
      (rtSigprocmaskSpecX86 how nset oset ss) i m := by
  unfold rtSigprocmaskSpecX86Small rtSigprocmaskSpecX86 rtSigprocmaskSpecWith writeOsetWith
    setSigmaskDeliver
  apply RestrictsAt.ite
  · intro _; exact RestrictsAt.refl _ i m
  · intro _
    apply RestrictsAt.bind_getModel
    apply RestrictsAt.ite
    · intro _
      apply RestrictsAt.ite
      · intro _; exact RestrictsAt.refl _ i m
      · intro _; exact gate_restrictsAt _ _ _ i m
    · intro _
      apply RestrictsAt.bind_input
      cases sigsetAt i.mem nset with
      | none => exact RestrictsAt.refl _ i m
      | some raw =>
        apply RestrictsAt.recordCopyins
        apply RestrictsAt.ite
        · intro _; exact RestrictsAt.refl _ i m
        · intro _
          apply RestrictsAt.bind_modify
          apply RestrictsAt.ite
          · intro _; exact RestrictsAt.refl _ _ _
          · intro _; exact gate_restrictsAt _ _ _ _ _

/-- The x86-64 `rt_sigprocmask` arm (14) under the base-only reading restricts the arm under
the whole-range one. -/
theorem rtSigprocmask_restricts :
    Restricts (fun i => rtSigprocmaskSpecX86Small (how32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) i)
      (fun i => rtSigprocmaskSpecX86 (how32 (i.arg 0)) (i.arg 1) (i.arg 2) (i.arg 3) i) :=
  fun i m => rtSigprocmask_restrictsAt _ _ _ _ i m

/-! ## `arch_prctl` -/

/-- `ARCH_SET_GS`. -/
def archSetGs : Word := 0x1001
/-- `ARCH_GET_FS`. -/
def archGetFs : Word := 0x1003
/-- `ARCH_GET_GS`. -/
def archGetGs : Word := 0x1004

/-- The eight little-endian bytes of a word. -/
def le8 (w : Word) : List Byte := zToLeBytes 8 (uns w)

/-- `put_user(base, (unsigned long __user *)addr)` of a base the input does not carry: any
word. A single 8-byte store: `-EFAULT` outside `access_ok`, the word inside a writable range,
and `unmodeled` where the writable view does not cover the range. -/
def getBaseSpec (addr : Word) : Sys SyscallEffect := do
  let i ← Sys.input
  if accessOkbX86 addr 8 then
    match readBytesMap i.wmem addr 8 with
    | none => Sys.unmodeled
    | some _ => do
      let v ← Sys.choose fun _ : Word => True
      Sys.pure (mkEffect 0 [(addr, le8 v)] [])
  else errRet EFAULT

/-- `do_arch_prctl_64` on the modelled options (see the module docstring). -/
def archPrctlSpecFull (operation arg : Word) : Sys SyscallEffect :=
  if operation = archSetFs ∨ operation = archSetGs then
    if uns arg < x86AddressSpace.taskSize then retOnly 0 else errRet EPERM
  else if operation = archGetFs ∨ operation = archGetGs then getBaseSpec arg
  else Sys.unmodeled

def archPrctlArmFull : SpecArm :=
  arm 158 "arch_prctl" (fun input => archPrctlSpecFull (input.arg 0) (input.arg 1))

theorem archPrctlFull_setFs (base : Word) :
    archPrctlSpecFull archSetFs base = archPrctlSpec archSetFs base := by
  have h₁ : archSetFs = archSetFs ∨ archSetFs = archSetGs := .inl rfl
  have h₂ : archSetFs = archSetFs := rfl
  unfold archPrctlSpecFull archPrctlSpec
  rw [ite_eq_left h₁, ite_eq_left h₂]

/-- The hub's `arch_prctl` (`ARCH_SET_FS` only) restricts the full one. -/
theorem archPrctl_restricts : Restricts archPrctlArm.spec archPrctlArmFull.spec := by
  intro i m
  by_cases h : i.arg 0 = archSetFs
  · refine .inl fun o => ?_
    show archPrctlSpec (i.arg 0) (i.arg 1) i m o ↔ archPrctlSpecFull (i.arg 0) (i.arg 1) i m o
    rw [h, archPrctlFull_setFs]
  · refine .inr fun o => ?_
    show archPrctlSpec (i.arg 0) (i.arg 1) i m o ↔ _
    exact archPrctl_unsupported _ _ i m o h

theorem bind_choose_pure_iff {α β : Type} (P : α → Prop) (f : α → β) (i : SyscallInput)
    (m : Model) (o : Outcome β) :
    (Sys.choose P >>= fun x => Sys.pure (f x)) i m o ↔ ∃ x, P x ∧ o = .ok (f x) m [] := by
  show Sys.bind (Sys.choose P) (fun x => Sys.pure (f x)) i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, ⟨x', hx, hc⟩, hp, rfl⟩
      cases hc
      cases hp
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, h⟩
      cases h
      exact ⟨x, m, [], [], ⟨x, hx, rfl⟩, rfl, rfl⟩
  | unmodeled =>
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, m₁, evs₁, ⟨x', hx, hc⟩, h⟩)
      · cases h
      · cases hc; cases h
    · rintro ⟨x, hx, h⟩; cases h

/-- Inside `access_ok` and a writable range, `ARCH_GET_FS`/`ARCH_GET_GS` return 0 having
stored some word, and nothing else. -/
theorem getBaseSpec_writable (addr : Word) (i : SyscallInput) (m : Model)
    (ok : accessOkbX86 addr 8 = true) (bs : List Byte) (w : readBytesMap i.wmem addr 8 = some bs)
    (o : Outcome SyscallEffect) :
    getBaseSpec addr i m o ↔ ∃ v : Word, o = .ok (mkEffect 0 [(addr, le8 v)] []) m [] := by
  unfold getBaseSpec
  refine (Sys.bind_input_iff _ i m o).trans ?_
  rw [ite_eq_left ok, w]
  refine (bind_choose_pure_iff (fun _ : Word => True)
    (fun v => mkEffect 0 [(addr, le8 v)] []) i m o).trans ?_
  simp

/-- Outside `access_ok`: `-EFAULT`. -/
theorem getBaseSpec_fault (addr : Word) (i : SyscallInput) (m : Model)
    (bad : accessOkbX86 addr 8 = false) (o : Outcome SyscallEffect) :
    getBaseSpec addr i m o ↔ o = .ok (mkEffect (errnoRet EFAULT) [] []) m [] := by
  have hb : ¬ (accessOkbX86 addr 8 = true) := by simp [bad]
  unfold getBaseSpec
  refine (Sys.bind_input_iff _ i m o).trans ?_
  rw [ite_eq_right hb]
  exact Iff.rfl

theorem archPrctlFull_getFs (addr : Word) :
    archPrctlSpecFull archGetFs addr = getBaseSpec addr := by
  have h₁ : ¬ (archGetFs = archSetFs ∨ archGetFs = archSetGs) := by decide
  have h₂ : archGetFs = archGetFs ∨ archGetFs = archGetGs := .inl rfl
  unfold archPrctlSpecFull
  rw [ite_eq_right h₁, ite_eq_left h₂]

theorem archPrctlFull_getGs (addr : Word) :
    archPrctlSpecFull archGetGs addr = getBaseSpec addr := by
  have h₁ : ¬ (archGetGs = archSetFs ∨ archGetGs = archSetGs) := by decide
  have h₂ : archGetGs = archGetFs ∨ archGetGs = archGetGs := .inr rfl
  unfold archPrctlSpecFull
  rw [ite_eq_right h₁, ite_eq_left h₂]

theorem archPrctlFull_setGs (arg : Word) :
    archPrctlSpecFull archSetGs arg =
      if uns arg < x86AddressSpace.taskSize then retOnly 0 else errRet EPERM := by
  have h₁ : archSetGs = archSetFs ∨ archSetGs = archSetGs := .inr rfl
  unfold archPrctlSpecFull
  rw [ite_eq_left h₁]

/-- Any other option stays `unmodeled`. -/
theorem archPrctlFull_other (operation arg : Word)
    (h₁ : ¬ (operation = archSetFs ∨ operation = archSetGs))
    (h₂ : ¬ (operation = archGetFs ∨ operation = archGetGs)) :
    archPrctlSpecFull operation arg = Sys.unmodeled := by
  unfold archPrctlSpecFull
  rw [ite_eq_right h₁, ite_eq_right h₂]

/-! ## `setrlimit`, `kill`, `epoll_pwait2` -/

/-- x86-64 `setrlimit` (160): `prlimit64(0, resource, rlim, NULL)`. -/
def setrlimitArm : SpecArm :=
  arm 160 "setrlimit" (fun i => prlimit64SpecX86 0 (i.arg 0) (i.arg 1) 0)

/-- x86-64 `kill(pid, sig)` (62): `tkill(pid, sig)` for a positive `pid`, `unmodeled`
otherwise. Both arguments arrive narrowed (`pid32`, `sig32`). -/
def killSpecX86 (pid sig : Word) : Sys SyscallEffect :=
  if pidPositive pid then tkillSpec pid sig else Sys.unmodeled

def killArm : SpecArm := arm 62 "kill" (fun i => killSpecX86 (pid32 (i.arg 0)) (sig32 (i.arg 1)))

theorem killSpecX86_positive (pid sig : Word) (h : pidPositive pid = true) :
    killSpecX86 pid sig = tkillSpec pid sig := by
  simp [killSpecX86, h]

theorem killSpecX86_nonpositive (pid sig : Word) (h : pidPositive pid = false) :
    killSpecX86 pid sig = Sys.unmodeled := by
  simp [killSpecX86, h]

/-- x86-64 `epoll_pwait2` (441): the `timespec`, then `epoll_pwait`. -/
def epollPwait2SpecX86 (epfd events maxevents32 tsp sigmask sigsetsize : Word) :
    Sys SyscallEffect := do
  let i ← Sys.input
  match pselectTimeout i.mem tsp with
  | .toFault => errRet EFAULT
  | .toInval => errRet EINVAL
  | _ => epollPwaitSpecX86 epfd events maxevents32 sigmask sigsetsize

/-- x86-64 `epoll_pwait2` (441) in the `do_epoll_wait` order of Linux from v6.15. -/
def epollPwait2SpecX86FdFirst (epfd events maxevents32 tsp sigmask sigsetsize : Word) :
    Sys SyscallEffect := do
  let i ← Sys.input
  match pselectTimeout i.mem tsp with
  | .toFault => errRet EFAULT
  | .toInval => errRet EINVAL
  | _ => epollPwaitSpecX86FdFirst epfd events maxevents32 sigmask sigsetsize

/-- `epoll_pwait2` in the order of Linux up to v6.14. -/
def epollPwait2ArmExact : SpecArm :=
  arm 441 "epoll_pwait2" (fun i =>
    epollPwait2SpecX86 (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 3) (i.arg 4)
      (i.arg 5))

/-- `epoll_pwait2` in the order of Linux from v6.15. -/
def epollPwait2ArmFdFirst : SpecArm :=
  arm 441 "epoll_pwait2" (fun i =>
    epollPwait2SpecX86FdFirst (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 3) (i.arg 4)
      (i.arg 5))

/-- The installed `epoll_pwait2` arm: the v6.14-order arm, declined where the v6.15 order
disagrees (`All.epollOrderChaos`). -/
def epollPwait2Arm : SpecArm := epollOrderChaos epollPwait2ArmExact

/-- A readable, valid timeout is `epoll_pwait` too. -/
theorem epollPwait2_valid (epfd events maxevents32 tsp sigmask sigsetsize : Word)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (valid : pselectTimeout i.mem tsp ≠ .toFault ∧ pselectTimeout i.mem tsp ≠ .toInval) :
    epollPwait2SpecX86 epfd events maxevents32 tsp sigmask sigsetsize i m o ↔
      epollPwaitSpecX86 epfd events maxevents32 sigmask sigsetsize i m o := by
  unfold epollPwait2SpecX86
  refine (Sys.bind_input_iff _ i m o).trans ?_
  cases h : pselectTimeout i.mem tsp with
  | toFault => exact absurd h valid.1
  | toInval => exact absurd h valid.2
  | toNone => exact Iff.rfl
  | toZero => exact Iff.rfl
  | toDeadline => exact Iff.rfl

/-- A NULL timeout is `epoll_pwait` (whose timeout no modelled answer reads). -/
theorem epollPwait2_null (epfd events maxevents32 sigmask sigsetsize : Word) (i : SyscallInput)
    (m : Model) (o : Outcome SyscallEffect) :
    epollPwait2SpecX86 epfd events maxevents32 0 sigmask sigsetsize i m o ↔
      epollPwaitSpecX86 epfd events maxevents32 sigmask sigsetsize i m o := by
  have hz : pselectTimeout i.mem 0 = .toNone := by simp [pselectTimeout, wIs0]
  exact epollPwait2_valid epfd events maxevents32 0 sigmask sigsetsize i m o
    ⟨fun h => (by cases hz.symm.trans h), fun h => (by cases hz.symm.trans h)⟩

/-- x86-64 `clock_nanosleep(CLOCK_MONOTONIC, flags, rqtp, rmtp)` (230) without
`TIMER_ABSTIME`: `nanosleep(rqtp, rmtp)`. Other clocks and absolute sleeps decline. -/
def clockNanosleepSpecX86 (clock flags rqtp rmtp : Word) : Sys SyscallEffect :=
  if clock = zw CLOCK_MONOTONIC ∧ flags &&& 1 = 0 then nanosleepSpec rqtp rmtp
  else Sys.unmodeled

def clockNanosleepArm : SpecArm :=
  arm 230 "clock_nanosleep" (fun i =>
    clockNanosleepSpecX86 (clockid32 (i.arg 0)) (flag32 (i.arg 1)) (i.arg 2) (i.arg 3))

theorem clockNanosleep_monotonic (flags rqtp rmtp : Word) (rel : flags &&& 1 = 0) :
    clockNanosleepSpecX86 (zw CLOCK_MONOTONIC) flags rqtp rmtp = nanosleepSpec rqtp rmtp := by
  have h : zw CLOCK_MONOTONIC = zw CLOCK_MONOTONIC ∧ flags &&& 1 = 0 := ⟨rfl, rel⟩
  unfold clockNanosleepSpecX86
  rw [ite_eq_left h]

theorem clockNanosleep_other (clock flags rqtp rmtp : Word)
    (h : ¬ (clock = zw CLOCK_MONOTONIC ∧ flags &&& 1 = 0)) :
    clockNanosleepSpecX86 clock flags rqtp rmtp = Sys.unmodeled := by
  unfold clockNanosleepSpecX86
  rw [ite_eq_right h]

/-! ## The guard and the table -/

/-- Constant-size pointer registers of the new numbers (`struct rlimit`, `timespec`,
`sigset_t`), in the hub's `constPtrArgs` form. -/
def extraConst : Nat → List (Nat × Nat)
  | 160 => [(1, 16)]
  | 441 => [(3, 16), (4, 8)]
  | 230 => [(2, 16), (3, 16)]
  | _ => []

/-- The hub's boundary test, with the new numbers' constant-size pointers. -/
def suspectGap (no : Nat) (i : SyscallInput) : Bool :=
  boundarySuspect no i || (extraConst no).any (fun p => inBand p.2 (i.arg p.1))

/-- Decline every outcome on a boundary-suspect input; otherwise the arm itself. -/
def guardGap (a : SpecArm) : SpecArm :=
  { a with spec := fun i m o => if suspectGap a.no i = true then o = .unmodeled
                                else a.spec i m o }

theorem guardGap_spec_of_not_suspect (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : suspectGap a.no i = false) :
    (guardGap a).spec i m o ↔ a.spec i m o := by
  simp [guardGap, h]

theorem guardGap_spec_of_suspect (a : SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : suspectGap a.no i = true) :
    (guardGap a).spec i m o ↔ o = .unmodeled := by
  simp [guardGap, h]

theorem suspectGap_158 (i : SyscallInput) : suspectGap 158 i = boundarySuspect 158 i := by
  unfold suspectGap
  cases boundarySuspect 158 i <;> rfl

/-- The five more-defined arms, guarded. -/
def gapArms : List SpecArm :=
  [archPrctlArmFull, setrlimitArm, killArm, epollPwait2Arm, clockNanosleepArm].map guardGap

/-- The variant: the five arms in front of the hub's table. `arch_prctl` shadows the hub's
`ARCH_SET_FS`-only arm; the other four numbers have no hub arm. -/
def gapTable : List SpecArm := gapArms ++ nativeTable

def gapNumbers : List Nat := [158, 160, 62, 441, 230]

theorem gapArms_numbers : armNumbers gapArms = gapNumbers := rfl

theorem gapArms_names :
    gapArms.map (fun a => (a.no, a.name, a.status)) =
      [(158, "arch_prctl", .translated), (160, "setrlimit", .translated),
       (62, "kill", .translated), (441, "epoll_pwait2", .translated),
       (230, "clock_nanosleep", .translated)] := rfl

/-- The new numbers are not in the hub. -/
theorem nativeTable_lacks : ∀ n ∈ [160, 62, 441, 230], n ∉ armNumbers nativeTable := by
  rw [nativeTable, tableWith_numbers chaos chaos_no]; decide +kernel

theorem lookup_extension_158 : lookupArm extensionArms 158 = some archPrctlArm := by
  rw [extensionArms, lookupArm_append,
    lookupArm_none_of_not_mem familyExtensionArms 158 (by decide +kernel)]
  rfl

theorem lookup_native_158 : lookupArm nativeTable 158 = some (chaos archPrctlArm) := by
  rw [nativeTable_eq, lookupArm_append, lookupArm_map chaos chaos_no, lookup_extension_158]
  rfl

theorem dispatch_gapTable_other (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat ∉ gapNumbers) :
    dispatch gapTable i m o ↔ dispatch nativeTable i m o := by
  have hn : lookupArm gapArms i.sysno.toNat = none :=
    lookupArm_none_of_not_mem _ _ (by rw [gapArms_numbers]; exact h)
  simp only [dispatch, gapTable, lookupArm_append, hn, Option.none_or]

theorem dispatch_gapTable_arm (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (a : SpecArm) (h : lookupArm gapArms i.sysno.toNat = some a) :
    dispatch gapTable i m o ↔ a.spec i m o := by
  simp [dispatch, gapTable, lookupArm_append, h]

theorem dispatch_native_absent (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat ∉ armNumbers nativeTable) :
    dispatch nativeTable i m o ↔ o = .unmodeled := by
  simp only [dispatch, lookupArm_none_of_not_mem _ _ h]
  exact Iff.rfl

/-- At `arch_prctl`, the variant dispatches to its guarded full arm. -/
theorem dispatch_gapTable_158 (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 158) :
    dispatch gapTable i m o ↔ (guardGap archPrctlArmFull).spec i m o :=
  dispatch_gapTable_arm i m o _ (by rw [h]; rfl)

/-- At `arch_prctl`, the hub dispatches to its guarded `ARCH_SET_FS`-only arm. -/
theorem dispatch_native_158 (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 158) :
    dispatch nativeTable i m o ↔ (guard archPrctlArm).spec i m o := by
  have e3 : chaos archPrctlArm = guard archPrctlArm := by
    simp [chaos, sigaltstackChaos_other archPrctlArm (by decide),
      epollOrderChaos_other archPrctlArm (by decide) (by decide) (by decide)]
  simp only [dispatch, h, lookup_native_158, e3]

/-- **`ARCH_GET_FS` at the variant's dispatch**: off the boundary guard it is `getBaseSpec`
of the second register. -/
theorem dispatch_gapTable_getFs (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 158) (op : i.arg 0 = archGetFs) (ns : suspectGap 158 i = false) :
    dispatch gapTable i m o ↔ getBaseSpec (i.arg 1) i m o := by
  rw [dispatch_gapTable_158 i m o h,
    guardGap_spec_of_not_suspect (a := archPrctlArmFull) i m o ns]
  show archPrctlSpecFull (i.arg 0) (i.arg 1) i m o ↔ _
  rw [op, archPrctlFull_getFs]

/-- **`ARCH_GET_FS` at the hub's dispatch**: the hub only declines, guarded or not. -/
theorem dispatch_native_getFs (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 158) (op : i.arg 0 = archGetFs) :
    dispatch nativeTable i m o ↔ o = .unmodeled := by
  rw [dispatch_native_158 i m o h]
  cases hs : boundarySuspect 158 i
  · rw [guard_spec_of_not_suspect archPrctlArm i m o hs]
    show archPrctlSpec (i.arg 0) (i.arg 1) i m o ↔ _
    rw [op]
    exact archPrctl_unsupported _ _ i m o (by decide)
  · exact guard_spec_of_suspect archPrctlArm i m o hs

/-- **The variant is more defined than the hub**: at every input the hub's dispatch is the
variant's, or the hub only declines. -/
theorem gapTable_restricts : Restricts (dispatch nativeTable) (dispatch gapTable) := by
  intro i m
  by_cases hmem : i.sysno.toNat ∈ gapNumbers
  · simp only [gapNumbers, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h
    · have e1 : ∀ o, dispatch nativeTable i m o ↔ (guard archPrctlArm).spec i m o :=
        fun o => dispatch_native_158 i m o h
      have e2 : ∀ o, dispatch gapTable i m o ↔ (guardGap archPrctlArmFull).spec i m o :=
        fun o => dispatch_gapTable_158 i m o h
      cases hs : boundarySuspect 158 i
      · have g1 : ∀ o, (guard archPrctlArm).spec i m o ↔ archPrctlArm.spec i m o :=
          fun o => guard_spec_of_not_suspect archPrctlArm i m o hs
        have g2 : ∀ o, (guardGap archPrctlArmFull).spec i m o ↔ archPrctlArmFull.spec i m o :=
          fun o => guardGap_spec_of_not_suspect archPrctlArmFull i m o
            ((suspectGap_158 i).trans hs)
        rcases archPrctl_restricts i m with same | dec
        · exact .inl fun o => by rw [e1, g1, e2, g2]; exact same o
        · exact .inr fun o => by rw [e1, g1]; exact dec o
      · exact .inl fun o => by
          rw [e1, e2, guard_spec_of_suspect archPrctlArm i m o hs,
            guardGap_spec_of_suspect archPrctlArmFull i m o ((suspectGap_158 i).trans hs)]
    all_goals
      refine .inr fun o => dispatch_native_absent i m o ?_
      rw [h]
      exact nativeTable_lacks _ (by simp)
  · exact .inl fun o => (dispatch_gapTable_other i m o hmem).symm

/-! ## `do_epoll_wait`'s order

The profile (v6.13 to v6.18) spans the v6.15 change of `do_epoll_wait`'s order (commit
`6b47d35d4d9e`, see `All` and `Sys/FdEvents/Common.lean`). The installed `epoll_wait`,
`epoll_pwait` and `epoll_pwait2` arms are the v6.14-order arms under `epollOrderChaos`:

* (a) they restrict the v6.14-order (exact) arms, and the tables restrict the exact tables
  (`nativeTable_restricts_exact`, `gapTable_restricts_exact`);
* (b) they also restrict the v6.15-order arms: every answer they give is the answer of both
  kernels (`epollWait_restricts_v615`, `epollPwait_restricts_v615`,
  `epollPwait2_restricts_v615`, and the `…_v614` forms). -/

/-- An arm under `epollOrderChaos` restricts any arm that agrees with it wherever the orders
agree. -/
theorem epollOrderChaos_restricts_of (a b : SpecArm)
    (h : ∀ i m, epollOrderDiffers a.no i m = false → ∀ o, a.spec i m o ↔ b.spec i m o) :
    Restricts (epollOrderChaos a).spec b.spec := by
  intro i m
  cases hd : epollOrderDiffers a.no i m
  · exact .inl fun o => (epollOrderChaos_spec_of_agree a i m o hd).trans (h i m hd o)
  · exact .inr fun o => epollOrderChaos_spec_of_differ a i m o hd

/-- The same through the hub's `chaos` (the `sigaltstack` chaos is the identity off 131). -/
theorem chaos_restricts_of (a b : SpecArm) (h131 : a.no ≠ 131)
    (h : ∀ i m, epollOrderDiffers a.no i m = false → ∀ o, a.spec i m o ↔ b.spec i m o) :
    Restricts (chaos a).spec b.spec := by
  intro i m
  have e : chaos a = guard (epollOrderChaos a) := by
    simp only [chaos, sigaltstackChaos_other a h131]
  rw [e]
  rcases guard_restricts (epollOrderChaos a) i m with g | g
  · rcases epollOrderChaos_restricts_of a b h i m with r | r
    · exact .inl fun o => (g o).trans (r o)
    · exact .inr fun o => (g o).trans (r o)
  · exact .inr g

/-- The same through the gap sweep's `guardGap`. -/
theorem guardGap_restricts_of (a b : SpecArm)
    (h : ∀ i m, epollOrderDiffers a.no i m = false → ∀ o, a.spec i m o ↔ b.spec i m o) :
    Restricts (guardGap (epollOrderChaos a)).spec b.spec := by
  intro i m
  cases hs : suspectGap (epollOrderChaos a).no i
  · rcases epollOrderChaos_restricts_of a b h i m with r | r
    · exact .inl fun o => (guardGap_spec_of_not_suspect _ i m o hs).trans (r o)
    · exact .inr fun o => (guardGap_spec_of_not_suspect _ i m o hs).trans (r o)
  · exact .inr fun o => guardGap_spec_of_suspect _ i m o hs

theorem epollOrderDiffers_232 (i : SyscallInput) (m : Model) :
    epollOrderDiffers 232 i m =
      epollWaitOrdersDiffer m (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) := by
  simp [epollOrderDiffers]

theorem epollOrderDiffers_281 (i : SyscallInput) (m : Model) :
    epollOrderDiffers 281 i m =
      epollPwaitOrdersDiffer i m (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4)
        (i.arg 5) := by
  simp [epollOrderDiffers]

theorem epollOrderDiffers_441 (i : SyscallInput) (m : Model) :
    epollOrderDiffers 441 i m =
      (timeoutPasses (pselectTimeout i.mem (i.arg 3)) &&
        epollPwaitOrdersDiffer i m (fd32 (i.arg 0)) (i.arg 1) (int32 (i.arg 2)) (i.arg 4)
          (i.arg 5)) := by
  simp [epollOrderDiffers]

/-- Where the orders agree, the v6.14 and v6.15 `epoll_wait` arms agree. -/
theorem epollWait_agree (i : SyscallInput) (m : Model)
    (h : epollOrderDiffers epollWaitArmX86.no i m = false) (o : Outcome SyscallEffect) :
    epollWaitArmX86.spec i m o ↔ epollWaitArmX86FdFirst.spec i m o := by
  have hd := (epollOrderDiffers_232 i m).symm.trans h
  exact epollWaitSpecWith_congr .x86 .x86FdFirst _ _ _ i m
    (epollWaitOrders_agree m _ _ _ hd) o

/-- Where the orders agree, the v6.14 and v6.15 `epoll_pwait` arms agree. -/
theorem epollPwait_agree (i : SyscallInput) (m : Model)
    (h : epollOrderDiffers epollPwaitArmX86.no i m = false) (o : Outcome SyscallEffect) :
    epollPwaitArmX86.spec i m o ↔ epollPwaitArmX86FdFirst.spec i m o := by
  have hd := (epollOrderDiffers_281 i m).symm.trans h
  exact epollPwaitSpecWith_congr .x86 .x86FdFirst _ _ _ _ _ i m
    (epollPwaitOrders_agree i m _ _ _ _ _ hd) o

/-- Where the orders agree, the v6.14 and v6.15 `epoll_pwait2` arms agree. -/
theorem epollPwait2_agree (i : SyscallInput) (m : Model)
    (h : epollOrderDiffers epollPwait2ArmExact.no i m = false) (o : Outcome SyscallEffect) :
    epollPwait2ArmExact.spec i m o ↔ epollPwait2ArmFdFirst.spec i m o := by
  have hd := (epollOrderDiffers_441 i m).symm.trans h
  show epollPwait2SpecX86 _ _ _ _ _ _ i m o ↔ epollPwait2SpecX86FdFirst _ _ _ _ _ _ i m o
  unfold epollPwait2SpecX86 epollPwait2SpecX86FdFirst
  rw [Sys.bind_input_iff, Sys.bind_input_iff]
  cases ht : pselectTimeout i.mem (i.arg 3) with
  | toFault => exact Iff.rfl
  | toInval => exact Iff.rfl
  | toNone | toZero | toDeadline =>
    rw [ht] at hd
    exact epollPwaitSpecWith_congr .x86 .x86FdFirst _ _ _ _ _ i m
      (epollPwaitOrders_agree i m _ _ _ _ _ (by simpa [timeoutPasses] using hd)) o

/-- (a) The installed `epoll_wait` arm restricts the v6.14-order arm. -/
theorem epollWait_restricts_v614 :
    Restricts (chaos epollWaitArmX86).spec epollWaitArmX86.spec :=
  fun i m => chaos_restricts epollWaitArmX86 i m

/-- (b) The installed `epoll_wait` arm restricts the v6.15-order arm. -/
theorem epollWait_restricts_v615 :
    Restricts (chaos epollWaitArmX86).spec epollWaitArmX86FdFirst.spec :=
  chaos_restricts_of _ _ (by decide) epollWait_agree

/-- (a) The installed `epoll_pwait` arm restricts the v6.14-order arm. -/
theorem epollPwait_restricts_v614 :
    Restricts (chaos epollPwaitArmX86).spec epollPwaitArmX86.spec :=
  fun i m => chaos_restricts epollPwaitArmX86 i m

/-- (b) The installed `epoll_pwait` arm restricts the v6.15-order arm. -/
theorem epollPwait_restricts_v615 :
    Restricts (chaos epollPwaitArmX86).spec epollPwaitArmX86FdFirst.spec :=
  chaos_restricts_of _ _ (by decide) epollPwait_agree

/-- (a) The installed `epoll_pwait2` arm restricts the v6.14-order arm. -/
theorem epollPwait2_restricts_v614 :
    Restricts (guardGap epollPwait2Arm).spec epollPwait2ArmExact.spec :=
  guardGap_restricts_of _ _ fun _ _ _ _ => Iff.rfl

/-- (b) The installed `epoll_pwait2` arm restricts the v6.15-order arm. -/
theorem epollPwait2_restricts_v615 :
    Restricts (guardGap epollPwait2Arm).spec epollPwait2ArmFdFirst.spec :=
  guardGap_restricts_of _ _ epollPwait2_agree

/-- Both guarded: the installed `epoll_pwait2` restricts the guarded v6.14-order arm. -/
theorem epollPwait2_guarded_restricts :
    Restricts (guardGap epollPwait2Arm).spec (guardGap epollPwait2ArmExact).spec := by
  intro i m
  cases hs : suspectGap 441 i
  · rcases epollOrderChaos_restricts epollPwait2ArmExact i m with r | r
    · exact .inl fun o => (guardGap_spec_of_not_suspect _ i m o hs).trans
        ((r o).trans (guardGap_spec_of_not_suspect _ i m o hs).symm)
    · exact .inr fun o => (guardGap_spec_of_not_suspect _ i m o hs).trans (r o)
  · exact .inl fun o => (guardGap_spec_of_suspect _ i m o hs).trans
      (guardGap_spec_of_suspect _ i m o hs).symm

/-- The gap sweep's arms with the exact (v6.14-order) `epoll_pwait2`. -/
def gapArmsExact : List SpecArm :=
  [archPrctlArmFull, setrlimitArm, killArm, epollPwait2ArmExact, clockNanosleepArm].map guardGap

/-- The exact variant of the gap table: the exact `epoll_pwait2` in front of the hub's exact
table. -/
def gapTableExact : List SpecArm := gapArmsExact ++ exactTable

/-- (a) **The gap table restricts its exact variant** (`Lattice.Restricts`): it only declines. -/
theorem gapTable_restricts_exact : Restricts (dispatch gapTable) (dispatch gapTableExact) := by
  intro i m
  have hnum : armNumbers gapArmsExact = gapNumbers := rfl
  by_cases hmem : i.sysno.toNat ∈ gapNumbers
  · have key : ∀ (a b : SpecArm), lookupArm gapArms i.sysno.toNat = some a →
        lookupArm gapArmsExact i.sysno.toNat = some b →
        ((∀ o, a.spec i m o ↔ b.spec i m o) ∨ (∀ o, a.spec i m o ↔ o = .unmodeled)) →
        RestrictsAt (dispatch gapTable) (dispatch gapTableExact) i m := by
      intro a b ha hb r
      have e1 : ∀ o, dispatch gapTable i m o ↔ a.spec i m o := fun o => by
        simp [dispatch, gapTable, lookupArm_append, ha]
      have e2 : ∀ o, dispatch gapTableExact i m o ↔ b.spec i m o := fun o => by
        simp [dispatch, gapTableExact, lookupArm_append, hb]
      rcases r with r | r
      · exact .inl fun o => (e1 o).trans ((r o).trans (e2 o).symm)
      · exact .inr fun o => (e1 o).trans (r o)
    simp only [gapNumbers, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h <;> rw [h] at key
    · exact key _ _ rfl rfl (.inl fun _ => Iff.rfl)
    · exact key _ _ rfl rfl (.inl fun _ => Iff.rfl)
    · exact key _ _ rfl rfl (.inl fun _ => Iff.rfl)
    · exact key _ _ rfl rfl (epollPwait2_guarded_restricts i m)
    · exact key _ _ rfl rfl (.inl fun _ => Iff.rfl)
  · have ha : lookupArm gapArms i.sysno.toNat = none :=
      lookupArm_none_of_not_mem _ _ (by rw [gapArms_numbers]; exact hmem)
    have hb : lookupArm gapArmsExact i.sysno.toNat = none :=
      lookupArm_none_of_not_mem _ _ (by rw [hnum]; exact hmem)
    have e1 : ∀ o, dispatch gapTable i m o ↔ dispatch nativeTable i m o := fun o => by
      simp only [dispatch, gapTable, lookupArm_append, ha, Option.none_or]
    have e2 : ∀ o, dispatch gapTableExact i m o ↔ dispatch exactTable i m o := fun o => by
      simp only [dispatch, gapTableExact, lookupArm_append, hb, Option.none_or]
    rcases nativeTable_restricts_exact i m with r | r
    · exact .inl fun o => (e1 o).trans ((r o).trans (e2 o).symm)
    · exact .inr fun o => (e1 o).trans (r o)

/-- Hence (`Lattice.obsTrace_mono`) the hub's observable traces are the variant's. -/
theorem obsTrace_hub_le_gap {isa : UserIsa} {segs : List Segment} {c : Config isa}
    {tr : List Event} (h : ObsTrace segs (dispatch nativeTable) noFilter c tr) :
    ObsTrace segs (dispatch gapTable) noFilter c tr :=
  obsTrace_mono gapTable_restricts (filtersAgree_noFilter _ _) h

end Silmaril.Process.LPS.NativeX86.GapSweep

/-! ## The FS-base read-back machine -/

namespace Silmaril.Process.LPS.Machines

open Silmaril.Process.LPS Silmaril.Process.LPS.NativeX86.GapSweep

/-- A successful `ARCH_GET_FS` at the native machine. -/
def IsGetFs (s : X86State) (effect : SyscallEffect) : Prop :=
  s.pending = some 158 ∧ s.m.core.read .rdi = 0x1003 ∧ effect.ret = 0

instance (s : X86State) (effect : SyscallEffect) : Decidable (IsGetFs s effect) := by
  unfold IsGetFs; infer_instance

/-- `x86ApplyEffectNative`, except that a successful `ARCH_GET_FS` stores the machine's FS
base at RSI instead of the bytes the effect carries. -/
def x86ApplyEffectNativeFs (s : X86State) (effect : SyscallEffect) : X86State :=
  if IsGetFs s effect then
    x86ApplyEffectNative s { effect with writes := [
      (s.m.core.read .rsi, NativeX86.GapSweep.le8 s.m.core.fsBase)] }
  else x86ApplyEffectNative s effect

/-- The native machine with the FS-base read-back. -/
def x86ExtNativeFs : UserIsa := { x86ExtNative with applyEffect := x86ApplyEffectNativeFs }

theorem x86ApplyEffectNativeFs_other (s : X86State) (effect : SyscallEffect)
    (h : ¬ IsGetFs s effect) : x86ApplyEffectNativeFs s effect = x86ApplyEffectNative s effect := by
  simp [x86ApplyEffectNativeFs, h]

theorem x86ApplyEffectNativeFs_getFs (s : X86State) (v : Word) (h : IsGetFs s (mkEffect 0
      [(s.m.core.read .rsi, NativeX86.GapSweep.le8 v)] [])) :
    x86ApplyEffectNativeFs s (mkEffect 0 [(s.m.core.read .rsi, NativeX86.GapSweep.le8 v)] []) =
      x86ApplyEffectNative s (mkEffect 0 [
        (s.m.core.read .rsi, NativeX86.GapSweep.le8 s.m.core.fsBase)] []) := by
  simp only [x86ApplyEffectNativeFs, h, ↓reduceIte]
  rfl

/-- `ARCH_SET_FS` is unchanged: the read-back machine stores the base. -/
theorem x86ApplyEffectNativeFs_setFs (s : X86State) (effect : SyscallEffect)
    (pending : s.pending = some 158) (operation : s.m.core.read .rdi = 0x1002)
    (success : effect.ret = 0) :
    (x86ApplyEffectNativeFs s effect).m.core.fsBase = s.m.core.read .rsi := by
  have h : ¬ IsGetFs s effect := by
    rintro ⟨-, op, -⟩; rw [operation] at op; exact absurd op (by decide)
  rw [x86ApplyEffectNativeFs_other s effect h]
  exact x86ApplyEffectNative_setFs s effect pending operation success

/-- A successful `ARCH_GET_FS` step of the read-back machine is the native machine's step for
an effect the variant's specification admits: the one whose chosen base is the FS base. -/
theorem getFs_step_admitted (s : X86State) (i : SyscallInput) (m m' : Model)
    (evs : List Event) (effect : SyscallEffect) (pending : s.pending = some 158)
    (operation : s.m.core.read .rdi = 0x1003) (spec : archPrctlSpecFull archGetFs
      (s.m.core.read .rsi) i m (.ok effect m' evs))
    (ok : accessOkbX86 (s.m.core.read .rsi) 8 = true) (bs : List Byte)
    (w : readBytesMap i.wmem (s.m.core.read .rsi) 8 = some bs) :
    x86ApplyEffectNativeFs s effect =
        x86ApplyEffectNative s (mkEffect 0 [
          (s.m.core.read .rsi, NativeX86.GapSweep.le8 s.m.core.fsBase)] []) ∧
      archPrctlSpecFull archGetFs (s.m.core.read .rsi) i m
        (.ok (mkEffect 0 [(s.m.core.read .rsi, NativeX86.GapSweep.le8 s.m.core.fsBase)] [])
          m []) := by
  rw [archPrctlFull_getFs] at spec ⊢
  obtain ⟨v, hv⟩ := (getBaseSpec_writable _ i m ok bs w _).1 spec
  cases hv
  refine ⟨x86ApplyEffectNativeFs_getFs s v ⟨pending, operation, rfl⟩, ?_⟩
  exact (getBaseSpec_writable _ i m ok bs w _).2 ⟨_, rfl⟩

/-- `getFs_step_admitted` at the variant's guarded dispatch: a successful, non-suspect
`ARCH_GET_FS` step of `dispatch gapTable` whose input is the machine's call applies, on the
read-back machine, the effect that stores the FS base, and `dispatch gapTable` admits that
effect. -/
theorem getFs_dispatch_admitted (s : X86State) (i : SyscallInput) (m m' : Model)
    (evs : List Event) (effect : SyscallEffect) (pending : s.pending = some 158)
    (operation : s.m.core.read .rdi = 0x1003) (no : i.sysno.toNat = 158)
    (op : i.arg 0 = archGetFs) (addr : i.arg 1 = s.m.core.read .rsi)
    (ns : suspectGap 158 i = false) (step : dispatch gapTable i m (.ok effect m' evs))
    (ok : accessOkbX86 (s.m.core.read .rsi) 8 = true) (bs : List Byte)
    (w : readBytesMap i.wmem (s.m.core.read .rsi) 8 = some bs) :
    x86ApplyEffectNativeFs s effect =
        x86ApplyEffectNative s (mkEffect 0 [
          (s.m.core.read .rsi, NativeX86.GapSweep.le8 s.m.core.fsBase)] []) ∧
      dispatch gapTable i m
        (.ok (mkEffect 0 [(s.m.core.read .rsi, NativeX86.GapSweep.le8 s.m.core.fsBase)] [])
          m []) := by
  rw [dispatch_gapTable_getFs i m _ no op ns, addr] at step
  have h := getFs_step_admitted s i m m' evs effect pending operation
    (by rw [archPrctlFull_getFs]; exact step) ok bs w
  refine ⟨h.1, ?_⟩
  rw [dispatch_gapTable_getFs i m _ no op ns, addr, ← archPrctlFull_getFs]
  exact h.2

end Silmaril.Process.LPS.Machines
