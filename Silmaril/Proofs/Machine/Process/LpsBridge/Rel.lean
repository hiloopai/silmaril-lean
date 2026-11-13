module

public import Silmaril.Machine.Process.LpsBridge.Rel.Defs
public import Silmaril.Machine.Process.LpsBridge.Thms
public import Silmaril.Machine.X86.RelIsa.Thms
public import Silmaril.Machine.X86.RelIsa.Safe.Thms
public import Silmaril.Process.LPS.Equivalence

/-!
# Proofs: the LPS bridge over relational machines

Names are in `Silmaril.Proofs.Machine.Process.LpsBridge` (as the rest of the
bridge). Everything is generic in the native step `nstep` and the deterministic machine `c`
with `Agrees nstep c`; the original bridge is the instance `nstep := x86NativeStep8`,
`c := Open.step` (`agrees_open8`, `flagMachine_eight`).

* Steps: `sstepF_of_account`, `sstepF_step` (an `Agrees` step from an aligned configuration is
  the only LPS step), `sstepF_trap` (the trap).
* **`psafeF_of_safeN`** (the instruction half for any agreeing `c`), and
  **`psafe_of_safeNR`**: demonic safety `∀ n, SafeNR A Q n m` on any relational `A` that
  `ofFun c` refines gives process safety, given process safety at the `Q` states.
* The syscall half over `flagMachine`: `haltedF_no_step`, `starF_halted`, `psafeF_syscall`,
  `psafeF_exit`.
* Must-exit: `mustExitF_exit`, `mustExitF_of_mustFun`, and **`mustExit_of_must`**: a demonic
  total run `Must A ⊤ (AtSyscall ∧ exit request)` on any `A` above `ofFun c` gives LPS's
  must-exit tier. This replaces a terminating-run hypothesis (`mustExit_of_run`) by a
  relational one.
* Launch: `initF_aligned`, `processSafeF_of_launchR`, `mustExitF_of_launchR`.
* The Ext8 instance: `flagMachine_eight`, **`agrees_open8`** (from the facts behind
  `sstep_open`/`account_trap`), `alignedF_iff`, `psafeF_iff`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.X86 (RelIsa)
open Silmaril.Machine.X86.RelIsa (Le Must SafeNR ofFun)
open Silmaril.Machine.X86.Safe (SafeN)

variable {oracle : Oracle} {nstep : NStep} {c : MState → Option MState}
  {segs : List Segment} {refused : RefusalFilter}

/-! ## LPS steps of `flagMachine` from an aligned configuration -/

/-- With no syscall pending, the only LPS step is the accounted instruction. -/
theorem sstepF_of_account {cfg : Config (flagMachine oracle nstep)}
    {ms' : (flagMachine oracle nstep).State} {model' : Model} (alive : cfg.model.halted = none)
    (pending : cfg.ms.native.pending = none)
    (account : accountStep (flagMachine oracle nstep) segs cfg.ms cfg.model = .ok (ms', model')) :
    SStep segs spec refused cfg [] (.next ⟨ms', model'⟩) ∧
      ∀ evs st, SStep segs spec refused cfg evs st → evs = [] ∧ st = .next ⟨ms', model'⟩ := by
  obtain ⟨ms, model⟩ := cfg
  have svc : (flagMachine oracle nstep).svcPending ms = none := pending
  refine ⟨.instr alive svc account, fun evs st s => ?_⟩
  cases s with
  | instr _ _ a => rw [account] at a; cases a; exact ⟨rfl, rfl⟩
  | instrFault _ _ a => rw [account] at a; cases a
  | instrUnmodeled _ _ a => rw [account] at a; cases a
  | syscall _ p => rw [svc] at p; cases p
  | syscallMaterializationFault _ p => rw [svc] at p; cases p
  | exit _ p => rw [svc] at p; cases p
  | killed _ p => rw [svc] at p; cases p
  | syscallUnmodeled _ p => rw [svc] at p; cases p

theorem cfg_ms_eq {cfg : Config (flagMachine oracle nstep)} {m : MState} (al : AlignedF cfg m) :
    cfg.ms = ⟨⟨m, none⟩, cfg.ms.counter⟩ := by
  obtain ⟨⟨n, k⟩, model⟩ := cfg
  have := al.native
  simp only at this
  subst this
  rfl

/-- **An agreeing step from an aligned configuration is the only LPS step.** -/
theorem sstepF_step (hM : Agrees nstep c) {cfg : Config (flagMachine oracle nstep)}
    {m m' : MState} (al : AlignedF cfg m) (hs : c m = some m') :
    SStep segs spec refused cfg [] (.next ⟨⟨⟨m', none⟩, cfg.ms.counter⟩, cfg.model⟩) ∧
      ∀ evs st, SStep segs spec refused cfg evs st →
        evs = [] ∧ st = .next ⟨⟨⟨m', none⟩, cfg.ms.counter⟩, cfg.model⟩ := by
  have nt : ¬ AtSyscall m := fun ht => by rw [hM.stuck ht] at hs; cases hs
  obtain ⟨acc, hn⟩ := hM.step hs
  have st : (flagMachine oracle nstep).step segs ⟨⟨m, none⟩, cfg.ms.counter⟩ =
      .ok ⟨⟨⟨m', none⟩, cfg.ms.counter⟩, acc⟩ := by
    show flagStep oracle nstep _ = _
    unfold flagStep
    dsimp only
    rw [ite_eq_right (show ¬ (m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05])
      from nt), hn]
    rfl
  have acc' : accountStep (flagMachine oracle nstep) segs cfg.ms cfg.model =
      .ok (⟨⟨m', none⟩, cfg.ms.counter⟩, cfg.model) := by
    rw [cfg_ms_eq al]
    simp only [accountStep, st]
    rw [show (flagMachine oracle nstep).reportsAccesses = true from rfl]
    simp [X86Launch.materializeModelAccesses_no_lazy _ _ al.lazy]
  refine sstepF_of_account al.alive ?_ acc'
  rw [al.native]

/-- **The trap from an aligned configuration is the only LPS step.** -/
theorem sstepF_trap (hM : Agrees nstep c) {cfg : Config (flagMachine oracle nstep)} {m : MState}
    (al : AlignedF cfg m) (ht : AtSyscall m) :
    SStep segs spec refused cfg []
        (.next ⟨⟨trapped ⟨m, none⟩ (oracle cfg.ms.counter), cfg.ms.counter + 1⟩, cfg.model⟩) ∧
      ∀ evs st, SStep segs spec refused cfg evs st →
        evs = [] ∧ st = .next ⟨⟨trapped ⟨m, none⟩ (oracle cfg.ms.counter), cfg.ms.counter + 1⟩,
          cfg.model⟩ := by
  have hr := X86FlagChoices.completeFlags_rflagsImage m.core.flags (oracle cfg.ms.counter)
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hr
  have st : (flagMachine oracle nstep).step segs ⟨⟨m, none⟩, cfg.ms.counter⟩ =
      .ok ⟨⟨trapped ⟨m, none⟩ (oracle cfg.ms.counter), cfg.ms.counter + 1⟩, [(m.core.rip, 2)]⟩ := by
    show flagStep oracle nstep _ = _
    unfold flagStep
    dsimp only
    rw [ite_eq_left (show m.memory.fetchBytes m.core.rip.toNat 2 = some [0x0f, 0x05] from ht)]
    rw [hM.trap _ w ht hw]
    rfl
  have acc' : accountStep (flagMachine oracle nstep) segs cfg.ms cfg.model =
      .ok (⟨trapped ⟨m, none⟩ (oracle cfg.ms.counter), cfg.ms.counter + 1⟩, cfg.model) := by
    rw [cfg_ms_eq al]
    simp only [accountStep, st]
    rw [show (flagMachine oracle nstep).reportsAccesses = true from rfl]
    simp [X86Launch.materializeModelAccesses_no_lazy _ _ al.lazy]
  refine sstepF_of_account al.alive ?_ acc'
  rw [al.native]

/-! ## The instruction half -/

theorem safeN_succ_of {Q : MState → Prop} {m m' : MState} (hq : ¬ Q m) (hs : c m = some m')
    (h : ∀ n, SafeN c Q n m) : ∀ n, SafeN c Q n m' := by
  intro n
  rcases h (n + 1) with h | ⟨m'', hs', hn⟩
  · exact absurd h hq
  · rw [hs] at hs'; cases hs'; exact hn

theorem safeN_step_of {Q : MState → Prop} {m : MState} (hq : ¬ Q m) (h : ∀ n, SafeN c Q n m) :
    ∃ m', c m = some m' := by
  rcases h 1 with h | ⟨m', hs, -⟩
  · exact absurd h hq
  · exact ⟨m', hs⟩

/-- **The instruction half for any agreeing deterministic machine.** -/
theorem psafeF_of_safeN (hM : Agrees nstep c) {Q : MState → Prop}
    {Allowed : List Event → Prop} {model : Model} (hA : Allowed [])
    (hQ : ∀ (c' : Config (flagMachine oracle nstep)) m', AlignedF c' m' → c'.model = model →
      Q m' → PSafeF segs refused Allowed c')
    {cfg : Config (flagMachine oracle nstep)} {m : MState} (al : AlignedF cfg m)
    (hm : cfg.model = model) (h : ∀ n, SafeN c Q n m) : PSafeF segs refused Allowed cfg := by
  constructor
  · intro tr c' hstar
    induction hstar generalizing m with
    | refl => exact hA
    | @step c₁ evs c₂ tr c₃ s rest ih =>
      by_cases hq : Q m
      · exact (hQ c₁ m al hm hq).1 _ _ (.step s rest)
      · obtain ⟨m₁, hs⟩ := safeN_step_of hq h
        obtain ⟨-, uniq⟩ := sstepF_step (segs := segs) (refused := refused) hM al hs
        obtain ⟨rfl, e⟩ := uniq _ _ s
        cases e
        exact ih ⟨rfl, al.alive, al.lazy⟩ hm (safeN_succ_of hq hs h)
  · intro tr c' evs hstar
    induction hstar generalizing m with
    | refl c₀ =>
      intro herr
      by_cases hq : Q m
      · exact (hQ c₀ m al hm hq).2 [] c₀ evs (.refl _) herr
      · obtain ⟨m₁, hs⟩ := safeN_step_of hq h
        obtain ⟨-, uniq⟩ := sstepF_step (segs := segs) (refused := refused) hM al hs
        cases (uniq _ _ herr).2
    | @step c₁ evs' c₂ tr c₃ s rest ih =>
      by_cases hq : Q m
      · exact (hQ c₁ m al hm hq).2 _ _ evs (.step s rest)
      · obtain ⟨m₁, hs⟩ := safeN_step_of hq h
        obtain ⟨-, uniq⟩ := sstepF_step (segs := segs) (refused := refused) hM al hs
        obtain ⟨rfl, e⟩ := uniq _ _ s
        cases e
        exact ih ⟨rfl, al.alive, al.lazy⟩ hm (safeN_succ_of hq hs h)

/-- **Process safety from demonic safety on a relational machine.** If `nstep` agrees with the
deterministic `c`, `ofFun c` refines `A`, and the open state of an aligned configuration is
`SafeNR A Q n` for every `n`, the configuration is process-safe, given process safety at
every aligned `Q` state with the same model. -/
theorem psafe_of_safeNR {A : RelIsa MState} (hM : Agrees nstep c) (hle : Le (ofFun c) A)
    {Q : MState → Prop} {Allowed : List Event → Prop} {model : Model} (hA : Allowed [])
    (hQ : ∀ (c' : Config (flagMachine oracle nstep)) m', AlignedF c' m' → c'.model = model →
      Q m' → PSafeF segs refused Allowed c')
    {cfg : Config (flagMachine oracle nstep)} {m : MState} (al : AlignedF cfg m)
    (hm : cfg.model = model) (h : ∀ n, SafeNR A Q n m) : PSafeF segs refused Allowed cfg :=
  psafeF_of_safeN hM hA hQ al hm fun n => Silmaril.Machine.X86.RelIsa.safeN_of_safeNR hle (h n)

/-! ## The syscall half over `flagMachine` -/

theorem haltedF_no_step {cfg : Config (flagMachine oracle nstep)} (h : cfg.model.halted ≠ none)
    {evs : List Event} {st : StepTo (flagMachine oracle nstep)} :
    ¬ SStep segs spec refused cfg evs st := by
  intro s
  cases s with
  | instr a _ _ => exact h a
  | instrFault a _ _ => exact h a
  | instrUnmodeled a _ _ => exact h a
  | syscall a _ _ _ _ _ => exact h a
  | syscallMaterializationFault a _ _ _ _ _ => exact h a
  | exit a _ _ _ _ => exact h a
  | killed a _ _ _ => exact h a
  | syscallUnmodeled a _ _ => exact h a

theorem starF_halted {c₁ c₂ : Config (flagMachine oracle nstep)} {tr : List Event}
    (h : c₁.model.halted ≠ none) (s : Star segs spec refused c₁ tr c₂) : tr = [] ∧ c₂ = c₁ := by
  cases s with
  | refl => exact ⟨rfl, rfl⟩
  | step s₁ _ => exact absurd s₁ (haltedF_no_step h)

/-- The trap configuration of an aligned configuration. -/
abbrev trapCfgF (cfg : Config (flagMachine oracle nstep)) (m : MState) :
    Config (flagMachine oracle nstep) :=
  ⟨⟨trapped ⟨m, none⟩ (oracle cfg.ms.counter), cfg.ms.counter + 1⟩, cfg.model⟩

/-- The request LPS reads at the trap. -/
abbrev trapRequestF (segs : List Segment) (cfg : Config (flagMachine oracle nstep))
    (m : MState) : SyscallInput :=
  sysInput (flagMachine oracle nstep) segs (trapCfgF cfg m).ms
    ((trapCfgF cfg m).ms.native.m.core.read .rax)

/-- The outcome obligations of a syscall from an aligned trap. -/
def OutcomesF (segs : List Segment) (refused : RefusalFilter) (Allowed : List Event → Prop)
    (cfg : Config (flagMachine oracle nstep)) (m : MState) : Prop :=
  ∀ eff model' evs, spec (trapRequestF segs cfg m) cfg.model (.ok eff model' evs) →
    model'.killedBy = none ∧
    (model'.halted = none → model'.vmLazy = [] ∧
      (¬ refused (trapRequestF segs cfg m) cfg.model eff →
        ∀ c' : Config (flagMachine oracle nstep),
          AlignedF c' (resume (trapped ⟨m, none⟩ (oracle cfg.ms.counter)) eff) →
          c'.model = model' → PSafeF segs refused (fun tr => Allowed (evs ++ tr)) c')) ∧
    (∀ code, model'.halted = some code → Allowed (evs ++ [.exitEv code model'.fs]))

theorem trapF_steps {Allowed : List Event → Prop} {cfg : Config (flagMachine oracle nstep)}
    {m : MState} (hunmod : ¬ spec (trapRequestF segs cfg m) cfg.model .unmodeled)
    (hok : OutcomesF segs refused Allowed cfg m) (hA : Allowed []) :
    (∀ tr c', Star segs spec refused (trapCfgF cfg m) tr c' → Allowed tr) ∧
      ∀ tr c' evs, Star segs spec refused (trapCfgF cfg m) tr c' →
        ¬ SStep segs spec refused c' evs .error := by
  have svc : (flagMachine oracle nstep).svcPending (trapCfgF cfg m).ms =
      some (m.core.read .rax) := rfl
  constructor
  · intro tr c' hstar
    cases hstar with
    | refl => exact hA
    | step s rest =>
      cases s with
      | instr _ p => rw [svc] at p; cases p
      | @syscall _ _ x8 eff model' model'' evs _ p hs hr hh hmat =>
        rw [svc] at p; cases p
        obtain ⟨-, hres, -⟩ := hok _ _ _ hs
        obtain ⟨lazy, cont⟩ := hres hh
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ lazy] at hmat
        cases hmat
        exact (cont hr _ ⟨rfl, hh, lazy⟩ rfl).1 _ _ rest
      | @exit _ _ x8 eff model' evs code _ p hs hh hk =>
        rw [svc] at p; cases p
        obtain ⟨rfl, rfl⟩ := starF_halted (by simp [hh]) rest
        rw [List.append_nil]
        exact (hok _ _ _ hs).2.2 code hh
      | @killed _ _ x8 eff model' evs sig _ p hs hk =>
        rw [svc] at p; cases p
        rw [(hok _ _ _ hs).1] at hk; cases hk
  · intro tr c' evs hstar herr
    cases hstar with
    | refl =>
      cases herr with
      | instrFault _ p => rw [svc] at p; cases p
      | instrUnmodeled _ p => rw [svc] at p; cases p
      | @syscallMaterializationFault _ _ x8 eff model' evs _ p hs hr hh hmat =>
        rw [svc] at p; cases p
        obtain ⟨-, hres, -⟩ := hok _ _ _ hs
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ (hres hh).1] at hmat
        cases hmat
      | syscallUnmodeled _ p hs => rw [svc] at p; cases p; exact hunmod hs
    | step s rest =>
      cases s with
      | instr _ p => rw [svc] at p; cases p
      | @syscall _ _ x8 eff model' model'' evs' _ p hs hr hh hmat =>
        rw [svc] at p; cases p
        obtain ⟨-, hres, -⟩ := hok _ _ _ hs
        obtain ⟨lazy, cont⟩ := hres hh
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ lazy] at hmat
        cases hmat
        exact (cont hr _ ⟨rfl, hh, lazy⟩ rfl).2 _ _ _ rest herr
      | @exit _ _ x8 eff model' evs' code _ p hs hh hk =>
        obtain ⟨-, rfl⟩ := starF_halted (by simp [hh]) rest
        exact haltedF_no_step (by simp [hh]) herr
      | @killed _ _ x8 eff model' evs' sig _ p hs hk =>
        rw [svc] at p; cases p
        rw [(hok _ _ _ hs).1] at hk; cases hk

/-- **The generic syscall half** over `flagMachine`. -/
theorem psafeF_syscall (hM : Agrees nstep c) {Allowed : List Event → Prop}
    {cfg : Config (flagMachine oracle nstep)} {m : MState} (al : AlignedF cfg m)
    (ht : AtSyscall m) (hA : Allowed [])
    (hunmod : ¬ spec (trapRequestF segs cfg m) cfg.model .unmodeled)
    (hok : OutcomesF segs refused Allowed cfg m) : PSafeF segs refused Allowed cfg := by
  obtain ⟨-, uniq⟩ := sstepF_trap (segs := segs) (refused := refused) hM al ht
  have T := trapF_steps hunmod hok hA
  constructor
  · intro tr c' hstar
    cases hstar with
    | refl => exact hA
    | step s rest =>
      obtain ⟨rfl, e⟩ := uniq _ _ s
      cases e
      exact T.1 _ _ rest
  · intro tr c' evs hstar herr
    cases hstar with
    | refl => cases (uniq _ _ herr).2
    | step s rest =>
      obtain ⟨rfl, e⟩ := uniq _ _ s
      cases e
      exact T.2 _ _ _ rest herr

/-- **The `exit` arm** over `flagMachine`. -/
theorem psafeF_exit (hM : Agrees nstep c) {Allowed : List Event → Prop}
    {cfg : Config (flagMachine oracle nstep)} {m : MState} (al : AlignedF cfg m)
    (ht : AtSyscall m)
    (number : (m.core.read .rax).toNat = 60 ∨ (m.core.read .rax).toNat = 231)
    (hA : Allowed []) (hE : Allowed [.exitEv (m.core.read .rdi &&& 255) cfg.model.fs]) :
    PSafeF segs refused Allowed cfg := by
  have hno : (trapRequestF segs cfg m).sysno.toNat = 60 ∨
      (trapRequestF segs cfg m).sysno.toNat = 231 := number
  have harg : (trapRequestF segs cfg m).arg 0 = m.core.read .rdi := rfl
  refine psafeF_syscall hM al ht hA ?_ ?_
  · intro hs
    have := (exit_dispatch _ _ _ hno).1 hs
    cases this
  · intro eff model' evs hs
    have := (exit_dispatch _ _ _ hno).1 hs
    cases this
    refine ⟨?_, fun hh => by simp [Model.withHalted, Model.halted] at hh, ?_⟩
    · simp [Model.withHalted, Model.killedBy]
    · intro code hc
      simp only [Model.withHalted, Model.halted, Option.some.injEq] at hc
      subst hc
      rw [harg, List.nil_append]
      exact hE

/-! ## Must-exit -/

/-- **The `exit` request must exit** (over `flagMachine`). -/
theorem mustExitF_exit (hM : Agrees nstep c) {cfg : Config (flagMachine oracle nstep)}
    {m : MState} (al : AlignedF cfg m) (ht : AtSyscall m)
    (number : (m.core.read .rax).toNat = 60 ∨ (m.core.read .rax).toNat = 231) :
    MustExitInAt segs spec refused [m.core.read .rdi &&& 255] cfg := by
  obtain ⟨hstep, uniq⟩ := sstepF_trap (segs := segs) (refused := refused) hM al ht
  have hno : (trapRequestF segs cfg m).sysno.toNat = 60 ∨
      (trapRequestF segs cfg m).sysno.toNat = 231 := number
  have harg : (trapRequestF segs cfg m).arg 0 = m.core.read .rdi := rfl
  have svc : (flagMachine oracle nstep).svcPending (trapCfgF cfg m).ms =
      some (m.core.read .rax) := rfl
  have disp := fun o => exit_dispatch (trapRequestF segs cfg m) cfg.model o hno
  refine .running al.alive ⟨_, _, hstep⟩ (fun evs herr => by cases (uniq _ _ herr).2) ?_
  intro evs c' hs
  obtain ⟨-, e⟩ := uniq _ _ hs
  cases e
  refine .running al.alive ⟨_, _, SStep.exit (code := m.core.read .rdi &&& 255) al.alive svc
    ((disp _).2 (by rw [harg])) (by simp [Model.withHalted, Model.halted])
    (by simp [Model.withHalted, Model.killedBy])⟩ ?_ ?_
  · intro evs herr
    cases herr with
    | instrFault _ p => rw [svc] at p; cases p
    | instrUnmodeled _ p => rw [svc] at p; cases p
    | syscallMaterializationFault _ p hs hr hh hmat =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      simp [Model.withHalted, Model.halted] at hh
    | syscallUnmodeled _ p hs =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
  · intro evs c'' hs
    cases hs with
    | instr _ p => rw [svc] at p; cases p
    | syscall _ p hs hr hh hmat =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      simp [Model.withHalted, Model.halted] at hh
    | exit _ p hs hh hk =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      refine .halted hh ?_ hk
      simp only [Model.withHalted, Model.halted, Option.some.injEq] at hh
      rw [← hh, harg]; exact List.mem_singleton_self _
    | killed _ p hs hk =>
      rw [svc] at p; cases p
      have := (disp _).1 hs; cases this
      simp [Model.withHalted, Model.killedBy] at hk

/-- An `exit` request: `0F 05` at `rip` and `rax ∈ {60, 231}`. -/
def ExitReq (m : MState) : Prop :=
  AtSyscall m ∧ ((m.core.read .rax).toNat = 60 ∨ (m.core.read .rax).toNat = 231)

/-- **Must-exit from a total demonic run of the deterministic machine** whose every final state
is an `exit` request with status `code`. -/
theorem mustExitF_of_mustFun (hM : Agrees nstep c) {code : Silmaril.X86.Word} {R : MState → Prop}
    {m : MState}
    (h : Must (ofFun c) R (fun m' => ExitReq m' ∧ m'.core.read .rdi &&& 255 = code) m) :
    ∀ {cfg : Config (flagMachine oracle nstep)}, AlignedF cfg m →
      MustExitInAt segs spec refused [code] cfg := by
  induction h with
  | done hq =>
    intro cfg al
    obtain ⟨⟨ht, hn⟩, hc⟩ := hq
    rw [← hc]
    exact mustExitF_exit hM al ht hn
  | @step s _ hs _ ih =>
    intro cfg al
    cases e : c s with
    | none =>
      exact absurd (Silmaril.Machine.X86.RelIsa.ofFun_step_stop.mpr e) hs
    | some s' =>
      obtain ⟨hstep, uniq⟩ := sstepF_step (segs := segs) (refused := refused) hM al e
      refine .running al.alive ⟨_, _, hstep⟩ (fun evs herr => by cases (uniq _ _ herr).2) ?_
      intro evs c' hs'
      obtain ⟨-, e'⟩ := uniq _ _ hs'
      cases e'
      exact ih s' (Silmaril.Machine.X86.RelIsa.ofFun_step_ok.mpr e) ⟨rfl, al.alive, al.lazy⟩

/-- **Must-exit from a total demonic run on a relational machine.** If `nstep` agrees with `c`,
`ofFun c` refines `A`, and every run of `A` from the open state of an aligned configuration
terminates, without stopping, at an `exit` request with status `code`, the configuration must
exit with `code` (LPS's must-exit tier: never an error, never stalls). -/
theorem mustExit_of_must {A : RelIsa MState} (hM : Agrees nstep c) (hle : Le (ofFun c) A)
    {code : Silmaril.X86.Word} {cfg : Config (flagMachine oracle nstep)} {m : MState}
    (al : AlignedF cfg m)
    (h : Must A (fun _ => True) (fun m' => ExitReq m' ∧ m'.core.read .rdi &&& 255 = code) m) :
    MustExitInAt segs spec refused [code] cfg :=
  mustExitF_of_mustFun hM (Silmaril.Machine.X86.RelIsa.Must.of_le hle trivial h) al

/-! ## Launch -/

theorem initF_aligned (oracle : Oracle) (nstep : NStep) (snapshot : X86Launch.Snapshot)
    (en : ExecEntry) (limit : Int) (inp : ProcInput) :
    AlignedF (X86Launch.init (flagMachine oracle nstep) snapshot en limit inp)
      (launchState snapshot en inp) :=
  ⟨rfl, rfl, rfl⟩

/-- **The whole-process schema** over a relational machine. -/
theorem processSafeF_of_launchR {A : RelIsa MState} (hM : Agrees nstep c) (hle : Le (ofFun c) A)
    {snapshot : X86Launch.Snapshot} {refusals : SpuriousCfg}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {Allowed : List Event → Prop}
    {Q : MState → Prop} (hA : Allowed [])
    (hrun : ∀ n, SafeNR A Q n (launchState snapshot en inp))
    (hQ : ∀ oracle (c' : Config (flagMachine oracle nstep)) m, AlignedF c' m →
      c'.model = (X86Launch.init (flagMachine oracle nstep) snapshot en limit inp).model → Q m →
      PSafeF snapshot.image.segments (NativeX86.defaultRefusalFilter refusals) Allowed c') :
    ProcessSafeF nstep snapshot refusals limit en inp Allowed := fun oracle =>
  psafe_of_safeNR hM hle hA (hQ oracle) (initF_aligned oracle nstep snapshot en limit inp) rfl hrun

/-- **The must-exit tier of a launch** over a relational machine. -/
theorem mustExitF_of_launchR {A : RelIsa MState} (hM : Agrees nstep c) (hle : Le (ofFun c) A)
    {snapshot : X86Launch.Snapshot} {en : ExecEntry} {inp : ProcInput} {limit : Int}
    {code : Silmaril.X86.Word}
    (h : Must A (fun _ => True) (fun m' => ExitReq m' ∧ m'.core.read .rdi &&& 255 = code)
      (launchState snapshot en inp))
    (oracle : Oracle) (refused : RefusalFilter) :
    MustExitInAt snapshot.image.segments spec refused [code]
      (X86Launch.init (flagMachine oracle nstep) snapshot en limit inp) :=
  mustExit_of_must hM hle (initF_aligned oracle nstep snapshot en limit inp) h

/-! ## The Ext8 instance -/

/-- The bridge's machine is `flagMachine` over `x86NativeStep8`, by definition. -/
theorem flagMachine_eight (oracle : Oracle) : flagMachine oracle x86NativeStep8 = machine oracle :=
  rfl

/-- **`Open.step` agrees with LPS's native `Ext8` step.** -/
theorem agrees_open8 : Agrees x86NativeStep8 Silmaril.Machine.X86.Open.step where
  stuck ht := open_step_trap ht
  step {m m'} hs := native8_open hs fun ht => by rw [open_step_trap ht] at hs; cases hs
  trap s w ht hw := by
    unfold x86NativeStep8
    rw [ite_eq_left (show s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] from ht),
      hw]

theorem alignedF_iff {cfg : Config (machine oracle)} {m : MState} :
    AlignedF (oracle := oracle) (nstep := x86NativeStep8) cfg m ↔ Aligned cfg m :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

theorem psafeF_iff {Allowed : List Event → Prop} {cfg : Config (machine oracle)} :
    PSafeF (oracle := oracle) (nstep := x86NativeStep8) segs refused Allowed cfg ↔
      PSafe segs refused Allowed cfg :=
  Iff.rfl

end Silmaril.Proofs.Machine.Process.LpsBridge
