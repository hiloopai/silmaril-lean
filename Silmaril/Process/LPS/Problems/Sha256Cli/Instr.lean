module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Bridge
public import Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

/-! # Segment `bridge`: the instruction level, and what is left for system calls

`SimulationAt` (`Bridge.lean`) asks for a `StutterSim` between the LPS run of the pinned ELF
and the CLI process. This file builds it from a concrete relation and proves every part that
concerns instructions (VERIFIED), leaving the system-call part and the launch as explicit
obligations (`SyscallSimAt`).

**The relation.** It is parametrised by a descriptor relation `MR` (between the LPS model and
the CLI descriptor table and history, chosen per launch):

* `RunRel MR c x h` (aligned, running): no LPS syscall pending; the cores agree up to more
  defined LPS flags (`FlagMono.CoreLe`); the memories are equal; neither has exited; LPS has
  no lazy reservation; `MR`.
* `ExitRel c x`: the CLI process has exited with `k` and LPS has halted with `k`, not killed.
* `PendRel MR c x h` (pending): LPS has executed `syscall` (pending number = `rax`); the CLI
  state is still at the `0F 05`; otherwise as `RunRel`.

**Proved here (VERIFIED).** A non-`syscall` instruction: the CLI step retires (it can move,
and `X86Linux.step` is deterministic), so by flag monotonicity (`FlagMono.exec_mono`) the
LPS instruction retires to the same memory with a `CoreLe` core, no lazy page is charged
(`materializeModelAccesses_no_lazy`), and the relation is kept. The `syscall` instruction:
LPS completes the flags and goes to `PendRel` silently. No LPS error is possible from an
aligned pair. Aligned goal states are `ExitRel` with status `0`.

**Obligations (`SyscallObligations`, WIP).** From a pending pair: every LPS syscall step is a
successful step matched by one CLI step (with flattened events) to an aligned pair; LPS can
move; every CLI step is matched by one LPS syscall step. Together with the launch
(`SyscallSimAt`: a CLI launch and an `MR` making the initial configurations aligned), they
give `SimulationAt` (`simulationAt_of_syscallSim`, VERIFIED), hence `BridgeSegment`
(`bridge_of_syscallSim`, VERIFIED).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

variable {oracle : Nat → X86FlagChoices.Choice}

/-- A relation between the LPS model and the CLI system state (memory, descriptors) and
history. -/
abbrev DescRel := Model → Syscall.State → List Syscall.Event → Prop

/-- Aligned, running. -/
structure RunRel (MR : DescRel) (c : Config (machine oracle)) (x : PS) (h : List Syscall.Event) :
    Prop where
  pending : c.ms.native.pending = none
  core : CoreLe x.core c.ms.native.m.core
  memory : c.ms.native.m.memory = x.env.memory
  running : x.env.exited = none
  alive : c.model.halted = none
  lazy : c.model.vmLazy = []
  model : MR c.model x.env h

/-- Aligned, exited. -/
def ExitRel (c : Config (machine oracle)) (x : PS) : Prop :=
  ∃ k, x.env.exited = some k ∧ c.model.halted = some (BitVec.ofNat 64 k) ∧ c.model.killedBy = none

def Rel (MR : DescRel) (c : Config (machine oracle)) (x : PS) (h : List Syscall.Event) : Prop :=
  RunRel MR c x h ∨ ExitRel c x

/-- Pending: LPS has trapped, the CLI state is at the `syscall`. -/
structure PendRel (MR : DescRel) (c : Config (machine oracle)) (x : PS) (h : List Syscall.Event) :
    Prop where
  pending : c.ms.native.pending = some (x.core.read .rax)
  trap : x.env.memory.fetchBytes x.core.rip.toNat 2 = some [0x0f, 0x05]
  core : CoreLe x.core c.ms.native.m.core
  memory : c.ms.native.m.memory = x.env.memory
  running : x.env.exited = none
  alive : c.model.halted = none
  lazy : c.model.vmLazy = []
  model : MR c.model x.env h

/-! ## One LPS instruction against one CLI instruction -/

theorem optLe_completeFlag {a b : Option Bool} (h : OptLe a b) (v : Bool) :
    OptLe a (X86FlagChoices.completeFlag b v) := by
  rcases h with rfl | rfl
  · exact .inl rfl
  · cases a with
    | none => exact .inl rfl
    | some w => exact .refl _

theorem coreLe_complete {s t : Silmaril.X86.State} (h : CoreLe s t) (choice : X86FlagChoices.Choice) :
    CoreLe s { t with flags := X86FlagChoices.completeFlags t.flags choice } := by
  obtain ⟨teq, hf⟩ := h
  refine ⟨?_, ?_⟩
  · rw [teq]
  · exact ⟨optLe_completeFlag hf.carry _, optLe_completeFlag hf.parity _,
      optLe_completeFlag hf.adjust _, optLe_completeFlag hf.zero _, optLe_completeFlag hf.sign _,
      optLe_completeFlag hf.overflow _⟩

theorem CoreLe.rip_eq {s t : Silmaril.X86.State} (h : CoreLe s t) : t.rip = s.rip := by
  rw [h.1]

theorem CoreLe.read_eq {s t : Silmaril.X86.State} (h : CoreLe s t) (r : Silmaril.X86.Reg) :
    t.read r = s.read r := by
  rw [h.1]; rfl

/-- The trapping instruction: LPS completes the flags and records the pending number. -/
theorem account_trap (segs : List Segment) (c : Config (machine oracle)) (lazy : c.model.vmLazy = [])
    (trap : c.ms.native.m.memory.fetchBytes c.ms.native.m.core.rip.toNat 2 = some [0x0f, 0x05]) :
    accountStep (machine oracle) segs c.ms c.model =
      .ok (⟨{ X86FlagChoices.completeState c.ms.native (oracle c.ms.counter) with
          pending := some (c.ms.native.m.core.read .rax) }, c.ms.counter + 1⟩, c.model) := by
  have step : (machine oracle).step segs c.ms = X86FlagChoices.step oracle c.ms := rfl
  simp only [accountStep, step, X86FlagChoices.step_syscall oracle c.ms trap]
  rw [show (machine oracle).reportsAccesses = true from rfl]
  simp [X86Launch.materializeModelAccesses_no_lazy _ _ lazy]

/-- A retiring CLI instruction: the LPS instruction retires to the same memory with a
`CoreLe` core. -/
theorem account_retire (segs : List Segment) (c : Config (machine oracle)) (x : PS)
    (core : CoreLe x.core c.ms.native.m.core) (memory : c.ms.native.m.memory = x.env.memory)
    (lazy : c.model.vmLazy = []) {core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory}
    (retired : CLI.X86Linux.step x.core x.env.memory = .retired core' memory') :
    ∃ t, CoreLe core' t ∧ accountStep (machine oracle) segs c.ms c.model =
      .ok (⟨⟨⟨t, memory'⟩, none⟩, c.ms.counter⟩, c.model) := by
  unfold CLI.X86Linux.step at retired
  split at retired
  · cases retired
  · rename_i notTrap
    have notTrap' : c.ms.native.m.memory.fetchBytes c.ms.native.m.core.rip.toNat 2 ≠
        some [0x0f, 0x05] := by
      rw [memory, CoreLe.rip_eq core]; exact notTrap
    split at retired
    · cases retired
    · cases retired
    · rename_i instr length fetched
      have exec : Silmaril.X86.Ext.exec instr x.core x.env.memory length = .ok core' memory' := by
        revert retired
        cases Silmaril.X86.Ext.exec instr x.core x.env.memory length <;>
          simp [CLI.X86Linux.execResult]
      obtain ⟨t, exec', le⟩ := exec_mono instr x.env.memory length core exec
      refine ⟨t, le, ?_⟩
      have step : (machine oracle).step segs c.ms = X86FlagChoices.step oracle c.ms := rfl
      simp only [accountStep, step, X86FlagChoices.step_not_syscall oracle c.ms notTrap']
      rw [show (machine oracle).reportsAccesses = true from rfl]
      unfold x86NativeStep
      rw [ite_eq_right notTrap', memory, CoreLe.rip_eq core, fetched]
      dsimp only
      rw [exec']
      simp [x86ExecResult, X86FlagChoices.lift, X86Launch.materializeModelAccesses_no_lazy _ _ lazy]

/-! ## LPS steps from an aligned configuration -/

/-- With no syscall pending, the LPS step is the accounted instruction. -/
theorem sstep_of_account {segs : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}
    {c : Config (machine oracle)} {ms' : (machine oracle).State} {model' : Model}
    (alive : c.model.halted = none) (pending : c.ms.native.pending = none)
    (account : accountStep (machine oracle) segs c.ms c.model = .ok (ms', model')) :
    SStep segs spec refused c [] (.next ⟨ms', model'⟩) ∧
      ∀ evs st, SStep segs spec refused c evs st → evs = [] ∧ st = .next ⟨ms', model'⟩ := by
  obtain ⟨ms, model⟩ := c
  have svc : (machine oracle).svcPending ms = none := pending
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

theorem cli_step_syscall_trap {core core' : Silmaril.X86.State} {memory : Silmaril.Process.Memory}
    (h : CLI.X86Linux.step core memory = .syscall core') :
    memory.fetchBytes core.rip.toNat 2 = some [0x0f, 0x05] := by
  unfold CLI.X86Linux.step at h
  split at h
  · rename_i trap; exact trap
  · split at h
    · cases h
    · cases h
    · revert h
      cases Silmaril.X86.Ext.exec _ _ _ _ <;> simp [CLI.X86Linux.execResult]

/-- What the CLI step at `x` is, when one exists: a retirement or the `syscall`. -/
theorem cli_step_form {x : PS} (moves : ∃ e y, CStep x e y) :
    (∃ core' memory', CLI.X86Linux.step x.core x.env.memory = .retired core' memory') ∨
      x.env.memory.fetchBytes x.core.rip.toNat 2 = some [0x0f, 0x05] := by
  obtain ⟨e, y, s⟩ := moves
  cases s with
  | retire _ step => exact .inl ⟨_, _, step.symm⟩
  | call _ step => exact .inr (cli_step_syscall_trap step.symm)
  | exit _ step => exact .inr (cli_step_syscall_trap step.symm)

section Aligned

variable {segs : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}
  {MR : DescRel} {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event}

/-- The `syscall` instruction from an aligned pair: one silent LPS step to a pending pair. -/
theorem aligned_trap (r : RunRel MR c x h)
    (trap : x.env.memory.fetchBytes x.core.rip.toNat 2 = some [0x0f, 0x05]) :
    ∃ c', PendRel MR c' x h ∧ SStep segs spec refused c [] (.next c') ∧
      ∀ evs st, SStep segs spec refused c evs st → evs = [] ∧ st = .next c' := by
  have trap' : c.ms.native.m.memory.fetchBytes c.ms.native.m.core.rip.toNat 2 =
      some [0x0f, 0x05] := by
    rw [r.memory, CoreLe.rip_eq r.core]; exact trap
  obtain ⟨step, unique⟩ := sstep_of_account (spec := spec) (refused := refused) r.alive r.pending
    (account_trap segs c r.lazy trap')
  refine ⟨_, ?_, step, unique⟩
  exact { pending := by
            show some (c.ms.native.m.core.read .rax) = some (x.core.read .rax)
            rw [CoreLe.read_eq r.core]
          trap := trap
          core := coreLe_complete r.core _
          memory := r.memory
          running := r.running
          alive := r.alive
          lazy := r.lazy
          model := r.model }

/-- A retiring instruction from an aligned pair: one silent LPS step, matched by the CLI
retirement, to an aligned pair. -/
theorem aligned_retire (r : RunRel MR c x h) {core' : Silmaril.X86.State}
    {memory' : Silmaril.Process.Memory}
    (retired : CLI.X86Linux.step x.core x.env.memory = .retired core' memory')
    (keep : MR c.model x.env h → MR c.model { x.env with memory := memory' } h) :
    ∃ c', RunRel MR c' ⟨core', { x.env with memory := memory' }⟩ h ∧
      CStep x [] ⟨core', { x.env with memory := memory' }⟩ ∧
      SStep segs spec refused c [] (.next c') ∧
      ∀ evs st, SStep segs spec refused c evs st → evs = [] ∧ st = .next c' := by
  obtain ⟨t, le, account⟩ := account_retire segs c x r.core r.memory r.lazy retired
  obtain ⟨step, unique⟩ := sstep_of_account (spec := spec) (refused := refused) r.alive r.pending
    account
  refine ⟨_, ?_, ?_, step, unique⟩
  · exact { pending := rfl, core := le, memory := rfl, running := r.running, alive := r.alive,
            lazy := r.lazy, model := keep r.model }
  · obtain ⟨core, env⟩ := x
    exact .retire r.running retired.symm

end Aligned

/-! ## The system-call obligations and the assembled simulation -/

/-- The system-call part of the simulation, for one launch and descriptor relation `MR`
(WIP: these are the open obligations of the bridge). -/
structure SyscallObligations (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (inp : ProcInput) (message : List Byte) (input : CLI.ProcInput) (MR : DescRel) : Prop where
  /-- `MR` survives a retiring instruction (it may constrain memory, for instance that every
  permitted byte is backed; instructions only store to permitted bytes). -/
  retire : ∀ {model s h} {core core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory},
    MR model s h → CLI.X86Linux.step core s.memory = .retired core' memory' →
    MR model { s with memory := memory' } h
  /-- Every LPS syscall step from a pending pair succeeds and is one CLI call. -/
  step : ∀ {c : Config (machine oracle)} {x h evs st}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h →
    SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st →
    ∃ c', st = .next c' ∧ ∃ es y, CStep x es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
      Rel MR c' y (h ++ es)
  /-- LPS can complete the call. -/
  progress : ∀ {c : Config (machine oracle)} {x h}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h →
    ∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st
  /-- Some CLI call is one LPS syscall step. -/
  back : ∀ {c : Config (machine oracle)} {x h}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h →
    ∃ es y, CStep x es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
      Rel MR c' y (h ++ es)

/-- The launch-local remainder of the bridge: a CLI launch with the same stdin, a descriptor
relation aligning the initial configurations, and the system-call obligations. -/
def SyscallSimAt (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (input : CLI.ProcInput) (x₀ : PS) (MR : DescRel),
    input.stdin = .ofList message ∧ input.Valid ∧ Launch input x₀ ∧
      Rel MR (initial oracle limit en inp) x₀ [] ∧
      SyscallObligations oracle refusals inp message input MR

/-- **The instruction level (VERIFIED).** The system-call obligations give the simulation. -/
theorem simulationAt_of_syscallSim {refusals : SpuriousCfg} {limit : Int} {en : ExecEntry}
    {inp : ProcInput} {message : List Byte} (h : SyscallSimAt oracle refusals limit en inp message) :
    SimulationAt oracle refusals limit en inp message := by
  obtain ⟨input, x₀, MR, stdin, valid, launch, related, obl⟩ := h
  let sim : StutterSim (isa := machine oracle) snapshot.image.segments
      NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter refusals) CStep
      (Ok message) (Done input message) (evFlat inp.fs) [0] :=
    { rel := Rel MR
      pend := PendRel MR
      stepRel := by
        intro c x h evs st r safe s
        rcases r with r | ⟨k, exited, -, -⟩
        · rcases cli_step_form safe.2.1 with ⟨core', memory', retired⟩ | trap
          · obtain ⟨c', r', cs, -, unique⟩ := aligned_retire (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r retired (obl.retire · retired)
            obtain ⟨rfl, rfl⟩ := unique evs st s
            exact ⟨c', rfl, .inr ⟨[], _, cs, rfl, .inl (by simpa using r')⟩⟩
          · obtain ⟨c', p', -, unique⟩ := aligned_trap (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r trap
            obtain ⟨rfl, rfl⟩ := unique evs st s
            exact ⟨c', rfl, .inl ⟨rfl, p'⟩⟩
        · exact absurd (exited.symm.trans safe.1.1) (by simp)
      stepPend := fun p safe s => obl.step p safe s
      progressRel := by
        intro c x h r safe
        rcases r with r | ⟨k, exited, -, -⟩
        · rcases cli_step_form safe.2.1 with ⟨core', memory', retired⟩ | trap
          · obtain ⟨c', -, -, s, -⟩ := aligned_retire (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r retired (obl.retire · retired)
            exact ⟨_, _, s⟩
          · obtain ⟨c', -, s, -⟩ := aligned_trap (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r trap
            exact ⟨_, _, s⟩
        · exact absurd (exited.symm.trans safe.1.1) (by simp)
      progressPend := fun p safe => obl.progress p safe
      doneRel := by
        intro c x h r done
        rcases r with r | ⟨k, exited, halted, alive⟩
        · exact absurd (done.1.symm.trans r.running) (by simp)
        · have k0 : k = 0 := by simpa using exited.symm.trans done.1
          subst k0
          exact ⟨_, halted, by simp, alive⟩
      donePend := fun p done => absurd (done.1.symm.trans p.running) (by simp)
      back := by
        intro c x h r safe
        rcases r with r | ⟨k, exited, -, -⟩
        · rcases cli_step_form safe.2.1 with ⟨core', memory', retired⟩ | trap
          · obtain ⟨c', r', cs, s, -⟩ := aligned_retire (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r retired (obl.retire · retired)
            refine ⟨[], _, cs, c', Star.one s, .inl ?_⟩
            rw [List.append_nil]
            exact r'
          · obtain ⟨c₁, p₁, s₁, -⟩ := aligned_trap (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r trap
            obtain ⟨es, y, cs, c', s', r'⟩ := obl.back p₁ safe
            exact ⟨es, y, cs, c', by simpa using Star.step s₁ (Star.one s'), r'⟩
        · exact absurd (exited.symm.trans safe.1.1) (by simp) }
  exact ⟨input, x₀, sim, stdin, valid, launch, related⟩

/-- **Reduction (VERIFIED).** The launch-local system-call simulations give the bridge. -/
theorem bridge_of_syscallSim
    (h : ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
      SyscallSimAt oracle refusals limit en inp message) : BridgeSegment :=
  bridge_of_simulation fun oracle refusals limit en inp message admissible =>
    simulationAt_of_syscallSim (h oracle refusals limit en inp message admissible)

end Silmaril.Process.LPS.Problems.Sha256Cli
