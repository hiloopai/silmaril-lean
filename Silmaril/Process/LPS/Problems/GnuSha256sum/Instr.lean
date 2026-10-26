module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysBridge
public import Silmaril.Process.LPS.Problems.Sha256Cli.Instr
public import Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono8

/-! # Segment `bridge` for GNU `sha256sum`: the instruction level

`SimulationAt` (`SysBridge.lean`) asks for a `StutterSim` between the LPS run of
`sha256sum-min` (over `x86WithFlagOracle8`) and the `X86Sys` middle model `GStep`. As for the
`sha256` filter (`Sha256Cli.Instr`), this file builds it from a concrete relation and proves
every part that concerns instructions (VERIFIED), now including the 8-bit forms of `Ext8`
(`FlagMono.exec8_mono`), leaving the system calls and the launch as explicit obligations
(`SyscallSimAt`).

**The relation**, parametrised by a per-launch relation `MR` between the LPS model and the
middle process and history:

* `RunRel MR c g h` (aligned, running): no LPS syscall pending; the cores agree up to more
  defined LPS flags (`FlagMono.CoreLe`); the memories are equal; neither has exited; the
  middle program has not faulted; LPS has no lazy reservation; `MR`.
* `ExitRel c g`: the middle process exited with `k`, LPS halted with `k`, not killed.
* `PendRel MR c g h`: LPS has executed `syscall` (pending number = `rax`); the middle state
  is still at the `0F 05`; otherwise as `RunRel`.

**Obligations (`SyscallObligations`, WIP).** `MR` survives a retiring instruction; from a
pending pair every LPS syscall step is a successful step matched by one middle-model step
(`read(0)`, `write(1)`, `close`, `exit_group`), LPS can move, and some middle step is
matched by one LPS step. With the launch (`SyscallSimAt`) they give `SimulationAt`
(`simulationAt_of_syscallSim`, VERIFIED) and the bridge (`bridge_of_syscallSim`, VERIFIED).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli (Safe StutterSim)
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

variable {oracle : Nat → X86FlagChoices.Choice}

/-- A relation between the LPS model and the middle process and history. -/
abbrev DescRel := Model → GS → List Ev → Prop

/-- Aligned, running. -/
structure RunRel (MR : DescRel) (c : Config (machine oracle)) (g : GS) (h : List Ev) : Prop where
  pending : c.ms.native.pending = none
  core : CoreLe g.x.core c.ms.native.m.core
  memory : c.ms.native.m.memory = g.x.memory
  running : g.exited = none
  faulted : g.x.faulted = false
  alive : c.model.halted = none
  lazy : c.model.vmLazy = []
  model : MR c.model g h

/-- Aligned, exited. -/
def ExitRel (c : Config (machine oracle)) (g : GS) : Prop :=
  ∃ k, g.exited = some k ∧ c.model.halted = some (BitVec.ofNat 64 k) ∧ c.model.killedBy = none

def Rel (MR : DescRel) (c : Config (machine oracle)) (g : GS) (h : List Ev) : Prop :=
  RunRel MR c g h ∨ ExitRel c g

/-- Pending: LPS has trapped, the middle state is at the `syscall`. -/
structure PendRel (MR : DescRel) (c : Config (machine oracle)) (g : GS) (h : List Ev) : Prop where
  pending : c.ms.native.pending = some (g.x.core.read .rax)
  trap : g.x.memory.fetchBytes g.x.core.rip.toNat 2 = some [0x0f, 0x05]
  core : CoreLe g.x.core c.ms.native.m.core
  memory : c.ms.native.m.memory = g.x.memory
  running : g.exited = none
  faulted : g.x.faulted = false
  alive : c.model.halted = none
  lazy : c.model.vmLazy = []
  model : MR c.model g h

/-! ## One LPS instruction against one middle-model instruction -/

theorem step8_eq_of_trap (state : X86FlagChoices.State)
    (trap : state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05]) :
    X86FlagChoices.step8 oracle state = X86FlagChoices.step oracle state := by
  unfold X86FlagChoices.step8 X86FlagChoices.step
  rw [ite_eq_left trap, ite_eq_left trap]
  congr 1
  unfold x86NativeStep8 x86NativeStep
  have trap' : (X86FlagChoices.completeState state.native (oracle state.counter)).m.memory.fetchBytes
      (X86FlagChoices.completeState state.native (oracle state.counter)).m.core.rip.toNat 2 =
      some [0x0f, 0x05] := trap
  rw [ite_eq_left trap', ite_eq_left trap']
  split <;> rename_i e <;> simp [e]

/-- The trapping instruction: LPS completes the flags and records the pending number. -/
theorem account_trap (segs : List Segment) (c : Config (machine oracle)) (lazy : c.model.vmLazy = [])
    (trap : c.ms.native.m.memory.fetchBytes c.ms.native.m.core.rip.toNat 2 = some [0x0f, 0x05]) :
    accountStep (machine oracle) segs c.ms c.model =
      .ok (⟨{ X86FlagChoices.completeState c.ms.native (oracle c.ms.counter) with
          pending := some (c.ms.native.m.core.read .rax) }, c.ms.counter + 1⟩, c.model) := by
  have step : (machine oracle).step segs c.ms = X86FlagChoices.step oracle c.ms :=
    step8_eq_of_trap c.ms trap
  simp only [accountStep, step, X86FlagChoices.step_syscall oracle c.ms trap]
  rw [show (machine oracle).reportsAccesses = true from rfl]
  simp [X86Launch.materializeModelAccesses_no_lazy _ _ lazy]

/-- A retiring middle-model instruction: the LPS instruction retires to the same memory with a
`CoreLe` core. -/
theorem account_retire (segs : List Segment) (c : Config (machine oracle)) (g : GS)
    (core : CoreLe g.x.core c.ms.native.m.core) (memory : c.ms.native.m.memory = g.x.memory)
    (lazy : c.model.vmLazy = []) {core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory}
    (retired : CLI.X86Linux8.step g.x.core g.x.memory = .retired core' memory') :
    ∃ t, CoreLe core' t ∧ accountStep (machine oracle) segs c.ms c.model =
      .ok (⟨⟨⟨t, memory'⟩, none⟩, c.ms.counter⟩, c.model) := by
  unfold CLI.X86Linux8.step at retired
  split at retired
  · cases retired
  · rename_i notTrap
    have notTrap' : c.ms.native.m.memory.fetchBytes c.ms.native.m.core.rip.toNat 2 ≠
        some [0x0f, 0x05] := by
      rw [memory, Sha256Cli.CoreLe.rip_eq core]; exact notTrap
    have step : (machine oracle).step segs c.ms = X86FlagChoices.step8 oracle c.ms := rfl
    have step8 : X86FlagChoices.step8 oracle c.ms =
        X86FlagChoices.lift c.ms.counter (x86NativeStep8 c.ms.native) := by
      unfold X86FlagChoices.step8; rw [ite_eq_right notTrap']
    split at retired
    · cases retired
    · cases retired
    · rename_i instr length fetched
      have exec : Silmaril.X86.Ext.exec instr g.x.core g.x.memory length = .ok core' memory' := by
        revert retired
        cases Silmaril.X86.Ext.exec instr g.x.core g.x.memory length <;>
          simp [CLI.X86Linux.execResult]
      obtain ⟨t, exec', le⟩ := exec_mono instr g.x.memory length core exec
      refine ⟨t, le, ?_⟩
      simp only [accountStep, step, step8]
      rw [show (machine oracle).reportsAccesses = true from rfl]
      unfold x86NativeStep8
      rw [ite_eq_right notTrap', memory, Sha256Cli.CoreLe.rip_eq core, fetched]
      dsimp only
      rw [exec']
      simp [x86ExecResult, X86FlagChoices.lift, X86Launch.materializeModelAccesses_no_lazy _ _ lazy]
    · rename_i instr length fetched
      have exec : Silmaril.X86.Ext8.execNew instr g.x.core g.x.memory
          (g.x.core.rip + BitVec.ofNat 64 length) = .ok core' memory' := by
        revert retired
        cases Silmaril.X86.Ext8.execNew instr g.x.core g.x.memory _ <;>
          simp [CLI.X86Linux.execResult]
      obtain ⟨t, exec', le⟩ := execNew_mono instr g.x.memory _ core exec
      refine ⟨t, le, ?_⟩
      simp only [accountStep, step, step8]
      rw [show (machine oracle).reportsAccesses = true from rfl]
      unfold x86NativeStep8
      rw [ite_eq_right notTrap', memory, Sha256Cli.CoreLe.rip_eq core, fetched]
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

theorem step8_syscall_trap {core core' : Silmaril.X86.State} {memory : Silmaril.Process.Memory}
    (h : CLI.X86Linux8.step core memory = .syscall core') :
    memory.fetchBytes core.rip.toNat 2 = some [0x0f, 0x05] := by
  unfold CLI.X86Linux8.step at h
  split at h
  · rename_i trap; exact trap
  · split at h
    · cases h
    · cases h
    · revert h
      cases Silmaril.X86.Ext.exec _ _ _ _ <;> simp [CLI.X86Linux.execResult]
    · revert h
      cases Silmaril.X86.Ext8.execNew _ _ _ _ <;> simp [CLI.X86Linux.execResult]

/-- What the middle step at `g` is, when one exists: a retirement or the `syscall`. -/
theorem gstep_form {w : Apps.Sha256sum.World} {g : GS} (moves : ∃ e y, GStep w g e y) :
    (∃ core' memory', CLI.X86Linux8.step g.x.core g.x.memory = .retired core' memory') ∨
      g.x.memory.fetchBytes g.x.core.rip.toNat 2 = some [0x0f, 0x05] := by
  obtain ⟨e, y, s⟩ := moves
  cases s with
  | retire _ _ step => exact .inl ⟨_, _, step⟩
  | call _ _ _ step => exact .inr (step8_syscall_trap step)
  | exit _ _ step => exact .inr (step8_syscall_trap step)

section Aligned

variable {segs : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}
  {MR : DescRel} {c : Config (machine oracle)} {g : GS} {h : List Ev}

/-- The `syscall` instruction from an aligned pair: one silent LPS step to a pending pair. -/
theorem aligned_trap (r : RunRel MR c g h)
    (trap : g.x.memory.fetchBytes g.x.core.rip.toNat 2 = some [0x0f, 0x05]) :
    ∃ c', PendRel MR c' g h ∧ SStep segs spec refused c [] (.next c') ∧
      ∀ evs st, SStep segs spec refused c evs st → evs = [] ∧ st = .next c' := by
  have trap' : c.ms.native.m.memory.fetchBytes c.ms.native.m.core.rip.toNat 2 =
      some [0x0f, 0x05] := by
    rw [r.memory, Sha256Cli.CoreLe.rip_eq r.core]; exact trap
  obtain ⟨step, unique⟩ := sstep_of_account (spec := spec) (refused := refused) r.alive r.pending
    (account_trap segs c r.lazy trap')
  refine ⟨_, ?_, step, unique⟩
  exact { pending := by
            show some (c.ms.native.m.core.read .rax) = some (g.x.core.read .rax)
            rw [Sha256Cli.CoreLe.read_eq r.core]
          trap := trap
          core := Sha256Cli.coreLe_complete r.core _
          memory := r.memory
          running := r.running
          faulted := r.faulted
          alive := r.alive
          lazy := r.lazy
          model := r.model }

/-- A retiring instruction from an aligned pair: one silent LPS step, matched by the middle
retirement, to an aligned pair. -/
theorem aligned_retire {w : Apps.Sha256sum.World} (r : RunRel MR c g h) {core' : Silmaril.X86.State}
    {memory' : Silmaril.Process.Memory}
    (retired : CLI.X86Linux8.step g.x.core g.x.memory = .retired core' memory')
    (keep : MR c.model g h → MR c.model { g with x := { g.x with core := core', memory := memory' } } h) :
    ∃ c', RunRel MR c' { g with x := { g.x with core := core', memory := memory' } } h ∧
      GStep w g [] { g with x := { g.x with core := core', memory := memory' } } ∧
      SStep segs spec refused c [] (.next c') ∧
      ∀ evs st, SStep segs spec refused c evs st → evs = [] ∧ st = .next c' := by
  obtain ⟨t, le, account⟩ := account_retire segs c g r.core r.memory r.lazy retired
  obtain ⟨step, unique⟩ := sstep_of_account (spec := spec) (refused := refused) r.alive r.pending
    account
  refine ⟨_, ?_, .retire r.running r.faulted retired, step, unique⟩
  exact { pending := rfl, core := le, memory := rfl, running := r.running, faulted := r.faulted,
          alive := r.alive, lazy := r.lazy, model := keep r.model }

end Aligned

/-! ## The system-call obligations and the assembled simulation -/

/-- The system-call part of the simulation, for one launch, world and relation `MR`
(WIP: the open obligations of the bridge). -/
structure SyscallObligations (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (inp : ProcInput) (message : List Byte) (w : Apps.Sha256sum.World) (MR : DescRel) : Prop where
  /-- `MR` survives a retiring instruction. -/
  retire : ∀ {model g h} {core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory},
    MR model g h → CLI.X86Linux8.step g.x.core g.x.memory = .retired core' memory' →
    MR model { g with x := { g.x with core := core', memory := memory' } } h
  /-- Every LPS syscall step from a pending pair succeeds and is one middle-model step. -/
  step : ∀ {c : Config (machine oracle)} {g h evs st}, PendRel MR c g h →
    Safe (GStep w) (Ok message) (Done message) g h →
    SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st →
    ∃ c', st = .next c' ∧ ∃ es y, GStep w g es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
      Rel MR c' y (h ++ es)
  /-- LPS can complete the call. -/
  progress : ∀ {c : Config (machine oracle)} {g h}, PendRel MR c g h →
    Safe (GStep w) (Ok message) (Done message) g h →
    ∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st
  /-- Some middle-model call is one LPS syscall step. -/
  back : ∀ {c : Config (machine oracle)} {g h}, PendRel MR c g h →
    Safe (GStep w) (Ok message) (Done message) g h →
    ∃ es y, GStep w g es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
      Rel MR c' y (h ++ es)

/-- The launch-local remainder of the bridge: a middle-model launch on a stdin-tier world of
the same message, a relation aligning the initial configurations, and the system-call
obligations. -/
def SyscallSimAt (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (prog : List Byte) (posix : Bool) (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult)
    (g₀ : GS) (MR : DescRel),
    Launch (world [prog] posix fs message) g₀ ∧ Rel MR (initial oracle limit en inp) g₀ [] ∧
      SyscallObligations oracle refusals inp message (world [prog] posix fs message) MR

/-- **The instruction level (VERIFIED).** The system-call obligations give the simulation. -/
theorem simulationAt_of_syscallSim {refusals : SpuriousCfg} {limit : Int} {en : ExecEntry}
    {inp : ProcInput} {message : List Byte} (h : SyscallSimAt oracle refusals limit en inp message) :
    SimulationAt oracle refusals limit en inp message := by
  obtain ⟨prog, posix, fs, g₀, MR, launch, related, obl⟩ := h
  let sim : StutterSim (isa := machine oracle) snapshot.image.segments
      NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter refusals)
      (GStep (world [prog] posix fs message)) (Ok message) (Done message) (evFlat inp.fs) [0] :=
    { rel := Rel MR
      pend := PendRel MR
      stepRel := by
        intro c x h evs st r safe s
        rcases r with r | ⟨k, exited, -, -⟩
        · rcases gstep_form safe.2.1 with ⟨core', memory', retired⟩ | trap
          · obtain ⟨c', r', cs, -, unique⟩ := aligned_retire (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals)
              (w := world [prog] posix fs message) r retired (obl.retire · retired)
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
        · rcases gstep_form safe.2.1 with ⟨core', memory', retired⟩ | trap
          · obtain ⟨c', -, -, s, -⟩ := aligned_retire (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals)
              (w := world [prog] posix fs message) r retired (obl.retire · retired)
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
        · rcases gstep_form safe.2.1 with ⟨core', memory', retired⟩ | trap
          · obtain ⟨c', r', cs, s, -⟩ := aligned_retire (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals)
              (w := world [prog] posix fs message) r retired (obl.retire · retired)
            refine ⟨[], _, cs, c', Star.one s, .inl ?_⟩
            rw [List.append_nil]
            exact r'
          · obtain ⟨c₁, p₁, s₁, -⟩ := aligned_trap (spec := NativeX86.extendedSyscallSpec)
              (refused := NativeX86.defaultRefusalFilter refusals) r trap
            obtain ⟨es, y, cs, c', s', r'⟩ := obl.back p₁ safe
            exact ⟨es, y, cs, c', by simpa using Star.step s₁ (Star.one s'), r'⟩
        · exact absurd (exited.symm.trans safe.1.1) (by simp) }
  exact ⟨prog, posix, fs, g₀, sim, launch, related⟩

/-- **Reduction (VERIFIED).** The launch-local system-call simulations give the bridge. -/
theorem bridge_of_syscallSim
    (h : ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
      SyscallSimAt oracle refusals limit en inp message) : BridgeSegment :=
  bridge_of_simulation fun oracle refusals limit en inp message admissible =>
    simulationAt_of_syscallSim (h oracle refusals limit en inp message admissible)

end Silmaril.Process.LPS.Problems.GnuSha256sum
