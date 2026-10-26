module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Instr
public import Silmaril.Process.LPS.ExitBridge

/-! # Segment `bridge`: system calls

The system-call obligations of `Instr.lean` (`SyscallObligations`), call by call.

* Dispatch (VERIFIED): in the native x86 table, numbers 60 and 231 are LPS `exit_spec`
  (`exit_dispatch`); no refusal filter ever refuses `read`, `write`, `exit` or `exit_group`
  (`not_refused`: none of them has an injected-failure arm).
* `exit`/`exit_group` (VERIFIED, `pend_exit`): from a pending pair whose CLI request is an
  exit, the only LPS step is the exit step, with event `exitEv (rdi &&& 255) fs`; the only CLI
  step is `exit`, with event `exit (rdi mod 256)`; they flatten to the same events and lead to
  an `ExitRel` pair. It needs only that the LPS file system is the launch one.
* `read` of stdin and `write` to stdout: open (WIP).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

/-! ## Dispatch and refusals -/

theorem exit_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 60 ∨ i.sysno.toNat = 231) :
    NativeX86.extendedSyscallSpec i m o ↔
      o = .ok (mkEffect 0 [] []) (m.withHalted (i.arg 0 &&& 255)) [] := by
  rcases number with number | number
  · simp only [NativeX86.extendedSyscallSpec, dispatch, number]
    exact ExitBridge.exitSpec_iff (i.arg 0) _ m o
  · simp only [NativeX86.extendedSyscallSpec, dispatch, number]
    exact ExitBridge.exitSpec_iff (i.arg 0) _ m o

theorem not_refused (refusals : SpuriousCfg) (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (number : i.sysno.toNat = 0 ∨ i.sysno.toNat = 1 ∨ i.sysno.toNat = 60 ∨ i.sysno.toNat = 231) :
    ¬ NativeX86.defaultRefusalFilter refusals i m eff := by
  have off : ∀ n, injectedArm n = none → ∀ j : SyscallInput, j.sysno.toNat = n →
      ¬ spuriousRefusalCfg syscallSpec refusals j m eff := by
    intro n none j hj bad
    have := bad.1
    simp [injectedFamilyOff, hj, none] at this
  have a63 : injectedArm 63 = none := by decide
  have a64 : injectedArm 64 = none := by decide
  have a93 : injectedArm 93 = none := by decide
  have a94 : injectedArm 94 = none := by decide
  rcases number with number | number | number | number <;>
  · simp only [NativeX86.defaultRefusalFilter, NativeX86.refusalFilter, NativeX86.referenceInput,
      number]
    first
    | exact off 63 a63 _ rfl
    | exact off 64 a64 _ rfl
    | exact off 93 a93 _ rfl
    | exact off 94 a94 _ rfl

theorem and255_eq (w : Word) : w &&& 255 = BitVec.ofNat 64 (w.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have : (255 : Word).toNat = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## `exit` and `exit_group` -/

theorem cli_request_exit (core : Silmaril.X86.State)
    (number : (core.read .rax).toNat = 60 ∨ (core.read .rax).toNat = 231) :
    CLI.X86Linux.request core = some (.exit (core.read .rdi).toNat) := by
  have h0 : (core.read .rax).toNat ≠ 0 := by omega
  have h1 : (core.read .rax).toNat ≠ 1 := by omega
  simp [CLI.X86Linux.request, CLI.X86Linux.readNumber, CLI.X86Linux.writeNumber,
    CLI.X86Linux.exitNumber, CLI.X86Linux.exitGroupNumber, h0, h1, number]

theorem cli_step_trap {core : Silmaril.X86.State} {memory : Silmaril.Process.Memory}
    (trap : memory.fetchBytes core.rip.toNat 2 = some [0x0f, 0x05]) :
    CLI.X86Linux.step core memory = .syscall { core with rip := core.rip + 2 } := by
  unfold CLI.X86Linux.step
  rw [ite_eq_left (by simpa [CLI.X86Linux.syscallBytes] using trap)]

section Exit

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event}

/-- The CLI exit step from a pending pair whose request is an exit. -/
theorem cli_exit_step (p : PendRel MR c x h)
    (number : (x.core.read .rax).toNat = 60 ∨ (x.core.read .rax).toNat = 231) :
    CStep x [.exit ((x.core.read .rdi).toNat % 256)]
      ⟨{ x.core with rip := x.core.rip + 2 },
        { x.env with exited := some ((x.core.read .rdi).toNat % 256) }⟩ := by
  obtain ⟨core, env⟩ := x
  refine CLI.Proc.Step.exit (q := .exit (core.read .rdi).toNat)
    (status := (core.read .rdi).toNat % 256) p.running (cli_step_trap p.trap).symm ?_ ?_
  · exact cli_request_exit { core with rip := core.rip + 2 } number
  · refine ⟨.exit _ p.running, ?_, ?_⟩
    · intro fd address count q; cases q
    · intro bad; exact bad

/-- Every CLI step from a pending pair whose request is an exit is that exit step. -/
theorem cli_exit_unique (p : PendRel MR c x h)
    (number : (x.core.read .rax).toNat = 60 ∨ (x.core.read .rax).toNat = 231)
    {es : List Syscall.Event} {y : PS} (s : CStep x es y) :
    es = [.exit ((x.core.read .rdi).toNat % 256)] ∧
      y.env.exited = some ((x.core.read .rdi).toNat % 256) := by
  obtain ⟨core, env⟩ := x
  have trap : CLI.X86Linux.step core env.memory = .syscall { core with rip := core.rip + 2 } :=
    cli_step_trap p.trap
  cases s with
  | retire _ step =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
  | call _ step request effect _ =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    have req : CLI.X86Linux.request { core with rip := core.rip + 2 } =
        some (.exit (core.read .rdi).toNat) := cli_request_exit _ number
    have request' : CLI.X86Linux.request _ = some _ := request
    rw [req] at request'; cases request'
    obtain ⟨effect, -⟩ := effect
    cases effect
  | exit _ step request effect =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    have req : CLI.X86Linux.request { core with rip := core.rip + 2 } =
        some (.exit (core.read .rdi).toNat) := cli_request_exit _ number
    have request' : CLI.X86Linux.request _ = some _ := request
    rw [req] at request'; cases request'
    obtain ⟨effect, -⟩ := effect
    cases effect
    exact ⟨rfl, rfl⟩

/-- **`exit` and `exit_group` (VERIFIED).** -/
theorem pend_exit (p : PendRel MR c x h)
    (number : (x.core.read .rax).toNat = 60 ∨ (x.core.read .rax).toNat = 231)
    (fs : c.model.fs = inp.fs) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, CStep x es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        ExitRel c' y) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∀ es y, CStep x es y → ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        ExitRel c' y) := by
  obtain ⟨ms, model⟩ := c
  have svc : (machine oracle).svcPending ms = some (x.core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (x.core.read .rax) with hi
  have sysno : i.sysno = x.core.read .rax := rfl
  have arg0 : i.arg 0 = x.core.read .rdi := by
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD 0 0) = _
    simp [CoreLe.read_eq p.core]
  -- the LPS exit step
  have exitStep : SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩
      ([] ++ [Event.exitEv (x.core.read .rdi &&& 255)
        (model.withHalted (x.core.read .rdi &&& 255)).fs])
      (.next ⟨ms, model.withHalted (x.core.read .rdi &&& 255)⟩) :=
    .exit p.alive svc ((exit_dispatch i model _ (by rw [sysno]; exact number)).2
      (by rw [arg0])) rfl rfl
  have flat : [Syscall.Event.exit ((x.core.read .rdi).toNat % 256)].flatMap (evFlat inp.fs) =
      [] ++ [Event.exitEv (x.core.read .rdi &&& 255)
        (model.withHalted (x.core.read .rdi &&& 255)).fs] := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evFlat, List.nil_append]
    rw [and255_eq]
    exact congrArg (fun f => [Event.exitEv _ f]) fs.symm
  have exitRel : ∀ y : PS, y.env.exited = some ((x.core.read .rdi).toNat % 256) →
      ExitRel (oracle := oracle) ⟨ms, model.withHalted (x.core.read .rdi &&& 255)⟩ y := by
    intro y exited
    exact ⟨_, exited, by rw [and255_eq]; rfl, rfl⟩
  refine ⟨fun evs st s => ?_, ⟨_, _, exitStep⟩, fun es y s => ?_⟩
  · cases s with
    | syscall _ p' sp _ halted =>
      rw [svc] at p'; cases p'
      rw [exit_dispatch _ _ _ (by rw [sysno]; exact number)] at sp
      cases sp; cases halted
    | syscallMaterializationFault _ p' sp _ halted =>
      rw [svc] at p'; cases p'
      rw [exit_dispatch _ _ _ (by rw [sysno]; exact number)] at sp
      cases sp; cases halted
    | exit _ p' sp halted _ =>
      rw [svc] at p'; cases p'
      rw [exit_dispatch _ _ _ (by rw [sysno]; exact number), arg0] at sp
      cases sp
      simp only [Model.halted, Model.withHalted, Option.some.injEq] at halted
      subst halted
      exact ⟨_, rfl, _, _, cli_exit_step p number, flat.symm, exitRel _ rfl⟩
    | killed _ p' sp killed =>
      rw [svc] at p'; cases p'
      rw [exit_dispatch _ _ _ (by rw [sysno]; exact number)] at sp
      cases sp; cases killed
    | syscallUnmodeled _ p' sp =>
      rw [svc] at p'; cases p'
      rw [exit_dispatch _ _ _ (by rw [sysno]; exact number)] at sp
      cases sp
    | instr _ p' => rw [svc] at p'; cases p'
    | instrFault _ p' => rw [svc] at p'; cases p'
    | instrUnmodeled _ p' => rw [svc] at p'; cases p'
  · obtain ⟨rfl, exited⟩ := cli_exit_unique p number s
    exact ⟨_, flat ▸ exitStep, exitRel y exited⟩

end Exit

/-! ## Reducing the obligations to `read` and `write` -/

theorem cli_request_number (core : Silmaril.X86.State) {q : Syscall.Request}
    (request : CLI.X86Linux.request core = some q) :
    (core.read .rax).toNat = 0 ∨ (core.read .rax).toNat = 1 ∨
      (core.read .rax).toNat = 60 ∨ (core.read .rax).toNat = 231 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨a, b, c, d⟩ := hne
  simp [CLI.X86Linux.request, CLI.X86Linux.readNumber, CLI.X86Linux.writeNumber,
    CLI.X86Linux.exitNumber, CLI.X86Linux.exitGroupNumber, a, b, c, d] at request

/-- At a pending pair whose CLI state can move, the call number is `read`, `write`, `exit` or
`exit_group`. -/
theorem pend_number {oracle : Nat → X86FlagChoices.Choice} {MR : DescRel}
    {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event} (p : PendRel MR c x h)
    (moves : ∃ e y, CStep x e y) :
    (x.core.read .rax).toNat = 0 ∨ (x.core.read .rax).toNat = 1 ∨
      (x.core.read .rax).toNat = 60 ∨ (x.core.read .rax).toNat = 231 := by
  obtain ⟨e, y, s⟩ := moves
  obtain ⟨core, env⟩ := x
  have trap : CLI.X86Linux.step core env.memory = .syscall { core with rip := core.rip + 2 } :=
    cli_step_trap p.trap
  cases s with
  | retire _ step =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
  | call _ step request =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    exact cli_request_number { core with rip := core.rip + 2 } request
  | exit _ step request =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    exact cli_request_number { core with rip := core.rip + 2 } request

/-- The obligations left once `exit` is proved: `read` and `write` from a pending pair, the
file system recorded by `MR`, and `MR` surviving instructions. -/
structure ReadWriteObligations (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (inp : ProcInput) (message : List Byte) (input : CLI.ProcInput) (MR : DescRel) : Prop where
  retire : ∀ {model s h} {core core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory},
    MR model s h → CLI.X86Linux.step core s.memory = .retired core' memory' →
    MR model { s with memory := memory' } h
  fs : ∀ {model s h}, MR model s h → model.fs = inp.fs
  step : ∀ {c : Config (machine oracle)} {x h evs st}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h →
    ((x.core.read .rax).toNat = 0 ∨ (x.core.read .rax).toNat = 1) →
    SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st →
    ∃ c', st = .next c' ∧ ∃ es y, CStep x es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
      Rel MR c' y (h ++ es)
  progress : ∀ {c : Config (machine oracle)} {x h}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h →
    ((x.core.read .rax).toNat = 0 ∨ (x.core.read .rax).toNat = 1) →
    ∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st
  back : ∀ {c : Config (machine oracle)} {x h}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h →
    ((x.core.read .rax).toNat = 0 ∨ (x.core.read .rax).toNat = 1) →
    ∃ es y, CStep x es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
      Rel MR c' y (h ++ es)

/-- `exit` discharged (VERIFIED): the read/write obligations give the system-call ones. -/
theorem ReadWriteObligations.toSyscall {oracle : Nat → X86FlagChoices.Choice}
    {refusals : SpuriousCfg} {inp : ProcInput} {message : List Byte} {input : CLI.ProcInput}
    {MR : DescRel} (rw : ReadWriteObligations oracle refusals inp message input MR) :
    SyscallObligations oracle refusals inp message input MR where
  retire := rw.retire
  step := by
    intro c x h evs st p safe s
    rcases pend_number p safe.2.1 with n | n | n | n
    · exact rw.step p safe (.inl n) s
    · exact rw.step p safe (.inr n) s
    all_goals
      obtain ⟨c', same, es, y, cs, eq, r⟩ :=
        (pend_exit (inp := inp) (refusals := refusals) p (by omega) (rw.fs p.model)).1 evs st s
      exact ⟨c', same, es, y, cs, eq, .inr r⟩
  progress := by
    intro c x h p safe
    rcases pend_number p safe.2.1 with n | n | n | n
    · exact rw.progress p safe (.inl n)
    · exact rw.progress p safe (.inr n)
    all_goals
      exact (pend_exit (inp := inp) (refusals := refusals) p (by omega) (rw.fs p.model)).2.1
  back := by
    intro c x h p safe
    rcases pend_number p safe.2.1 with n | n | n | n
    · exact rw.back p safe (.inl n)
    · exact rw.back p safe (.inr n)
    all_goals
      obtain ⟨es, y, cs⟩ := safe.2.1
      obtain ⟨c', s, r⟩ :=
        (pend_exit (inp := inp) (refusals := refusals) p (by omega) (rw.fs p.model)).2.2 es y cs
      exact ⟨es, y, cs, c', s, .inr r⟩

/-- The launch-local remainder after `exit`: a CLI launch, an `MR` aligning the initial
configurations, and the read/write obligations. -/
def ReadWriteSimAt (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (input : CLI.ProcInput) (x₀ : PS) (MR : DescRel),
    input.stdin = .ofList message ∧ input.Valid ∧ Launch input x₀ ∧
      Rel MR (initial oracle limit en inp) x₀ [] ∧
      ReadWriteObligations oracle refusals inp message input MR

/-- **Reduction (VERIFIED).** Launch-local read/write simulations give the bridge segment. -/
theorem bridge_of_readWriteSim
    (h : ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
      ReadWriteSimAt oracle refusals limit en inp message) : BridgeSegment :=
  bridge_of_syscallSim fun oracle refusals limit en inp message admissible => by
    obtain ⟨input, x₀, MR, stdin, valid, launch, related, rw⟩ :=
      h oracle refusals limit en inp message admissible
    exact ⟨input, x₀, MR, stdin, valid, launch, related, rw.toSyscall⟩

end Silmaril.Process.LPS.Problems.Sha256Cli
