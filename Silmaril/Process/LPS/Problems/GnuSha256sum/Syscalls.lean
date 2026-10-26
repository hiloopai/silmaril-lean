module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Instr
public import Silmaril.Process.LPS.Problems.Sha256Cli.Syscalls
public import Silmaril.Process.LPS.Problems.Sha256Cli.WriteSpec

/-! # Segment `bridge` for GNU `sha256sum`: system calls

The system-call obligations of `GnuSha256sum.Instr` (`SyscallObligations`), call by call,
against the `X86Sys` middle model.

* `exit`/`exit_group` (VERIFIED, `pend_exit`): from a pending pair whose request is an exit,
  the only LPS step is the exit step with event `exitEv (rdi &&& 255) fs`, the only middle
  step is `GStep.exit` with event `exit (rdi mod 256)`; they flatten to the same events and
  lead to an `ExitRel` pair (the LPS file system must be the launch one).
* `close` (VERIFIED, `closeSpec_iff`, `pend_close`): LPS `close` in closed form; from a
  pending pair whose request is `close(fd)`, if LPS and the middle kernel agree on whether `fd`
  is open, the LPS step (removal and 0, or `EBADF`) and `Sys.WorldStep.closeOk`/`closeBad`
  match, with the same (empty) flattened events, to an aligned pair (`MR` must survive).
* `read(0)` and `write(1)`: open (WIP); the LPS halves are `Sha256Cli.read_channel_iff`
  and `Sha256Cli.write_channel_iff`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli (exit_dispatch and255_eq input_getModel_iff)
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

/-! ## The middle model at a `syscall` -/

theorem step8_trap {core : Silmaril.X86.State} {memory : Silmaril.Process.Memory}
    (trap : memory.fetchBytes core.rip.toNat 2 = some [0x0f, 0x05]) :
    CLI.X86Linux8.step core memory = .syscall { core with rip := core.rip + 2 } := by
  unfold CLI.X86Linux8.step
  rw [ite_eq_left (by simpa [CLI.X86Linux.syscallBytes] using trap)]

theorem decode_exit (t : Silmaril.X86.State) (m : Silmaril.Process.Memory)
    (number : (t.read .rax).toNat = 60 ∨ (t.read .rax).toNat = 231) :
    Apps.Sha256sum.X86Sys.decode t m = some (.exit (t.read .rdi).toNat) := by
  have h0 : (t.read .rax).toNat ≠ 0 := by omega
  have h1 : (t.read .rax).toNat ≠ 1 := by omega
  have h3 : (t.read .rax).toNat ≠ 3 := by omega
  have h12 : (t.read .rax).toNat ≠ 12 := by omega
  have h257 : (t.read .rax).toNat ≠ 257 := by omega
  simp [Apps.Sha256sum.X86Sys.decode, h0, h1, h3, h12, h257, number]

theorem decode_close (t : Silmaril.X86.State) (m : Silmaril.Process.Memory)
    (number : (t.read .rax).toNat = 3) :
    Apps.Sha256sum.X86Sys.decode t m =
      some (.call (.close (Apps.Sha256sum.X86Sys.fd32 (t.read .rdi)))) := by
  simp [Apps.Sha256sum.X86Sys.decode, number]

/-! ## `exit` and `exit_group` -/

section Exit

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {g : GS} {h : List Ev} {w : Apps.Sha256sum.World}

/-- The middle exit step from a pending pair whose request is an exit. -/
theorem gstep_exit (p : PendRel MR c g h)
    (number : (g.x.core.read .rax).toNat = 60 ∨ (g.x.core.read .rax).toNat = 231) :
    GStep w g [.exit ((g.x.core.read .rdi).toNat % 256)]
      { g with exited := some ((g.x.core.read .rdi).toNat % 256) } :=
  GStep.exit p.running p.faulted (step8_trap p.trap) (decode_exit _ _ number)

/-- Every middle step from a pending pair whose request is an exit is that exit step. -/
theorem gstep_exit_unique (p : PendRel MR c g h)
    (number : (g.x.core.read .rax).toNat = 60 ∨ (g.x.core.read .rax).toNat = 231)
    {es : List Ev} {y : GS} (s : GStep w g es y) :
    es = [.exit ((g.x.core.read .rdi).toNat % 256)] ∧
      y.exited = some ((g.x.core.read .rdi).toNat % 256) := by
  have trap := step8_trap p.trap
  cases s with
  | retire _ _ step => rw [trap] at step; cases step
  | call _ _ _ step dec =>
    rw [trap] at step; cases step
    rw [decode_exit { g.x.core with rip := g.x.core.rip + 2 } _ number] at dec; cases dec
  | exit _ _ step dec =>
    rw [trap] at step; cases step
    rw [decode_exit { g.x.core with rip := g.x.core.rip + 2 } _ number] at dec; cases dec
    exact ⟨rfl, rfl⟩

/-- **`exit` and `exit_group` (VERIFIED).** -/
theorem pend_exit (p : PendRel MR c g h)
    (number : (g.x.core.read .rax).toNat = 60 ∨ (g.x.core.read .rax).toNat = 231)
    (fs : c.model.fs = inp.fs) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, GStep w g es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        ExitRel c' y) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∀ es y, GStep w g es y → ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        ExitRel c' y) := by
  obtain ⟨ms, model⟩ := c
  have svc : (machine oracle).svcPending ms = some (g.x.core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (g.x.core.read .rax) with hi
  have sysno : i.sysno = g.x.core.read .rax := rfl
  have arg0 : i.arg 0 = g.x.core.read .rdi := by
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD 0 0) = _
    simp [Sha256Cli.CoreLe.read_eq p.core]
  have exitStep : SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩
      ([] ++ [Event.exitEv (g.x.core.read .rdi &&& 255)
        (model.withHalted (g.x.core.read .rdi &&& 255)).fs])
      (.next ⟨ms, model.withHalted (g.x.core.read .rdi &&& 255)⟩) :=
    .exit p.alive svc ((exit_dispatch i model _ (by rw [sysno]; exact number)).2
      (by rw [arg0])) rfl rfl
  have flat : [Ev.exit ((g.x.core.read .rdi).toNat % 256)].flatMap (evFlat inp.fs) =
      [] ++ [Event.exitEv (g.x.core.read .rdi &&& 255)
        (model.withHalted (g.x.core.read .rdi &&& 255)).fs] := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evFlat, readBytes,
      outBytes, exitPart, List.map_nil, List.nil_append]
    rw [and255_eq]
    exact congrArg (fun f => [Event.exitEv _ f]) fs.symm
  have exitRel : ∀ y : GS, y.exited = some ((g.x.core.read .rdi).toNat % 256) →
      ExitRel (oracle := oracle) ⟨ms, model.withHalted (g.x.core.read .rdi &&& 255)⟩ y := by
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
      exact ⟨_, rfl, _, _, gstep_exit p number, flat.symm, exitRel _ rfl⟩
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
  · obtain ⟨rfl, exited⟩ := gstep_exit_unique p number s
    exact ⟨_, flat ▸ exitStep, exitRel y exited⟩

end Exit

/-! ## `close` -/

theorem close_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 3) :
    NativeX86.extendedSyscallSpec i m o ↔
      closeSpec (fd32 (i.arg 0)) (NativeX86.referenceInputFor ⟨57, 3, "close"⟩ i) m o := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  rfl

/-- **LPS `close`, closed form.** -/
theorem closeSpec_iff (fd : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    closeSpec fd i m o ↔
      (fdLookup m.fds fd = none ∧ o = .ok (mkEffect (errnoRet EBADF) [] []) m []) ∨
      ((fdLookup m.fds fd).isSome ∧ o = .ok (mkEffect 0 [] []) (m.withFds (fdRemove m.fds fd)) []) := by
  unfold closeSpec
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, hx, hk, rfl⟩
      cases hx
      try dsimp only at hk
      cases hl : fdLookup m.fds fd with
      | none =>
        rw [hl] at hk
        simp only [errRet, retOnly, Sys.pure] at hk
        cases hk
        exact .inl ⟨rfl, rfl⟩
      | some e =>
        rw [hl] at hk
        obtain ⟨u, m₃, e₃, e₄, hm, hp, rfl⟩ := hk
        cases hm
        simp only [retOnly, Sys.pure] at hp
        cases hp
        exact .inr ⟨rfl, rfl⟩
    · rintro (⟨hl, h⟩ | ⟨hl, h⟩) <;> cases h
      · refine ⟨m, m, [], [], rfl, ?_, rfl⟩
        dsimp only
        rw [hl]; rfl
      · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hl
        refine ⟨m, m, [], [], rfl, ?_, rfl⟩
        dsimp only
        rw [he]
        exact ⟨(), m.withFds (fdRemove m.fds fd), [], [], rfl, rfl, rfl⟩
  | unmodeled =>
    constructor
    · rintro (hx | ⟨x, m₁, e₁, hx, hk⟩)
      · cases hx
      · cases hx
        try dsimp only at hk
        cases hl : fdLookup m.fds fd with
        | none => rw [hl] at hk; cases hk
        | some e =>
          rw [hl] at hk
          rcases hk with hm | ⟨u, m₃, e₃, hm, hp⟩
          · cases hm
          · cases hm; cases hp
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> cases h


theorem fd32_eq (w : Word) : fd32 w = BitVec.ofNat 64 (Apps.Sha256sum.X86Sys.fd32 w) := by
  unfold fd32 abiLow32 zw uns Apps.Sha256sum.X86Sys.fd32
  rw [BitVec.toNat_setWidth]
  have : ((w.toNat : Int) % 2 ^ 32) = ((w.toNat % 2 ^ 32 : Nat) : Int) := by push_cast; rfl
  rw [this, BitVec.ofInt_natCast]

theorem raxOf_ok_zero : Apps.Sha256sum.X86Sys.raxOf (.ok 0) = (mkEffect 0 [] []).ret := rfl

theorem raxOf_ebadf : Apps.Sha256sum.X86Sys.raxOf (.err .EBADF) = (mkEffect (errnoRet EBADF) [] []).ret := by
  decide

theorem not_refused_close (refusals : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (number : i.sysno.toNat = 3) :
    ¬ NativeX86.defaultRefusalFilter refusals i m eff := by
  have a57 : injectedArm 57 = none := by decide
  simp only [NativeX86.defaultRefusalFilter, NativeX86.refusalFilter, NativeX86.referenceInput,
    number]
  intro bad
  have := bad.1
  have hj : (NativeX86.referenceInputFor ⟨57, 3, "close"⟩ i).sysno.toNat = 57 := rfl
  simp [injectedFamilyOff, hj, a57] at this

/-- The middle state after `close(fd)` with reply `r`, kernel state `k'`, and `r11` value
`r11`. -/
def closeNext (g : GS) (r11 : Word) (r : Apps.Sha256sum.Sys.Ret) (k' : Apps.Sha256sum.Sys.KState) :
    GS :=
  ⟨Apps.Sha256sum.X86Sys.resume (fun _ => r11) g.x { g.x.core with rip := g.x.core.rip + 2 }
    (.close (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi))) r, k', none⟩

section Close

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {g : GS} {h : List Ev} {w : Apps.Sha256sum.World}

/-- **`close` (VERIFIED).** From a pending pair whose request is `close(fd)`, where LPS and the
middle kernel agree on whether `fd` is open, every LPS step is the matching `close` (success
and removal, or `EBADF`), LPS can move, and the middle `close` is matched; the relation `MR`
must survive the call. -/
theorem pend_close (p : PendRel MR c g h) (number : (g.x.core.read .rax).toNat = 3)
    (corr : (fdLookup c.model.fds (fd32 (g.x.core.read .rdi))).isSome =
      (g.k.fds (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi))).isSome)
    (keepOk : ∀ r11, (g.k.fds (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi))).isSome →
      MR (c.model.withFds (fdRemove c.model.fds (fd32 (g.x.core.read .rdi))))
        (closeNext g r11 (.ok 0) (g.k.set (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi)) none))
        (h ++ [.sys (.close (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi))) (.ok 0)]))
    (keepBad : ∀ r11, g.k.fds (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi)) = none →
      MR c.model (closeNext g r11 (.err .EBADF) g.k)
        (h ++ [.sys (.close (Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi))) (.err .EBADF)])) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, GStep w g es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        Rel MR c' y (h ++ es)) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∃ es y, GStep w g es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        Rel MR c' y (h ++ es)) := by
  obtain ⟨ms, model⟩ := c
  set fd := Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi) with hfd
  have svc : (machine oracle).svcPending ms = some (g.x.core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (g.x.core.read .rax) with hi
  have sysno : i.sysno = g.x.core.read .rax := rfl
  have a0 : i.arg 0 = g.x.core.read .rdi := by
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD 0 0) = _
    simp [Sha256Cli.CoreLe.read_eq p.core]
  have spec_iff : ∀ o, NativeX86.extendedSyscallSpec i model o ↔
      (fdLookup model.fds (fd32 (g.x.core.read .rdi)) = none ∧
          o = .ok (mkEffect (errnoRet EBADF) [] []) model []) ∨
        ((fdLookup model.fds (fd32 (g.x.core.read .rdi))).isSome ∧
          o = .ok (mkEffect 0 [] [])
            (model.withFds (fdRemove model.fds (fd32 (g.x.core.read .rdi)))) []) := by
    intro o
    rw [close_dispatch i model o (by rw [sysno]; exact number), closeSpec_iff]
    have : (NativeX86.referenceInputFor ⟨57, 3, "close"⟩ i).arg 0 = i.arg 0 := rfl
    rw [a0]
  have notRefused : ∀ eff, ¬ NativeX86.defaultRefusalFilter refusals i model eff :=
    fun eff => not_refused_close refusals i model eff (by rw [sysno]; exact number)
  have killed : model.killedBy = none := by
    have alive : model.halted = none := p.alive
    simp only [Model.killedBy]
    split
    · exact alive
    · rfl
  have pend158 : ∀ eff : SyscallEffect, ¬ (ms.native.pending = some 158 ∧
      ms.native.m.core.read .rdi = 0x1002 ∧ eff.ret = 0) := by
    rintro eff ⟨hp, -, -⟩
    have hp' : some (g.x.core.read .rax) = some 158 := p.pending.symm.trans hp
    have := congrArg (fun o => o.map BitVec.toNat) hp'
    simp [number] at this
  set r11 := (rflagsImage ms.native.m.core.flags).getD 0 with hr11
  -- the matched pair after the call with reply `r`, LPS effect `eff` and LPS model `model'`
  have related : ∀ (r : Apps.Sha256sum.Sys.Ret) (k' : Apps.Sha256sum.Sys.KState) (v : Word)
      (model' : Model), Apps.Sha256sum.X86Sys.raxOf r = (mkEffect v [] []).ret →
      model'.halted = none →
      model'.vmLazy = [] → MR model' (closeNext g r11 r k') (h ++ [.sys (.close fd) r]) →
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms (mkEffect v [] [])),
          model'⟩
        (closeNext g r11 r k') (h ++ [.sys (.close fd) r]) := by
    intro r k' v model' rax alive lazy mr
    obtain ⟨eq, fle⟩ := p.core
    refine { pending := rfl, core := ?_, memory := ?_, running := rfl, faulted := ?_,
             alive := alive, lazy := lazy, model := mr }
    · show CoreLe _ (x86AdvancePastSvc (x86ApplyEffectNative ms.native (mkEffect v [] []))).m.core
      simp only [x86AdvancePastSvc, x86ApplyEffectNative, ite_eq_right (pend158 _)]
      have shape : (closeNext g r11 r k').x.core = Apps.Sha256sum.X86Sys.returnCore (fun _ => r11)
          { g.x.core with rip := g.x.core.rip + 2 } (Apps.Sha256sum.X86Sys.raxOf r) := by
        cases r <;> rfl
      rw [shape, hr11, eq]
      refine ⟨?_, fle⟩
      simp only [Apps.Sha256sum.X86Sys.returnCore, rax]
      rfl
    · show (x86AdvancePastSvc (x86ApplyEffectNative ms.native (mkEffect v [] []))).m.memory =
        (closeNext g r11 r k').x.memory
      simp only [x86AdvancePastSvc, x86ApplyEffectNative]
      rw [show applyMemoryEffect ms.native.m.memory (mkEffect v [] []) = ms.native.m.memory from rfl]
      cases r <;> exact p.memory
    · show (closeNext g r11 r k').x.faulted = false
      cases r <;> exact p.faulted
  have gstep : ∀ r k', Apps.Sha256sum.Sys.WorldStep w g.k (.close fd) r k' →
      GStep w g [.sys (.close fd) r] (closeNext g r11 r k') :=
    fun r k' ws => GStep.call r11 p.running p.faulted (step8_trap p.trap)
      (decode_close { g.x.core with rip := g.x.core.rip + 2 } _ number) trivial ws
  have flat : ∀ r, [Ev.sys (.close fd) r].flatMap (evFlat inp.fs) = [] := by
    intro r; simp [evFlat, readBytes, outBytes, exitPart]
  have lazyFds : ∀ fds, (model.withFds fds).vmLazy = [] := fun _ => p.lazy
  have haltedFds : ∀ fds, (model.withFds fds).halted = none := fun _ => p.alive
  -- the two outcomes
  have caseOpen : (g.k.fds fd).isSome →
      ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ [] (.next c') ∧
        GStep w g [.sys (.close fd) (.ok 0)] (closeNext g r11 (.ok 0) (g.k.set fd none)) ∧
        RunRel MR c' (closeNext g r11 (.ok 0) (g.k.set fd none)) (h ++ [.sys (.close fd) (.ok 0)]) := by
    intro isOpen
    obtain ⟨src, hsrc⟩ := Option.isSome_iff_exists.mp isOpen
    have lpsOpen : (fdLookup model.fds (fd32 (g.x.core.read .rdi))).isSome := by
      rw [show model = (⟨ms, model⟩ : Config (machine oracle)).model from rfl, corr]; exact isOpen
    refine ⟨_, .syscall p.alive svc ((spec_iff _).2 (.inr ⟨lpsOpen, rfl⟩)) (notRefused _)
      (haltedFds _) (X86Launch.materializeModelAccesses_no_lazy _ _ (lazyFds _)),
      gstep _ _ (.closeOk hsrc), related _ _ _ _ raxOf_ok_zero (haltedFds _) (lazyFds _)
        (keepOk r11 isOpen)⟩
  have caseClosed : g.k.fds fd = none →
      ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ [] (.next c') ∧
        GStep w g [.sys (.close fd) (.err .EBADF)] (closeNext g r11 (.err .EBADF) g.k) ∧
        RunRel MR c' (closeNext g r11 (.err .EBADF) g.k) (h ++ [.sys (.close fd) (.err .EBADF)]) := by
    intro isClosed
    have lpsClosed : fdLookup model.fds (fd32 (g.x.core.read .rdi)) = none := by
      have := corr
      simp only [isClosed, Option.isSome_none] at this
      exact Option.not_isSome_iff_eq_none.mp (by simp [this])
    refine ⟨_, .syscall p.alive svc ((spec_iff _).2 (.inl ⟨lpsClosed, rfl⟩)) (notRefused _)
      p.alive (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy),
      gstep _ _ (.closeBad isClosed), related _ _ _ _ raxOf_ebadf p.alive p.lazy
        (keepBad r11 isClosed)⟩
  refine ⟨fun evs st s => ?_, ?_, ?_⟩
  · cases s with
    | syscall _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨lpsClosed, out⟩ | ⟨lpsOpen, out⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy] at materialized
        cases materialized
        have isClosed : g.k.fds fd = none := by
          have := corr
          rw [show (⟨ms, model⟩ : Config (machine oracle)).model = model from rfl, lpsClosed] at this
          exact Option.not_isSome_iff_eq_none.mp (by simp [← this])
        exact ⟨_, rfl, _, _, gstep _ _ (.closeBad isClosed), (flat _).symm,
          .inl (related _ _ _ _ raxOf_ebadf p.alive p.lazy (keepBad r11 isClosed))⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ (lazyFds _)] at materialized
        cases materialized
        have isOpen : (g.k.fds fd).isSome := by
          rw [← corr]; exact lpsOpen
        obtain ⟨src, hsrc⟩ := Option.isSome_iff_exists.mp isOpen
        exact ⟨_, rfl, _, _, gstep _ _ (.closeOk hsrc), (flat _).symm,
          .inl (related _ _ _ _ raxOf_ok_zero (haltedFds _) (lazyFds _) (keepOk r11 isOpen))⟩
    | syscallMaterializationFault _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, out⟩ <;> cases out
      · rw [X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy] at materialized
        cases materialized
      · rw [X86Launch.materializeModelAccesses_no_lazy _ _ (lazyFds _)] at materialized
        cases materialized
    | exit _ p' sp halted _ =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, out⟩ <;> cases out
      · rw [show model.halted = none from p.alive] at halted; cases halted
      · rw [haltedFds] at halted; cases halted
    | killed _ p' sp k =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, out⟩ <;> cases out
      · rw [killed] at k; cases k
      · have : (model.withFds (fdRemove model.fds (fd32 (g.x.core.read .rdi)))).killedBy = none := by
          simp only [Model.killedBy]
          split
          · exact haltedFds _
          · rfl
        rw [this] at k; cases k
    | syscallUnmodeled _ p' sp =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, out⟩ <;> cases out
    | instr _ p' => rw [svc] at p'; cases p'
    | instrFault _ p' => rw [svc] at p'; cases p'
    | instrUnmodeled _ p' => rw [svc] at p'; cases p'
  · cases hk : g.k.fds fd with
    | none =>
      obtain ⟨c', s, -⟩ := caseClosed hk
      exact ⟨_, _, s⟩
    | some src =>
      obtain ⟨c', s, -⟩ := caseOpen (by rw [hk]; rfl)
      exact ⟨_, _, s⟩
  · cases hk : g.k.fds fd with
    | none =>
      obtain ⟨c', s, gs, r⟩ := caseClosed hk
      exact ⟨_, _, gs, c', by rw [flat]; exact s, .inl r⟩
    | some src =>
      obtain ⟨c', s, gs, r⟩ := caseOpen (by rw [hk]; rfl)
      exact ⟨_, _, gs, c', by rw [flat]; exact s, .inl r⟩

end Close

end Silmaril.Process.LPS.Problems.GnuSha256sum
