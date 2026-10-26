module

public import Silmaril.Process.LPS.Problems.Sha256Cli.WriteSpec

/-! # Segment `bridge`: the `write` call (VERIFIED, under stated hypotheses)

`pend_write`: from a pending pair whose call is `write` on CLI descriptor 1, given that LPS
descriptor 1 is channel 1, that the range is modelled (`modeledRwRange`, which holds for counts
up to 128 KiB and for every range below `TASK_SIZE`) and that `MR` survives the write, every
LPS step is a successful write of a prefix that the CLI matches with the same bytes, LPS can
move, and some CLI step is matched by one LPS step. The results are aligned pairs.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

theorem write_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 1) :
    NativeX86.extendedSyscallSpec i m o ↔
      writeSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)
        (NativeX86.referenceInputFor ⟨64, 1, "write"⟩ i) m o := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  rfl

theorem fd32_of_low (w : Word) (low : (w.setWidth 32).toNat = 1) : fd32 w = 1 := by
  have mod : w.toNat % 2 ^ 32 = 1 := by simpa [BitVec.toNat_setWidth] using low
  unfold fd32 abiLow32 zw uns
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have : ((w.toNat : Int) % 2 ^ 32) = 1 := by exact_mod_cast mod
  rw [this]; rfl

theorem lenWord_eq {α : Type} (l : List α) : lenWord l = BitVec.ofNat 64 l.length := by
  simp [lenWord, zw]

theorem clamp_toNat (count : Word) :
    (zw (rwCountClamp count)).toNat = min count.toNat 0x7ffff000 := by
  unfold zw rwCountClamp uns MAX_RW_COUNT
  have h : min (count.toNat : Int) 0x7ffff000 = ((min count.toNat 0x7ffff000 : Nat) : Int) := by
    omega
  rw [h, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := count.isLt
  omega

theorem applyMemoryEffect_retOnly (memory : Silmaril.Process.Memory) (r : Word)
    (reads : List (Word × Nat)) :
    applyMemoryEffect memory ((mkEffect r [] []).withCopyins reads) = memory := rfl

section Write

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event}

/-- **`write` to stdout.** -/
theorem pend_write (p : PendRel MR c x h) (number : (x.core.read .rax).toNat = 1)
    (fd1 : ((x.core.read .rdi).setWidth 32).toNat = 1)
    (lookup : fdLookup c.model.fds 1 = some (.channel 1))
    (modeled : modeledRwRangeWith accessOkb (x.core.read .rsi) (x.core.read .rdx) = true)
    (keep : ∀ d bs, x.env.descriptors 1 = some d →
      MR c.model (x.env.setDescriptor 1 { d with output := d.output ++ bs }) (h ++ [.write 1 bs]))
    (moves : ∃ e y, CStep x e y) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, CStep x es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        Rel MR c' y (h ++ es)) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∃ es y, CStep x es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        Rel MR c' y (h ++ es)) := by
  -- the CLI side: the buffer is readable and descriptor 1 is writable
  obtain ⟨e₀, y₀, s₀⟩ := moves
  obtain ⟨d, bytes, written₀, -, open1, writable, loaded, pos₀, bound₀, -, -, -⟩ :=
    cli_write_cases p number s₀
  rw [fd1] at open1
  have count_pos : 1 ≤ (x.core.read .rdx).toNat := by omega
  have bytes_len : bytes.length = (x.core.read .rdx).toNat :=
    (Silmaril.X86.Memory.readWith_eq_some_iff.mp loaded).1
  -- the LPS side
  obtain ⟨ms, model⟩ := c
  have svc : (machine oracle).svcPending ms = some (x.core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (x.core.read .rax) with hi
  have sysno : i.sysno = x.core.read .rax := rfl
  have arg : ∀ r k, k < 6 → [Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9][k]? = some r →
      i.arg k = x.core.read r := by
    intro r k _ hk
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD k 0) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hk]
    simp [CoreLe.read_eq p.core]
  have a0 : i.arg 0 = x.core.read .rdi := arg _ 0 (by omega) rfl
  have a1 : i.arg 1 = x.core.read .rsi := arg _ 1 (by omega) rfl
  have a2 : i.arg 2 = x.core.read .rdx := arg _ 2 (by omega) rfl
  have mem : i.mem = viewByte x.env.memory .read := by
    show viewByte ms.native.m.memory .read = _
    rw [show ms.native.m.memory = x.env.memory from p.memory]
  set clamp := min (x.core.read .rdx).toNat 0x7ffff000 with hclamp
  have source : writeSource i.mem (x.core.read .rsi) (x.core.read .rdx) = bytes.take clamp := by
    unfold writeSource readableBytes
    rw [mem, clamp_toNat, ← hclamp]
    have rsi : x.core.read .rsi = BitVec.ofNat 64 (x.core.read .rsi).toNat := by simp
    conv => lhs; rw [rsi]
    exact readableBytesAux_of_readBytes clamp _ _ bytes loaded (by omega)
  have nonempty : bytes.take clamp ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp only [List.length_take, List.length_nil] at this
    omega
  have nonzero : wIs0 (x.core.read .rdx) = false := by
    unfold wIs0
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h0; rw [h0] at count_pos; simp at count_pos
  have spec_iff : ∀ o, NativeX86.extendedSyscallSpec i model o ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (x.core.read .rdx) ∧
        ds = (bytes.take clamp).take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins ([(x.core.read .rsi, ds.length)] ++ []))
          model (ds.map (.writeEv 1)) := by
    intro o
    rw [write_dispatch i model o (by rw [sysno]; exact number), a0, a1, a2, fd32_of_low _ fd1]
    rw [write_channel_iff 1 (x.core.read .rsi) (x.core.read .rdx) _ model o lookup modeled nonzero
      (by simpa [NativeX86.referenceInputFor, source] using nonempty)]
    simp only [NativeX86.referenceInputFor_mem]
    rw [source]
  have notRefused : ∀ eff, ¬ NativeX86.defaultRefusalFilter refusals i model eff :=
    fun eff => not_refused refusals i model eff (.inr (.inl (by rw [sysno]; exact number)))
  have clampInt : ∀ n : Nat, ((n : Int) ≤ rwCountClamp (x.core.read .rdx)) ↔ n ≤ clamp := by
    intro n; unfold rwCountClamp uns MAX_RW_COUNT; omega
  -- the matched pair after writing `ds`
  let ret (ds : List Byte) : SyscallEffect :=
    (mkEffect (lenWord ds) [] []).withCopyins ([(x.core.read .rsi, ds.length)] ++ [])
  have after : ∀ ds : List Byte, 1 ≤ ds.length → ds.length ≤ clamp → ds = bytes.take ds.length →
      CStep x [.write 1 ds] ⟨resumeWrite x.core ds.length
          ((rflagsImage ms.native.m.core.flags).getD 0),
        x.env.setDescriptor 1 { d with output := d.output ++ ds }⟩ ∧
      SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ (ds.map (.writeEv 1))
        (.next ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms (ret ds)), model⟩) ∧
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms (ret ds)), model⟩
        ⟨resumeWrite x.core ds.length ((rflagsImage ms.native.m.core.flags).getD 0),
          x.env.setDescriptor 1 { d with output := d.output ++ ds }⟩ (h ++ [.write 1 ds]) := by
    intro ds dpos dbound dtake
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨core, env⟩ := x
      have trap : CLI.X86Linux.step core env.memory = .syscall { core with rip := core.rip + 2 } :=
        cli_step_trap p.trap
      have q : CLI.X86Linux.request { core with rip := core.rip + 2 } =
          some (.write 1 (core.read .rsi).toNat (core.read .rdx).toNat) := by
        rw [cli_request_write { core with rip := core.rip + 2 } number]
        exact congrArg (fun f => some (Syscall.Request.write f _ _)) fd1
      refine CLI.Proc.Step.call (r := .ok ds.length) p.running trap.symm q ⟨?_, ?_, ?_⟩ ⟨_, rfl⟩
      · have ws := Syscall.Step.writeSome (written := ds.length) p.running open1 writable loaded
          (by omega) (by simp only [Syscall.maxTransfer]; omega)
        rw [← dtake] at ws
        exact ws
      · intro fd address count' q'; cases q'
      · intro bad
        cases ds with
        | nil => simp at dpos
        | cons => exact bad
    · refine .syscall p.alive svc ((spec_iff _).2 ⟨ds, ⟨dpos, (clampInt _).2 dbound, ?_⟩, rfl⟩)
        (notRefused _) p.alive (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy)
      rw [List.take_take, Nat.min_eq_left dbound]; exact dtake
    · have pend158 : ¬ (ms.native.pending = some 158 ∧ ms.native.m.core.read .rdi = 0x1002 ∧
          (ret ds).ret = 0) := by
        rintro ⟨hp, -, -⟩
        have hp' : some (x.core.read .rax) = some 158 := p.pending.symm.trans hp
        have := congrArg (fun o => o.map BitVec.toNat) hp'
        simp [number] at this
      obtain ⟨eq, fle⟩ := p.core
      refine { pending := rfl, core := ?_, memory := ?_, running := p.running, alive := p.alive,
               lazy := p.lazy, model := keep d ds open1 }
      · show CoreLe _ (x86AdvancePastSvc (x86ApplyEffectNative ms.native (ret ds))).m.core
        simp only [x86AdvancePastSvc, x86ApplyEffectNative, ite_eq_right pend158]
        rw [eq]
        refine ⟨?_, fle⟩
        simp only [ret, mkEffect, SyscallEffect.withCopyins, lenWord_eq]
        rfl
      · exact p.memory
  have killed : model.killedBy = none := by
    have alive : model.halted = none := p.alive
    simp only [Model.killedBy]
    split
    · exact alive
    · rfl
  have flat : ∀ ds : List Byte, [Syscall.Event.write 1 ds].flatMap (evFlat inp.fs) =
      ds.map (.writeEv 1) := by
    intro ds; simp [evFlat]
  have choice : ∀ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (x.core.read .rdx) ∧
      ds = (bytes.take clamp).take ds.length) → ds.length ≤ clamp ∧ ds = bytes.take ds.length := by
    rintro ds ⟨-, le, tk⟩
    have le' := (clampInt _).1 le
    refine ⟨le', ?_⟩
    rw [List.take_take, Nat.min_eq_left le'] at tk
    exact tk
  have first : 1 ≤ (bytes.take 1).length ∧ (bytes.take 1).length ≤ clamp ∧
      bytes.take 1 = bytes.take (bytes.take 1).length := by
    have : (bytes.take 1).length = 1 := by simp; omega
    rw [this]; exact ⟨le_refl _, by omega, rfl⟩
  refine ⟨fun evs st s => ?_, ?_, ?_⟩
  · cases s with
    | syscall _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      obtain ⟨ds, props, out⟩ := (spec_iff _).1 sp
      cases out
      rw [X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy] at materialized
      cases materialized
      obtain ⟨le, tk⟩ := choice ds props
      obtain ⟨cs, -, r⟩ := after ds props.1 le tk
      exact ⟨_, rfl, _, _, cs, (flat ds).symm, .inl r⟩
    | syscallMaterializationFault _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      obtain ⟨ds, props, out⟩ := (spec_iff _).1 sp
      cases out
      rw [X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy] at materialized
      cases materialized
    | exit _ p' sp halted _ =>
      rw [svc] at p'; cases p'
      obtain ⟨ds, props, out⟩ := (spec_iff _).1 sp
      cases out
      rw [show model.halted = none from p.alive] at halted; cases halted
    | killed _ p' sp k =>
      rw [svc] at p'; cases p'
      obtain ⟨ds, props, out⟩ := (spec_iff _).1 sp
      cases out
      rw [killed] at k; cases k
    | syscallUnmodeled _ p' sp =>
      rw [svc] at p'; cases p'
      obtain ⟨ds, props, out⟩ := (spec_iff _).1 sp
      cases out
    | instr _ p' => rw [svc] at p'; cases p'
    | instrFault _ p' => rw [svc] at p'; cases p'
    | instrUnmodeled _ p' => rw [svc] at p'; cases p'
  · obtain ⟨-, s, -⟩ := after (bytes.take 1) first.1 first.2.1 first.2.2
    exact ⟨_, _, s⟩
  · obtain ⟨cs, s, r⟩ := after (bytes.take 1) first.1 first.2.1 first.2.2
    exact ⟨_, _, cs, _, (flat _) ▸ s, .inl r⟩

end Write

/-! ## Reducing the obligations to `read` -/

/-- At a pending `write` that the CLI can complete within the invariant, the descriptor is 1. -/
theorem pend_write_fd {oracle : Nat → X86FlagChoices.Choice} {MR : DescRel}
    {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event} {message : List Byte}
    {input : CLI.ProcInput} (p : PendRel MR c x h) (number : (x.core.read .rax).toNat = 1)
    (safe : Safe CStep (Ok message) (Done input message) x h) :
    ((x.core.read .rdi).setWidth 32).toNat = 1 := by
  obtain ⟨e, y, s⟩ := safe.2.1
  obtain ⟨d, bytes, written, flagsWord, -, -, -, -, -, -, rfl, -⟩ := cli_write_cases p number s
  have only : CLI.WritesOnlyTo [1] (h ++ [.write ((x.core.read .rdi).setWidth 32).toNat
      (bytes.take written)]) := by
    rcases safe.2.2 _ _ s with ok | done
    · exact ok.2.1
    · exact done.2.2.1
  have := only _ _ (List.mem_append_right h (List.mem_singleton_self _))
  simpa using this

/-- The obligations left once `exit` and `write` are proved. `MR` must record the file system,
LPS descriptor 1 as channel 1, that a CLI-readable buffer is in LPS's modelled range (true when
memory lies below `TASK_SIZE`), survive writes to descriptor 1 and instructions, and `read`
of stdin must be simulated. -/
structure ReadObligations (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (inp : ProcInput) (message : List Byte) (input : CLI.ProcInput) (MR : DescRel) : Prop where
  retire : ∀ {model s h} {core core' : Silmaril.X86.State} {memory' : Silmaril.Process.Memory},
    MR model s h → CLI.X86Linux.step core s.memory = .retired core' memory' →
    MR model { s with memory := memory' } h
  fs : ∀ {model s h}, MR model s h → model.fs = inp.fs
  stdout : ∀ {model s h}, MR model s h → fdLookup model.fds 1 = some (.channel 1)
  modeled : ∀ {model s h} {buf count : Word} {bytes : List Byte}, MR model s h →
    s.memory.readBytes buf.toNat count.toNat = some bytes →
    modeledRwRangeWith accessOkb buf count = true
  keepWrite : ∀ {model s h} {d : Syscall.Descriptor} (bs : List Byte), MR model s h →
    s.descriptors 1 = some d →
    MR model (s.setDescriptor 1 { d with output := d.output ++ bs }) (h ++ [.write 1 bs])
  step : ∀ {c : Config (machine oracle)} {x h evs st}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h → (x.core.read .rax).toNat = 0 →
    SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st →
    ∃ c', st = .next c' ∧ ∃ es y, CStep x es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
      Rel MR c' y (h ++ es)
  progress : ∀ {c : Config (machine oracle)} {x h}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h → (x.core.read .rax).toNat = 0 →
    ∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c evs st
  back : ∀ {c : Config (machine oracle)} {x h}, PendRel MR c x h →
    Safe CStep (Ok message) (Done input message) x h → (x.core.read .rax).toNat = 0 →
    ∃ es y, CStep x es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
      Rel MR c' y (h ++ es)

/-- `write` discharged (VERIFIED). -/
theorem ReadObligations.toReadWrite {oracle : Nat → X86FlagChoices.Choice}
    {refusals : SpuriousCfg} {inp : ProcInput} {message : List Byte} {input : CLI.ProcInput}
    {MR : DescRel} (ro : ReadObligations oracle refusals inp message input MR) :
    ReadWriteObligations oracle refusals inp message input MR := by
  refine ⟨ro.retire, ro.fs, ?_, ?_, ?_⟩
  · intro c x h evs st p safe n s
    rcases n with n | n
    · exact ro.step p safe n s
    · obtain ⟨e, y, s₀⟩ := safe.2.1
      obtain ⟨d, bytes, -, -, -, -, loaded, -⟩ := cli_write_cases p n s₀
      exact (pend_write (inp := inp) (refusals := refusals) p n (pend_write_fd p n safe)
        (ro.stdout p.model) (ro.modeled p.model loaded)
        (fun d bs open1 => ro.keepWrite bs p.model open1) safe.2.1).1 evs st s
  · intro c x h p safe n
    rcases n with n | n
    · exact ro.progress p safe n
    · obtain ⟨e, y, s₀⟩ := safe.2.1
      obtain ⟨d, bytes, -, -, -, -, loaded, -⟩ := cli_write_cases p n s₀
      exact (pend_write (inp := inp) (refusals := refusals) p n (pend_write_fd p n safe)
        (ro.stdout p.model) (ro.modeled p.model loaded)
        (fun d bs open1 => ro.keepWrite bs p.model open1) safe.2.1).2.1
  · intro c x h p safe n
    rcases n with n | n
    · exact ro.back p safe n
    · obtain ⟨e, y, s₀⟩ := safe.2.1
      obtain ⟨d, bytes, -, -, -, -, loaded, -⟩ := cli_write_cases p n s₀
      exact (pend_write (inp := inp) (refusals := refusals) p n (pend_write_fd p n safe)
        (ro.stdout p.model) (ro.modeled p.model loaded)
        (fun d bs open1 => ro.keepWrite bs p.model open1) safe.2.1).2.2

/-- The launch-local remainder after `exit` and `write`. -/
def ReadSimAt (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop :=
  ∃ (input : CLI.ProcInput) (x₀ : PS) (MR : DescRel),
    input.stdin = .ofList message ∧ input.Valid ∧ Launch input x₀ ∧
      Rel MR (initial oracle limit en inp) x₀ [] ∧
      ReadObligations oracle refusals inp message input MR

/-- **Reduction (VERIFIED).** Launch-local read simulations give the bridge segment. -/
theorem bridge_of_readSim
    (h : ∀ oracle refusals limit en inp message, Admissible oracle en inp message →
      ReadSimAt oracle refusals limit en inp message) : BridgeSegment :=
  bridge_of_readWriteSim fun oracle refusals limit en inp message admissible => by
    obtain ⟨input, x₀, MR, stdin, valid, launch, related, ro⟩ :=
      h oracle refusals limit en inp message admissible
    exact ⟨input, x₀, MR, stdin, valid, launch, related, ro.toReadWrite⟩

end Silmaril.Process.LPS.Problems.Sha256Cli
