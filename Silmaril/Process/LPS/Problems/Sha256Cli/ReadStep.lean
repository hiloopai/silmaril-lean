module

public import Silmaril.Process.LPS.Problems.Sha256Cli.WriteStep
public import Silmaril.Process.LPS.Problems.Sha256Cli.ReadSpec

/-! # Segment `bridge`: the stdin `read` call (VERIFIED, under stated hypotheses)

`pend_read`: from a pending pair whose call is `read` on CLI descriptor 0, given that LPS
descriptor 0 is channel 0, that the LPS stdin is the CLI stream after the cursor, that the
buffer passes `access_ok`, that permitted-writable bytes are backed, and that the relation
survives the read, every LPS step is a read the CLI matches with the same bytes, LPS can move,
and some CLI step is matched by one LPS step.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

theorem read_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (number : i.sysno.toNat = 0) :
    NativeX86.extendedSyscallSpec i m o ↔
      readSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)
        (NativeX86.referenceInputFor ⟨63, 0, "read"⟩ i) m o := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  rfl

theorem fd32_of_low_zero (w : Word) (low : (w.setWidth 32).toNat = 0) : fd32 w = 0 := by
  have mod : w.toNat % 2 ^ 32 = 0 := by simpa [BitVec.toNat_setWidth] using low
  unfold fd32 abiLow32 zw uns
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have : ((w.toNat : Int) % 2 ^ 32) = 0 := by exact_mod_cast mod
  rw [this]; rfl

/-! ## Streams -/

namespace StreamFacts

theorem ext {s t : InputStream} (h : ∀ i, s.byteAt i = t.byteAt i) : s = t := by
  cases s; cases t
  congr
  funext i; exact h i

theorem drop_drop (s : InputStream) (a b : Nat) :
    InputStream.drop (InputStream.drop s a) b = InputStream.drop s (a + b) :=
  ext fun i => by simp only [InputStream.drop, Nat.add_assoc]

theorem drop_byteAt (s : InputStream) (a i : Nat) :
    (InputStream.drop s a).byteAt i = s.byteAt (a + i) := rfl

theorem takeFrom_matches (s : InputStream) :
    ∀ (k start : Nat), s.Matches start (InputStream.takeFrom s start k) := by
  intro k
  induction k with
  | zero => intro start i bound; simp [InputStream.takeFrom] at bound
  | succ k ih =>
    intro start i bound
    cases hb : s.byteAt start with
    | none => simp [InputStream.takeFrom, hb] at bound
    | some b =>
      simp only [InputStream.takeFrom, hb] at bound ⊢
      cases i with
      | zero => simpa using hb
      | succ i =>
        have := ih (start + 1) i (by simpa using bound)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem takeFrom_of_matches (s : InputStream) :
    ∀ (bytes : List Byte) (start k : Nat), s.Matches start bytes → bytes.length ≤ k →
      (bytes.length < k → s.byteAt (start + bytes.length) = none) →
      InputStream.takeFrom s start k = bytes := by
  intro bytes
  induction bytes with
  | nil =>
    intro start k _ _ stop
    cases k with
    | zero => rfl
    | succ k =>
      have h := stop (by simp)
      simp only [List.length_nil, Nat.add_zero] at h
      simp [InputStream.takeFrom, h]
  | cons b rest ih =>
    intro start k m len stop
    cases k with
    | zero => simp at len
    | succ k =>
      have hb : s.byteAt start = some b := m 0 (by simp)
      simp only [InputStream.takeFrom, hb]
      congr 1
      apply ih (start + 1) k
      · intro i bound
        have := m (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      · simp at len; omega
      · intro lt
        have := stop (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem takeFrom_length_le (s : InputStream) :
    ∀ (k start : Nat), (InputStream.takeFrom s start k).length ≤ k := by
  intro k
  induction k with
  | zero => intro; simp [InputStream.takeFrom]
  | succ k ih =>
    intro start
    unfold InputStream.takeFrom
    cases s.byteAt start with
    | none => simp
    | some b => simpa using ih (start + 1)

/-- A prefix of `n` bytes of a stream that matches `bytes` is `bytes`. -/
theorem take_of_matches (s : InputStream) (cursor : Nat) (bytes : List Byte)
    (m : s.Matches cursor bytes) :
    (InputStream.take (InputStream.drop s cursor) bytes.length).1 = bytes := by
  apply takeFrom_of_matches _ bytes 0 _ _ (le_refl _) (fun lt => absurd lt (lt_irrefl _))
  intro i bound
  simpa [drop_byteAt] using m i bound

theorem matches_of_take (s : InputStream) (cursor n : Nat) (bytes : List Byte)
    (h : (InputStream.take (InputStream.drop s cursor) n).1 = bytes) : s.Matches cursor bytes := by
  intro i bound
  have m := takeFrom_matches (InputStream.drop s cursor) n 0 i
  simp only [InputStream.take] at h
  subst h
  simpa [drop_byteAt] using m bound

theorem take_snd (s : InputStream) (cursor : Nat) (bytes : List Byte) (n : Nat)
    (h : (InputStream.take (InputStream.drop s cursor) n).1 = bytes) :
    (InputStream.take (InputStream.drop s cursor) n).2 = InputStream.drop s (cursor + bytes.length) := by
  simp only [InputStream.take] at h ⊢
  rw [h, drop_drop]

theorem atEof_drop (s : InputStream) (cursor : Nat) :
    (InputStream.drop s cursor).atEof = (s.byteAt cursor).isNone := by
  simp [InputStream.atEof, drop_byteAt]

end StreamFacts

/-! ## The writable view of backed, permitted memory -/

/-- Every byte that may be written is backed. -/
def Backed (memory : Silmaril.Process.Memory) : Prop :=
  ∀ a : Nat, memory.permits .write a = true → (memory.bytes.get? a).isSome = true

theorem readBytesAux_write_isSome {memory : Silmaril.Process.Memory} (backed : Backed memory) :
    ∀ (k a n : Nat), memory.Permitted .write a n → k ≤ n →
      (readBytesAux (Machines.viewByte memory .write) (BitVec.ofNat 64 a) k).isSome = true := by
  intro k
  induction k with
  | zero => intro a n _ _; rfl
  | succ k ih =>
    intro a n perm bound
    have perm' := perm
    rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at perm'
    obtain ⟨start, limit, perms⟩ := perm'
    have p0 : memory.permits .write a = true := by simpa using perms 0 (by omega)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (backed a p0)
    have toNat : (BitVec.ofNat 64 a).toNat = a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa [Silmaril.Process.addressLimit] using start)
    have first : Machines.viewByte memory .write (BitVec.ofNat 64 a) = some b := by
      unfold Machines.viewByte
      rw [toNat, ite_eq_left p0]; exact hb
    unfold readBytesAux
    rw [first]
    rcases Nat.eq_zero_or_pos k with rfl | kpos
    · rfl
    · have next : BitVec.ofNat 64 a + 1 = BitVec.ofNat 64 (a + 1) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
      rw [next]
      have perm1 : memory.Permitted .write (a + 1) (n - 1) := by
        rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff]
        refine ⟨by simp [Silmaril.Process.addressLimit] at limit ⊢; omega,
          by simp [Silmaril.Process.addressLimit] at limit ⊢; omega, fun i hi => ?_⟩
        have := perms (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      have := ih (a + 1) (n - 1) perm1 (by omega)
      cases h : readBytesAux (Machines.viewByte memory .write) (BitVec.ofNat 64 (a + 1)) k with
      | none => rw [h] at this; simp at this
      | some l => simp

/-! ## The pending `read` -/

section Read

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {x : PS} {h : List Syscall.Event}

/-- **`read` from stdin.** -/
theorem pend_read (p : PendRel MR c x h) (number : (x.core.read .rax).toNat = 0)
    (fd0 : ((x.core.read .rdi).setWidth 32).toNat = 0)
    (lookup : fdLookup c.model.fds 0 = some (.channel 0))
    (stdin : ∀ d, x.env.descriptors 0 = some d →
      c.model.stdin = InputStream.drop d.input d.cursor)
    (ok : accessOkb (x.core.read .rsi) (uns (x.core.read .rdx)) = true)
    (backed : Backed x.env.memory)
    (keep : ∀ (d : Syscall.Descriptor) (bs : List Byte) (memory' : Silmaril.Process.Memory),
      x.env.descriptors 0 = some d →
      x.env.memory.writeBytes (x.core.read .rsi).toNat bs = some memory' →
      MR (c.model.withStdin (InputStream.drop d.input (d.cursor + bs.length)))
        { x.env.setDescriptor 0 { d with cursor := d.cursor + bs.length } with memory := memory' }
        (h ++ [.read 0 bs]))
    (keepEof : MR c.model x.env (h ++ [.read 0 []]))
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
  obtain ⟨core, env⟩ := x
  dsimp only at *
  -- the CLI side
  obtain ⟨e₀, y₀, s₀⟩ := moves
  obtain ⟨d, flags₀, open0, readable, accessible, -⟩ := cli_read_cases p number s₀
  rw [fd0] at open0
  have stdinEq := stdin d open0
  -- the LPS side
  obtain ⟨ms, model⟩ := c
  have svc : (machine oracle).svcPending ms = some (core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (core.read .rax) with hi
  have sysno : i.sysno = core.read .rax := rfl
  have arg : ∀ r k, k < 6 → [Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9][k]? = some r →
      i.arg k = core.read r := by
    intro r k _ hk
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD k 0) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hk]
    simp [CoreLe.read_eq p.core]
  have a0 : i.arg 0 = core.read .rdi := arg _ 0 (by omega) rfl
  have a1 : i.arg 1 = core.read .rsi := arg _ 1 (by omega) rfl
  have a2 : i.arg 2 = core.read .rdx := arg _ 2 (by omega) rfl
  have wmem : i.wmem = viewByte env.memory .write := by
    show viewByte ms.native.m.memory .write = _
    rw [show ms.native.m.memory = env.memory from p.memory]
  have rsi : core.read .rsi = BitVec.ofNat 64 (core.read .rsi).toNat := by simp
  have room : ∀ n, n ≤ (core.read .rdx).toNat →
      (readBytesAux (viewByte env.memory .write) (core.read .rsi) n).isSome = true := by
    intro n hn
    rw [rsi]
    exact readBytesAux_write_isSome backed n _ _ accessible hn
  set clamp := min (core.read .rdx).toNat 0x7ffff000 with hclamp
  have clampInt : ∀ n : Nat, ((n : Int) ≤ rwCountClamp (core.read .rdx)) ↔ n ≤ clamp := by
    intro n; unfold rwCountClamp uns MAX_RW_COUNT; omega
  have lenWord_toNat : ∀ l : List Byte, l.length ≤ (core.read .rdx).toNat →
      (lenWord l).toNat = l.length := by
    intro l hl
    rw [lenWord_eq, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hl (core.read .rdx).isLt)
  have spec_iff : ∀ o, NativeX86.extendedSyscallSpec i model o ↔
      ((wIs0 (core.read .rdx) = true ∨ model.stdin.atEof = true) ∧
          o = .ok (mkEffect 0 [] []) model []) ∨
      (wIs0 (core.read .rdx) = false ∧ model.stdin.atEof = false ∧
        ∃ bs : List Byte, (1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp (core.read .rdx) ∧
          (model.stdin.take bs.length).1 = bs ∧
          (readBytesMap i.wmem (core.read .rsi) (lenWord bs)).isSome) ∧
          o = .ok (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])
            (model.withStdin (model.stdin.take bs.length).2) (bs.map (.readEv 0))) := by
    intro o
    rw [read_dispatch i model o (by rw [sysno]; exact number), a0, a1, a2,
      fd32_of_low_zero _ fd0]
    apply read_channel_iff 0 (core.read .rsi) (core.read .rdx) _ model o lookup ok
    · intro nz
      simp only [NativeX86.referenceInputFor_wmem, readBytesMap, wmem]
      have : (core.read .rdx).toNat ≠ 0 := by
        intro z; apply absurd nz; unfold wIs0; simp [BitVec.eq_of_toNat_eq (x := core.read .rdx) (y := 0) (by simpa using z)]
      exact room 1 (by omega)
    · intro _
      simp only [NativeX86.referenceInputFor_wmem, readBytesMap, wmem]
      have le := StreamFacts.takeFrom_length_le model.stdin
      unfold InputStream.takeZ
      split
      · rename_i pos
        rw [lenWord_toNat]
        · apply room
          have := le (rwCountClamp (core.read .rdx)).toNat 0
          simp only [InputStream.take]
          unfold rwCountClamp uns MAX_RW_COUNT at this pos ⊢
          omega
        · have := le (rwCountClamp (core.read .rdx)).toNat 0
          simp only [InputStream.take]
          unfold rwCountClamp uns MAX_RW_COUNT at this pos ⊢
          omega
      · exact room 0 (by omega)
  have notRefused : ∀ eff, ¬ NativeX86.defaultRefusalFilter refusals i model eff :=
    fun eff => not_refused refusals i model eff (.inl (by rw [sysno]; exact number))
  have stdinM : model.stdin = InputStream.drop d.input d.cursor := stdinEq
  have killed : model.killedBy = none := by
    have alive : model.halted = none := p.alive
    simp only [Model.killedBy]
    split
    · exact alive
    · rfl
  have trap : CLI.X86Linux.step core env.memory = .syscall { core with rip := core.rip + 2 } :=
    cli_step_trap p.trap
  have q : CLI.X86Linux.request { core with rip := core.rip + 2 } =
      some (.read 0 (core.read .rsi).toNat (core.read .rdx).toNat) := by
    rw [cli_request_read { core with rip := core.rip + 2 } number]
    exact congrArg (fun f => some (Syscall.Request.read f _ _)) fd0
  have pend158 : ∀ eff : SyscallEffect, ¬ (ms.native.pending = some 158 ∧
      ms.native.m.core.read .rdi = 0x1002 ∧ eff.ret = 0) := by
    rintro eff ⟨hp, -, -⟩
    have hp' : some (core.read .rax) = some 158 := p.pending.symm.trans hp
    have := congrArg (fun o => o.map BitVec.toNat) hp'
    simp [number] at this
  -- a positive read of `bs`
  have afterPos : ∀ bs : List Byte, 1 ≤ bs.length → bs.length ≤ clamp →
      d.input.Matches d.cursor bs →
      ∃ memory', env.memory.writeBytes (core.read .rsi).toNat bs = some memory' ∧
      CStep ⟨core, env⟩ [.read 0 bs] ⟨resumeRead core bs.length
          ((rflagsImage ms.native.m.core.flags).getD 0),
        { env.setDescriptor 0 { d with cursor := d.cursor + bs.length } with memory := memory' }⟩ ∧
      SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ (bs.map (.readEv 0))
        (.next ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])),
          model.withStdin (model.stdin.take bs.length).2⟩) ∧
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])),
          model.withStdin (model.stdin.take bs.length).2⟩
        ⟨resumeRead core bs.length ((rflagsImage ms.native.m.core.flags).getD 0),
          { env.setDescriptor 0 { d with cursor := d.cursor + bs.length } with memory := memory' }⟩
        (h ++ [.read 0 bs]) := by
    intro bs pos le m
    have lenRdx : bs.length ≤ (core.read .rdx).toNat := by omega
    have perm : env.memory.Permitted .write (core.read .rsi).toNat bs.length := by
      have a := accessible
      simp only [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at a ⊢
      exact ⟨a.1, by omega, fun o ho => a.2.2 o (by omega)⟩
    obtain ⟨memory', copied⟩ : ∃ memory', env.memory.writeBytes (core.read .rsi).toNat bs = some memory' :=
      ⟨_, by unfold Silmaril.Process.Memory.writeBytes; rw [ite_eq_left (show env.memory.checkSpan .write _ bs.length = true from perm)]⟩
    have take1 : (model.stdin.take bs.length).1 = bs := by
      rw [stdinM]; exact StreamFacts.take_of_matches _ _ _ m
    refine ⟨memory', copied, ?_, ?_, ?_⟩
    · refine CLI.Proc.Step.call (r := .ok bs.length) p.running trap.symm q ⟨?_, ?_, ?_⟩ ⟨_, rfl⟩
      · exact Syscall.Step.readSome p.running open0 readable m (by omega) lenRdx
          (by simp only [Syscall.maxTransfer]; omega) accessible copied
      · intro fd address count' q' bad; cases bad
      · intro bad; exact bad
    · refine .syscall p.alive svc ((spec_iff _).2 (.inr ⟨?_, ?_, bs, ⟨pos, (clampInt _).2 le, take1, ?_⟩, rfl⟩))
        (notRefused _) p.alive (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy)
      · unfold wIs0; simp only [beq_eq_false_iff_ne, ne_eq]
        have nz : (core.read .rdx).toNat ≠ 0 := by omega
        intro h0; apply nz; rw [h0]; rfl
      · rw [stdinM, StreamFacts.atEof_drop]
        have := m 0 (by omega)
        rw [Nat.add_zero] at this
        rw [this]; rfl
      · simp only [readBytesMap, wmem]
        rw [lenWord_toNat _ lenRdx]
        exact room _ lenRdx
    · obtain ⟨eq, fle⟩ := p.core
      refine { pending := rfl, core := ?_, memory := ?_, running := p.running, alive := p.alive,
               lazy := p.lazy, model := ?_ }
      · show CoreLe _ (x86AdvancePastSvc (x86ApplyEffectNative ms.native _)).m.core
        simp only [x86AdvancePastSvc, x86ApplyEffectNative, ite_eq_right (pend158 _)]
        rw [eq]
        refine ⟨?_, fle⟩
        simp only [mkEffect, lenWord_eq]
        rfl
      · show applyMemoryEffect ms.native.m.memory _ = memory'
        rw [p.memory]
        exact applyMemoryEffect_read _ copied
      · rw [stdinM, StreamFacts.take_snd _ _ bs _ (stdinM ▸ take1)]
        exact keep d bs memory' open0 copied
  -- end of file, or a zero count
  have eofCase : (wIs0 (core.read .rdx) = true ∨ model.stdin.atEof = true) →
      CStep ⟨core, env⟩ [.read 0 []] ⟨resumeRead core 0
          ((rflagsImage ms.native.m.core.flags).getD 0), env⟩ ∧
      SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ []
        (.next ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect 0 [] [])), model⟩) ∧
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect 0 [] [])), model⟩
        ⟨resumeRead core 0 ((rflagsImage ms.native.m.core.flags).getD 0), env⟩
        (h ++ [.read 0 []]) := by
    intro cond
    refine ⟨?_, ?_, ?_⟩
    · refine CLI.Proc.Step.call (r := .ok 0) p.running trap.symm q ⟨?_, ?_, ?_⟩ ⟨_, rfl⟩
      · rcases cond with z | e
        · have z' : (core.read .rdx).toNat = 0 := by
            unfold wIs0 at z; simp only [beq_iff_eq] at z; simp [z]
          have acc0 : env.memory.Permitted .write (core.read .rsi).toNat 0 := z' ▸ accessible
          show Syscall.Step env (.read 0 (core.read .rsi).toNat (core.read .rdx).toNat) _ _ _
          rw [z']
          exact Syscall.Step.readZero p.running open0 readable acc0
        · rw [stdinM, StreamFacts.atEof_drop] at e
          exact Syscall.Step.readEof p.running open0 readable (by simpa using e) accessible
      · intro fd address count' q' bad; cases bad
      · intro bad; exact bad
    · exact .syscall p.alive svc ((spec_iff _).2 (.inl ⟨cond, rfl⟩))
        (notRefused _) p.alive (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy)
    · obtain ⟨eq, fle⟩ := p.core
      refine { pending := rfl, core := ?_, memory := ?_, running := p.running, alive := p.alive,
               lazy := p.lazy, model := keepEof }
      · show CoreLe _ (x86AdvancePastSvc (x86ApplyEffectNative ms.native _)).m.core
        simp only [x86AdvancePastSvc, x86ApplyEffectNative, ite_eq_right (pend158 _)]
        rw [eq]
        refine ⟨?_, fle⟩
        simp only [mkEffect]
        rfl
      · exact p.memory
  have flatPos : ∀ bs : List Byte, [Syscall.Event.read 0 bs].flatMap (evFlat inp.fs) =
      bs.map (.readEv 0) := by
    intro bs; simp [evFlat]
  have flatEof : [Syscall.Event.read 0 []].flatMap (evFlat inp.fs) = [] := by simp [evFlat]
  -- one LPS step that some CLI step matches
  have oneStep : ∃ es y, CStep ⟨core, env⟩ es y ∧ ∃ c', SStep snapshot.image.segments
      NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩
      (es.flatMap (evFlat inp.fs)) (.next c') ∧ Rel MR c' y (h ++ es) := by
    by_cases cond : wIs0 (core.read .rdx) = true ∨ model.stdin.atEof = true
    · obtain ⟨cs, ss, r⟩ := eofCase cond
      exact ⟨_, _, cs, _, flatEof ▸ ss, .inl r⟩
    · simp only [not_or, Bool.not_eq_true] at cond
      obtain ⟨nz, ne⟩ := cond
      rw [stdinM, StreamFacts.atEof_drop] at ne
      obtain ⟨b, hb⟩ : ∃ b, d.input.byteAt d.cursor = some b := by
        cases hh : d.input.byteAt d.cursor with
        | none => rw [hh] at ne; simp at ne
        | some b => exact ⟨b, rfl⟩
      have rdxPos : 1 ≤ (core.read .rdx).toNat := by
        unfold wIs0 at nz; simp only [beq_eq_false_iff_ne, ne_eq] at nz
        have : (core.read .rdx).toNat ≠ 0 := fun z => nz (BitVec.eq_of_toNat_eq (by simpa using z))
        omega
      obtain ⟨memory', -, cs, ss, r⟩ := afterPos [b] (by simp) (by simp; omega)
        (fun i bound => by
          cases i with
          | zero => simpa using hb
          | succ i => simp at bound)
      exact ⟨_, _, cs, _, (flatPos [b]) ▸ ss, .inl r⟩
  refine ⟨fun evs st s => ?_, ?_, oneStep⟩
  · cases s with
    | syscall _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨cond, out⟩ | ⟨-, -, bs, ⟨pos, le, take1, -⟩, out⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ ?_] at materialized
        · cases materialized
          obtain ⟨cs, -, r⟩ := eofCase cond
          exact ⟨_, rfl, _, _, cs, flatEof.symm, .inl r⟩
        · exact p.lazy
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ ?_] at materialized
        · cases materialized
          have m := StreamFacts.matches_of_take d.input d.cursor _ bs (stdinM ▸ take1)
          obtain ⟨memory', -, cs, -, r⟩ := afterPos bs pos ((clampInt _).1 le) m
          exact ⟨_, rfl, _, _, cs, (flatPos bs).symm, .inl r⟩
        · exact p.lazy
    | syscallMaterializationFault _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, -, bs, -, out⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ ?_] at materialized
        · cases materialized
        · exact p.lazy
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ ?_] at materialized
        · cases materialized
        · exact p.lazy
    | exit _ p' sp halted _ =>
      rw [svc] at p'; cases p'
      have alive : model.halted = none := p.alive
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, -, bs, -, out⟩
      · cases out
        have h' : model.halted = some _ := halted
        rw [alive] at h'; cases h'
      · cases out
        have h' : model.halted = some _ := halted
        rw [alive] at h'; cases h'
    | killed _ p' sp k =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, -, bs, -, out⟩
      · cases out
        rw [killed] at k; cases k
      · cases out
        have k' : model.killedBy = some _ := k
        rw [killed] at k'; cases k'
    | syscallUnmodeled _ p' sp =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, -, bs, -, out⟩ <;> cases out
    | instr _ p' => rw [svc] at p'; cases p'
    | instrFault _ p' => rw [svc] at p'; cases p'
    | instrUnmodeled _ p' => rw [svc] at p'; cases p'
  · obtain ⟨es, y, -, c', ss, -⟩ := oneStep
    exact ⟨_, _, ss⟩

end Read

end Silmaril.Process.LPS.Problems.Sha256Cli
