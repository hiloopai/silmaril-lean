module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Syscalls
public import Silmaril.Process.LPS.Problems.Sha256Cli.ReadSim

/-! # Segment `bridge` for GNU `sha256sum`: `read(0)` and `write(1)` against `GStep`

The `sha256` filter's `ReadStep.pend_read` / `WriteStep.pend_write`, with the middle model
`GStep` (the world kernel `Sys.WorldStep`, arbitrary `r11`) in place of the CLI model.

* `pend_read` (VERIFIED): from a pending pair whose request is `read(0, buf, n)` with `n > 0`,
  where LPS descriptor 0 is channel 0 and the middle descriptor 0 is standard input, the LPS
  stdin is the message after position `pos` and the middle stdin the same bytes, the whole
  buffer is writable (`ReadBuf`), passes `access_ok`, and permitted-writable bytes are
  backed: every LPS step is a read the middle model matches with the same bytes (or the
  end of file), LPS can move, and some middle step is matched by one LPS step.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Problems.Sha256Cli.StreamFacts
open Silmaril.Process.LPS.Problems.Sha256Cli (Backed

  readBytesAux_write_isSome lenWord_eq not_refused
  read_dispatch read_channel_iff applyMemoryEffect_read)
open Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

/-! ## Bytes and streams -/

theorem ofU8_toSpec (bs : List Byte) : (toSpec bs).map Apps.Sha256sum.X86Sys.ofU8 = bs := by
  simp only [toSpec, List.map_map]
  conv => rhs; rw [← List.map_id bs]
  apply List.map_congr_left
  intro b _
  simp [Apps.Sha256sum.X86Sys.ofU8]

theorem toBitVec_toSpec (bs : List Byte) : (toSpec bs).map UInt8.toBitVec = bs := by
  simp [toSpec, List.map_map, Function.comp_def]

theorem matches_ofList_iff (l : List Byte) (pos : Nat) (bs : List Byte) :
    (Syscall.InputStream.ofList l).Matches pos bs ↔ bs <+: l.drop pos := by
  constructor
  · intro m
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < bs.length
    · have := m i hi
      simp only [Syscall.InputStream.ofList_byteAt] at this
      rw [List.getElem?_take, ite_eq_left hi, List.getElem?_drop, this, List.getElem?_eq_getElem hi]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_take, ite_eq_right hi]
  · intro pre i hi
    obtain ⟨rest, e⟩ := pre
    have := congrArg (fun l => l[i]?) e
    simp only [List.getElem?_append_left hi, List.getElem?_drop] at this
    simp only [Syscall.InputStream.ofList_byteAt]
    rw [← this, List.getElem?_eq_getElem hi]

theorem stdin_drop_drop (message : List Byte) (pos n : Nat) :
    (toSpec (message.drop pos)).drop n = toSpec (message.drop (pos + n)) := by
  simp [toSpec, List.drop_drop]

/-! ## The middle model at a `read` -/

theorem decode_read (t : Silmaril.X86.State) (m : Silmaril.Process.Memory)
    (number : (t.read .rax).toNat = 0) :
    Apps.Sha256sum.X86Sys.decode t m = some (.call (.read
      (Apps.Sha256sum.X86Sys.fd32 (t.read .rdi)) (t.read .rdx).toNat)) := by
  simp [Apps.Sha256sum.X86Sys.decode, number]

/-- The middle state after `read(fd, buf, n)` returned `data b` into memory `memory'`. -/
def readNext (g : GS) (r11 : Word) (b : Apps.Sha256sum.Bytes) (memory' : Silmaril.Process.Memory)
    (k' : Apps.Sha256sum.Sys.KState) : GS :=
  ⟨{ g.x with
      core := Apps.Sha256sum.X86Sys.returnCore (fun _ => r11)
        ({ g.x.core with rip := g.x.core.rip + 2 }) (BitVec.ofNat 64 b.length)
      memory := memory' },
    k', none⟩

theorem resume_read_eq (g : GS) (r11 : Word) (fd n : Nat) (b : Apps.Sha256sum.Bytes)
    {memory' : Silmaril.Process.Memory}
    (written : g.x.memory.writeBytes (g.x.core.read .rsi).toNat
      (b.map Apps.Sha256sum.X86Sys.ofU8) = some memory') (k' : Apps.Sha256sum.Sys.KState) :
    (⟨Apps.Sha256sum.X86Sys.resume (fun _ => r11) g.x { g.x.core with rip := g.x.core.rip + 2 }
      (.read fd n) (.data b), k', none⟩ : GS) = readNext g r11 b memory' k' := by
  have : ({ g.x.core with rip := g.x.core.rip + 2 } : Silmaril.X86.State).read .rsi =
      g.x.core.read .rsi := rfl
  simp only [Apps.Sha256sum.X86Sys.resume, this, written, readNext, Apps.Sha256sum.X86Sys.raxOf]

/-! ## `read(0)` -/

section Read

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {g : GS} {h : List Ev} {w : Apps.Sha256sum.World}
  {message : List Byte}

/-- **`read` from stdin.** -/
theorem pend_read (p : PendRel MR c g h) (number : (g.x.core.read .rax).toNat = 0)
    (fd0 : Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi) = 0)
    (lookup : fdLookup c.model.fds 0 = some (.channel 0))
    (open0 : g.k.fds 0 = some .stdin) (pos : Nat)
    (kstdin : g.k.stdin = .bytes (toSpec (message.drop pos)))
    (stdin : c.model.stdin = InputStream.drop (InputStream.ofList message) pos)
    (count : 0 < (g.x.core.read .rdx).toNat)
    (buf : g.x.memory.Permitted .write (g.x.core.read .rsi).toNat (g.x.core.read .rdx).toNat)
    (ok : accessOkb (g.x.core.read .rsi) (uns (g.x.core.read .rdx)) = true)
    (backed : Backed g.x.memory)
    (keep : ∀ (r11 : Word) (bs : List Byte) (memory' : Silmaril.Process.Memory),
      g.x.memory.writeBytes (g.x.core.read .rsi).toNat bs = some memory' →
      MR (c.model.withStdin (InputStream.drop (InputStream.ofList message) (pos + bs.length)))
        (readNext g r11 (toSpec bs) memory'
          { g.k with stdin := .bytes (toSpec (message.drop (pos + bs.length))) })
        (h ++ [.sys (.read 0 (g.x.core.read .rdx).toNat) (.data (toSpec bs))])) :
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
  set core := g.x.core with hcore
  set n := (core.read .rdx).toNat with hn
  have svc : (machine oracle).svcPending ms = some (core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (core.read .rax) with hi
  have sysno : i.sysno = core.read .rax := rfl
  have arg : ∀ r k, k < 6 → [Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9][k]? = some r →
      i.arg k = core.read r := by
    intro r k _ hk
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD k 0) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hk]
    simp [Sha256Cli.CoreLe.read_eq p.core, hcore]
  have a0 : i.arg 0 = core.read .rdi := arg _ 0 (by omega) rfl
  have a1 : i.arg 1 = core.read .rsi := arg _ 1 (by omega) rfl
  have a2 : i.arg 2 = core.read .rdx := arg _ 2 (by omega) rfl
  have wmem : i.wmem = viewByte g.x.memory .write := by
    show viewByte ms.native.m.memory .write = _
    rw [show ms.native.m.memory = g.x.memory from p.memory]
  have rsi : core.read .rsi = BitVec.ofNat 64 (core.read .rsi).toNat := by simp
  have room : ∀ k, k ≤ n →
      (readBytesAux (viewByte g.x.memory .write) (core.read .rsi) k).isSome = true := by
    intro k hk
    rw [rsi]
    exact readBytesAux_write_isSome backed k _ _ buf hk
  set clamp := min n 0x7ffff000 with hclamp
  have clampInt : ∀ k : Nat, ((k : Int) ≤ rwCountClamp (core.read .rdx)) ↔ k ≤ clamp := by
    intro k; unfold rwCountClamp uns MAX_RW_COUNT; omega
  have lenWord_toNat : ∀ l : List Byte, l.length ≤ n → (lenWord l).toNat = l.length := by
    intro l hl
    rw [lenWord_eq, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt hl (core.read .rdx).isLt)
  have nz : wIs0 (core.read .rdx) = false := by
    unfold wIs0; simp only [beq_eq_false_iff_ne, ne_eq]
    intro h0; rw [h0] at hn; simp at hn; omega
  have lowFd : ((core.read .rdi).setWidth 32).toNat = 0 := fd0
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
      Sha256Cli.fd32_of_low_zero _ lowFd]
    apply read_channel_iff 0 (core.read .rsi) (core.read .rdx) _ model o lookup ok
    · intro _
      simp only [NativeX86.referenceInputFor_wmem, readBytesMap, wmem]
      exact room 1 (by omega)
    · intro _
      simp only [NativeX86.referenceInputFor_wmem, readBytesMap, wmem]
      have le := takeFrom_length_le model.stdin
      unfold InputStream.takeZ
      split
      · rename_i posC
        rw [lenWord_toNat]
        · apply room
          have := le (rwCountClamp (core.read .rdx)).toNat 0
          simp only [InputStream.take]
          unfold rwCountClamp uns MAX_RW_COUNT at this posC ⊢
          omega
        · have := le (rwCountClamp (core.read .rdx)).toNat 0
          simp only [InputStream.take]
          unfold rwCountClamp uns MAX_RW_COUNT at this posC ⊢
          omega
      · exact room 0 (by omega)
  have notRefused : ∀ eff, ¬ NativeX86.defaultRefusalFilter refusals i model eff :=
    fun eff => not_refused refusals i model eff (.inl (by rw [sysno]; exact number))
  have killed : model.killedBy = none := by
    have alive : model.halted = none := p.alive
    simp only [Model.killedBy]
    split
    · exact alive
    · rfl
  have pend158 : ∀ eff : SyscallEffect, ¬ (ms.native.pending = some 158 ∧
      ms.native.m.core.read .rdi = 0x1002 ∧ eff.ret = 0) := by
    rintro eff ⟨hp, -, -⟩
    have hp' : some (core.read .rax) = some 158 := p.pending.symm.trans hp
    have := congrArg (fun o => o.map BitVec.toNat) hp'
    simp [number] at this
  set r11 := (rflagsImage ms.native.m.core.flags).getD 0 with hr11
  have decoded := decode_read { core with rip := core.rip + 2 } g.x.memory number
  rw [show ({ core with rip := core.rip + 2 } : Silmaril.X86.State).read .rdi = core.read .rdi
    from rfl, fd0] at decoded
  have readBuf : ReadBuf { core with rip := core.rip + 2 } g.x.memory (.read 0 n) := buf
  -- the middle step for a chunk `b`
  have gstep : ∀ (b : Apps.Sha256sum.Bytes), Apps.Sha256sum.Sys.Chunk (toSpec (message.drop pos)) n b →
      GStep w g [.sys (.read 0 n) (.data b)]
        ⟨Apps.Sha256sum.X86Sys.resume (fun _ => r11) g.x { core with rip := core.rip + 2 }
          (.read 0 n) (.data b),
          { g.k with stdin := .bytes ((toSpec (message.drop pos)).drop b.length) }, none⟩ :=
    fun b chunk => GStep.call r11 p.running p.faulted (step8_trap p.trap) decoded readBuf
      (.readStdin open0 kstdin chunk)
  -- the related pair after a read of `bs`
  have related : ∀ (bs : List Byte) (memory' : Silmaril.Process.Memory) (model' : Model),
      bs.length ≤ n → g.x.memory.writeBytes (core.read .rsi).toNat bs = some memory' →
      model'.halted = none → model'.vmLazy = [] →
      MR model' (readNext g r11 (toSpec bs) memory'
          { g.k with stdin := .bytes (toSpec (message.drop (pos + bs.length))) })
        (h ++ [.sys (.read 0 n) (.data (toSpec bs))]) →
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect (lenWord bs) (if bs = [] then [] else [(core.read .rsi, bs)]) [])), model'⟩
        (readNext g r11 (toSpec bs) memory'
          { g.k with stdin := .bytes (toSpec (message.drop (pos + bs.length))) })
        (h ++ [.sys (.read 0 n) (.data (toSpec bs))]) := by
    intro bs memory' model' le written alive lazy mr
    obtain ⟨eq, fle⟩ := p.core
    refine { pending := rfl, core := ?_, memory := ?_, running := rfl, faulted := p.faulted,
             alive := alive, lazy := lazy, model := mr }
    · show CoreLe _ (x86AdvancePastSvc (x86ApplyEffectNative ms.native _)).m.core
      simp only [x86AdvancePastSvc, x86ApplyEffectNative, ite_eq_right (pend158 _)]
      rw [eq]
      refine ⟨?_, fle⟩
      simp only [mkEffect, lenWord_eq, readNext, Apps.Sha256sum.X86Sys.returnCore, toSpec,
        List.length_map]
      rfl
    · show applyMemoryEffect ms.native.m.memory _ = memory'
      rw [p.memory]
      split
      · rename_i e
        subst e
        unfold Silmaril.Process.Memory.writeBytes at written
        split at written
        · cases written; rfl
        · cases written
      · exact applyMemoryEffect_read _ written
  have flat : ∀ bs : List Byte,
      [Ev.sys (.read 0 n) (.data (toSpec bs))].flatMap (evFlat inp.fs) = bs.map (.readEv 0) := by
    intro bs; simp [evFlat, readBytes, outBytes, exitPart, toBitVec_toSpec]
  -- a positive read of `bs`
  have afterPos : ∀ bs : List Byte, 1 ≤ bs.length → bs.length ≤ clamp →
      bs <+: message.drop pos →
      ∃ memory', g.x.memory.writeBytes (core.read .rsi).toNat bs = some memory' ∧
      GStep w g [.sys (.read 0 n) (.data (toSpec bs))]
        (readNext g r11 (toSpec bs) memory'
          { g.k with stdin := .bytes (toSpec (message.drop (pos + bs.length))) }) ∧
      SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ (bs.map (.readEv 0))
        (.next ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])),
          model.withStdin (model.stdin.take bs.length).2⟩) ∧
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect (lenWord bs) [(core.read .rsi, bs)] [])),
          model.withStdin (model.stdin.take bs.length).2⟩
        (readNext g r11 (toSpec bs) memory'
          { g.k with stdin := .bytes (toSpec (message.drop (pos + bs.length))) })
        (h ++ [.sys (.read 0 n) (.data (toSpec bs))]) := by
    intro bs posLen le pre
    have lenN : bs.length ≤ n := by omega
    have perm : g.x.memory.Permitted .write (core.read .rsi).toNat bs.length := by
      have a := buf
      simp only [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at a ⊢
      exact ⟨a.1, by omega, fun o ho => a.2.2 o (by omega)⟩
    obtain ⟨memory', copied⟩ : ∃ memory',
        g.x.memory.writeBytes (core.read .rsi).toNat bs = some memory' :=
      ⟨_, by
        unfold Silmaril.Process.Memory.writeBytes
        rw [ite_eq_left (show g.x.memory.checkSpan .write _ bs.length = true from perm)]⟩
    have m : (Syscall.InputStream.ofList message).Matches pos bs :=
      (matches_ofList_iff message pos bs).mpr pre
    have take1 : (model.stdin.take bs.length).1 = bs := by
      rw [stdin]; exact take_of_matches _ _ _ m
    have take2 : (model.stdin.take bs.length).2 =
        InputStream.drop (InputStream.ofList message) (pos + bs.length) := by
      rw [stdin]; exact take_snd _ _ bs _ (stdin ▸ take1)
    have copied' : g.x.memory.writeBytes (g.x.core.read .rsi).toNat
        ((toSpec bs).map Apps.Sha256sum.X86Sys.ofU8) = some memory' := by
      rw [ofU8_toSpec]; exact copied
    have chunk : Apps.Sha256sum.Sys.Chunk (toSpec (message.drop pos)) n (toSpec bs) :=
      ⟨pre.map _, by simp only [toSpec, List.length_map]; exact lenN,
        fun e => absurd (by simpa [toSpec] using e : bs = []) fun e' => by simp [e'] at posLen⟩
    have gs := gstep (toSpec bs) chunk
    rw [resume_read_eq g r11 0 n (toSpec bs) copied', show (toSpec bs).length = bs.length by
      simp [toSpec], stdin_drop_drop] at gs
    refine ⟨memory', copied, gs, ?_, ?_⟩
    · refine .syscall p.alive svc ((spec_iff _).2 (.inr ⟨nz, ?_, bs, ⟨posLen, (clampInt _).2 le,
        take1, ?_⟩, rfl⟩)) (notRefused _) p.alive
        (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy)
      · rw [stdin, atEof_drop]
        have := m 0 (by omega)
        rw [Nat.add_zero] at this
        show ((Syscall.InputStream.ofList message).byteAt pos).isNone = false
        rw [this]; rfl
      · simp only [readBytesMap, wmem]
        rw [lenWord_toNat _ lenN]
        exact room _ lenN
    · have r := related bs memory' (model.withStdin (model.stdin.take bs.length).2) lenN copied
        p.alive p.lazy (by rw [take2]; exact keep r11 bs memory' copied)
      have ne : bs ≠ [] := fun e => by simp [e] at posLen
      simpa [ne] using r
  -- end of file
  have eofCase : message.drop pos = [] →
      GStep w g [.sys (.read 0 n) (.data (toSpec []))]
        (readNext g r11 (toSpec []) g.x.memory
          { g.k with stdin := .bytes (toSpec (message.drop (pos + ([] : List Byte).length))) }) ∧
      SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ []
        (.next ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect 0 [] [])), model⟩) ∧
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms
          (mkEffect 0 [] [])), model⟩
        (readNext g r11 (toSpec []) g.x.memory
          { g.k with stdin := .bytes (toSpec (message.drop (pos + ([] : List Byte).length))) })
        (h ++ [.sys (.read 0 n) (.data (toSpec []))]) := by
    intro eof
    have span : g.x.memory.writeBytes (core.read .rsi).toNat [] = some g.x.memory := by
      have a := buf
      simp only [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at a
      unfold Silmaril.Process.Memory.writeBytes
      have span0 : g.x.memory.checkSpan .write (core.read .rsi).toNat ([] : List Byte).length =
          true := by
        rw [List.length_nil, Silmaril.Process.Memory.checkSpan_iff]
        exact ⟨a.1, by have := a.2.1; omega, fun o ho => absurd ho (Nat.not_lt_zero _)⟩
      rw [ite_eq_left span0]
      rfl
    have chunk : Apps.Sha256sum.Sys.Chunk (toSpec (message.drop pos)) n (toSpec []) :=
      ⟨by simp [toSpec], by simp [toSpec], fun _ => .inl (by simp [toSpec, eof])⟩
    have gs := gstep (toSpec []) chunk
    rw [resume_read_eq g r11 0 n (toSpec []) (by simpa [toSpec] using span)] at gs
    have modelEof : model.stdin.atEof = true := by
      rw [stdin, atEof_drop]
      show ((Syscall.InputStream.ofList message).byteAt pos).isNone = true
      simp [List.drop_eq_nil_iff.mp eof]
    have mr := keep r11 [] g.x.memory span
    simp only [List.length_nil, Nat.add_zero] at mr ⊢
    refine ⟨by simpa [toSpec] using gs, .syscall p.alive svc ((spec_iff _).2 (.inl ⟨.inr modelEof, rfl⟩))
        (notRefused _) p.alive (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy), ?_⟩
    have dropPos : InputStream.drop (InputStream.ofList message) pos = model.stdin := stdin.symm
    rw [dropPos] at mr
    have r := related [] g.x.memory model (by simp) span p.alive p.lazy
      mr
    simpa [lenWord_eq] using r
  have flatEof : [Ev.sys (.read 0 n) (.data (toSpec []))].flatMap (evFlat inp.fs) = [] := by
    simpa using flat []
  -- one LPS step that some middle step matches
  have oneStep : ∃ es y, GStep w g es y ∧ ∃ c', SStep snapshot.image.segments
      NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩
      (es.flatMap (evFlat inp.fs)) (.next c') ∧ Rel MR c' y (h ++ es) := by
    cases hd : message.drop pos with
    | nil =>
      obtain ⟨gs, ss, r⟩ := eofCase hd
      exact ⟨_, _, gs, _, by rw [flatEof]; exact ss, .inl r⟩
    | cons b rest =>
      obtain ⟨memory', -, gs, ss, r⟩ := afterPos [b] (by simp)
        (by show 1 ≤ min n 2147479552; omega) (by rw [hd]; simp)
      exact ⟨_, _, gs, _, by rw [flat]; exact ss, .inl r⟩
  refine ⟨fun evs st s => ?_, ?_, oneStep⟩
  · cases s with
    | syscall _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨cond, out⟩ | ⟨-, -, bs, ⟨posLen, le, take1, -⟩, out⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy] at materialized
        cases materialized
        have eof : message.drop pos = [] := by
          rcases cond with z | e
          · rw [nz] at z; cases z
          · rw [stdin, atEof_drop] at e
            have e' : ((Syscall.InputStream.ofList message).byteAt pos).isNone = true := e
            simpa [List.drop_eq_nil_iff] using e'
        obtain ⟨gs, -, r⟩ := eofCase eof
        exact ⟨_, rfl, _, _, gs, flatEof.symm, .inl r⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ (show (model.withStdin
          (model.stdin.take bs.length).2).vmLazy = [] from p.lazy)] at materialized
        cases materialized
        have m := matches_of_take (InputStream.ofList message) pos _ bs (stdin ▸ take1)
        have pre : bs <+: message.drop pos := (matches_ofList_iff message pos bs).mp m
        obtain ⟨memory', -, gs, -, r⟩ := afterPos bs posLen ((clampInt _).1 le) pre
        exact ⟨_, rfl, _, _, gs, (flat bs).symm, .inl r⟩
    | syscallMaterializationFault _ p' sp _ _ materialized =>
      rw [svc] at p'; cases p'
      rcases (spec_iff _).1 sp with ⟨-, out⟩ | ⟨-, -, bs, -, out⟩
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy] at materialized
        cases materialized
      · cases out
        rw [X86Launch.materializeModelAccesses_no_lazy _ _ (show (model.withStdin
          (model.stdin.take bs.length).2).vmLazy = [] from p.lazy)] at materialized
        cases materialized
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

/-! ## `write(1)` -/

theorem decode_write (t : Silmaril.X86.State) (m : Silmaril.Process.Memory)
    (number : (t.read .rax).toNat = 1) {bytes : List Byte}
    (loaded : m.readBytes (t.read .rsi).toNat (t.read .rdx).toNat = some bytes) :
    Apps.Sha256sum.X86Sys.decode t m = some (.call (.write
      (Apps.Sha256sum.X86Sys.fd32 (t.read .rdi)) (bytes.map Apps.Sha256sum.X86Sys.toU8))) := by
  simp [Apps.Sha256sum.X86Sys.decode, number, loaded]

theorem toBitVec_toU8 (bytes : List Byte) :
    (bytes.map Apps.Sha256sum.X86Sys.toU8).map UInt8.toBitVec = bytes := by
  simp only [List.map_map]
  conv => rhs; rw [← List.map_id bytes]
  apply List.map_congr_left
  intro b _
  simp [Apps.Sha256sum.X86Sys.toU8]

/-- The middle state after `write` returned `n`. -/
def writeNext (g : GS) (r11 : Word) (n : Nat) : GS :=
  ⟨{ g.x with
      core := Apps.Sha256sum.X86Sys.returnCore (fun _ => r11)
        ({ g.x.core with rip := g.x.core.rip + 2 }) (BitVec.ofNat 64 n) }, g.k, none⟩

section Write

variable {oracle : Nat → X86FlagChoices.Choice} {refusals : SpuriousCfg} {inp : ProcInput}
  {MR : DescRel} {c : Config (machine oracle)} {g : GS} {h : List Ev} {w : Apps.Sha256sum.World}

/-- **`write` to stdout.** -/
theorem pend_write (p : PendRel MR c g h) (number : (g.x.core.read .rax).toNat = 1)
    (fd1 : Apps.Sha256sum.X86Sys.fd32 (g.x.core.read .rdi) = 1)
    (lookup : fdLookup c.model.fds 1 = some (.channel 1))
    (open1 : g.k.fds 1 = some .stdout) (notFull : w.stdoutFull = false) {bytes : List Byte}
    (loaded : g.x.memory.readBytes (g.x.core.read .rsi).toNat (g.x.core.read .rdx).toNat =
      some bytes)
    (count_pos : 0 < (g.x.core.read .rdx).toNat)
    (modeled : modeledRwRangeWith accessOkb (g.x.core.read .rsi) (g.x.core.read .rdx) = true)
    (keep : ∀ (r11 : Word) (n : Nat), MR c.model (writeNext g r11 n)
      (h ++ [.sys (.write 1 (bytes.map Apps.Sha256sum.X86Sys.toU8)) (.ok n)])) :
    (∀ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st →
      ∃ c', st = .next c' ∧ ∃ es y, GStep w g es y ∧ evs = es.flatMap (evFlat inp.fs) ∧
        Rel MR c' y (h ++ es)) ∧
    (∃ evs st, SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c evs st) ∧
    (∃ es y, GStep w g es y ∧ ∃ c', SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) c (es.flatMap (evFlat inp.fs)) (.next c') ∧
        Rel MR c' y (h ++ es)) := by
  have bytes_len : bytes.length = (g.x.core.read .rdx).toNat :=
    (Silmaril.X86.Memory.readWith_eq_some_iff.mp loaded).1
  obtain ⟨ms, model⟩ := c
  set core := g.x.core with hcore
  have svc : (machine oracle).svcPending ms = some (core.read .rax) := p.pending
  set i := sysInput (machine oracle) snapshot.image.segments ms (core.read .rax) with hi
  have sysno : i.sysno = core.read .rax := rfl
  have arg : ∀ r k, k < 6 → [Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9][k]? = some r →
      i.arg k = core.read r := by
    intro r k _ hk
    show (([Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map ms.native.m.core.read).getD k 0) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hk]
    simp [Sha256Cli.CoreLe.read_eq p.core, hcore]
  have a0 : i.arg 0 = core.read .rdi := arg _ 0 (by omega) rfl
  have a1 : i.arg 1 = core.read .rsi := arg _ 1 (by omega) rfl
  have a2 : i.arg 2 = core.read .rdx := arg _ 2 (by omega) rfl
  have mem : i.mem = viewByte g.x.memory .read := by
    show viewByte ms.native.m.memory .read = _
    rw [show ms.native.m.memory = g.x.memory from p.memory]
  set clamp := min (core.read .rdx).toNat 0x7ffff000 with hclamp
  have source : writeSource i.mem (core.read .rsi) (core.read .rdx) = bytes.take clamp := by
    unfold writeSource readableBytes
    rw [mem, Sha256Cli.clamp_toNat, ← hclamp]
    have rsi : core.read .rsi = BitVec.ofNat 64 (core.read .rsi).toNat := by simp
    conv => lhs; rw [rsi]
    exact Sha256Cli.readableBytesAux_of_readBytes clamp _ _ bytes loaded (by omega)
  have nonempty : bytes.take clamp ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp only [List.length_take, List.length_nil] at this
    omega
  have nonzero : wIs0 (core.read .rdx) = false := by
    unfold wIs0
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h0; rw [h0] at count_pos; simp at count_pos
  have lowFd : ((core.read .rdi).setWidth 32).toNat = 1 := fd1
  have spec_iff : ∀ o, NativeX86.extendedSyscallSpec i model o ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (core.read .rdx) ∧
        ds = (bytes.take clamp).take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins ([(core.read .rsi, ds.length)] ++ []))
          model (ds.map (.writeEv 1)) := by
    intro o
    rw [Sha256Cli.write_dispatch i model o (by rw [sysno]; exact number), a0, a1, a2,
      Sha256Cli.fd32_of_low _ lowFd]
    rw [Sha256Cli.write_channel_iff 1 (core.read .rsi) (core.read .rdx) _ model o lookup modeled
      nonzero (by simpa [NativeX86.referenceInputFor, source] using nonempty)]
    simp only [NativeX86.referenceInputFor_mem]
    rw [source]
  have notRefused : ∀ eff, ¬ NativeX86.defaultRefusalFilter refusals i model eff :=
    fun eff => not_refused refusals i model eff (.inr (.inl (by rw [sysno]; exact number)))
  have clampInt : ∀ n : Nat, ((n : Int) ≤ rwCountClamp (core.read .rdx)) ↔ n ≤ clamp := by
    intro n; unfold rwCountClamp uns MAX_RW_COUNT; omega
  set r11 := (rflagsImage ms.native.m.core.flags).getD 0 with hr11
  have decoded := decode_write { core with rip := core.rip + 2 } g.x.memory number loaded
  rw [show ({ core with rip := core.rip + 2 } : Silmaril.X86.State).read .rdi = core.read .rdi
    from rfl, fd1] at decoded
  -- the matched pair after writing `ds`
  let ret (ds : List Byte) : SyscallEffect :=
    (mkEffect (lenWord ds) [] []).withCopyins ([(core.read .rsi, ds.length)] ++ [])
  have after : ∀ ds : List Byte, 1 ≤ ds.length → ds.length ≤ clamp → ds = bytes.take ds.length →
      GStep w g [.sys (.write 1 (bytes.map Apps.Sha256sum.X86Sys.toU8)) (.ok ds.length)]
        (writeNext g r11 ds.length) ∧
      SStep snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) ⟨ms, model⟩ (ds.map (.writeEv 1))
        (.next ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms (ret ds)), model⟩) ∧
      RunRel MR ⟨(machine oracle).advancePastSvc ((machine oracle).applyEffect ms (ret ds)), model⟩
        (writeNext g r11 ds.length)
        (h ++ [.sys (.write 1 (bytes.map Apps.Sha256sum.X86Sys.toU8)) (.ok ds.length)]) := by
    intro ds dpos dbound dtake
    refine ⟨?_, ?_, ?_⟩
    · have accepts : Apps.Sha256sum.Sys.Accepts (bytes.map Apps.Sha256sum.X86Sys.toU8)
          ds.length := ⟨by simp; omega, fun _ => by omega⟩
      exact GStep.call r11 p.running p.faulted (step8_trap p.trap) decoded trivial
        (.writeOut open1 notFull accepts)
    · refine .syscall p.alive svc ((spec_iff _).2 ⟨ds, ⟨dpos, (clampInt _).2 dbound, ?_⟩, rfl⟩)
        (notRefused _) p.alive (X86Launch.materializeModelAccesses_no_lazy _ _ p.lazy)
      rw [List.take_take, Nat.min_eq_left dbound]; exact dtake
    · have pend158 : ¬ (ms.native.pending = some 158 ∧ ms.native.m.core.read .rdi = 0x1002 ∧
          (ret ds).ret = 0) := by
        rintro ⟨hp, -, -⟩
        have hp' : some (core.read .rax) = some 158 := p.pending.symm.trans hp
        have := congrArg (fun o => o.map BitVec.toNat) hp'
        simp [number] at this
      obtain ⟨eq, fle⟩ := p.core
      refine { pending := rfl, core := ?_, memory := ?_, running := rfl, faulted := p.faulted,
               alive := p.alive, lazy := p.lazy, model := keep r11 ds.length }
      · show CoreLe _ (x86AdvancePastSvc (x86ApplyEffectNative ms.native (ret ds))).m.core
        simp only [x86AdvancePastSvc, x86ApplyEffectNative, ite_eq_right pend158]
        rw [eq]
        refine ⟨?_, fle⟩
        simp only [ret, mkEffect, SyscallEffect.withCopyins, lenWord_eq, writeNext,
          Apps.Sha256sum.X86Sys.returnCore]
        rfl
      · exact p.memory
  have killed : model.killedBy = none := by
    have alive : model.halted = none := p.alive
    simp only [Model.killedBy]
    split
    · exact alive
    · rfl
  have flat : ∀ ds : List Byte, ds = bytes.take ds.length →
      [Ev.sys (.write 1 (bytes.map Apps.Sha256sum.X86Sys.toU8)) (.ok ds.length)].flatMap
        (evFlat inp.fs) = ds.map (.writeEv 1) := by
    intro ds dtake
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, evFlat, readBytes, outBytes,
      exitPart, List.map_nil, List.nil_append]
    rw [← List.map_take, toBitVec_toU8, ← dtake]
  have choice : ∀ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (core.read .rdx) ∧
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
      obtain ⟨gs, -, r⟩ := after ds props.1 le tk
      exact ⟨_, rfl, _, _, gs, (flat ds tk).symm, .inl r⟩
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
  · obtain ⟨gs, s, r⟩ := after (bytes.take 1) first.1 first.2.1 first.2.2
    exact ⟨_, _, gs, _, by rw [flat _ first.2.2]; exact s, .inl r⟩

end Write

end Silmaril.Process.LPS.Problems.GnuSha256sum
