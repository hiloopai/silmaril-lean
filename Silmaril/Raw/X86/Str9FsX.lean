module

public import Silmaril.X86.Str9FsX.Defs
public import Silmaril.X86.Str9Fs.Thms
public import Silmaril.X86.Sse9.Thms

/-!
# `Str9FsX`: both conservative extensions, the listing laws, the machine

* `step_of_str9fs`: every `Str9Fs` step of `x.m` is a step that keeps the XMM file, so
  `extendsStr9Fs : Str9Fs.isa.Extends isa` (along the lens `x ↦ x.m`) and, by composition,
  `extendsStr9`, `extendsOpen9`, `extendsOpen`.
* `step_of_sse9`: **every `Sse9` step is a step**, so `extendsSse9 : Sse9.isa.Extends isa`
  (the same states). It rests on `sse_not_lower`: bytes `Sse9` reads as an SSE form are
  never a string form (`decodeStr_none_of_pSse`), an atomic form (`atomic_bad_of_pSse`) or an
  FS form (`fs_bad_of_pSse`).
* Listing laws: `step_of_listed` (`isa`: `Str9Fs`'s instructions and `rep stosd`), and
  `step_of_listed_sse` for the SSE forms (as in `Sse9`).
-/

@[expose] public section

namespace Silmaril.X86.Str9FsX

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded PResult ByteParser pHead)
open Silmaril.X86.Ext.ByteParser
open Silmaril.X86.Sse9 (XState XFile XResult)
open Silmaril.Process (Memory)

/-! ## Rejections extend -/

theorem atomic_none {w : List Byte} (h : atomicBad w = true) (more : List Byte) :
    Silmaril.X86.Atomic9.decodeNew (w ++ more) = none := by
  unfold atomicBad at h
  split at h
  · rename_i hb
    unfold Silmaril.X86.Atomic9.decodeNew
    rw [Silmaril.X86.Str9Fs.good_pNewAtomic.bad hb more]
  · cases h

theorem fs_bad {w : List Byte} (h : fsBad w = true) (more : List Byte) :
    Silmaril.X86.Str9Fs.pFs (w ++ more) = .bad := by
  unfold fsBad at h
  split at h
  · rename_i hb; exact Silmaril.X86.Str9Fs.good_pFs.bad hb more
  · cases h

theorem str9fsNew_none {w : List Byte} (ha : atomicBad w = true) (hf : fsBad w = true)
    (more : List Byte) : Silmaril.X86.Str9Fs.decodeNew (w ++ more) = none := by
  unfold Silmaril.X86.Str9Fs.decodeNew
  rw [atomic_none ha more, fs_bad hf more]

theorem sse_none {w : List Byte} (h : sseBad w = true) (more : List Byte) :
    Silmaril.X86.Sse9.decodeSse (w ++ more) = none := by
  unfold sseBad at h
  split at h
  · rename_i hb
    unfold Silmaril.X86.Sse9.decodeSse
    rw [Silmaril.X86.Sse9.good_pSse.bad hb more]
  · cases h

/-! ## No lower decoder reads an SSE form -/

theorem sse_head {W : List Byte} {i : Silmaril.X86.Sse9.Instr} {r : List Byte}
    (h : Silmaril.X86.Sse9.pSse W = .ok i r) :
    ∃ hd t, pHead W = .ok hd t ∧ hd.1 = false ∧ ∃ b, hd.2.2.2 = .two b ∧
      Silmaril.X86.Sse9.pBody hd.2.1 hd.2.2.1 b t = .ok i r := by
  unfold Silmaril.X86.Sse9.pSse at h
  cases hh : pHead W with
  | ok hd t =>
    rw [bind_ok hh] at h
    refine ⟨hd, t, rfl, ?_⟩
    by_cases h1 : hd.1 = true
    · simp [h1] at h
    · simp only [h1] at h
      refine ⟨by simpa using h1, ?_⟩
      revert h
      cases hd.2.2.2 with
      | two b => intro h; exact ⟨b, rfl, h⟩
      | one b => intro h; simp at h
  | eof => simp [ByteParser.bind, hh] at h
  | bad => simp [ByteParser.bind, hh] at h

theorem fs_bad_of_pSse {W : List Byte} {i : Silmaril.X86.Sse9.Instr} {r : List Byte}
    (h : Silmaril.X86.Sse9.pSse W = .ok i r) : Silmaril.X86.Str9Fs.pFs W = .bad := by
  obtain ⟨hd, t, hh, h1, -⟩ := sse_head h
  unfold Silmaril.X86.Str9Fs.pFs
  rw [bind_ok hh]
  simp [h1]

theorem atomic_bad_of_pSse {W : List Byte} {i : Silmaril.X86.Sse9.Instr} {r : List Byte}
    (h : Silmaril.X86.Sse9.pSse W = .ok i r) : Silmaril.X86.Atomic9.pNew W = .bad := by
  obtain ⟨hd, t, hh, h1, b, hb, hbody⟩ := sse_head h
  unfold Silmaril.X86.Atomic9.pNew
  rw [bind_ok hh]
  simp only [h1, Bool.false_eq_true, ite_false]
  cases hp : hd.2.1 with
  | none =>
    simp only [hb, reduceCtorEq, and_false, ite_false]
    rw [hp] at hbody
    unfold Silmaril.X86.Sse9.pBody at hbody
    simp only at hbody
    split_ifs at hbody <;> first
      | (rw [fail_apply] at hbody; cases hbody)
      | (subst_vars; simp [Silmaril.X86.Atomic9.pBody])
  | rep => simp [hb]
  | opsize => rfl
  | nopPad _ => rfl

theorem decodeStr_none_of_pSse {W : List Byte} {i : Silmaril.X86.Sse9.Instr} {r : List Byte}
    (h : Silmaril.X86.Sse9.pSse W = .ok i r) : Silmaril.X86.Str9.decodeStr W = none := by
  cases hs : Silmaril.X86.Str9.decodeStr W with
  | none => rfl
  | some p =>
    obtain ⟨j, n⟩ := p
    obtain ⟨⟨rest, rfl⟩, -⟩ := Silmaril.X86.Str9.decodeStr_some hs
    have hbad : sseBad j.bytes = true := by cases j <;> decide
    have := sse_none hbad rest
    unfold Silmaril.X86.Sse9.decodeSse at this
    rw [h] at this
    cases this

theorem pSse_ok_of_fetchSse {mem : Memory} {a : Nat} {i : Silmaril.X86.Sse9.Instr} {n : Nat}
    (h : Silmaril.X86.Sse9.fetchSse mem a = some (some (i, n))) :
    ∃ j r, Silmaril.X86.Sse9.pSse (fetchWindow mem maxInstrLength a) = .ok j r := by
  unfold Silmaril.X86.Sse9.fetchSse at h
  cases hd : Silmaril.X86.Sse9.decodeSse (fetchWindow mem maxInstrLength a) with
  | none => rw [hd] at h; cases h
  | some p =>
    unfold Silmaril.X86.Sse9.decodeSse at hd
    split at hd
    · rename_i j r hp; exact ⟨j, r, hp⟩
    · cases hd

/-! ## Conservative extensions -/

/-- **Every `Str9Fs` step of `x.m` is a step that keeps the XMM file.** -/
theorem step_of_str9fs {x : XState} {t : MState}
    (h : Silmaril.X86.Str9Fs.step x.m = some t) : step x = some ⟨t, x.xmm⟩ := by
  unfold Silmaril.X86.Str9Fs.step at h
  unfold step
  split at h
  · rename_i h8
    rw [h8]
    simp only
    split at h
    · rename_i i n h9; rw [h9]; simp [keep, h]
    · cases h
    · rename_i h9
      rw [h9]
      simp only
      split at h
      · rename_i i n hs; rw [hs]; simp [keep, h]
      · cases h
      · rename_i hs
        rw [hs]
        simp only
        split at h
        · rename_i i n hn; rw [hn]; simp [keep, h]
        · cases h
  · rename_i h8
    split
    · rename_i h8'; exact absurd h8' h8
    · simp [h]

/-- **Every `Sse9` step is a step.** -/
theorem step_of_sse9 {x y : XState} (h : Silmaril.X86.Sse9.step x = some y) : step x = some y := by
  unfold Silmaril.X86.Sse9.step at h
  unfold step
  split at h
  · rename_i h8
    rw [h8]
    simp only
    split at h
    · rename_i i n h9; rw [h9]; exact h
    · cases h
    · rename_i h9
      rw [h9]
      simp only
      split at h
      · rename_i i n hsse
        obtain ⟨j, r, hp⟩ := pSse_ok_of_fetchSse hsse
        have hfs : Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat = none := by
          unfold Silmaril.X86.Str9.fetchStr
          rw [decodeStr_none_of_pSse hp]
          rfl
        have hfn : Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat = none := by
          unfold Silmaril.X86.Str9Fs.fetchNew Silmaril.X86.Str9Fs.decodeNew
          unfold Silmaril.X86.Atomic9.decodeNew
          rw [atomic_bad_of_pSse hp, fs_bad_of_pSse hp]
          rfl
        rw [hfs, hfn, hsse]
        exact h
      · cases h
  · rename_i h8
    split
    · rename_i h8'; exact absurd h8' h8
    · exact h

/-! ## Listing laws -/

theorem decodeSseL_spec {w : List Byte} {i : Silmaril.X86.Sse9.Instr} {n : Nat}
    (h : decodeSseL w = some (i, n)) :
    Silmaril.X86.Sse9.decodeL w = some (i, n) ∧ Silmaril.X86.Str9Fs.strBad w = true ∧
      atomicBad w = true ∧ fsBad w = true := by
  unfold decodeSseL at h
  split at h
  · rename_i j k hj
    split at h
    · rename_i c
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hj, c⟩
    · cases h
  · cases h

/-- **The fetch form of the SSE law.** -/
theorem step_of_fetch_sse {x : XState} {l : Nat} {w : List Byte} {i : Silmaril.X86.Sse9.Instr}
    {c : State} {xs : XFile} {mem : Memory}
    (fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some w)
    (hdec : decodeSseL w = some (i, l))
    (hx : Silmaril.X86.Sse9.exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) =
      .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ := by
  obtain ⟨hL, hstr, ha, hf⟩ := decodeSseL_spec hdec
  obtain ⟨hnone, hbad, hne, hbad9, hsse, -, h15⟩ := Silmaril.X86.Sse9.decodeL_spec hL
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn9 : Silmaril.X86.Ext9.fetchNew x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Sse9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, str9fsNew_none ha hf more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse x.m.memory x.m.core.rip.toNat = some (some (i, l)) := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Silmaril.X86.Sse9.decodeSse_append hsse more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn9, hfs, hfn, hss, hx, XResult.toOption]

/-- **The SSE listing law.** -/
theorem step_of_listed_sse {x : XState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Sse9.Instr} {c : State} {xs : XFile} {mem : Memory}
    (hl : Loaded x.m.memory base code) (hrip : x.m.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : decodeSseL ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Sse9.exec i x.m.core x.xmm x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) =
      .ok c xs mem) :
    step x = some ⟨⟨c, mem⟩, xs⟩ := by
  have h1 : 0 < l :=
    (Silmaril.X86.Sse9.decodeL_spec (decodeSseL_spec hdec).1).2.2.2.2.2.1
  have hA : x.m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_sse fetched hdec hx

theorem decodeStosd_append {w : List Byte} {n : Nat} (h : decodeStosd w = some n)
    (more : List Byte) : decodeStosd (w ++ more) = some n := by
  match w, h with
  | 0xF3 :: 0xAB :: _, h => exact h

/-- **The fetch form of the `rep stosd` law.** -/
theorem step_of_fetch_stosd {x : XState} {l : Nat} {w : List Byte} {c : State} {mem : Memory}
    (fetched : x.m.memory.fetchBytes x.m.core.rip.toNat l = some w)
    (hdec : decodeStosdL w = some l)
    (hx : execStosd x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step x = some ⟨⟨c, mem⟩, x.xmm⟩ := by
  unfold decodeStosdL at hdec
  split at hdec
  · rename_i hc
    simp only [Option.some.injEq] at hdec
    subst hdec
    obtain ⟨hd, hnone, hbad, hne, hbad9, hstr, ha, hf, hs⟩ := hc
    obtain ⟨more, hmore, hf8⟩ :=
      Silmaril.X86.Open9.fetch8_undecodable_of fetched (by decide) hnone hbad hne
    have hfn9 : Silmaril.X86.Ext9.fetchNew x.m.memory x.m.core.rip.toNat = none := by
      unfold Silmaril.X86.Ext9.fetchNew
      rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
      rfl
    have hfs : Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat = none := by
      unfold Silmaril.X86.Str9.fetchStr
      rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
      rfl
    have hfn : Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat = none := by
      unfold Silmaril.X86.Str9Fs.fetchNew
      rw [hmore, str9fsNew_none ha hf more]
      rfl
    have hss : Silmaril.X86.Sse9.fetchSse x.m.memory x.m.core.rip.toNat = none := by
      unfold Silmaril.X86.Sse9.fetchSse
      rw [hmore, sse_none hs more]
      rfl
    have hst : fetchStosd x.m.memory x.m.core.rip.toNat = some (some 2) := by
      unfold fetchStosd
      rw [hmore, decodeStosd_append hd more]
      simp [Silmaril.Process.Memory.readWith_permitted fetched]
    simp only [step, hf8, hfn9, hfs, hfn, hss, hst, hx, keep, Silmaril.X86.Open.ofResult,
      Option.map_some]
  · cases hdec

/-- **The listing law of the integer instructions.** -/
theorem step_of_listed {x : XState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded x.m.memory base code)
    (hrip : x.m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i x.m.core x.m.memory l = .ok c mem) :
    step x = some ⟨⟨c, mem⟩, x.xmm⟩ := by
  unfold decode at hdec
  split at hdec
  · rename_i j n hj
    simp only [Option.some.injEq, Prod.mk.injEq] at hdec
    obtain ⟨rfl, rfl⟩ := hdec
    exact step_of_str9fs (Silmaril.X86.Str9Fs.step_of_listed hl hrip hfit hj hx)
  · cases hs : decodeStosdL ((code.drop o).take l) with
    | none => rw [hs] at hdec; cases hdec
    | some n =>
      rw [hs] at hdec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      have hA : x.m.core.rip.toNat = base.toNat + o := by
        rw [hrip]; exact hl.toNat_add (by
          have : n = 2 := by unfold decodeStosdL at hs; split at hs <;> simp_all
          omega)
      have h2 : n = 2 := by unfold decodeStosdL at hs; split at hs <;> simp_all
      have fetched : x.m.memory.fetchBytes x.m.core.rip.toNat n = some ((code.drop o).take n) := by
        rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
      exact step_of_fetch_stosd fetched hs hx

/-! ## The machine -/

/-- **`Str9FsX` as a segment-VC instance** over its integer instructions (`Str9Fs`'s and
`rep stosd`); the SSE forms have `step_of_listed_sse`. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa XState where
  Instr := Instr
  instDecEq := inferInstance
  decode := decode
  exec := exec
  core := fun x => x.m.core
  mem := fun x => x.m.memory
  upd := fun x c m => ⟨⟨c, m⟩, x.xmm⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Str9FsX` extends `Str9Fs`** along the lens `x ↦ x.m` (the XMM file is the frame). -/
@[reducible] def extendsStr9Fs : Silmaril.X86.Str9Fs.isa.Extends isa where
  view x := x.m
  put x m := ⟨m, x.xmm⟩
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ _ := trivial
  step h := step_of_str9fs h

/-- `Str9FsX` extends `Str9`. -/
@[reducible] def extendsStr9 : Silmaril.X86.Str9.isa.Extends isa :=
  Silmaril.X86.Str9Fs.extendsStr9.trans extendsStr9Fs

/-- `Str9FsX` extends the open machine over `Ext9`. -/
@[reducible] def extendsOpen9 : Silmaril.X86.Open9.isa.Extends isa :=
  Silmaril.X86.Str9Fs.extendsOpen9.trans extendsStr9Fs

/-- `Str9FsX` extends the open machine over `Ext8`. -/
@[reducible] def extendsOpen : Silmaril.X86.Open.isa.Extends isa :=
  Silmaril.X86.Str9Fs.extendsOpen.trans extendsStr9Fs

/-- **`Str9FsX` extends `Sse9`** on the same states: every `Sse9` step (integer or SSE) is a
step. -/
@[reducible] def extendsSse9 : Silmaril.X86.Sse9.isa.Extends isa :=
  .ofStep (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) step_of_sse9

/-! ## Decoding vectors (kernel-checked) -/

/-- `movaps %xmm0, -0x80(%rbp)` (the varargs prologue) is an SSE form here. -/
theorem decodeSseL_movaps : (decodeSseL [0x0F, 0x29, 0x45, 0x80]).map (·.2) = some 4 := by decide

/-- `movdqu 0x8(%rsi), %xmm0`. -/
theorem decodeSseL_movdqu : (decodeSseL [0xF3, 0x0F, 0x6F, 0x46, 0x08]).map (·.2) = some 5 := by
  decide

/-- `rep stos %eax, %es:(%rdi)`. -/
theorem decode_stosd : decode [0xF3, 0xAB] = some (.stosd, 2) := by decide

/-- `rep stosq` stays `Str9`'s. -/
theorem decode_stosq : (decode [0xF3, 0x48, 0xAB]).map
    (fun p => match p.1 with | .base _ => true | .stosd => false) = some true := by decide

end Silmaril.X86.Str9FsX
