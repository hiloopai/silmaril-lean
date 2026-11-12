module

public import Silmaril.X86.Str9G.Defs
public import Silmaril.X86.Str9FsX.Thms

/-!
# `Str9G`: the extension of `Str9FsX`, the listing laws, the machine

* `step_of_str9fsx`: every `Str9FsX` step of `g.x` is a step that keeps the ghost state
  (`tsc`, `cetOff`), so `extendsStr9FsX : Str9FsX.isa.Extends isa` (lens `g ↦ g.x`) and, by
  composition, `extendsSse9`, `extendsStr9Fs`, `extendsStr9`, `extendsOpen9`, `extendsOpen`.
* `good_pNew`, `decodeNew_append`: the layer's parser has the prefix laws.
* `step_of_fetch_g`, `step_of_listed_g`: the law of the layer's forms (`rdtsc`, the CET forms,
  the SSE2 forms); `step_of_listed` (integer, `isa`) and `step_of_listed_sse` (`Sse9`'s forms)
  carry over from `Str9FsX`.
-/

@[expose] public section

namespace Silmaril.X86.Str9G

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded PResult ByteParser pHead)
open Silmaril.X86.Ext.ByteParser
open Silmaril.X86.Sse9 (XState XFile XResult)
open Silmaril.Process (Memory)

/-! ## Decoder laws -/

theorem good_regP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (regP rex mp) := by
  unfold regP; exact good_ite (good_pure _) good_fail

theorem good_memP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (memP rex mp) := by
  unfold memP; split
  · exact good_pure _
  · exact good_fail

theorem good_packed (f : Silmaril.X86.XReg → Silmaril.X86.Sse9.XRM → Sse2)
    (rex : Option Silmaril.X86.Ext.Rex) : Good (packed f rex) := by
  unfold packed; exact good_map _ Silmaril.X86.Ext8.good_pM

theorem good_pF2Rest : Good pF2Rest := by
  unfold pF2Rest
  exact good_bind Silmaril.X86.Ext.good_pHead fun _ =>
    good_ite (good_map _ Silmaril.X86.Ext8.good_pM) good_fail

theorem good_p67Rest : Good p67Rest := by
  unfold p67Rest
  exact good_bind Silmaril.X86.Ext.good_pHead fun _ =>
    good_ite (good_bind Silmaril.X86.Ext8.good_pM fun _ => good_map _ (good_memP _ _)) good_fail

/-- Discharge `Good` goals of the layer's parsers. -/
macro "good_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact good_pure _ | exact good_regP _ _ | exact good_memP _ _ | exact good_packed _ _
  | exact good_pF2Rest | exact good_p67Rest
  | apply good_ite | apply good_map | apply good_bind | intro _ | split))

theorem good_pBody (pfx : Silmaril.X86.Ext.Pfx) (rex : Option Silmaril.X86.Ext.Rex)
    (opc : Silmaril.X86.Ext.Opc) : Good (pBody pfx rex opc) := by
  cases opc <;> simp only [pBody] <;> good_tac

/-- **The layer's parser has the prefix laws.** -/
theorem good_pNew : Good pNew :=
  good_bind Silmaril.X86.Ext.good_pHead fun _ => good_ite good_fail (good_pBody _ _ _)

/-- A decoded form keeps its reading whatever bytes follow. -/
theorem decodeNew_append {w : List Byte} {i : New} {n : Nat} (h : decodeNew w = some (i, n))
    (more : List Byte) : decodeNew (w ++ more) = some (i, n) := by
  unfold decodeNew at h ⊢
  split at h
  · rename_i j rest hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, ext⟩ := good_pNew.ok hp
    rw [ext more]
    simp only [List.length_append, Option.some.injEq, Prod.mk.injEq, true_and]
    omega
  · cases h

theorem stosd_none {w : List Byte} (h : stosdBad w = true) (more : List Byte) :
    Silmaril.X86.Str9FsX.decodeStosd (w ++ more) = none := by
  unfold stosdBad at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨hl, hn⟩ := h
  match w, hl, hn with
  | a :: b :: rest, _, hn =>
    revert hn
    unfold Silmaril.X86.Str9FsX.decodeStosd
    split <;> simp_all

theorem decodeL_spec {w : List Byte} {i : New} {n : Nat} (h : decodeL w = some (i, n)) :
    Silmaril.X86.Ext.decode w = none ∧ Silmaril.X86.Open9.newBad w = true ∧
      Silmaril.X86.Open9.rawNotEof w = true ∧ Silmaril.X86.Str9.ext9Bad w = true ∧
      Silmaril.X86.Str9Fs.strBad w = true ∧ Silmaril.X86.Str9FsX.atomicBad w = true ∧
      Silmaril.X86.Str9FsX.fsBad w = true ∧ Silmaril.X86.Str9FsX.sseBad w = true ∧
      stosdBad w = true ∧ decodeNew w = some (i, n) ∧ n ≤ maxInstrLength := by
  unfold decodeL at h
  split at h
  · rename_i j k hj
    split at h
    · rename_i c
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2.1,
        c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2.1, hj, c.2.2.2.2.2.2.2.2.2.2⟩
    · cases h
  · cases h

/-! ## Extension of `Str9FsX` -/

/-- **Every `Str9FsX` step of `g.x` is a step that keeps the ghost state.** -/
theorem step_of_str9fsx {g : GState} {y : XState}
    (h : Silmaril.X86.Str9FsX.step g.x = some y) : step g = some { g with x := y } := by
  have hx := h
  unfold Silmaril.X86.Str9FsX.step at hx
  unfold step
  simp only
  split
  · rename_i h8
    rw [h8] at hx
    split
    · simp [lift, h]
    · rename_i h9; rw [h9] at hx; cases hx
    · rename_i h9
      rw [h9] at hx
      split
      · simp [lift, h]
      · rename_i hs; rw [hs] at hx; cases hx
      · rename_i hs
        rw [hs] at hx
        split
        · simp [lift, h]
        · rename_i hn; rw [hn] at hx; cases hx
        · rename_i hn
          rw [hn] at hx
          split
          · simp [lift, h]
          · rename_i hse; rw [hse] at hx; cases hx
          · rename_i hse
            rw [hse] at hx
            split
            · simp [lift, h]
            · rename_i ht; rw [ht] at hx; cases hx
            · rename_i ht; rw [ht] at hx; cases hx
  · simp [lift, h]

/-! ## The law of the layer's forms -/

/-- **The fetch form of the layer's law.** -/
theorem step_of_fetch_g {g g' : GState} {l : Nat} {w : List Byte} {i : New}
    (fetched : g.x.m.memory.fetchBytes g.x.m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execNew i g (g.x.m.core.rip + BitVec.ofNat 64 l) = some g') :
    step g = some g' := by
  obtain ⟨hnone, hbad, hne, hbad9, hstr, ha, hf, hs, hst, hdn, h15⟩ := decodeL_spec hdec
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn9 : Silmaril.X86.Ext9.fetchNew g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, Silmaril.X86.Str9FsX.str9fsNew_none ha hf more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Silmaril.X86.Str9FsX.sse_none hs more]
    rfl
  have hsd : Silmaril.X86.Str9FsX.fetchStosd g.x.m.memory g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9FsX.fetchStosd
    rw [hmore, stosd_none hst more]
    rfl
  have hg : fetchNew g.x.m.memory g.x.m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchNew
    rw [hmore, decodeNew_append hdn more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hf8, hfn9, hfs, hfn, hss, hsd, hg, hx]

/-- **The layer's listing law.** -/
theorem step_of_listed_g {g g' : GState} {base : Word} {code : List Byte} {o l : Nat} {i : New}
    (hl : Loaded g.x.m.memory base code) (hrip : g.x.m.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execNew i g (g.x.m.core.rip + BitVec.ofNat 64 l) = some g') :
    step g = some g' := by
  have h1 : 0 < l := by
    have := (decodeL_spec hdec).2.2.2.2.2.2.2.2.1
    unfold stosdBad at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [List.length_take, List.length_drop] at this
    omega
  have hA : g.x.m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : g.x.m.memory.fetchBytes g.x.m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_g fetched hdec hx

/-! ## The machine -/

/-- **`Str9G` as a segment-VC instance** over the integer instructions of `Str9FsX`; the SSE
forms and this layer's forms have their own laws. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa GState where
  Instr := Silmaril.X86.Str9FsX.Instr
  instDecEq := inferInstance
  decode := Silmaril.X86.Str9FsX.decode
  exec := Silmaril.X86.Str9FsX.exec
  core := fun g => g.x.m.core
  mem := fun g => g.x.m.memory
  upd := fun g c m => { g with x := ⟨⟨c, m⟩, g.x.xmm⟩ }
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ =>
    step_of_str9fsx (Silmaril.X86.Str9FsX.step_of_listed hl hrip hfit hdec hx)

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Str9G` extends `Str9FsX`** along `g ↦ g.x` (the ghost state is the frame). -/
@[reducible] def extendsStr9FsX : Silmaril.X86.Str9FsX.isa.Extends isa where
  view g := g.x
  put g x := { g with x := x }
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ _ := trivial
  step h := step_of_str9fsx h

@[reducible] def extendsSse9 : Silmaril.X86.Sse9.isa.Extends isa :=
  Silmaril.X86.Str9FsX.extendsSse9.trans extendsStr9FsX

@[reducible] def extendsStr9Fs : Silmaril.X86.Str9Fs.isa.Extends isa :=
  Silmaril.X86.Str9FsX.extendsStr9Fs.trans extendsStr9FsX

@[reducible] def extendsStr9 : Silmaril.X86.Str9.isa.Extends isa :=
  Silmaril.X86.Str9FsX.extendsStr9.trans extendsStr9FsX

@[reducible] def extendsOpen9 : Silmaril.X86.Open9.isa.Extends isa :=
  Silmaril.X86.Str9FsX.extendsOpen9.trans extendsStr9FsX

@[reducible] def extendsOpen : Silmaril.X86.Open.isa.Extends isa :=
  Silmaril.X86.Str9FsX.extendsOpen.trans extendsStr9FsX

/-- **The SSE listing law**, carried over. -/
theorem step_of_listed_sse {g : GState} {base : Word} {code : List Byte} {o l : Nat}
    {i : Silmaril.X86.Sse9.Instr} {c : State} {xs : XFile} {mem : Memory}
    (hl : Loaded g.x.m.memory base code) (hrip : g.x.m.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length)
    (hdec : Silmaril.X86.Str9FsX.decodeSseL ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Sse9.exec i g.x.m.core g.x.xmm g.x.m.memory
      (g.x.m.core.rip + BitVec.ofNat 64 l) = .ok c xs mem) :
    step g = some { g with x := ⟨⟨c, mem⟩, xs⟩ } :=
  step_of_str9fsx (Silmaril.X86.Str9FsX.step_of_listed_sse hl hrip hfit hdec hx)

/-! ## Vectors (kernel-checked) -/

theorem decodeL_rdsspq : (decodeL [0xF3, 0x48, 0x0F, 0x1E, 0xC8]).map (·.1) = some (.cet false .rax) := by
  decide

theorem decodeL_rdtsc : (decodeL [0x0F, 0x31]).map (·.1) = some .rdtsc := by decide

theorem decodeL_pcmpeqb : (decodeL [0x66, 0x0F, 0x74, 0xC1]).map (·.2) = some 4 := by decide

theorem decodeL_pmovmskb : (decodeL [0x66, 0x0F, 0xD7, 0xC0]).map (·.2) = some 4 := by decide

theorem decodeL_movsd : (decodeL [0xF2, 0x0F, 0x10, 0x05, 0, 0, 0, 0]).map (·.2) = some 8 := by
  decide

/-- `endbr64` stays `Ext`'s. -/
theorem decodeL_lea32 : decodeL [0x67, 0x8D, 0x51, 0xFF] =
    some (.lea32 .rdx (Silmaril.X86.Ext.Mem.ofReg .rcx none 0xFFFFFFFF#32), 4) := by decide

theorem decode_endbr64 : (Silmaril.X86.Str9FsX.decode [0xF3, 0x0F, 0x1E, 0xFA]).isSome = true := by
  decide

/-- With CET off, `rdsspq` leaves its destination and the ghost state, and advances `rip`. -/
theorem execNew_rdssp (g : GState) (r : Silmaril.X86.Reg) (next : Word) (h : g.cetOff = true) :
    execNew (.cet false r) g next =
      some { g with x := ⟨⟨{ g.x.m.core with rip := next }, g.x.m.memory⟩, g.x.xmm⟩ } := by
  simp [execNew, h, xmmOnly]

/-- `pmovmskb` of `pcmpeqb x, x` (all bytes equal) is `0xFFFF`. -/
theorem movmskb_cmpeqb_self (v : Silmaril.X86.Sse9.Xmm) : movmskb (cmpeqb v v) = 0xFFFF := by
  unfold movmskb cmpeqb bytewise
  simp [byteOf, ofBytes]
  decide

end Silmaril.X86.Str9G
