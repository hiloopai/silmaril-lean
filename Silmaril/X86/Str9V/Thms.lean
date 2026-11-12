module

public import Silmaril.X86.Str9V.Defs
public import Silmaril.X86.Str9G.Thms

/-!
# `Str9V`: the extension of `Str9G`, the listing law, the machine

* `step_of_lower`: every `Str9G` step of `v.g` is a step of `v` that keeps the YMM upper halves,
  so `extendsStr9G : Str9G.isa.Extends isa` (lens `v ↦ v.g`) and, composed, the extensions of
  every lower machine.
* `good_pNew`, `decodeNew_append`: the layer's parser has the prefix laws.
* `step_of_listed_v`: the law of the layer's forms.
-/

@[expose] public section

namespace Silmaril.X86.Str9V

open Silmaril.X86 (State MState Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Loaded PResult ByteParser pHead)
open Silmaril.X86.Ext.ByteParser
open Silmaril.X86.Sse9 (XState XFile XResult)
open Silmaril.Process (Memory)
open Silmaril.X86.Str9G (GState)

/-! ## Decoder laws -/

theorem good_regP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (regP rex mp) := by
  unfold regP; exact good_ite (good_pure _) good_fail

theorem good_memP (rex : Option Silmaril.X86.Ext.Rex) (mp : Silmaril.X86.Ext.ModrmPart) :
    Good (memP rex mp) := by
  unfold memP; split
  · exact good_pure _
  · exact good_fail

/-- Discharge `Good` goals of the layer's parsers. -/
macro "goodv_tac" : tactic => `(tactic| repeat (first
  | exact good_fail | exact good_byte | exact Silmaril.X86.Ext8.good_pM
  | exact good_pure _ | exact good_regP _ _ | exact good_memP _ _
  | exact Silmaril.X86.Ext.good_pHead | exact Silmaril.X86.Ext.good_pAfterSeg _ _
  | apply good_ite | apply good_map | apply good_bind | intro _ | split))

theorem good_vexBody (v : Vex) (op : Byte) : Good (vexBody v op) := by
  unfold vexBody; goodv_tac

theorem good_vexRest (v : Vex) : Good (vexRest v) := by
  unfold vexRest
  exact good_bind good_byte fun _ => good_ite (good_pure _) (good_vexBody _ _)

theorem good_pLegacy (pfx : Silmaril.X86.Ext.Pfx) (rex : Option Silmaril.X86.Ext.Rex)
    (opc : Silmaril.X86.Ext.Opc) : Good (pLegacy pfx rex opc) := by
  cases opc <;> simp only [pLegacy] <;> goodv_tac

theorem good_pLea32 : Good pLea32 := by unfold pLea32; goodv_tac

/-- **The layer's parser has the prefix laws.** -/
theorem good_pNew : Good pNew := by
  unfold pNew
  refine good_bind good_byte fun b0 => ?_
  refine good_ite (good_bind good_byte fun _ => good_vexRest _) ?_
  refine good_ite (good_bind good_byte fun _ => good_bind good_byte fun _ => good_vexRest _) ?_
  refine good_ite good_pLea32 ?_
  refine good_ite good_fail ?_
  exact good_bind (Silmaril.X86.Ext.good_pAfterSeg _ _) fun _ => good_ite good_fail (good_pLegacy _ _ _)

/-- A decoded form keeps its reading whatever bytes follow. -/
theorem decodeNew_append {w : List Byte} {i : Instr} {n : Nat} (h : decodeNew w = some (i, n))
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

/-- `Str9G`'s own forms stay rejected whatever bytes follow. -/
theorem gNew_none {w : List Byte} (h : gBad w = true) (more : List Byte) :
    Silmaril.X86.Str9G.decodeNew (w ++ more) = none := by
  unfold gBad at h
  split at h
  · rename_i hb
    unfold Silmaril.X86.Str9G.decodeNew
    rw [Silmaril.X86.Str9G.good_pNew.bad hb more]
  · cases h

theorem decodeL_spec {w : List Byte} {i : Instr} {n : Nat} (h : decodeL w = some (i, n)) :
    Silmaril.X86.Ext.decode w = none ∧ Silmaril.X86.Open9.newBad w = true ∧
      Silmaril.X86.Open9.rawNotEof w = true ∧ Silmaril.X86.Str9.ext9Bad w = true ∧
      Silmaril.X86.Str9Fs.strBad w = true ∧ Silmaril.X86.Str9FsX.atomicBad w = true ∧
      Silmaril.X86.Str9FsX.fsBad w = true ∧ Silmaril.X86.Str9FsX.sseBad w = true ∧
      Silmaril.X86.Str9G.stosdBad w = true ∧ gBad w = true ∧ decodeNew w = some (i, n) ∧
      2 ≤ n ∧ n ≤ maxInstrLength := by
  unfold decodeL at h
  split at h
  · rename_i j k hj
    split at h
    · rename_i c
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, c.2.2.2.2.2.1, c.2.2.2.2.2.2.1,
        c.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2.1, c.2.2.2.2.2.2.2.2.2.1, hj, c.2.2.2.2.2.2.2.2.2.2.1,
        c.2.2.2.2.2.2.2.2.2.2.2⟩
    · cases h
  · cases h

/-! ## Extension of `Str9G` -/

/-- Where no lower layer claims the bytes, `Str9G` has no step. -/
theorem lower_none {g : GState} (h : lowerClaims g = false) : Silmaril.X86.Str9G.step g = none := by
  unfold lowerClaims at h
  unfold Silmaril.X86.Str9G.step
  simp only at h ⊢
  split at h
  · rename_i h8
    simp only [Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨⟨h9, hs⟩, hn⟩, hse⟩, ht⟩, hg⟩ := h
    simp [h8, h9, hs, hn, hse, ht, hg]
  · cases h

/-- **Every `Str9G` step of `v.g` is a step that keeps the YMM upper halves.** -/
theorem step_of_lower {v : VState} {g : GState} (h : Silmaril.X86.Str9G.step v.g = some g) :
    step v = some ⟨g, v.hi⟩ := by
  unfold step
  cases hc : lowerClaims v.g
  · rw [lower_none hc] at h; cases h
  · simp [h]

/-! ## The law of the layer's forms -/

/-- **The fetch form of the layer's law.** -/
theorem step_of_fetch_v {v v' : VState} {l : Nat} {w : List Byte} {i : Instr}
    (fetched : v.g.x.m.memory.fetchBytes v.g.x.m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execV i v (v.g.x.m.core.rip + BitVec.ofNat 64 l) = some v') :
    step v = some v' := by
  obtain ⟨hnone, hbad, hne, hbad9, hstr, ha, hf, hs, hst, hgb, hdn, -, h15⟩ := decodeL_spec hdec
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn9 : Silmaril.X86.Ext9.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, Silmaril.X86.Str9FsX.str9fsNew_none ha hf more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Silmaril.X86.Str9FsX.sse_none hs more]
    rfl
  have hsd : Silmaril.X86.Str9FsX.fetchStosd v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9FsX.fetchStosd
    rw [hmore, Silmaril.X86.Str9G.stosd_none hst more]
    rfl
  have hgn : Silmaril.X86.Str9G.fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9G.fetchNew
    rw [hmore, gNew_none hgb more]
    rfl
  have hc : lowerClaims v.g = false := by
    unfold lowerClaims; simp only; rw [hf8]; simp [hfn9, hfs, hfn, hss, hsd, hgn]
  have hv : fetchNew v.g.x.m.memory v.g.x.m.core.rip.toNat = some (some (i, l)) := by
    unfold fetchNew
    rw [hmore, decodeNew_append hdn more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [step, hc, hv, hx, Bool.false_eq_true, ite_false]

/-- **The layer's listing law.** -/
theorem step_of_listed_v {v v' : VState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    (hl : Loaded v.g.x.m.memory base code) (hrip : v.g.x.m.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execV i v (v.g.x.m.core.rip + BitVec.ofNat 64 l) = some v') :
    step v = some v' := by
  have h1 : 0 < l := by have := (decodeL_spec hdec).2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hA : v.g.x.m.core.rip.toNat = base.toNat + o := by rw [hrip]; exact hl.toNat_add (by omega)
  have fetched : v.g.x.m.memory.fetchBytes v.g.x.m.core.rip.toNat l = some ((code.drop o).take l) := by
    rw [hA]; exact hl.fetchBytes_sub (by omega) hfit
  exact step_of_fetch_v fetched hdec hx

/-! ## The machine -/

/-- **`Str9V` as a segment-VC instance** over the integer instructions of `Str9FsX`. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa VState where
  Instr := Silmaril.X86.Str9FsX.Instr
  instDecEq := inferInstance
  decode := Silmaril.X86.Str9FsX.decode
  exec := Silmaril.X86.Str9FsX.exec
  core := fun v => v.g.x.m.core
  mem := fun v => v.g.x.m.memory
  upd := fun v c m => ⟨{ v.g with x := ⟨⟨c, m⟩, v.g.x.xmm⟩ }, v.hi⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ =>
    step_of_lower (Silmaril.X86.Str9G.isa.step_of (s := _) trivial hl hrip hfit hdec hx trivial)

@[simp] theorem isa_step : isa.step = step := rfl

/-- **`Str9V` extends `Str9G`** along `v ↦ v.g` (the YMM upper halves are the frame). -/
@[reducible] def extendsStr9G : Silmaril.X86.Str9G.isa.Extends isa where
  view v := v.g
  put v g := ⟨g, v.hi⟩
  view_put _ _ := rfl
  put_put _ _ _ := rfl
  put_view _ := rfl
  core _ := rfl
  mem _ := rfl
  upd _ _ _ := rfl
  live _ _ := trivial
  step h := step_of_lower h

@[reducible] def extendsStr9FsX : Silmaril.X86.Str9FsX.isa.Extends isa :=
  Silmaril.X86.Str9G.extendsStr9FsX.trans extendsStr9G

@[reducible] def extendsOpen : Silmaril.X86.Open.isa.Extends isa :=
  Silmaril.X86.Str9G.extendsOpen.trans extendsStr9G

/-! ## Vectors (kernel-checked) -/

theorem decodeL_vpxor_ymm : (decodeL [0xC5, 0xFD, 0xEF, 0xC0]).map (·.2) = some 4 := by decide

theorem decodeL_vzeroupper : (decodeL [0xC5, 0xF8, 0x77]).map (·.1) = some .vzeroupper := by decide

theorem decodeL_repMovsb : (decodeL [0xF3, 0xA4]).map (·.1) = some .repMovsb := by decide

end Silmaril.X86.Str9V
