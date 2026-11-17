module

public import Silmaril.X86.Str9L.Defs
public import Silmaril.X86.Str9X.Thms

/-!
# `Str9L`: the conservative extension of `Str9X`, the lane law

* `str9x_none`, `step_of_str9x`: where `Str9X` claims no bytes it has no step, so **every
  `Str9X` step is a step** with MXCSR kept.
* `step_of_fetch_lane`: a lane form decoded at the fetch window.
* `lowerClaims_of_laneBad`, `step_of_fetch_lane_head`, `step_of_listed_lane_head`: a form of the
  first lane at a listed offset, whatever bytes follow it (`laneBad`).
* `towerMissing_of_lowerClaims`, `towerMissing_of_listed_lane`, `towerMissing_of_listed`,
  `towerMissing_of_listed_v`: the feature gate `towerMissing` is `none` at a lane form and at a
  listed integer instruction, and is `vRequires`'s missing feature at a listed `Str9V` form.
* `view_toFloat`, `back_withFloat`, `step_of_listed_float`: a committed scalar SSE form
  (`floatExt`) on the tower: the core, the XMM file and MXCSR from the `X86.Float` result, the
  upper YMM halves, DF, the x87 state and the ghost state kept.
-/

@[expose] public section

namespace Silmaril.X86.Str9L

open Silmaril.X86 (State Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Features (Extension FeatureSet)
open Silmaril.Process (Memory)

/-- Where no decoder of `Str9X` claims the bytes, `Str9X` has no step. -/
theorem str9x_none {x : Str9X.XState} (h : lowerClaims x = false) : Str9X.step x = none := by
  simp only [lowerClaims, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Str9X.step, h1, Bool.false_eq_true, ite_false, h2]

/-- **Every `Str9X` step is a step**, with MXCSR kept. -/
theorem step_of_str9x {F : FeatureSet} {exts : List Extension} {s : LState} {x' : Str9X.XState}
    (h : Str9X.step s.x = some x') : step F exts s = some ⟨x', s.mxcsr⟩ := by
  cases hc : lowerClaims s.x
  · rw [str9x_none hc] at h; cases h
  · simp [step, hc, h]

/-- **The law of a lane form** at the fetch window: where `Str9X` claims nothing, the first
lane that decodes the window runs on the lane view. -/
theorem step_of_fetch_lane {F : FeatureSet} {exts : List Extension} {s : LState} {e : Extension}
    {i : e.Syntax} {n : Nat} {m : Silmaril.X86.Features.MState} (hc : lowerClaims s.x = false)
    (hd : Silmaril.X86.Features.extDecode exts
      (fetchWindow s.memory maxInstrLength s.core.rip.toNat) = some ⟨e, i, n⟩)
    (hp : s.memory.Permitted .execute s.core.rip.toNat n)
    (hx : Silmaril.X86.Features.extStep F e i n ⟨view s, s.memory⟩ = .retired m) :
    step F exts s = some (back s m.state m.memory) := by
  simp only [step, hc, Bool.false_eq_true, ite_false, hd, hp, ite_true, execLane, hx]

/-! ## Listed lane forms -/

/-- `fpuNo` rejects for the x87 decoder whatever follows. -/
theorem fpu_none {w : List Byte} (h : fpuNo w = true) (more : List Byte) :
    Silmaril.X86.Features.Fpu.decode (w ++ more) = none := by
  match w, h with
  | b :: t, h =>
    simp only [fpuNo, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hp : Silmaril.X86.Features.Fpu.parse (b :: (t ++ more)) = none := by
      simp only [Silmaril.X86.Features.Fpu.parse, h1, h2, ite_false,
        Silmaril.X86.Features.Fpu.parseEsc, h3, Bool.false_eq_true,
        Silmaril.X86.Features.Fpu.parseOpc, h4]
    simp only [List.cons_append, Silmaril.X86.Features.Fpu.decode, hp]

/-- **No decoder of `Str9X` claims a fetch window starting with `laneBad` bytes.** -/
theorem lowerClaims_of_laneBad {s : LState} {l : Nat} {w : List Byte}
    (fetched : s.memory.fetchBytes s.core.rip.toNat l = some w) (h15 : l ≤ maxInstrLength)
    (hw : laneBad w = true) : lowerClaims s.x = false := by
  simp only [laneBad, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨hb, hfl⟩, hsc⟩, hfpu⟩ := hw
  obtain ⟨hc, hv⟩ := Str9D.str9v_rejects (v := s.x.d.v) fetched h15 hb
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow fetched h15
  have hws : Str9D.strClaims (fetchWindow s.memory maxInstrLength s.core.rip.toNat) = false := by
    rw [← hmore]; exact Str9D.strClaims_append more hsc
  have hff : Str9D.fetchFlag s.memory s.core.rip.toNat = none := by
    unfold Str9D.fetchFlag
    rw [← hmore, Str9X.decodeFlag_append_none (Str9D.ne_nil_of_strClaims hsc) hfl more]
    rfl
  have hfp : Str9X.fetchFpu s.memory s.core.rip.toNat = none := by
    unfold Str9X.fetchFpu
    rw [← hmore, fpu_none hfpu more]
    rfl
  simp only [LState.memory, LState.core, Str9X.XState.memory, Str9X.XState.core] at hws hff hfp
  simp only [lowerClaims, Str9X.lowerClaims, Str9D.DState.memory, Str9D.DState.core, hws, hc, hv,
    hff, hfp, Bool.and_false, Bool.or_false, Option.isSome_none]

/-- **A form of the first lane at the fetch window**, whatever bytes follow it. -/
theorem step_of_fetch_lane_head {F : FeatureSet} {e : Extension} {rest : List Extension}
    {s : LState} {l : Nat} {w : List Byte} {i : e.Syntax} {m : Silmaril.X86.Features.MState}
    (fetched : s.memory.fetchBytes s.core.rip.toNat l = some w) (h15 : l ≤ maxInstrLength)
    (hw : laneBad w = true) (hd : e.decoder.decode w = some (i, l))
    (hx : Silmaril.X86.Features.extStep F e i l ⟨view s, s.memory⟩ = .retired m) :
    step F (e :: rest) s = some (back s m.state m.memory) := by
  obtain ⟨more, hmore⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow fetched h15
  refine step_of_fetch_lane (lowerClaims_of_laneBad fetched h15 hw) ?_
    (Silmaril.Process.Memory.readWith_permitted fetched) hx
  rw [← hmore]
  simp only [Silmaril.X86.Features.extDecode, e.decoder.decode_append more hd]

/-- **A form of the first lane at a listed offset.** -/
theorem step_of_listed_lane_head {F : FeatureSet} {e : Extension} {rest : List Extension}
    {s : LState} {base : Word} {code : List Byte} {o l : Nat} {i : e.Syntax}
    {m : Silmaril.X86.Features.MState} (hl : Silmaril.X86.Ext.Loaded s.memory base code)
    (hrip : s.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (h15 : l ≤ maxInstrLength) (hw : laneBad ((code.drop o).take l) = true)
    (hd : e.decoder.decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Features.extStep F e i l ⟨view s, s.memory⟩ = .retired m) :
    step F (e :: rest) s = some (back s m.state m.memory) :=
  step_of_fetch_lane_head
    (Str9D.fetched_of_listed (d := s.x.d) hl hrip (e.decoder.decode_length_pos hd) hfit) h15 hw
    hd hx

/-! ## Scalar SSE on the tower -/

theorem xregOf_toV (r : Silmaril.X86.XReg) : xregOf r.toV = r := by cases r <;> rfl

theorem low_setWidth_append (a b : BitVec 128) :
    ((a ++ b : BitVec 256).setWidth 512).extractLsb' 0 128 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hj, show j < 512 by omega]

theorem hi_ymm_append (u : BitVec 384) (a b v : BitVec 128)
    (hu : u = ((a ++ b : BitVec 256).setWidth 512).extractLsb' 128 384) :
    ((u ++ v : BitVec 512).extractLsb' 0 256).extractLsb' 128 128 = a := by
  subst hu
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp only [Nat.zero_add, Nat.add_sub_cancel_left, hj, decide_true, Bool.true_and,
    show 128 + j < 256 by omega, show ¬ (128 + j < 128) by omega, ite_false,
    show j < 384 by omega, show 128 + j < 512 by omega]

/-- The scalar view of the lane view: the core, the XMM file and MXCSR. -/
theorem view_toFloat (s : LState) :
    (view s).toFloat = ⟨s.core, s.x.d.v.g.x.xmm, s.mxcsr⟩ := by
  simp only [Silmaril.X86.Features.State.toFloat, view, Silmaril.X86.Features.State.xmm,
    Silmaril.X86.Float.State.mk.injEq, true_and, and_true]
  funext r
  simp only [Silmaril.X86.XReg.toV_lt r, ↓reduceIte, xregOf_toV, low_setWidth_append]

/-- **A scalar SSE result taken back**: the core, the XMM file and MXCSR from `t`, the memory
`m`; the upper YMM halves, DF, the x87 state and the ghost state kept. -/
theorem back_withFloat (s : LState) (t : Silmaril.X86.Float.State) (m : Memory) :
    back s ((view s).withFloat t) m =
      ⟨⟨⟨⟨{ s.x.d.v.g with x := ⟨⟨t.core, m⟩, t.xmm⟩ }, s.x.d.v.hi⟩, s.x.d.df⟩, s.x.fpu⟩,
        t.mxcsr⟩ := by
  simp only [back, Silmaril.X86.Features.State.withFloat_core,
    Silmaril.X86.Features.State.withFloat_mxcsr, Silmaril.X86.Features.State.withFloat_x87]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 2
          funext r
          simp only [Silmaril.X86.Features.State.xmm, Silmaril.X86.Features.State.zmm_withFloat,
            Silmaril.X86.XReg.toV_lt r, ↓reduceIte]
          rw [show XReg.ofBitVec (BitVec.ofNat 4 r.toV.val) = r from xregOf_toV r]
          apply BitVec.eq_of_getLsbD_eq; intro j hj
          rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
          simp [hj]
        · funext r
          simp only [Silmaril.X86.Features.State.ymm, Silmaril.X86.Features.State.zmm_withFloat,
            Silmaril.X86.XReg.toV_lt r, ↓reduceIte]
          exact hi_ymm_append _ (s.hi r) (s.xmm r) _
            (by simp only [Silmaril.X86.Features.State.upper128, view,
              Silmaril.X86.XReg.toV_lt r, ↓reduceIte, xregOf_toV])

/-- **A scalar SSE form at a listed offset** (`floatExt`, the first lane) that commits. -/
theorem step_of_listed_float {F : FeatureSet} {rest : List Extension} {s : LState} {base : Word}
    {code : List Byte} {o l : Nat} {i : Silmaril.X86.Float.Instr} {t : Silmaril.X86.Float.State}
    {after : Memory} (hl : Silmaril.X86.Ext.Loaded s.memory base code)
    (hrip : s.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (h15 : l ≤ maxInstrLength) (hw : laneBad ((code.drop o).take l) = true)
    (hd : Silmaril.X86.Float.decode ((code.drop o).take l) = some (i, l))
    (hF : F.missing [i.feature.toFeature] = none)
    (hx : i.exec ⟨s.core, s.x.d.v.g.x.xmm, s.mxcsr⟩ s.memory = .commit t after) :
    step F (Silmaril.X86.Features.floatExt :: rest) s =
      some ⟨⟨⟨⟨{ s.x.d.v.g with x := ⟨⟨t.core, after⟩, t.xmm⟩ }, s.x.d.v.hi⟩, s.x.d.df⟩, s.x.fpu⟩,
        t.mxcsr⟩ := by
  rw [← back_withFloat]
  refine step_of_listed_lane_head (m := ⟨(view s).withFloat t, after⟩) hl hrip hfit h15 hw hd ?_
  simp only [Silmaril.X86.Features.extStep, Silmaril.X86.Features.floatExt_requires, hF,
    Silmaril.X86.Features.floatExt_exec, view_toFloat, hx, Silmaril.X86.Features.floatResult]

/-! ## The feature gate of the tower's forms -/

/-- Where the lane forms run, no tower form needs a feature. -/
theorem towerMissing_of_lowerClaims {F : FeatureSet} {s : LState} (h : lowerClaims s.x = false) :
    towerMissing F s = none := by
  simp only [lowerClaims, Str9X.lowerClaims, Bool.or_eq_false_iff] at h
  have hv : Str9V.fetchNew s.memory s.core.rip.toNat = none :=
    Option.isSome_eq_false_iff.mp h.1.1.2 |> Option.isNone_iff_eq_none.mp
  unfold towerMissing
  split
  · rfl
  · rw [hv]

/-- At a listed lane form (`laneBad`), no tower form needs a feature. -/
theorem towerMissing_of_listed_lane {F : FeatureSet} {s : LState} {base : Word}
    {code : List Byte} {o l : Nat} (hl : Silmaril.X86.Ext.Loaded s.memory base code)
    (hrip : s.core.rip = base + BitVec.ofNat 64 o) (h1 : 0 < l) (hfit : o + l ≤ code.length)
    (h15 : l ≤ maxInstrLength) (hw : laneBad ((code.drop o).take l) = true) :
    towerMissing F s = none :=
  towerMissing_of_lowerClaims
    (lowerClaims_of_laneBad (Str9D.fetched_of_listed (d := s.x.d) hl hrip h1 hfit) h15 hw)

/-- **At a listed integer instruction no tower form needs a feature**: a layer below `Str9V`
claims the bytes. -/
theorem towerMissing_of_listed {F : FeatureSet} {s : LState} {base : Word} {code : List Byte}
    {o l : Nat} {i : Silmaril.X86.Str9FsX.Instr} {c : State} {mem : Memory}
    (hl : Silmaril.X86.Ext.Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hfit : o + l ≤ code.length) (hdec : Str9D.decode ((code.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Str9FsX.exec i s.core s.memory l = .ok c mem) :
    towerMissing F s = none := by
  unfold Str9D.decode at hdec
  split at hdec
  · rename_i j n hj
    split at hdec
    · simp only [Option.some.injEq, Prod.mk.injEq] at hdec
      obtain ⟨rfl, rfl⟩ := hdec
      have hG := Silmaril.X86.Str9G.isa.step_of (s := s.x.d.v.g) trivial hl hrip hfit hj hx
        trivial
      have hc : Str9V.lowerClaims s.x.d.v.g = true := by
        cases h : Str9V.lowerClaims s.x.d.v.g
        · rw [Silmaril.X86.Str9G.isa_step, Str9V.lower_none h] at hG; cases hG
        · rfl
      simp only [towerMissing, hc, ite_true]
    · cases hdec
  · cases hdec

/-- **A listed `Str9V` form needs `vRequires`**: at a form of `Str9V.decodeL`, the gate is the
first feature of `vRequires` missing from `F`. -/
theorem towerMissing_of_listed_v {F : FeatureSet} {s : LState} {base : Word} {code : List Byte}
    {o l : Nat} {i : Str9V.Instr} (hl : Silmaril.X86.Ext.Loaded s.memory base code)
    (hrip : s.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : Str9V.decodeL ((code.drop o).take l) = some (i, l)) :
    towerMissing F s = F.missing (vRequires i) := by
  obtain ⟨hnone, hbad, hne, hbad9, hstr, ha, hf, hs, hst, hgb, hdn, h2, h15⟩ :=
    Str9V.decodeL_spec hdec
  have fetched := Str9D.fetched_of_listed (d := s.x.d) hl hrip (by omega) hfit
  obtain ⟨more, hmore, hf8⟩ :=
    Silmaril.X86.Open9.fetch8_undecodable_of fetched h15 hnone hbad hne
  have hfn9 : Silmaril.X86.Ext9.fetchNew s.memory s.core.rip.toNat = none := by
    unfold Silmaril.X86.Ext9.fetchNew
    rw [hmore, Silmaril.X86.Str9.decodeNew_none_of_bad hbad9 more]
    rfl
  have hfs : Silmaril.X86.Str9.fetchStr s.memory s.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9.fetchStr
    rw [hmore, Silmaril.X86.Str9Fs.decodeStr_none_of_strBad hstr more]
    rfl
  have hfn : Silmaril.X86.Str9Fs.fetchNew s.memory s.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9Fs.fetchNew
    rw [hmore, Silmaril.X86.Str9FsX.str9fsNew_none ha hf more]
    rfl
  have hss : Silmaril.X86.Sse9.fetchSse s.memory s.core.rip.toNat = none := by
    unfold Silmaril.X86.Sse9.fetchSse
    rw [hmore, Silmaril.X86.Str9FsX.sse_none hs more]
    rfl
  have hsd : Silmaril.X86.Str9FsX.fetchStosd s.memory s.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9FsX.fetchStosd
    rw [hmore, Silmaril.X86.Str9G.stosd_none hst more]
    rfl
  have hgn : Silmaril.X86.Str9G.fetchNew s.memory s.core.rip.toNat = none := by
    unfold Silmaril.X86.Str9G.fetchNew
    rw [hmore, Str9V.gNew_none hgb more]
    rfl
  have hc : Str9V.lowerClaims s.x.d.v.g = false := by
    unfold Str9V.lowerClaims; simp only; rw [hf8]; simp [hfn9, hfs, hfn, hss, hsd, hgn]
  have hv : Str9V.fetchNew s.memory s.core.rip.toNat = some (some (i, l)) := by
    unfold Str9V.fetchNew
    rw [hmore, Str9V.decodeNew_append hdn more]
    simp [Silmaril.Process.Memory.readWith_permitted fetched]
  simp only [towerMissing, hc, Bool.false_eq_true, ite_false, hv]

end Silmaril.X86.Str9L
