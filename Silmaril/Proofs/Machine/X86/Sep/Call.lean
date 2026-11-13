module

public import Silmaril.Machine.X86.Sep.SysV.Defs
public import Silmaril.Machine.X86.Open.Thms
public import Silmaril.Proofs.Machine.X86.Sep.Bridge
public import Silmaril.X86.Ext.Machine

/-!
# Proofs: the `call rel32` and `ret` triples on the open machine

Single-instruction triples, from the semantics of the stack instructions of
`Silmaril.X86.Insn` (`Stack.lean`) carried to the open machine through the proved
embeddings `X86.MState.stepOpt → Ext.stepOpt → Ext8.stepOpt → Open.step`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Sep

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (union Disjoint Le reval)

/-- An instruction of the base machine that executes is one open step. -/
theorem open_step_of_insn {m : MState} {i : Insn} {core : State} {mem : Memory}
    (f : m.memory.fetchBytes m.core.rip.toNat i.encode.length = some i.encode)
    (e : i.exec m.core m.memory = some (core, mem)) :
    Silmaril.Machine.X86.Open.step m = some ⟨core, mem⟩ := by
  have h : Silmaril.X86.MState.stepOpt (core.rip + 1#64) m = some ⟨core, mem⟩ :=
    Silmaril.X86.MState.stepOpt_of_exec f (Silmaril.X86.Insn.decode_encode i) e (by
      rintro ⟨-, h⟩
      exact absurd h (by bv_omega))
  exact Silmaril.Machine.X86.Open.step_of_ext8_stepOpt
    (Silmaril.X86.Ext8.stepOpt_of_ext (Silmaril.X86.Ext.stepOpt_of_x86 h))

theorem reaches_one {m m' : MState} (h : Silmaril.Machine.X86.Open.step m = some m') :
    Reaches Silmaril.Machine.X86.Open.step m m' :=
  ⟨1, by simp [run, h]⟩

/-- Locations other than `rip`, `rsp` and the bytes in `W` are unchanged. -/
theorem toFrag_agree {m m' : MState} {W : Nat → Prop}
    (hreg : ∀ r, r ≠ .rsp → m'.core.read r = m.core.read r)
    (hflags : m'.core.flags = m.core.flags)
    (hregions : m'.memory.regions = m.memory.regions)
    (hbytes : ∀ a, ¬ W a → m'.memory.bytes.get? a = m.memory.bytes.get? a)
    {l : Loc} (hrip : l ≠ .rip) (hrsp : l ≠ .reg .rsp) (hmem : ∀ a, l = .mem a → ¬ W a) :
    toFrag m' l = toFrag m l := by
  cases l with
  | reg r =>
    have : r ≠ .rsp := fun e => hrsp (e ▸ rfl)
    simp [toFrag, hreg r this]
  | rip => exact absurd rfl hrip
  | flags => simp [toFrag, hflags]
  | mem a =>
    have hb := hbytes a (hmem a rfl)
    simp only [toFrag]
    rw [hb]
    simp [permsAt, Memory.permits, hregions]
  | regions => simp [toFrag, hregions]

theorem none_of_disjoint {a b : Frag} (hd : Disjoint a b) {l : Loc} (ha : (a l).isSome) :
    b l = none := by
  rcases hd l with e | e
  · rw [e] at ha; cases ha
  · exact e

theorem ne_of_isSome_none {h : Frag} {l l' : Loc} (hl : h l = none) (hl' : (h l').isSome) :
    l ≠ l' := by
  rintro rfl; rw [hl] at hl'; cases hl'

theorem toNat_sub_eight {s : Word} (hs : 8 ≤ s.toNat) : (s - 8#64).toNat = s.toNat - 8 := by
  bv_omega

/-- **`call rel32`**: push the return address into the eight bytes below `rsp` and jump. -/
theorem call_step (pc s : Word) (rel : BitVec 32) (hs : 8 ≤ s.toNat) :
    Triple (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt pc ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt (pc + 5#64 + rel.signExtend 64) ∗
        regPt .rsp (s - 8#64) ∗ wordPt (s.toNat - 8) (pc + 5#64)) := by
  apply triple_of_local
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, r2, hripP, hr2, hlrip, hlr2, hd2, rfl⟩ := sep_le hr1 hlr1
  obtain ⟨hsp, hb, hspP, hbP, hlsp, hlb, hd3, rfl⟩ := sep_le hr2 hlr2
  have erip := ripPt_le hripP hlrip
  have ersp := regPt_le hspP hlsp
  have fetch := fetchBytes_of_codePt (by simp [Insn.encode]) hcP hlc
  have perm := permitted_of_blockAny (.inr rfl) (by omega) hbP hlb
  have hsub := toNat_sub_eight hs
  have hperm : m.memory.Permitted .write (m.core.read .rsp - 8#64).toNat 8 := by
    rw [ersp, hsub]; exact perm
  obtain ⟨core1, mem1, hpush⟩ : ∃ c mm, Silmaril.X86.pushWord m.core m.memory
      (m.core.rip + BitVec.ofNat 64 (Insn.call rel).length) = some (c, mm) :=
    ⟨_, _, Silmaril.X86.pushWord_eq_some hperm⟩
  have hexec : (Insn.call rel).exec m.core m.memory =
      some ({ core1 with
        rip := m.core.rip + BitVec.ofNat 64 (Insn.call rel).length + rel.signExtend 64 },
        mem1) := by
    simp only [Insn.exec, hpush, Option.map_some]
  have hstep := open_step_of_insn (by rw [erip]; exact fetch) hexec
  have hcore1 := Silmaril.X86.pushWord_state hpush
  have hwo := Silmaril.X86.pushWord_writesOnly hpush
  have hget := Silmaril.X86.pushWord_get hpush
  rw [ersp, hsub] at hwo hget
  set m' : MState := ⟨{ core1 with
    rip := m.core.rip + BitVec.ofNat 64 (Insn.call rel).length + rel.signExtend 64 }, mem1⟩
    with hm'
  have hregions : m'.memory.regions = m.memory.regions := hwo.1
  have hperms : ∀ a, permsAt m'.memory a = permsAt m.memory a := by
    intro a; simp [permsAt, Memory.permits, hregions]
  -- every location outside the instruction's own fragment is unchanged
  have unchanged : ∀ l, union hrip (union hsp hb) l = none → toFrag m' l = toFrag m l := by
    intro l hl0
    refine toFrag_agree (m := m) (m' := m') (W := fun a => s.toNat - 8 ≤ a ∧ a < s.toNat - 8 + 8)
      (fun r hr => ?_) ?_ hregions (fun a ha => hwo.2 a (by omega)) ?_ ?_ ?_
    · show core1.read r = _
      rw [hcore1]
      exact State.read_write_other _ _ _ _ hr
    · show core1.flags = _
      rw [hcore1]; rfl
    · exact ne_of_isSome_none hl0 (Frag.isSome_union.mpr (.inl (ripPt_dom hripP)))
    · exact ne_of_isSome_none hl0 (Frag.isSome_union.mpr (.inr
        (Frag.isSome_union.mpr (.inl (regPt_dom hspP)))))
    · rintro a rfl ⟨h1, h2⟩
      have := blockAny_dom hbP (a - (s.toNat - 8)) (by omega)
      rw [show s.toNat - 8 + (a - (s.toNat - 8)) = a by omega] at this
      exact ne_of_isSome_none hl0 (Frag.isSome_union.mpr (.inr
        (Frag.isSome_union.mpr (.inr this)))) rfl
  refine ⟨m', reaches_one hstep, fun l hl0 => unchanged l ?_, ?_⟩
  · exact (Frag.union_eq_none.mp hl0).2
  have d1 := Frag.reval_disjoint hd1 (toFrag m')
  have d2 := Frag.reval_disjoint hd2 (toFrag m')
  have d3 := Frag.reval_disjoint hd3 (toFrag m')
  rw [Frag.reval_union] at d1 d2 ⊢
  rw [Frag.reval_union] at d1 ⊢
  rw [Frag.reval_union]
  refine ⟨_, _, d1, rfl, ?_, _, _, d2, rfl, ?_, _, _, d3, rfl, ?_, ?_⟩
  · rw [Frag.reval_eq_of_agree hlc (fun l hl' => unchanged l (none_of_disjoint hd1 hl'))]
    exact hcP
  · have := ripPt_reval m' hripP
    have e : m'.core.rip = pc + 5#64 + rel.signExtend 64 := by
      show m.core.rip + BitVec.ofNat 64 5 + _ = _
      rw [erip]
    rwa [e] at this
  · have := regPt_reval m' hspP
    have e : m'.core.read .rsp = s - 8#64 := by
      show core1.read .rsp = _
      rw [hcore1, State.read_write_same, ersp]
    rwa [e] at this
  · refine blockAny_reval_bytes hbP (by simp) (fun i hi => ⟨?_, ?_⟩)
    · have := hget i (by simpa using hi)
      rw [this, erip]; rfl
    · rw [hperms]
      exact (blockAny_le hbP hlb i (by simpa using hi)).2

/-- **`ret`**: pop the return address into `rip`. -/
theorem ret_step (q s r : Word) :
    Triple (codePt q.toNat (Insn.encode .ret) ∗ ripPt q ∗ regPt .rsp s ∗ wordPt s.toNat r)
      (codePt q.toNat (Insn.encode .ret) ∗ ripPt r ∗ regPt .rsp (s + 8#64) ∗
        wordPt s.toNat r) := by
  apply triple_of_local
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, r2, hripP, hr2, hlrip, hlr2, hd2, rfl⟩ := sep_le hr1 hlr1
  obtain ⟨hsp, hw, hspP, hwP, hlsp, hlw, hd3, rfl⟩ := sep_le hr2 hlr2
  have erip := ripPt_le hripP hlrip
  have ersp := regPt_le hspP hlsp
  have fetch := fetchBytes_of_codePt (by simp [Insn.encode]) hcP hlc
  have hread := readBytes_of_wordPt hwP hlw
  have hpop := Silmaril.X86.popWord_of_readBytes (s := m.core) (by rw [ersp]; exact hread)
  have hexec : Insn.ret.exec m.core m.memory =
      some ({ m.core.write .rsp (m.core.read .rsp + 8#64) with rip := r }, m.memory) := by
    simp only [Insn.exec, hpop, Option.map_some]
  have hstep := open_step_of_insn (by rw [erip]; exact fetch) hexec
  set m' : MState := ⟨_, _⟩ with hm'
  have unchanged : ∀ l, union hrip hsp l = none → toFrag m' l = toFrag m l := by
    intro l hl0
    refine toFrag_agree (m := m) (m' := m') (W := fun _ => False) (fun r hr => ?_) rfl rfl (fun _ _ => rfl) ?_ ?_
      (fun _ _ h => h)
    · show (m.core.write .rsp _).read r = _
      exact State.read_write_other _ _ _ _ hr
    · exact ne_of_isSome_none hl0 (Frag.isSome_union.mpr (.inl (ripPt_dom hripP)))
    · exact ne_of_isSome_none hl0 (Frag.isSome_union.mpr (.inr (regPt_dom hspP)))
  have notIn : ∀ l, union hrip (union hsp hw) l = none → union hrip hsp l = none := by
    intro l h
    obtain ⟨h1, h2⟩ := Frag.union_eq_none.mp h
    exact Frag.union_eq_none.mpr ⟨h1, (Frag.union_eq_none.mp h2).1⟩
  refine ⟨m', reaches_one hstep, fun l hl0 => unchanged l (notIn l ?_), ?_⟩
  · exact (Frag.union_eq_none.mp hl0).2
  have d1 := Frag.reval_disjoint hd1 (toFrag m')
  have d2 := Frag.reval_disjoint hd2 (toFrag m')
  have d3 := Frag.reval_disjoint hd3 (toFrag m')
  rw [Frag.reval_union] at d1 d2 ⊢
  rw [Frag.reval_union] at d1 ⊢
  rw [Frag.reval_union]
  refine ⟨_, _, d1, rfl, ?_, _, _, d2, rfl, ?_, _, _, d3, rfl, ?_, ?_⟩
  · rw [Frag.reval_eq_of_agree hlc (fun l hl' => unchanged l (notIn l
      (none_of_disjoint hd1 hl')))]
    exact hcP
  · exact ripPt_reval m' hripP
  · have := regPt_reval m' hspP
    have e : m'.core.read .rsp = s + 8#64 := by
      show (m.core.write .rsp (m.core.read .rsp + 8#64)).read .rsp = _
      rw [State.read_write_same, ersp]
    rwa [e] at this
  · have hw' : ∀ l, (hw l).isSome → union hrip hsp l = none := by
      intro l hl'
      have := none_of_disjoint (Frag.Disjoint.symm hd3) hl'
      have h2 : hrip l = none := by
        have := none_of_disjoint (Frag.Disjoint.symm hd2)
          (Frag.isSome_union.mpr (.inr hl'))
        exact this
      exact Frag.union_eq_none.mpr ⟨h2, by assumption⟩
    rw [Frag.reval_eq_of_agree hlw (fun l hl' => unchanged l (hw' l hl'))]
    exact hwP

end Silmaril.Proofs.Machine.X86.Sep
