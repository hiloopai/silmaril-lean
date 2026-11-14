module

public import Silmaril.Machine.Link.FnSpec.Thms
public import Silmaril.X86.Ext.SymExec

/-!
# Proofs: the instruction triples of `_start` and `cmain` (ladder rung 12)

* `insn_triple`: a generic single-instruction triple. If from every state at `pc` holding the
  instruction bytes, whose fragment contains a part satisfying `X`, the open machine makes one
  step to `pc'` that changes nothing outside `X`'s part and `rip`, and the re-valued part
  satisfies `Y`, then `codePt ∗ ripPt pc ∗ X ⊢ codePt ∗ ripPt pc' ∗ Y` is a triple.
* Instances: `movI32_step` (`mov $imm32,%r32`), `movQ_step` (`mov %r64,%r64`), `movD_step`
  (`mov %r32,%r32`), `leaRsp_step` (`lea disp8(%rsp),%r64`), `xorSelf_step`
  (`xor %r32,%r32`), `storeI8Rsp_step` (`movb $imm8,disp8(%rsp)`).

Each run is a silmaril `Ext` step lemma (`stepOpt_of_loaded`, `stepOpt_mov_reg_mk`,
`stepOpt_alu_reg_mk`) or the `storeN` semantics, carried to the open machine through
`Ext8.stepOpt_of_ext` and `Open.step_of_ext8_stepOpt`, as R1's `aluI8_step`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Proofs.Machine.Link.FnSpec

/-- **A generic single-instruction triple.** -/
theorem insn_triple {pc pc' : Word} {bytes : List Byte} {X Y : SProp} (hne : bytes ≠ [])
    (h : ∀ (m : MState) (hX : Frag), X hX → Le hX (toFrag m) → m.core.rip = pc →
      Silmaril.X86.Ext.Loaded m.memory pc bytes →
      ∃ m', Silmaril.Machine.X86.Open.step m = some m' ∧ m'.core.rip = pc' ∧
        (∀ l, l ≠ .rip → hX l = none → toFrag m' l = toFrag m l) ∧
        Y (reval hX (toFrag m'))) :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ X) (codePt pc.toNat bytes ∗ ripPt pc' ∗ Y) := by
  apply Triple.of_local
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, hX, hripP, hXP, hlrip, hlX, hd2, rfl⟩ := sep_le hr1 hlr1
  have erip := ripPt_le hripP hlrip
  have fetch := fetchBytes_of_codePt hne hcP hlc
  obtain ⟨m', hstep, hrip', hsame, hY⟩ := h m hX hXP hlX erip fetch
  have hripS := ripPt_isSome hripP
  refine ⟨m', ⟨1, by simp [run, hstep]⟩, fun l hl0 => ?_, ?_⟩
  · obtain ⟨-, hrest⟩ := union_none hl0
    obtain ⟨n1, n2⟩ := union_none hrest
    exact hsame l (by rintro rfl; rw [n1] at hripS; cases hripS) n2
  have hcode : reval hc (toFrag m') = hc := by
    refine reval_agree hlc fun l hs => ?_
    have hn := isSome_of_disjoint (fun l => (hd1 l).symm) hs
    obtain ⟨n1, n2⟩ := union_none hn
    exact hsame l (by rintro rfl; rw [n1] at hripS; cases hripS) n2
  rw [reval_union', reval_union', hcode]
  refine ⟨_, _, ?_, rfl, hcP, _, _, ?_, rfl, ?_, hY⟩
  · rw [← hcode, ← reval_union']
    exact reval_disjoint' hd1 _
  · exact reval_disjoint' hd2 _
  · have := ripPt_reval' m' hripP
    rwa [hrip'] at this

/-- A register atom's fragment. -/
theorem regPt_frag {r : Reg} {v : Word} {h : Frag} (hp : regPt r v h) :
    h = Frag.single (.reg r) (.word v) := hp

/-- An `Ext` step from a loaded instruction is an open step. -/
theorem open_of_ext {m : MState} {pc : Word} {bytes : List Byte} {i : Silmaril.X86.Ext.Instr}
    {core : State} {memory : Memory} (hl : Silmaril.X86.Ext.Loaded m.memory pc bytes)
    (hrip : m.core.rip = pc) (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length))
    (hnr : i ≠ .ret) (hx : Silmaril.X86.Ext.exec i m.core m.memory = .ok core memory) :
    Silmaril.Machine.X86.Open.step m = some ⟨core, memory⟩ := by
  have hE := Silmaril.X86.Ext.stepOpt_of_loaded (exit := 0) (offset := 0) (len := bytes.length)
    hl (by rw [hrip]; simp) (by omega)
    (by rw [List.drop_zero, List.take_of_length_le (by omega)]; exact hdec) hnr hx
  exact Silmaril.Machine.X86.Open.step_of_ext8_stepOpt (Silmaril.X86.Ext8.stepOpt_of_ext hE)

/-- The instruction length decoded. -/
theorem len_of_dec {bytes : List Byte} {i : Silmaril.X86.Ext.Instr}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length)) : i.length = bytes.length :=
  (Silmaril.X86.Ext.decode_length hdec).1.symm

theorem ne_nil_of_dec {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, n)) : bytes ≠ [] := by
  rintro rfl; cases hdec

/-- Locations other than `rip`, register `r` and the flags agree after a register write. -/
theorem toFrag_write_other {m : MState} {c : State} {r : Reg}
    (hc : ∀ q, q ≠ r → c.read q = m.core.read q) (hf : c.flags = m.core.flags) {l : Loc}
    (h1 : l ≠ .rip) (h2 : l ≠ .reg r) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l := by
  cases l with
  | reg q =>
    have hq : q ≠ r := fun e => h2 (e ▸ rfl)
    simp only [toFrag]; rw [hc q hq]
  | rip => exact absurd rfl h1
  | flags => simp only [toFrag]; rw [hf]
  | mem a => rfl
  | regions => rfl

/-- Same, also allowing the flags to change. -/
theorem toFrag_write_other' {m : MState} {c : State} {r : Reg}
    (hc : ∀ q, q ≠ r → c.read q = m.core.read q) {l : Loc}
    (h1 : l ≠ .rip) (h2 : l ≠ .reg r) (h3 : l ≠ .flags) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l := by
  cases l with
  | reg q =>
    have hq : q ≠ r := fun e => h2 (e ▸ rfl)
    simp only [toFrag]; rw [hc q hq]
  | rip => exact absurd rfl h1
  | flags => exact absurd rfl h3
  | mem a => rfl
  | regions => rfl

theorem single_none {l l' : Loc} {v : Val} (h : Frag.single l v l' = none) : l' ≠ l := by
  rintro rfl; simp [Frag.single] at h

/-! ## `mov $imm32, %r32` -/

theorem movI32_step {pc pc' : Word} {bytes : List Byte} {r : Reg} {imm : BitVec 32}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.movI32 r imm, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ regAny r)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r (imm.setWidth 64)) := by
  have hne := ne_nil_of_dec hdec
  refine insn_triple hne fun m hX ⟨v, hXP⟩ hlX hrip hl => ?_
  have hlen := len_of_dec hdec
  set c : State := { Silmaril.X86.Ext.Sz.d.write m.core r imm with
    rip := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.movI32 r imm).length }
  have hx : Silmaril.X86.Ext.exec (.movI32 r imm) m.core m.memory = .ok c m.memory := rfl
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · rw [regPt_frag hXP] at h2
    exact toFrag_write_other (m := m) (c := c) (fun q hq => by
      show (Silmaril.X86.Ext.Sz.d.write m.core r imm).read q = _
      simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]) rfl h1 (single_none h2)
  · have := regPt_reval ⟨c, m.memory⟩ hXP
    have e : c.read r = imm.setWidth 64 := by
      show (Silmaril.X86.Ext.Sz.d.write m.core r imm).read r = _
      simp [Silmaril.X86.Ext.Sz.write, State.read_write_same]
    rwa [e] at this

/-- The memory operand `disp(%rsp)`. -/
def rspMem (disp : BitVec 32) : Silmaril.X86.Ext.Mem := ⟨.reg .rsp, none, disp, fun h => by cases h⟩

/-! ## Register moves -/

/-- Two register atoms, read back. -/
theorem two_regs {m : MState} {hX : Frag} {r₁ : Reg} {v₁ : Word} {Q : SProp}
    (hXP : (regPt r₁ v₁ ∗ Q) hX) (hlX : Le hX (toFrag m)) :
    ∃ h₁ h₂, Disjoint h₁ h₂ ∧ hX = union h₁ h₂ ∧ regPt r₁ v₁ h₁ ∧ Q h₂ ∧ Le h₂ (toFrag m) ∧
      m.core.read r₁ = v₁ := by
  obtain ⟨h₁, h₂, hP₁, hP₂, hl₁, hl₂, hd, rfl⟩ := sep_le hXP hlX
  exact ⟨h₁, h₂, hd, rfl, hP₁, hP₂, hl₂, regPt_le hP₁ hl₁⟩

/-- **`mov %src, %dst`** at size `sz` (64-bit, or 32-bit zero-extending). -/
theorem mov_step {pc pc' v : Word} {bytes : List Byte} {sz : Silmaril.X86.Ext.Sz}
    {dst src : Reg} (hne : dst ≠ src)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.mov sz (.reg dst) src, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt src v ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt src v ∗
        regPt dst ((v.setWidth sz.bits).setWidth 64)) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, ⟨w, hP₂⟩, -, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set c : State := { sz.write m.core dst (sz.read m.core src) with
    rip := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.mov sz (.reg dst) src).length }
  have hx : Silmaril.X86.Ext.exec (.mov sz (.reg dst) src) m.core m.memory = .ok c m.memory := rfl
  have hcr : ∀ q, q ≠ dst → c.read q = m.core.read q := fun q hq => by
    show (sz.write m.core dst _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨-, n2⟩ := union_none h2
    rw [regPt_frag hP₂] at n2
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n2)
  · rw [reval_union']
    refine ⟨_, _, reval_disjoint' hd _, rfl, ?_, ?_⟩
    · have := regPt_reval ⟨c, m.memory⟩ hP₁
      rwa [show c.read src = v by rw [hcr src (Ne.symm hne), ev]] at this
    · have := regPt_reval ⟨c, m.memory⟩ hP₂
      have e : c.read dst = (v.setWidth sz.bits).setWidth 64 := by
        show (sz.write m.core dst _).read dst = _
        simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, State.read_write_same, ev]
      rwa [e] at this

/-- **`lea disp(%rsp), %dst`** (64-bit). -/
theorem leaRsp_step {pc pc' s : Word} {bytes : List Byte} {dst : Reg} {disp : BitVec 32}
    (hne : dst ≠ .rsp)
    (hdec : Silmaril.X86.Ext.decode bytes =
      some (.lea .q dst (rspMem disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt .rsp s ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt .rsp s ∗
        regPt dst (s + disp.signExtend 64)) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, ⟨w, hP₂⟩, -, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.lea .q dst (rspMem disp)).length
  set c : State := { Silmaril.X86.Ext.Sz.q.write m.core dst
    ((((rspMem disp) : Silmaril.X86.Ext.Mem).addr m.core nx).setWidth 64) with rip := nx }
  have hx : Silmaril.X86.Ext.exec (.lea .q dst (rspMem disp)) m.core m.memory =
      .ok c m.memory := rfl
  have hcr : ∀ q, q ≠ dst → c.read q = m.core.read q := fun q hq => by
    show (Silmaril.X86.Ext.Sz.q.write m.core dst _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨-, n2⟩ := union_none h2
    rw [regPt_frag hP₂] at n2
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n2)
  · rw [reval_union']
    refine ⟨_, _, reval_disjoint' hd _, rfl, ?_, ?_⟩
    · have := regPt_reval ⟨c, m.memory⟩ hP₁
      rwa [show c.read .rsp = s by rw [hcr .rsp (Ne.symm hne), ev]] at this
    · have := regPt_reval ⟨c, m.memory⟩ hP₂
      have e : c.read dst = s + disp.signExtend 64 := by
        show (Silmaril.X86.Ext.Sz.q.write m.core dst _).read dst = _
        simp [Silmaril.X86.Ext.Sz.write, State.read_write_same, Silmaril.X86.Ext.Mem.addr,
          Silmaril.X86.Ext.Base.value, rspMem, ev]
      rwa [e] at this

/-- **`xor %r32, %r32`**: zero the register. -/
theorem xorSelf_step {pc pc' v : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.alu .d .xor (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r 0 ∗ flagsAny) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂, -, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  have hE := Silmaril.X86.Ext.stepOpt_alu_reg_mk (exit := 0) (offset := 0) (len := bytes.length)
    (result := 0) hl (by rw [hrip]; simp) (by omega)
    (by rw [List.drop_zero, List.take_of_length_le (by omega)]; exact hdec) (by decide)
    (by simp only [Silmaril.X86.Ext.AluOp.resultN]; rw [BitVec.xor_self]; rfl)
  have hstep := Silmaril.Machine.X86.Open.step_of_ext8_stepOpt (Silmaril.X86.Ext8.stepOpt_of_ext hE)
  set c : State := { m.core.write r 0 with
    flags := Silmaril.X86.Ext.AluOp.flagsN .xor (Silmaril.X86.Ext.Sz.d.read m.core r)
      (Silmaril.X86.Ext.Sz.d.read m.core r),
    rip := pc + BitVec.ofNat 64 (0 + bytes.length) }
  have hcr : ∀ q, q ≠ r → c.read q = m.core.read q := fun q hq => by
    show (m.core.write r 0).read q = _
    exact State.read_write_other _ _ _ _ hq
  refine ⟨⟨c, m.memory⟩, hstep, ?_, fun l h1 h2 => ?_, ?_⟩
  · show pc + _ = pc'; rw [Nat.zero_add, hnext]
  · obtain ⟨n1, n2⟩ := union_none h2
    rw [regPt_frag hP₁] at n1
    refine toFrag_write_other' (m := m) (c := c) hcr h1 (single_none n1) ?_
    rintro rfl; have := flagsAny_isSome hP₂; rw [n2] at this; cases this
  · rw [reval_union']
    refine ⟨_, _, reval_disjoint' hd _, rfl, ?_, flagsAny_reval _ hP₂⟩
    have := regPt_reval ⟨c, m.memory⟩ hP₁
    rwa [show c.read r = 0 from State.read_write_same _ _ _] at this

/-! ## A byte store into the stack -/

/-- A one-byte block, re-valued after a store: the byte now there. -/
theorem blockAny1_reval {a : Nat} {b : Byte} {h : Frag} {m : MState} (hp : blockAny a 1 h)
    (hb : m.memory.bytes.get? a = some b) (hn : RW (permsAt m.memory a)) :
    bytesPt a [b] (reval h (toFrag m)) := by
  obtain ⟨h1, h2, hd, rfl, ⟨ha, c, -, rfl⟩, rfl⟩ := hp
  refine ⟨Frag.single (.mem a) (.cell ⟨some b, permsAt m.memory a⟩), Frag.empty,
    fun _ => .inr rfl, ?_, ⟨ha, _, hn, rfl⟩, rfl⟩
  funext l
  by_cases e : l = .mem a
  · subst e; simp [reval, union, Frag.single, toFrag]; simpa using hb
  · simp [reval, union, Frag.single, Frag.empty, e]

/-- **`movb $imm8, disp(%rsp)`**: store one byte into an owned stack byte. -/
theorem storeI8Rsp_step {pc pc' s : Word} {bytes : List Byte} {disp : BitVec 32} {imm : BitVec 8}
    {a : Nat} (ha : (s + disp.signExtend 64).toNat = a)
    (hdec : Silmaril.X86.Ext.decode bytes =
      some (.movI8 (.mem (rspMem disp)) imm, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt .rsp s ∗ blockAny a 1)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt .rsp s ∗ bytesPt a [imm]) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂, hl₂, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.movI8 (.mem (rspMem disp)) imm).length
  have haddr : (((rspMem disp) : Silmaril.X86.Ext.Mem).addr m.core nx) =
      s + disp.signExtend 64 := by
    simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value, rspMem, ev]
  have perm := permitted_of_blockAny (.inr rfl) (by omega) hP₂ hl₂
  obtain ⟨after, hst, stored⟩ := Silmaril.X86.Ext.storeN_isSome (k := 1) (v := imm.setWidth 64)
    (memory := m.memory) (address := s + disp.signExtend 64) (by rw [ha]; exact perm)
  have hx : Silmaril.X86.Ext.exec (.movI8 (.mem (rspMem disp)) imm) m.core m.memory =
      .ok { m.core with rip := nx } after := by
    show Silmaril.X86.Ext.retire nx (Silmaril.X86.Ext.writeRM8 _ imm m.core m.memory nx) = _
    simp only [Silmaril.X86.Ext.writeRM8, haddr, hst, Option.map_some]
    rfl
  rw [ha] at stored
  have hregions : after.regions = m.memory.regions := stored.regions
  have hperms : ∀ b, permsAt after b = permsAt m.memory b := by
    intro b; simp [permsAt, Silmaril.Process.Memory.permits, hregions]
  have hbyte : after.bytes.get? a = some imm := by
    have := stored.installed 0 (by simp [Silmaril.X86.Ext.leBytes])
    simp only [Nat.add_zero] at this
    rw [this]
    simp [Silmaril.X86.Ext.leBytes, Silmaril.Machine.LittleEndian.wordByte]
  have hdom : (h₂ (.mem a)).isSome := blockAny_dom hP₂ 0 (by omega)
  refine ⟨⟨{ m.core with rip := nx }, after⟩, open_of_ext hl hrip hdec (by simp) hx, ?_,
    fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨n1, n2⟩ := union_none h2
    rw [regPt_frag hP₁] at n1
    cases l with
    | reg q => rfl
    | rip => exact absurd rfl h1
    | flags => rfl
    | mem b =>
      have hb : b ≠ a := by rintro rfl; rw [n2] at hdom; cases hdom
      simp only [toFrag]
      rw [hperms b, stored.frame.2 b (by simp [Silmaril.X86.Ext.leBytes]; omega)]
    | regions => simp only [toFrag]; rw [hregions]
  · rw [reval_union']
    refine ⟨_, _, reval_disjoint' hd _, rfl, ?_, ?_⟩
    · have := regPt_reval ⟨{ m.core with rip := nx }, after⟩ hP₁
      rwa [show ({ m.core with rip := nx } : State).read .rsp = s from ev] at this
    · exact blockAny1_reval hP₂ hbyte (by rw [hperms]; simpa using (blockAny_le hP₂ hl₂ 0 (by omega)).2)

end Silmaril.Proofs.Machine.Process.LibMiniClient
