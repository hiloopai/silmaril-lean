module

public import Silmaril.Libc.X86Alloc.Insn.Defs
public import Silmaril.X86.Sep.Insn.Thms
import Silmaril.Proofs.X86.Sep.Algebra

/-!
# Proofs: instruction triples of the allocator ladder

Generic register-only triples (`reg1_step`, `reg2_step`, `mov2_step`): the caller gives the
`Ext.exec` result for any core holding the owned registers, and the frame and re-valuation
conditions of `Silmaril.X86.Sep.Insn.insn_triple` are discharged once here. RIP-relative
eight-byte loads and stores (`loadRip_step`, `storeRip_step`) follow silmaril's `loadQ_step` and
`storeQ_step` without the base register.
-/

@[expose] public section

namespace Silmaril.Raw.Libc.X86Alloc.Insn

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Mem Sz)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Insn
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Libc.X86Alloc.Insn

variable {σ : Type} {I : Isa σ}

/-- **A one-register instruction with flags.** -/
theorem reg1_step (E : Silmaril.X86.Open.isa.Extends I)
    {pc pc' a a' : Word} {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {r : Reg} {f : Flags}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length)) (hnr : i ≠ .ret)
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc')
    (hx : ∀ (s : State) (mem : Memory), s.read r = a → ∃ s' : State,
      Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = s.rip + BitVec.ofNat 64 i.length ∧
      s'.read r = a' ∧ (∀ q, q ≠ r → s'.read q = s.read q) ∧ s'.flags = f) :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r a ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r a' ∗ flagsPt f) := by
  refine insn_triple E (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂, -, ev⟩ := two_regs hXP hlX
  obtain ⟨c, hx', hcrip, hcr, hco, hcf⟩ := hx m.core m.memory ev
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec hnr hx', ?_, fun l h1 h2 => ?_, ?_⟩
  · show c.rip = pc'; rw [hcrip, hrip, len_of_dec hdec, hnext]
  · obtain ⟨n1, n2⟩ := union_none h2
    rw [regPt_frag hP₁] at n1
    refine toFrag_write_other' (m := m) (c := c) hco h1 (single_none n1) ?_
    rintro rfl
    have := flagsAny_dom hP₂; rw [n2] at this; cases this
  · rw [Frag.reval_union]
    refine ⟨_, _, Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
    · have := regPt_reval ⟨c, m.memory⟩ hP₁; rwa [show c.read r = a' from hcr] at this
    · have := flagsAny_reval_exact ⟨c, m.memory⟩ hP₂; rwa [hcf] at this

/-- **A two-register instruction with flags**: `r` is written, `q` is only read. -/
theorem reg2_step (E : Silmaril.X86.Open.isa.Extends I)
    {pc pc' a a' b : Word} {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {r q : Reg}
    {f : Flags} (hrq : r ≠ q)
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length)) (hnr : i ≠ .ret)
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc')
    (hx : ∀ (s : State) (mem : Memory), s.read r = a → s.read q = b → ∃ s' : State,
      Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = s.rip + BitVec.ofNat 64 i.length ∧
      s'.read r = a' ∧ (∀ t, t ≠ r → s'.read t = s.read t) ∧ s'.flags = f) :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r a ∗ regPt q b ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r a' ∗ regPt q b ∗ flagsPt f) := by
  refine insn_triple E (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, r₁, hd, rfl, hP₁, hR, hlR, ea⟩ := two_regs hXP hlX
  obtain ⟨h₂, h₃, hd₂, rfl, hP₂, hP₃, -, eb⟩ := two_regs hR hlR
  obtain ⟨c, hx', hcrip, hcr, hco, hcf⟩ := hx m.core m.memory ea eb
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec hnr hx', ?_, fun l h1 h2 => ?_, ?_⟩
  · show c.rip = pc'; rw [hcrip, hrip, len_of_dec hdec, hnext]
  · obtain ⟨n1, n2⟩ := union_none h2
    obtain ⟨-, n3⟩ := union_none n2
    rw [regPt_frag hP₁] at n1
    refine toFrag_write_other' (m := m) (c := c) hco h1 (single_none n1) ?_
    rintro rfl
    have := flagsAny_dom hP₃; rw [n3] at this; cases this
  · rw [Frag.reval_union, Frag.reval_union]
    refine ⟨_, _, ?_, rfl, ?_, _, _, Frag.reval_disjoint hd₂ _, rfl, ?_, ?_⟩
    · rw [← Frag.reval_union]; exact Frag.reval_disjoint hd _
    · have := regPt_reval ⟨c, m.memory⟩ hP₁; rwa [show c.read r = a' from hcr] at this
    · have := regPt_reval ⟨c, m.memory⟩ hP₂
      rwa [show c.read q = b by rw [hco q (Ne.symm hrq), eb]] at this
    · have := flagsAny_reval_exact ⟨c, m.memory⟩ hP₃; rwa [hcf] at this

/-- **A register move**: `r` is written from `q`; the flags are untouched. -/
theorem mov2_step (E : Silmaril.X86.Open.isa.Extends I)
    {pc pc' a a' b : Word} {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {r q : Reg}
    (hrq : r ≠ q)
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length)) (hnr : i ≠ .ret)
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc')
    (hx : ∀ (s : State) (mem : Memory), s.read r = a → s.read q = b → ∃ s' : State,
      Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = s.rip + BitVec.ofNat 64 i.length ∧
      s'.read r = a' ∧ (∀ t, t ≠ r → s'.read t = s.read t) ∧ s'.flags = s.flags) :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r a ∗ regPt q b)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r a' ∗ regPt q b) := by
  refine insn_triple E (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂, hl₂, ea⟩ := two_regs hXP hlX
  have eb := regPt_le hP₂ hl₂
  obtain ⟨c, hx', hcrip, hcr, hco, hcf⟩ := hx m.core m.memory ea eb
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec hnr hx', ?_, fun l h1 h2 => ?_, ?_⟩
  · show c.rip = pc'; rw [hcrip, hrip, len_of_dec hdec, hnext]
  · obtain ⟨n1, -⟩ := union_none h2
    rw [regPt_frag hP₁] at n1
    exact toFrag_write_other (m := m) (c := c) hco hcf h1 (single_none n1)
  · rw [Frag.reval_union]
    refine ⟨_, _, Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
    · have := regPt_reval ⟨c, m.memory⟩ hP₁; rwa [show c.read r = a' from hcr] at this
    · have := regPt_reval ⟨c, m.memory⟩ hP₂
      rwa [show c.read q = b by rw [hco q (Ne.symm hrq), eb]] at this

theorem ripMem_addr (disp : BitVec 32) (s : State) (next : Word) :
    (ripMem disp).addr s next = next + disp.signExtend 64 := by
  simp [Mem.addr, ripMem, Silmaril.X86.Ext.Base.value]

/-- **`mov disp(%rip), %dst`** (64-bit load of an owned word). -/
theorem loadRip_step (E : Silmaril.X86.Open.isa.Extends I)
    {pc pc' w : Word} {bytes : List Byte} {dst : Reg} {disp : BitVec 32} {a : Nat}
    (ha : (pc' + disp.signExtend 64).toNat = a)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.load .q dst (ripMem disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ wordPt a w ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ wordPt a w ∗ regPt dst w) := by
  refine insn_triple E (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₂, h₃, hP₂, ⟨u, hP₃⟩, hl₂, -, hd₂, rfl⟩ := sep_le hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.load .q dst (ripMem disp)).length
  have hnx : nx = pc' := by
    show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  have hload : Silmaril.X86.Ext.loadN m.memory ((ripMem disp).addr m.core nx) 8 = some w := by
    rw [ripMem_addr, hnx]; exact loadN_of_wordPt ha hP₂ hl₂
  set c : State := { Sz.q.write m.core dst w with rip := nx }
  have hx : Silmaril.X86.Ext.exec (.load .q dst (ripMem disp)) m.core m.memory =
      .ok c m.memory := by
    show Silmaril.X86.Ext.retire nx ((Silmaril.X86.Ext.readRM .q (.mem (ripMem disp)) m.core
      m.memory nx).map fun v => (Sz.q.write m.core dst v, m.memory)) = _
    simp only [Silmaril.X86.Ext.readRM, Sz.bytes, hload, Option.map_some]
    rfl
  have hcr : ∀ q, q ≠ dst → c.read q = m.core.read q := fun q hq => by
    show (Sz.q.write m.core dst _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, hnx, fun l h1 h2 => ?_, ?_⟩
  · obtain ⟨-, n3⟩ := union_none h2
    rw [regPt_frag hP₃] at n3
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n3)
  · have hag : ∀ l, (h₂ l).isSome → toFrag ⟨c, m.memory⟩ l = toFrag m l := by
      intro l hs
      have n3 : h₃ l = none := isSome_of_disjoint (fun l => (hd₂ l).symm) hs
      rw [regPt_frag hP₃] at n3
      refine toFrag_write_other (m := m) (c := c) hcr rfl ?_ (single_none n3)
      rintro rfl
      rw [bytesAt_nonmem hP₂ .rip (fun _ => by simp)] at hs
      cases hs
    rw [Frag.reval_union]
    refine ⟨_, _, Frag.reval_disjoint hd₂ _, rfl, ?_, ?_⟩
    · rw [reval_agree hl₂ hag]; exact hP₂
    · have := regPt_reval ⟨c, m.memory⟩ hP₃
      have e : c.read dst = w := by
        show (Sz.q.write m.core dst w).read dst = _
        simp [Silmaril.X86.Ext.Sz.write, State.read_write_same]
      rwa [e] at this

/-- **`mov %src, disp(%rip)`** (64-bit store into an owned eight-byte block). -/
theorem storeRip_step (E : Silmaril.X86.Open.isa.Extends I)
    {pc pc' v : Word} {bytes : List Byte} {src : Reg} {disp : BitVec 32} {a : Nat}
    (ha : (pc' + disp.signExtend 64).toNat = a)
    (hdec : Silmaril.X86.Ext.decode bytes =
      some (.mov .q (.mem (ripMem disp)) src, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt src v ∗ blockAny a 8)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt src v ∗ wordPt a v) := by
  refine insn_triple E (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₂, h₃, hd₂, rfl, hP₂, hP₃, hl₃, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.mov .q (.mem (ripMem disp)) src).length
  have hnx : nx = pc' := by
    show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  have perm := permitted_of_blockAny (.inr rfl) (by omega) hP₃ hl₃
  obtain ⟨after, hst, stored⟩ := Silmaril.X86.Ext.storeN_isSome (k := 8) (v := v)
    (memory := m.memory) (address := pc' + disp.signExtend 64) (by rw [ha]; exact perm)
  have hx : Silmaril.X86.Ext.exec (.mov .q (.mem (ripMem disp)) src) m.core m.memory =
      .ok { m.core with rip := nx } after := by
    show Silmaril.X86.Ext.retire nx (Silmaril.X86.Ext.writeRM .q (.mem (ripMem disp))
      (Sz.q.read m.core src) m.core m.memory nx) = _
    have hv : (Sz.q.read m.core src).setWidth 64 = v := by
      rw [← ev]; exact BitVec.setWidth_eq _
    simp only [Silmaril.X86.Ext.writeRM, ripMem_addr, hnx, Sz.bytes, hv, hst, Option.map_some]
    rfl
  rw [ha] at stored
  have hregions : after.regions = m.memory.regions := stored.frame.1
  have hperms : ∀ x, permsAt after x = permsAt m.memory x := by
    intro x; simp [permsAt, Silmaril.Process.Memory.permits, hregions]
  have outside : ∀ x, h₃ (.mem x) = none → toFrag ⟨{ m.core with rip := nx }, after⟩ (.mem x) =
      toFrag m (.mem x) := by
    intro x n3
    have hx' : x < a ∨ a + (Silmaril.X86.Ext.leBytes v 8).length ≤ x := by
      rw [Silmaril.X86.Ext.length_leBytes]
      by_contra hc
      have := blockAny_dom hP₃ (x - a) (by omega)
      rw [show a + (x - a) = x by omega, n3] at this; cases this
    simp only [toFrag]
    rw [hperms x, stored.frame.2 x hx']
  refine ⟨⟨{ m.core with rip := nx }, after⟩, open_of_ext hl hrip hdec (by simp) hx, hnx,
    fun l h1 h2 => ?_, ?_⟩
  · obtain ⟨-, n3⟩ := union_none h2
    cases l with
    | reg q => rfl
    | rip => exact absurd rfl h1
    | flags => rfl
    | mem x => exact outside x n3
    | regions => simp only [toFrag]; rw [hregions]
  · rw [Frag.reval_union]
    refine ⟨_, _, Frag.reval_disjoint hd₂ _, rfl, ?_, ?_⟩
    · have e : reval h₂ (toFrag ⟨{ m.core with rip := nx }, after⟩) = reval h₂ (toFrag m) := by
        rw [regPt_frag hP₂]
        funext l
        by_cases e : l = .reg src
        · subst e; simp [reval, Frag.single, toFrag]
        · simp [reval, Frag.single, e]
      rw [e]
      have := regPt_reval m hP₂
      rwa [ev] at this
    · refine Silmaril.Proofs.X86.Sep.blockAny_reval_bytes hP₃ (by simp) (fun i hi => ⟨?_, ?_⟩)
      · have := stored.installed i (by simpa using hi)
        rw [this]
        simp [Silmaril.X86.Ext.leBytes_eight]
      · rw [hperms]
        exact (blockAny_le hP₃ hl₃ i (by simpa using hi)).2

/-- **`mov disp(%r), %r`** (64-bit load whose base is also its destination). -/
theorem loadSelf_step (E : Silmaril.X86.Open.isa.Extends I)
    {pc pc' b w : Word} {bytes : List Byte} {r : Reg} {disp : BitVec 32} {a : Nat}
    (ha : (b + disp.signExtend 64).toNat = a)
    (hdec : Silmaril.X86.Ext.decode bytes =
      some (.load .q r (Silmaril.X86.Sep.Insn.memAt r disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ wordPt a w ∗ regPt r b)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ wordPt a w ∗ regPt r w) := by
  refine insn_triple E (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₂, h₃, hP₂, hP₃, hl₂, hl₃, hd₂, rfl⟩ := sep_le hXP hlX
  have eb := regPt_le hP₃ hl₃
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.load .q r (Silmaril.X86.Sep.Insn.memAt r disp)).length
  have hnx : nx = pc' := by
    show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  have hload : Silmaril.X86.Ext.loadN m.memory
      ((Silmaril.X86.Sep.Insn.memAt r disp).addr m.core nx) 8 = some w := by
    rw [memAt_addr, eb]; exact loadN_of_wordPt ha hP₂ hl₂
  set c : State := { Sz.q.write m.core r w with rip := nx }
  have hx : Silmaril.X86.Ext.exec (.load .q r (Silmaril.X86.Sep.Insn.memAt r disp)) m.core m.memory =
      .ok c m.memory := by
    show Silmaril.X86.Ext.retire nx ((Silmaril.X86.Ext.readRM .q
      (.mem (Silmaril.X86.Sep.Insn.memAt r disp)) m.core m.memory nx).map fun v =>
        (Sz.q.write m.core r v, m.memory)) = _
    simp only [Silmaril.X86.Ext.readRM, Sz.bytes, hload, Option.map_some]
    rfl
  have hcr : ∀ q, q ≠ r → c.read q = m.core.read q := fun q hq => by
    show (Sz.q.write m.core r _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, hnx, fun l h1 h2 => ?_, ?_⟩
  · obtain ⟨-, n3⟩ := union_none h2
    rw [regPt_frag hP₃] at n3
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n3)
  · have hag : ∀ l, (h₂ l).isSome → toFrag ⟨c, m.memory⟩ l = toFrag m l := by
      intro l hs
      have n3 : h₃ l = none := isSome_of_disjoint (fun l => (hd₂ l).symm) hs
      rw [regPt_frag hP₃] at n3
      refine toFrag_write_other (m := m) (c := c) hcr rfl ?_ (single_none n3)
      rintro rfl
      rw [bytesAt_nonmem hP₂ .rip (fun _ => by simp)] at hs
      cases hs
    rw [Frag.reval_union]
    refine ⟨_, _, Frag.reval_disjoint hd₂ _, rfl, ?_, ?_⟩
    · rw [reval_agree hl₂ hag]; exact hP₂
    · have := regPt_reval ⟨c, m.memory⟩ hP₃
      have e : c.read r = w := by
        show (Sz.q.write m.core r w).read r = _
        simp [Silmaril.X86.Ext.Sz.write, State.read_write_same]
      rwa [e] at this

end Silmaril.Raw.Libc.X86Alloc.Insn
