module

public import Silmaril.Raw.Libc.X86Alloc.Whole
import Silmaril.X86.Sep.Thms

/-!
# Proofs: whole-frame steps with one memory operand

`c_whole` (`Whole.lean`) covers instructions that touch only registers and flags. Here the
same canonical frame gets **one memory operand**, given as the first memory atom:

* `c_rd`: an instruction that reads the owned bytes `bytesPt a bs` (memory unchanged);
* `c_wr`: an instruction that stores `n` bytes of a value `v` into the owned block
  `blockAny a n`, which afterwards holds `leBytes v n`.

The caller gives the `Ext.exec` result on every core with the frame's registers and flags (and,
for `c_rd`, on every memory where the bytes read back as `bs`; for `c_wr`, for every memory the
store produces). Each instruction form of the allocators is then a short `simp` over
`Ext.exec` (`c_cmpM`, `c_cmpB`, `c_addM`, `c_storeM`, `c_movI8M`, `c_movIM`), and the
register-only forms not in `Frame`/`Whole` come from `c_whole` (`c_jcc32_taken`,
`c_jcc32_not`, `c_cmov`, `c_aluI`, `c_shr`, `c_movIQ`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.MemStep

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Mem Sz)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Insn
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Raw.Libc.X86Alloc.Frame
open Silmaril.Raw.Libc.X86Alloc.Whole

variable {σ : Type} {I : Isa σ}

/-- **A register-and-flags instruction that reads one owned byte list.** -/
theorem c_rd (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
    {pc pc' : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)
    {i : Silmaril.X86.Ext.Instr} {f g : Reg → Word} {fl fl' : Flags} {a : Nat} {bs : List Byte}
    (hne : bs ≠ []) {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) (hnr : i ≠ .ret)
    (hx : ∀ (s : State) (mem : Memory), s.rip = pc → (∀ q ∈ frameRegs, s.read q = f q) →
      s.flags = fl → mem.readBytes a bs.length = some bs → ∃ s' : State,
        Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = pc' ∧
        (∀ q ∈ frameRegs, s'.read q = g q) ∧ (∀ q, q ∉ frameRegs → s'.read q = s.read q) ∧
        s'.flags = fl') :
    SPEC I (codePt b code) (St pc f fl (bytesPt a bs ∗ M)) (St pc' g fl' (bytesPt a bs ∗ M)) := by
  have hl : ((code.drop o).take k).length = k := by simp; omega
  have hdec' : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (i, ((code.drop o).take k).length) := by rw [hl]; exact hdec
  have t : Triple I (codePt pc.toNat ((code.drop o).take k) ∗ ripPt pc ∗
      ((regsPt frameRegs f ∗ flagsPt fl) ∗ bytesPt a bs))
      (codePt pc.toNat ((code.drop o).take k) ∗ ripPt pc' ∗
        ((regsPt frameRegs g ∗ flagsPt fl') ∗ bytesPt a bs)) := by
    refine insn_triple E (ne_nil_of_dec hdec') fun m hX hXP hlX hrip hld => ?_
    obtain ⟨h₁, h₂, hP₁, hP₂, hl₁, hl₂, hd, rfl⟩ := sep_le hXP hlX
    obtain ⟨h₃, h₄, hP₃, hP₄, hl₃, hl₄, hd', rfl⟩ := sep_le hP₁ hl₁
    obtain ⟨c, hxc, hcrip, hcg, hco, hcf⟩ :=
      hx m.core m.memory hrip (regsPt_le hP₃ hl₃) (flagsPt_le hP₄ hl₄)
        (readBytes_of_bytesPt hne hP₂ hl₂)
    refine ⟨⟨c, m.memory⟩, open_of_ext hld hrip hdec' hnr hxc, hcrip, fun l h1 h2 => ?_, ?_⟩
    · obtain ⟨n12, -⟩ := union_none h2
      obtain ⟨n1, n2⟩ := union_none n12
      cases l with
      | reg q =>
        by_cases hq : q ∈ frameRegs
        · exfalso
          have hp1 : (h₃ (.reg q)).isSome := regsPt_own hP₃ hq
          rw [n1] at hp1; cases hp1
        · show some (Val.word (c.read q)) = some (Val.word (m.core.read q))
          rw [hco q hq]
      | rip => exact absurd rfl h1
      | flags =>
        have := flagsAny_dom ⟨fl, hP₄⟩; rw [n2] at this; cases this
      | mem a => rfl
      | regions => rfl
    · rw [Frag.reval_union]
      refine ⟨_, _, Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
      · rw [Frag.reval_union]
        refine ⟨_, _, Frag.reval_disjoint hd' _, rfl, regsPt_reval hP₃ hcg, ?_⟩
        have := flagsAny_reval_exact ⟨c, m.memory⟩ ⟨fl, hP₄⟩; rwa [hcf] at this
      · have hag : ∀ l, (h₂ l).isSome → toFrag ⟨c, m.memory⟩ l = toFrag m l := by
          intro l hs
          cases l with
          | mem x => rfl
          | _ => rw [bytesAt_nonmem hP₂ _ (fun _ => by simp)] at hs; cases hs
        rw [reval_agree hl₂ hag]; exact hP₂
  exact c_step hpc hfit (R := M) t (entails_of_eq (by simp only [St]; ac_rfl))
    (entails_of_eq (by simp only [St]; ac_rfl))

/-- **A register-and-flags instruction that stores `n` bytes of `v` into one owned block.** -/
theorem c_wr (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
    {pc pc' : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)
    {i : Silmaril.X86.Ext.Instr} {f g : Reg → Word} {fl fl' : Flags} {a n : Nat} (hn : 0 < n)
    {v : Word} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) (hnr : i ≠ .ret)
    (hx : ∀ (s : State) (mem : Memory), s.rip = pc → (∀ q ∈ frameRegs, s.read q = f q) →
      s.flags = fl → ∃ A : Word, A.toNat = a ∧ ∃ s' : State,
        (∀ after, Silmaril.X86.Ext.storeN mem A n v = some after →
          Silmaril.X86.Ext.exec i s mem = .ok s' after) ∧ s'.rip = pc' ∧
        (∀ q ∈ frameRegs, s'.read q = g q) ∧ (∀ q, q ∉ frameRegs → s'.read q = s.read q) ∧
        s'.flags = fl') :
    SPEC I (codePt b code) (St pc f fl (blockAny a n ∗ M))
      (St pc' g fl' (bytesPt a (Silmaril.X86.Ext.leBytes v n) ∗ M)) := by
  have hl : ((code.drop o).take k).length = k := by simp; omega
  have hdec' : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (i, ((code.drop o).take k).length) := by rw [hl]; exact hdec
  have t : Triple I (codePt pc.toNat ((code.drop o).take k) ∗ ripPt pc ∗
      ((regsPt frameRegs f ∗ flagsPt fl) ∗ blockAny a n))
      (codePt pc.toNat ((code.drop o).take k) ∗ ripPt pc' ∗
        ((regsPt frameRegs g ∗ flagsPt fl') ∗ bytesPt a (Silmaril.X86.Ext.leBytes v n))) := by
    refine insn_triple E (ne_nil_of_dec hdec') fun m hX hXP hlX hrip hld => ?_
    obtain ⟨h₁, h₂, hP₁, hP₂, hl₁, hl₂, hd, rfl⟩ := sep_le hXP hlX
    obtain ⟨h₃, h₄, hP₃, hP₄, hl₃, hl₄, hd', rfl⟩ := sep_le hP₁ hl₁
    obtain ⟨A, hA, c, hxc, hcrip, hcg, hco, hcf⟩ :=
      hx m.core m.memory hrip (regsPt_le hP₃ hl₃) (flagsPt_le hP₄ hl₄)
    have perm := permitted_of_blockAny (.inr rfl) hn hP₂ hl₂
    obtain ⟨after, hst, stored⟩ := Silmaril.X86.Ext.storeN_isSome (k := n) (v := v)
      (memory := m.memory) (address := A) (by rw [hA]; exact perm)
    rw [hA] at stored
    have hregions : after.regions = m.memory.regions := stored.frame.1
    have hperms : ∀ x, permsAt after x = permsAt m.memory x := by
      intro x; simp [permsAt, Silmaril.Process.Memory.permits, hregions]
    refine ⟨⟨c, after⟩, open_of_ext hld hrip hdec' hnr (hxc after hst), hcrip,
      fun l h1 h2 => ?_, ?_⟩
    · obtain ⟨n12, n5⟩ := union_none h2
      obtain ⟨n1, n2⟩ := union_none n12
      cases l with
      | reg q =>
        by_cases hq : q ∈ frameRegs
        · exfalso
          have hp1 : (h₃ (.reg q)).isSome := regsPt_own hP₃ hq
          rw [n1] at hp1; cases hp1
        · show some (Val.word (c.read q)) = some (Val.word (m.core.read q))
          rw [hco q hq]
      | rip => exact absurd rfl h1
      | flags =>
        have := flagsAny_dom ⟨fl, hP₄⟩; rw [n2] at this; cases this
      | mem x =>
        have hx' : x < a ∨ a + (Silmaril.X86.Ext.leBytes v n).length ≤ x := by
          rw [Silmaril.X86.Ext.length_leBytes]
          by_contra hc
          have := blockAny_dom hP₂ (x - a) (by omega)
          rw [show a + (x - a) = x by omega, n5] at this; cases this
        simp only [toFrag]
        rw [hperms x, stored.frame.2 x hx']
      | regions => simp only [toFrag]; rw [hregions]
    · rw [Frag.reval_union]
      refine ⟨_, _, Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
      · rw [Frag.reval_union]
        refine ⟨_, _, Frag.reval_disjoint hd' _, rfl, regsPt_reval hP₃ hcg, ?_⟩
        have := flagsAny_reval_exact ⟨c, after⟩ ⟨fl, hP₄⟩; rwa [hcf] at this
      · refine Silmaril.Proofs.X86.Sep.blockAny_reval_bytes hP₂ (by simp)
          (fun j hj => ⟨stored.installed j hj, ?_⟩)
        rw [hperms]
        exact (blockAny_le hP₂ hl₂ j (by simpa using hj)).2
  exact c_step hpc hfit (R := M) t (entails_of_eq (by simp only [St]; ac_rfl))
    (entails_of_eq (by simp only [St]; ac_rfl))

end Silmaril.Raw.Libc.X86Alloc.MemStep
