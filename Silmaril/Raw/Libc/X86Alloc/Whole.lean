module

public import Silmaril.Raw.Libc.X86Alloc.Frame
import Silmaril.X86.Sep.Thms

/-!
# Proofs: the whole-register-file step

`c_whole`: any instruction that touches only registers and flags is a step of the canonical frame,
given its `Ext.exec` result on every core holding the frame's registers `f` and flags `fl`. It
covers every register-only form at once (three-operand `lea`, `cmp $imm32`, `jmp rel8`, …), so a
new compiler idiom needs no new triple.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Whole

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Insn
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Raw.Libc.X86Alloc.Frame

variable {σ : Type} {I : Isa σ}

theorem regsPt_le : ∀ {rs : List Reg} {f : Reg → Word} {h : Frag} {m : MState},
    regsPt rs f h → Le h (toFrag m) → ∀ q ∈ rs, m.core.read q = f q
  | [], _, _, _, _, _, q, hq => absurd hq List.not_mem_nil
  | r :: rs, f, h, m, hp, hl, q, hq => by
    obtain ⟨h₁, h₂, hP₁, hP₂, hl₁, hl₂, -, -⟩ := sep_le hp hl
    rcases List.mem_cons.1 hq with rfl | hq
    · exact regPt_le hP₁ hl₁
    · exact regsPt_le hP₂ hl₂ q hq

theorem regsPt_dom : ∀ {rs : List Reg} {f : Reg → Word} {h : Frag},
    regsPt rs f h → ∀ l, (h l).isSome → ∃ q ∈ rs, l = .reg q
  | [], _, h, hp, l, hs => by
    rw [show h = Frag.empty from hp] at hs; simp [Frag.empty] at hs
  | r :: rs, f, h, hp, l, hs => by
    obtain ⟨h₁, h₂, -, rfl, hP₁, hP₂⟩ := hp
    simp only [union] at hs
    cases e : h₁ l with
    | some v =>
      rw [show h₁ = Frag.single (.reg r) (.word (f r)) from hP₁] at e
      simp only [Frag.single] at e
      split at e
      · exact ⟨r, List.mem_cons_self, by assumption⟩
      · cases e
    | none =>
      rw [e] at hs
      obtain ⟨q, hq, rfl⟩ := regsPt_dom hP₂ l hs
      exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩

theorem regsPt_reval : ∀ {rs : List Reg} {f g : Reg → Word} {h : Frag} {m : MState},
    regsPt rs f h → (∀ q ∈ rs, m.core.read q = g q) → regsPt rs g (reval h (toFrag m))
  | [], _, _, h, _, hp, _ => by
    rw [show h = Frag.empty from hp]; exact Silmaril.Proofs.X86.Sep.Frag.reval_empty _
  | r :: rs, f, g, h, m, hp, hg => by
    obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂⟩ := hp
    rw [Frag.reval_union]
    refine ⟨_, _, Frag.reval_disjoint hd _, rfl, ?_,
      regsPt_reval hP₂ fun q hq => hg q (List.mem_cons_of_mem _ hq)⟩
    have := regPt_reval m hP₁
    rwa [hg r List.mem_cons_self] at this

theorem regsPt_own : ∀ {rs : List Reg} {f : Reg → Word} {h : Frag} {q : Reg},
    regsPt rs f h → q ∈ rs → (h (.reg q)).isSome
  | [], _, _, _, _, hq => absurd hq List.not_mem_nil
  | r :: rs, f, h, q, hp, hq => by
    obtain ⟨h₁, h₂, -, rfl, hP₁, hP₂⟩ := hp
    simp only [union]
    by_cases e : q = r
    · subst e; rw [show h₁ = Frag.single (.reg q) (.word (f q)) from hP₁]; simp [Frag.single]
    · have : h₁ (.reg q) = none := by
        rw [show h₁ = Frag.single (.reg r) (.word (f r)) from hP₁]
        simp [Frag.single, e]
      rw [this]
      exact regsPt_own hP₂ ((List.mem_cons.1 hq).resolve_left e)

/-- **A register-and-flags instruction on the canonical frame.** -/
theorem c_whole (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
    {pc pc' : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)
    {i : Silmaril.X86.Ext.Instr} {f g : Reg → Word} {fl fl' : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) (hnr : i ≠ .ret)
    (hx : ∀ (s : State) (mem : Silmaril.Process.Memory), s.rip = pc →
      (∀ q ∈ frameRegs, s.read q = f q) → s.flags = fl → ∃ s' : State, Silmaril.X86.Ext.exec i s mem = .ok s' mem ∧ s'.rip = pc' ∧
        (∀ q ∈ frameRegs, s'.read q = g q) ∧ (∀ q, q ∉ frameRegs → s'.read q = s.read q) ∧
        s'.flags = fl') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' g fl' M) := by
  have hl : ((code.drop o).take k).length = k := by simp; omega
  have hdec' : Silmaril.X86.Ext.decode ((code.drop o).take k) =
      some (i, ((code.drop o).take k).length) := by rw [hl]; exact hdec
  have t : Triple I (codePt pc.toNat ((code.drop o).take k) ∗ ripPt pc ∗
      (regsPt frameRegs f ∗ flagsPt fl))
      (codePt pc.toNat ((code.drop o).take k) ∗ ripPt pc' ∗ (regsPt frameRegs g ∗ flagsPt fl')) := by
    refine insn_triple E (ne_nil_of_dec hdec') fun m hX hXP hlX hrip hld => ?_
    obtain ⟨h₁, h₂, hP₁, hP₂, hl₁, hl₂, hd, rfl⟩ := sep_le hXP hlX
    obtain ⟨c, hxc, hcrip, hcg, hco, hcf⟩ :=
      hx m.core m.memory hrip (regsPt_le hP₁ hl₁) (flagsPt_le hP₂ hl₂)
    refine ⟨⟨c, m.memory⟩, open_of_ext hld hrip hdec' hnr hxc, hcrip, fun l h1 h2 => ?_, ?_⟩
    · obtain ⟨n1, n2⟩ := union_none h2
      cases l with
      | reg q =>
        by_cases hq : q ∈ frameRegs
        · exfalso
          have hp1 : (h₁ (.reg q)).isSome := regsPt_own hP₁ hq
          rw [n1] at hp1; cases hp1
        · show some (Val.word (c.read q)) = some (Val.word (m.core.read q))
          rw [hco q hq]
      | rip => exact absurd rfl h1
      | flags =>
        have := flagsAny_dom ⟨fl, hP₂⟩; rw [n2] at this; cases this
      | mem a => rfl
      | regions => rfl
    · rw [Frag.reval_union]
      refine ⟨_, _, Frag.reval_disjoint hd _, rfl, regsPt_reval hP₁ hcg, ?_⟩
      have := flagsAny_reval_exact ⟨c, m.memory⟩ ⟨fl, hP₂⟩; rwa [hcf] at this
  exact c_step hpc hfit (R := M) t (entails_of_eq (by simp only [St]; ac_rfl))
    (entails_of_eq (by simp only [St]; ac_rfl))

/-! ## Wrappers for the register-only forms of the free-list walk -/

theorem dec_len {code : List Byte} {o k : Nat} {i : Silmaril.X86.Ext.Instr}
    (hfit : o + k ≤ code.length)
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (i, k)) : k = i.length := by
  have hl : ((code.drop o).take k).length = k := by simp; omega
  have := len_of_dec (bytes := (code.drop o).take k) (i := i) (by rw [hl]; exact hdec)
  rw [this, hl]

section Forms

variable (E : Silmaril.X86.Open.isa.Extends I) {b : Nat} {code : List Byte} {o k : Nat}
  {pc : Word} (hpc : pc.toNat = b + o) (hfit : o + k ≤ code.length)

include E hpc hfit

/-- `cmp $imm32, %r` (64-bit). -/
theorem c_cmpI {r : Reg} (hr : r ∈ frameRegs) {imm : BitVec 32} {f : Reg → Word}
    {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.aluI .q .cmp (.reg r) imm, k)) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) f
        (Silmaril.X86.Ext.AluOp.flagsN .cmp (f r) (imm.signExtend 64)) M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs _ => ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.retire, ite_true]; rw [hrip, hl]
  · intro q hq; exact hregs q hq
  · intro q _; rfl
  · simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.retire, hregs r hr]

/-- `lea m, %dst` (64-bit), for an operand whose address the frame determines. -/
theorem c_lea {dst : Reg} (hd : dst ∈ frameRegs) {mo : Silmaril.X86.Ext.Mem} {a : Word}
    {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.lea .q dst mo, k))
    (haddr : ∀ s : State, (∀ q ∈ frameRegs, s.read q = f q) → ∀ next, mo.addr s next = a) :
    SPEC I (codePt b code) (St pc f fl M)
      (St (pc + BitVec.ofNat 64 k) (Function.update f dst a) fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl => ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · show s.rip + _ = _; rw [hrip, hl]
  · intro q hq
    show (Silmaril.X86.Ext.Sz.write .q s dst _).read q = _
    by_cases e : q = dst
    · subst e; simp [Silmaril.X86.Ext.Sz.write, haddr s hregs]
    · simp [Silmaril.X86.Ext.Sz.write, e, hregs q hq]
  · intro q hq
    show (Silmaril.X86.Ext.Sz.write .q s dst _).read q = _
    have : q ≠ dst := fun e => hq (e ▸ hd)
    simp [Silmaril.X86.Ext.Sz.write, this]
  · exact hfl

/-- `jmp rel8`. -/
theorem c_jmp8 {rel : BitVec 8} {f : Reg → Word} {fl : Flags} {M : SProp} {pc' : Word}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.jmp8 rel, k))
    (hnext : pc + BitVec.ofNat 64 k + rel.signExtend 64 = pc') :
    SPEC I (codePt b code) (St pc f fl M) (St pc' f fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl => ⟨_, rfl, ?_, ?_, ?_, hfl⟩
  · show s.rip + _ + _ = _; rw [hrip, ← hl, hnext]
  · exact hregs
  · intro q _; rfl

/-- A multi-byte `nop`. -/
theorem c_nop {m : Fin 15} {f : Reg → Word} {fl : Flags} {M : SProp}
    (hdec : Silmaril.X86.Ext.decode ((code.drop o).take k) = some (.nop m, k)) :
    SPEC I (codePt b code) (St pc f fl M) (St (pc + BitVec.ofNat 64 k) f fl M) := by
  have hl := dec_len hfit hdec
  refine c_whole E hpc hfit hdec (by simp) fun s mem hrip hregs hfl => ⟨_, rfl, ?_, hregs,
    fun q _ => rfl, hfl⟩
  show s.rip + _ = _; rw [hrip, hl]

end Forms

end Silmaril.Raw.Libc.X86Alloc.Whole
