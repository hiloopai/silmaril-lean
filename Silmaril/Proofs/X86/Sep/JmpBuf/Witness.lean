module

public import Silmaril.Proofs.X86.Sep.JmpBuf.Catch

/-!
# Proofs: the catch test is not vacuous

The concrete `Open9` state `m0` of `Sep/JmpBuf/Catch/Defs.lean` (one region mapping every
address read/write/execute) holds the 122 bytes of the catch test at `0x400000`, the return
address `0x777777` at `rsp = 0x7000`, `rdi = 0x6000` (the `jmp_buf`) and the callee-saved
registers `11 … 16`:

* `catchPre_m0`: `catchPre` holds of a part of `m0` (code, stack slots, `jmp_buf`, registers
  and flags pairwise disjoint), so the hypothesis of `catch_test` is satisfiable.
* `catch_m0`: therefore, at every index, the `Open9` run from `m0` does not get stuck before
  it reaches a state with `rip = 0x777777`, `rax = 0xffffffff`, `rsp = 0x7008` and the
  callee-saved registers `11 … 16`.

`HoldsIn P s D` (`P` holds of a part of `s` with domain in `D`) and `sep_in` assemble the
witness fragment from disjoint pieces; the memory domains are intervals (`iv`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.JmpBuf.Witness

open Silmaril.X86 (State MState Word Byte Reg Insn)
open Silmaril.Process (Memory Region Permissions addressLimit)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le diff)
open Silmaril.X86.Safe
open Silmaril.X86.Sep.JmpBuf
open Silmaril.Proofs.X86.Sep.JmpBuf.CatchTest
open Silmaril.X86.Sep.JmpBuf.CatchTest

/-! ## Holding in a part of a state -/

/-- `P` holds of a part of `s` whose domain lies in `D`. -/
def HoldsIn (P : SProp) (s : Frag) (D : Loc → Prop) : Prop :=
  ∃ h, P h ∧ Le h s ∧ ∀ l, (h l).isSome → D l

/-- The memory addresses `[a, a + n)`. -/
def iv (a n : Nat) : Loc → Prop := fun l => ∃ x, l = .mem x ∧ a ≤ x ∧ x < a + n

theorem emp_in (s : Frag) : HoldsIn emp s (fun _ => False) :=
  ⟨Frag.empty, rfl, fun _ _ e => by simp [Frag.empty] at e, fun _ e => by simp [Frag.empty] at e⟩

theorem sep_in {P Q : SProp} {s : Frag} {D₁ D₂ : Loc → Prop} (hp : HoldsIn P s D₁)
    (hq : HoldsIn Q s D₂) (hd : ∀ l, D₁ l → D₂ l → False) :
    HoldsIn (P ∗ Q) s (fun l => D₁ l ∨ D₂ l) := by
  obtain ⟨h₁, hP, hl₁, hD₁⟩ := hp
  obtain ⟨h₂, hQ, hl₂, hD₂⟩ := hq
  have disj : Disjoint h₁ h₂ := by
    intro l
    cases e₁ : h₁ l with
    | none => exact .inl rfl
    | some v =>
      cases e₂ : h₂ l with
      | none => exact .inr rfl
      | some w => exact absurd (hd l (hD₁ l (by simp [e₁])) (hD₂ l (by simp [e₂]))) id
  refine ⟨union h₁ h₂, ⟨h₁, h₂, disj, rfl, hP, hQ⟩, ?_, ?_⟩
  · intro l v e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact hl₂ l v e
    | some u => rw [e₁] at e; cases e; exact hl₁ l _ e₁
  · intro l e
    simp only [Frag.union] at e
    cases e₁ : h₁ l with
    | none => rw [e₁] at e; exact .inr (hD₂ l e)
    | some u => exact .inl (hD₁ l (by simp [e₁]))

theorem mono_in {P : SProp} {s : Frag} {D D' : Loc → Prop} (hp : HoldsIn P s D)
    (hD : ∀ l, D l → D' l) : HoldsIn P s D' := by
  obtain ⟨h, a, b, c⟩ := hp; exact ⟨h, a, b, fun l e => hD l (c l e)⟩

theorem single_le {l : Loc} {v : Val} {s : Frag} (e : s l = some v) :
    Le (Frag.single l v) s := by
  intro l' w h; simp only [Frag.single] at h; split at h <;> simp_all

theorem single_dom {l : Loc} {v : Val} : ∀ l', (Frag.single l v l').isSome → l' = l := by
  intro l' h; simp only [Frag.single] at h; split at h <;> simp_all

theorem regPt_in (m : MState) (r : Reg) {v : Word} (hv : m.core.read r = v) :
    HoldsIn (regPt r v) (toFrag m) (· = .reg r) := by
  subst hv; exact ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem regAny_in (m : MState) (r : Reg) : HoldsIn (regAny r) (toFrag m) (· = .reg r) :=
  ⟨_, ⟨_, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩

theorem ripPt_in (m : MState) {v : Word} (hv : m.core.rip = v) :
    HoldsIn (ripPt v) (toFrag m) (· = .rip) := by
  subst hv; exact ⟨_, rfl, single_le (s := toFrag m) rfl, single_dom⟩

theorem flagsAny_in (m : MState) : HoldsIn flagsAny (toFrag m) (· = .flags) :=
  ⟨_, ⟨_, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩

theorem bytesAt_in {need : Permissions → Prop} (m : MState) :
    ∀ (a : Nat) (bs : List Byte), (∀ i (hi : i < bs.length), a + i < addressLimit ∧
      m.memory.bytes.get? (a + i) = some bs[i] ∧ need (permsAt m.memory (a + i))) →
      HoldsIn (bytesAt need a bs) (toFrag m) (iv a bs.length)
  | a, [], _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, b :: bs, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hb : HoldsIn (byteAt need a b) (toFrag m) (· = .mem a) := by
      refine ⟨Frag.single (.mem a) (.cell ⟨some b, permsAt m.memory a⟩),
        ⟨h0.1, _, h0.2.2, rfl⟩, single_le ?_, single_dom⟩
      simp only [toFrag, h0.2.1]
    have ht := bytesAt_in m (a + 1) bs (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨x, e, h1, -⟩; cases e; omega
    · rintro l (rfl | ⟨x, rfl, h1, h2⟩)
      · exact ⟨a, rfl, by omega, by simp⟩
      · exact ⟨x, rfl, by omega, by simp; omega⟩

theorem blockAny_in (m : MState) :
    ∀ (a n : Nat), (∀ i < n, a + i < addressLimit ∧ RW (permsAt m.memory (a + i))) →
      HoldsIn (blockAny a n) (toFrag m) (iv a n)
  | a, 0, _ => mono_in (emp_in _) (fun _ h => h.elim)
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hb : HoldsIn (byteAny a) (toFrag m) (· = .mem a) :=
      ⟨_, ⟨h0.1, _, h0.2, rfl⟩, single_le (s := toFrag m) rfl, single_dom⟩
    have ht := blockAny_in m (a + 1) n (fun i hi => by
      have := h (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    refine mono_in (sep_in hb ht ?_) ?_
    · rintro l rfl ⟨x, e, h1, -⟩; cases e; omega
    · rintro l (rfl | ⟨x, rfl, h1, h2⟩)
      · exact ⟨a, rfl, by omega, by omega⟩
      · exact ⟨x, rfl, by omega, by omega⟩

/-- `P` holds of a part of `m`, so with the rest as frame `P ∗ ⊤` holds of all of `m`. -/
theorem sep_true_of_le {P : SProp} {h : Frag} {m : MState} (hp : P h) (hl : Le h (toFrag m)) :
    (P ∗ fun _ => True) (toFrag m) := by
  refine ⟨h, diff (toFrag m) h, fun l => ?_, ?_, hp, trivial⟩
  · simp only [diff]; cases e : h l <;> simp
  · funext l
    simp only [union, diff]
    cases e : h l with
    | none => simp
    | some v => simp [hl l v e]

/-! ## The concrete state -/

theorem catchBytes_length : catchBytes.length = 122 := by decide

theorem perms0 (a : Nat) (ha : a < 2 ^ 64) : permsAt mem0 a = ⟨true, true, true⟩ := by
  have : a < 18446744073709551616 := ha
  simp [permsAt, Memory.permits, mem0, allRegion, Region.Contains, Permissions.allows, this]

/-- A piece of the code at offset `o`. -/
theorem code_in (o : Nat) (bs : List Byte) (ho : o + bs.length ≤ 122)
    (hbs : ∀ i (hi : i < bs.length), catchBytes[o + i]? = some bs[i]) :
    HoldsIn (codePt (0x400000 + o) bs) (toFrag m0) (iv (0x400000 + o) bs.length) := by
  refine bytesAt_in (need := EX) m0 _ bs (fun i hi => ⟨by simp only [addressLimit]; omega, ?_, ?_⟩)
  · show (Memory.install _ _ _).get? _ = _
    have hl : o + i < catchBytes.length := by rw [catchBytes_length]; omega
    rw [Nat.add_assoc, Memory.install_get _ _ _ _ hl]
    have := hbs i hi
    rw [List.getElem?_eq_getElem hl] at this
    exact this
  · show EX (permsAt mem0 _)
    rw [perms0 _ (by omega)]; rfl

theorem code_in' (o : Nat) (bs : List Byte) (n : Nat) (hn : bs.length = n)
    (ho : o + bs.length ≤ 122)
    (hbs : ∀ i (hi : i < bs.length), catchBytes[o + i]? = some bs[i]) :
    HoldsIn (codePt (0x400000 + o) bs) (toFrag m0) (iv (0x400000 + o) n) :=
  hn ▸ code_in o bs ho hbs

theorem ret_in :
    HoldsIn (wordPt 0x7000 RA) (toFrag m0) (iv 0x7000 8) := by
  have := bytesAt_in (need := RW) m0 0x7000 (encodeWords [RA]) (fun i hi => by
    simp only [Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
      List.length_nil] at hi
    refine ⟨by simp only [addressLimit]; omega, ?_, ?_⟩
    · show (Memory.install _ _ _).get? _ = _
      rw [Memory.install_outside _ _ _ _ (by rw [catchBytes_length]; omega)]
      exact Memory.install_get _ _ _ _ (by simp; omega)
    · show RW (permsAt mem0 _)
      rw [perms0 _ (by omega)]; exact ⟨rfl, rfl⟩)
  simpa [wordPt, bytesPt] using this

theorem block_in (a n : Nat) (h : a + n < 2 ^ 64) :
    HoldsIn (blockAny a n) (toFrag m0) (iv a n) :=
  blockAny_in m0 a n (fun i hi => ⟨by simp only [addressLimit]; omega, by
    show RW (permsAt mem0 _)
    rw [perms0 _ (by omega)]; exact ⟨rfl, rfl⟩⟩)

/-- Disjointness of two domains built from `iv` and single locations. -/
macro "disj" : tactic => `(tactic| (intro l h1 h2; cases l <;> simp_all [iv] <;> omega))

/-- **The precondition of the catch test is satisfiable**: it holds of a part of `m0`. -/
theorem catchPre_m0 :
    ∃ h, catchPre 0x400000 0x7000 RA 0x6000 11 12 13 14 15 16 h ∧ Le h (toFrag m0) := by
  have e : ∀ k : Nat, k < 122 → ((0x400000 : Word) + BitVec.ofNat 64 k).toNat = 0x400000 + k :=
    fun k hk => by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
  unfold catchPre jbAny
  simp only [regsAny, regsWith, calleeSavedRegs, sep_emp, sep_assoc]
  rw [e 5 (by omega), e 7 (by omega), e 9 (by omega), e 15 (by omega), e 20 (by omega),
    e 21 (by omega), e 27 (by omega), e 32 (by omega), e 38 (by omega), e 81 (by omega),
    show (0x400000 : Word).toNat = 0x400000 + 0 from rfl,
    show (0x7000 : Word).toNat = 0x7000 from rfl, show (0x6000 : Word).toNat = 0x6000 from rfl]
  have hD := sep_in (code_in' 0 (Insn.encode (.call 0x21#32)) 5 (by decide) (by decide) (by decide))
    (sep_in (code_in' 5 cTest 2 (by decide) (by decide) (by decide))
    (sep_in (code_in' 7 cJne 2 (by decide) (by decide) (by decide))
    (sep_in (code_in' 9 (Insn.encode (.call 0x07#32)) 5 (by decide) (by decide) (by decide))
    (sep_in (code_in' 15 cMov 5 (by decide) (by decide) (by decide))
    (sep_in (code_in' 20 (Insn.encode .ret) 1 (by decide) (by decide) (by decide))
    (sep_in (code_in' 21 (Insn.encode (.call 0x01#32)) 5 (by decide) (by decide) (by decide))
    (sep_in (code_in' 27 t1Mov 5 (by decide) (by decide) (by decide))
    (sep_in (code_in' 32 (Insn.encode (.call 0x2c#32)) 5 (by decide) (by decide) (by decide))
    (sep_in (code_in' 38 setjmpBytes 43 (by decide) (by decide) (by decide))
    (sep_in (code_in' 81 longjmpBytes 41 (by decide) (by decide) (by decide))
    (sep_in (ripPt_in m0 rfl)
    (sep_in (regPt_in m0 .rsp rfl)
    (sep_in (ret_in)
    (sep_in (block_in (0x7000 - 8) 8 (by omega))
    (sep_in (block_in (0x7000 - 16) 8 (by omega))
    (sep_in (block_in (0x7000 - 24) 8 (by omega))
    (sep_in (regPt_in m0 .rdi rfl)
    (sep_in (regPt_in m0 .rbx rfl)
    (sep_in (regPt_in m0 .rbp rfl)
    (sep_in (regPt_in m0 .r12 rfl)
    (sep_in (regPt_in m0 .r13 rfl)
    (sep_in (regPt_in m0 .r14 rfl)
    (sep_in (regPt_in m0 .r15 rfl)
    (sep_in (regAny_in m0 .rax)
    (sep_in (regAny_in m0 .rsi)
    (sep_in (regAny_in m0 .rcx)
    (sep_in (regAny_in m0 .rdx)
    (sep_in (regAny_in m0 .r8)
    (sep_in (regAny_in m0 .r9)
    (sep_in (regAny_in m0 .r10)
    (sep_in (regAny_in m0 .r11)
    (sep_in (flagsAny_in m0)
    (block_in 0x6000 64 (by omega)) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨h, hp, hl, -⟩ := hD; exact ⟨h, hp, hl⟩
  all_goals disj

/-- **The catch test is not vacuous.** From `m0`, at every index, the `Open9` run does not get
stuck before `catch` has returned to `RA` with `rax = 0xffffffff`, `rsp = 0x7008` and the
callee-saved registers `11 … 16`. -/
theorem catch_m0 (n : Nat) :
    SafeN Open9.isa (fun m => m.core.rip = RA ∧ m.core.read .rax = 0xFFFFFFFF#64 ∧
      m.core.read .rsp = 0x7008 ∧ m.core.read .rbx = 11 ∧ m.core.read .rbp = 12 ∧
      m.core.read .r12 = 13 ∧ m.core.read .r13 = 14 ∧ m.core.read .r14 = 15 ∧
      m.core.read .r15 = 16) n m0 := by
  obtain ⟨h, hp, hl⟩ := catchPre_m0
  have T := catch_test_open9 (e := 0x400000) (jb := 0x6000) (c0 := 11) (c1 := 12) (c2 := 13)
    (c3 := 14) (c4 := 15) (c5 := 16) n (s := 0x7000) (r := RA) (by decide) (by decide)
    (by decide) _ m0 trivial (sep_true_of_le hp hl)
  refine safeN_post (fun m hm => ?_) T
  obtain ⟨_, -, hm, -, hlm, -, -, -⟩ := sep_le hm (fun _ _ e => e)
  unfold catchPost at hm
  obtain ⟨_, -, hm, -, hlm, -, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, hrip, hm, hl1, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, hsp, hm, hl2, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, hax, hm, hl3, hlm, -, -⟩ := sep_le hm hlm
  simp only [calleeSavedRegs, regsWith] at hm
  obtain ⟨_, _, h0, hm, hl4, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, h1, hm, hl5, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, h2, hm, hl6, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, h3, hm, hl7, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, h4, hm, hl8, hlm, -, -⟩ := sep_le hm hlm
  obtain ⟨_, _, h5, -, hl9, -, -, -⟩ := sep_le hm hlm
  exact ⟨ripPt_le hrip hl1, regPt_le hax hl3, regPt_le hsp hl2, regPt_le h0 hl4,
    regPt_le h1 hl5, regPt_le h2 hl6, regPt_le h3 hl7, regPt_le h4 hl8, regPt_le h5 hl9⟩

end Silmaril.Proofs.X86.Sep.JmpBuf.Witness
