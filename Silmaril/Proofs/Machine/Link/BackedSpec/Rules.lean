module

public import Silmaril.Machine.Link.BackedSpec.Defs
public import Silmaril.Machine.Link.FnSpec.Thms

/-!
# Proofs: the backed-stack template

* Weakenings: `blockB_blockAny`, `bytesPt_blockB`, `byteAny_byteRd`, `blockAny_blockRd`,
  `bytesAt_blockRd` (any permission that implies `RO`), `wordPt_blockRd`; splitting
  `blockB_split` and `blockRd_add`.
* `safeB_of_safe`: **backward compatibility.** Every `Safe` function is `SafeB`.
* `safeB_zero`, `safeB_mono`.
* `STriple.seq`: sequencing two step-indexed triples at the same index.
* `scallB_rule`: the step-indexed call rule for a `SafeB` callee: the caller hands over the
  return slot (`blockAny`) and a *backed* budget (`blockB`), and gets both back `blockRd`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.BackedSpec

open Silmaril.X86 (MState Word Byte Reg Insn)
open Silmaril.Process (Permissions)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.BackedSpec
open Silmaril.Proofs.Machine.Link.FnSpec

/-! ## Weakening and splitting -/

theorem blockB_blockAny (a n : Nat) : blockB a n ⊢ₛ blockAny a n :=
  sexists_elim fun zs => spure_sep_elim fun hl => hl ▸ bytesPt_blockAny a zs

theorem bytesPt_blockB (a : Nat) (zs : List Byte) : bytesPt a zs ⊢ₛ blockB a zs.length :=
  sexists_intro zs (spure_sep_intro rfl (entails_refl _))

theorem blockB_split (a m n : Nat) : blockB a (m + n) ⊢ₛ (blockB a m ∗ blockB (a + m) n) := by
  refine sexists_elim fun zs => spure_sep_elim fun hl => ?_
  have e : zs = zs.take m ++ zs.drop m := (List.take_append_drop m zs).symm
  have h1 : (zs.take m).length = m := by simp; omega
  have h2 : (zs.drop m).length = n := by simp; omega
  rw [e, bytesPt, bytesAt_append, h1]
  refine sep_mono ?_ ?_
  · exact entails_trans (bytesPt_blockB a _) (by rw [h1]; exact entails_refl _)
  · exact entails_trans (bytesPt_blockB (a + m) _) (by rw [h2]; exact entails_refl _)

theorem byteAny_byteRd (a : Nat) : byteAny a ⊢ₛ byteRd a := by
  rintro h ⟨ha, c, hc, rfl⟩; exact ⟨ha, c, hc.1, rfl⟩

theorem blockAny_blockRd : ∀ (a n : Nat), blockAny a n ⊢ₛ blockRd a n
  | _, 0 => entails_refl _
  | a, n + 1 => sep_mono (byteAny_byteRd a) (blockAny_blockRd (a + 1) n)

theorem byteAt_byteRd {need : Permissions → Prop} (hn : ∀ p, need p → RO p) (a : Nat)
    (b : Byte) : byteAt need a b ⊢ₛ byteRd a := by
  rintro h ⟨ha, p, hp, rfl⟩; exact ⟨ha, _, hn p hp, rfl⟩

theorem bytesAt_blockRd {need : Permissions → Prop} (hn : ∀ p, need p → RO p) :
    ∀ (a : Nat) (bs : List Byte), bytesAt need a bs ⊢ₛ blockRd a bs.length
  | _, [] => entails_refl _
  | a, _ :: bs => sep_mono (byteAt_byteRd hn _ _) (bytesAt_blockRd hn (a + 1) bs)

theorem rw_ro : ∀ p, RW p → RO p := fun _ h => h.1
theorem ro_ro : ∀ p, RO p → RO p := fun _ h => h

theorem wordPt_blockRd (a : Nat) (w : Word) : wordPt a w ⊢ₛ blockRd a 8 :=
  entails_trans (wordPt_blockAny a w) (blockAny_blockRd a 8)

theorem blockRd_add : ∀ (a m n : Nat), blockRd a (m + n) = (blockRd a m ∗ blockRd (a + m) n)
  | a, 0, n => by simp [blockRd, emp_sep]
  | a, m + 1, n => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [blockRd]
    rw [blockRd_add (a + 1) m n, sep_assoc]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-! ## Backward compatibility -/

/-- **Every `Safe` function is `SafeB`**: the backed budget is in particular a `blockAny`,
and the returned `blockAny` budget is in particular readable. -/
theorem safeB_of_safe {n a : Nat} {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image}
    (h : Safe n a S ctx) : SafeB n a S ctx := by
  intro D bs hc x sp ret hA hst
  refine STriple.conseq ?_ (h D bs hc x sp ret hA hst) ?_
  · simp only [FnSpecB.SysVPreB, FnSpec.SysVPre, FnSpec.SysVEntry]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_right _ (sep_mono_right _ (sep_mono_left _
        (blockB_blockAny _ _)))))))) (entails_of_eq ?_)
    ac_rfl
  · simp only [FnSpecB.SysVPostB, FnSpec.SysVPost, FnSpec.SysVExit]
    rw [sep_sexists, sep_sexists]
    refine sexists_elim fun v => sexists_intro v ?_
    refine entails_trans (entails_of_eq ?_) (sep_mono_right _ (sep_mono_right _
      (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
        (sep_mono_left _ (blockAny_blockRd _ _)))))))
    ac_rfl

theorem safeB_zero (a : Nat) (S : FnSpec) (ctx : Silmaril.Machine.Link.Contract.Image) :
    SafeB 0 a S ctx :=
  fun _ _ _ _ _ _ _ _ => STriple.zero _ _

theorem safeB_mono {n a : Nat} {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image}
    (h : SafeB (n + 1) a S ctx) : SafeB n a S ctx :=
  fun D bs hc x sp ret hA hst => STriple.mono (h D bs hc x sp ret hA hst)

/-! ## Sequencing and the call rule -/

/-- Two step-indexed triples at the same index compose. -/
theorem STriple.seq {n : Nat} {P R Q : SProp} (h₁ : STriple n P R) (h₂ : STriple n R Q) :
    STriple n P Q := fun F m hm =>
  safeN_bind (h₁ F m hm) fun m' hr => h₂ F m' hr

/-- **The step-indexed call rule for a backed-stack callee.** -/
theorem scallB_rule {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image} {n f : Nat}
    {D : Nat → Prop} {bs : Nat → Byte}
    {pc s : Word} {rel : BitVec 32} (hc : Covers ctx D bs) (hf : SafeB n f S ctx)
    (hD : ∀ i (hi : i < (Insn.encode (.call rel)).length),
      D (pc.toNat + i) ∧ bs (pc.toNat + i) = (Insn.encode (.call rel))[i])
    (htarget : pc + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hA : FnSpec.EntryAligned (s - 8#64)) (hlow : S.stack + 8 ≤ s.toNat) (x : S.Arg) :
    STriple (n + 1)
      (Code D bs ∗ ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8) 8 ∗ blockB (s.toNat - 8 - S.stack) S.stack ∗ S.pre x)
      (Code D bs ∗ sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockRd (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) := by
  have esp := toNat_sub_eight' (s := s) (by omega)
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have hne : s ≠ s - 8#64 := by bv_omega
  have hcall := code_triple hD (call_step pc s rel (by omega))
  rw [htarget] at hcall
  have hprog : Progress
      (regPt .rsp s ∗ Code D bs ∗ ripPt pc ∗ blockAny (s.toNat - 8) 8)
      (regPt .rsp (s - 8#64) ∗ Code D bs ∗ ripPt (BitVec.ofNat 64 f) ∗
        wordPt (s.toNat - 8) (pc + 5#64)) :=
    progress_of_rsp hne (Triple.conseq (entails_of_eq (by ac_rfl)) hcall
      (entails_of_eq (by ac_rfl)))
  have hcallee := hf D bs hc x (s - 8#64) (pc + 5#64) hA (by rw [esp]; omega)
  refine STriple.progress_seq
    (Progress.conseq ?_ (Progress.frame hprog
      (SysVRegs (S.args x) ∗ flagsAny ∗ blockB (s.toNat - 8 - S.stack) S.stack ∗ S.pre x))
      (entails_refl _))
    (STriple.conseq ?_ hcallee ?_)
  · apply entails_of_eq
    ac_rfl
  · apply entails_of_eq
    simp only [FnSpecB.SysVPreB]
    rw [esp]
    ac_rfl
  · simp only [FnSpecB.SysVPostB]
    rw [esp, eback, sep_sexists]
    refine sexists_elim fun v => ?_
    refine sexists_intro v (entails_of_eq ?_)
    ac_rfl

/-! ## Total variants -/

/-- Total safety implies step-indexed safety at every index. -/
theorem safe_of_safeT {a : Nat} {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image}
    (h : SafeT a S ctx) (n : Nat) : Safe n a S ctx :=
  fun D bs hc x sp ret hA hst => STriple.of_triple (h D bs hc x sp ret hA hst)

theorem safeB_of_safeTB {a : Nat} {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image}
    (h : SafeTB a S ctx) (n : Nat) : SafeB n a S ctx :=
  fun D bs hc x sp ret hA hst => STriple.of_triple (h D bs hc x sp ret hA hst)

/-- **A position-independent total proof of the exact bytes gives total safety** (the total
counterpart of R1's `safe_of_sat`; the separation-logic layer's libmini `exports_sat` has this form). -/
theorem safeT_of_sat {a : Nat} {S : FnSpec} {code : List Byte}
    {ctx : Silmaril.Machine.Link.Contract.Image} (ha : a < 2 ^ 64)
    (hcode : ∀ i (hi : i < code.length), ContainsX ctx (a + i) code[i])
    (hS : ∀ entry : Word, S.Sat (codePt entry.toNat code) entry) : SafeT a S ctx := by
  intro D bs hc x sp ret hA hst
  have hD : ∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i] :=
    fun i hi => hc _ _ (hcode i hi)
  have hsat := hS (BitVec.ofNat 64 a) x sp ret hA hst
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at hsat
  rw [code_split code a hD]
  exact Triple.conseq (entails_of_eq (by ac_rfl))
    (Triple.frame hsat (Code (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + code.length)) bs))
    (entails_of_eq (by ac_rfl))

/-- **The total call rule** (the total counterpart of R1's `scall_rule`). -/
theorem tcall_rule {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image} {f : Nat}
    {D : Nat → Prop} {bs : Nat → Byte}
    {pc s : Word} {rel : BitVec 32} (hc : Covers ctx D bs) (hf : SafeT f S ctx)
    (hD : ∀ i (hi : i < (Insn.encode (.call rel)).length),
      D (pc.toNat + i) ∧ bs (pc.toNat + i) = (Insn.encode (.call rel))[i])
    (htarget : pc + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hA : FnSpec.EntryAligned (s - 8#64)) (hlow : S.stack + 8 ≤ s.toNat) (x : S.Arg) :
    Triple
      (Code D bs ∗ ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.pre x)
      (Code D bs ∗ sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) := by
  have esp := toNat_sub_eight' (s := s) (by omega)
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have hcall := code_triple hD (call_step pc s rel (by omega))
  rw [htarget] at hcall
  have hcallee := hf D bs hc x (s - 8#64) (pc + 5#64) hA (by rw [esp]; omega)
  refine Triple.trans (Triple.conseq ?_ (Triple.frame hcall
      (SysVRegs (S.args x) ∗ flagsAny ∗ blockAny (s.toNat - 8 - S.stack) S.stack ∗ S.pre x))
      (entails_refl _))
    (Triple.conseq ?_ hcallee ?_)
  · apply entails_of_eq
    rw [show s.toNat - 8 = s.toNat - 8 - S.stack + S.stack by omega, blockAny_add,
      show s.toNat - 8 - S.stack + S.stack - S.stack = s.toNat - 8 - S.stack by omega,
      show s.toNat - 8 - S.stack + S.stack = s.toNat - 8 by omega]
    ac_rfl
  · apply entails_of_eq
    simp only [FnSpec.SysVPre, FnSpec.SysVEntry]
    rw [esp]
    ac_rfl
  · simp only [FnSpec.SysVPost, FnSpec.SysVExit]
    rw [esp, eback, sep_sexists]
    refine sexists_elim fun v => ?_
    rw [sep_sexists]
    refine sexists_intro v (entails_of_eq ?_)
    ac_rfl

/-- **The total call rule for a backed-stack callee.** -/
theorem tcallB_rule {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image} {f : Nat}
    {D : Nat → Prop} {bs : Nat → Byte}
    {pc s : Word} {rel : BitVec 32} (hc : Covers ctx D bs) (hf : SafeTB f S ctx)
    (hD : ∀ i (hi : i < (Insn.encode (.call rel)).length),
      D (pc.toNat + i) ∧ bs (pc.toNat + i) = (Insn.encode (.call rel))[i])
    (htarget : pc + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hA : FnSpec.EntryAligned (s - 8#64)) (hlow : S.stack + 8 ≤ s.toNat) (x : S.Arg) :
    Triple
      (Code D bs ∗ ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8) 8 ∗ blockB (s.toNat - 8 - S.stack) S.stack ∗ S.pre x)
      (Code D bs ∗ sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockRd (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) := by
  have esp := toNat_sub_eight' (s := s) (by omega)
  have eback : s - 8#64 + 8#64 = s := by bv_omega
  have hcall := code_triple hD (call_step pc s rel (by omega))
  rw [htarget] at hcall
  have hcallee := hf D bs hc x (s - 8#64) (pc + 5#64) hA (by rw [esp]; omega)
  refine Triple.trans (Triple.conseq ?_ (Triple.frame hcall
      (SysVRegs (S.args x) ∗ flagsAny ∗ blockB (s.toNat - 8 - S.stack) S.stack ∗ S.pre x))
      (entails_refl _))
    (Triple.conseq ?_ hcallee ?_)
  · apply entails_of_eq
    ac_rfl
  · apply entails_of_eq
    simp only [FnSpecB.SysVPreB]
    rw [esp]
    ac_rfl
  · simp only [FnSpecB.SysVPostB]
    rw [esp, eback, sep_sexists]
    refine sexists_elim fun v => ?_
    refine sexists_intro v (entails_of_eq ?_)
    ac_rfl

end Silmaril.Proofs.Machine.Link.BackedSpec
