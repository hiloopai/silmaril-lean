module

public import Silmaril.Machine.Link.FnSpec.Thms
public import Silmaril.Machine.Link.Examples.LibMiniClient.Defs

/-!
# Proofs: `len1`'s code meets `plusOneSpec S` whenever its callee is `Safe` for `S`

`plusOne_safe`: if the image holds `plusOneCode rel` at `a` (`sub $8,%rsp; call rel;
add $8,%rsp; add $1,%rax; ret`) and the call lands on an address `f` that is `Safe n` for
`S`, then `a` is `Safe (n + 1)` for `plusOneSpec S`. The proof is three instruction
triples (`aluI8_step`, A's `ret_step`), the step-indexed call rule `scall_rule`, and frame
bookkeeping. The callee is used only through its `Safe` assumption: nothing about its code.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.LibMiniClient

open Silmaril.X86 (MState Word Byte Reg Insn)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Proofs.Machine.Link.FnSpec
open Silmaril.Machine.Link.Unit (Contains)

variable {D : Nat → Prop} {bs : Nat → Byte}

/-- A piece of a covered code list is covered at its offset. -/
theorem piece_cov {code piece : List Byte} {a o : Nat}
    (hD : ∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i])
    (hp : ∀ i (hi : i < piece.length), code[o + i]? = some piece[i]) :
    ∀ i (hi : i < piece.length), D (a + o + i) ∧ bs (a + o + i) = piece[i] := by
  intro i hi
  have h := hp i hi
  have hlt : o + i < code.length := by
    rcases Nat.lt_or_ge (o + i) code.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  obtain ⟨h1, h2⟩ := hD (o + i) hlt
  rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at h
  rw [show a + o + i = a + (o + i) by omega]
  exact ⟨h1, h2.trans h⟩

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem cov_at {a o : Nat} {pc : Word} {piece : List Byte} (hpc : pc.toNat = a + o)
    (h : ∀ i (hi : i < piece.length), D (a + o + i) ∧ bs (a + o + i) = piece[i]) :
    ∀ i (hi : i < piece.length), D (pc.toNat + i) ∧ bs (pc.toNat + i) = piece[i] := by
  rw [hpc]; exact h

theorem dec_sub : Silmaril.X86.Ext.decode [0x48, 0x83, 0xec, 0x08] =
    some (.aluI8 .q .sub (.reg .rsp) 0x08#8, 4) := by decide
theorem dec_add_rsp : Silmaril.X86.Ext.decode [0x48, 0x83, 0xc4, 0x08] =
    some (.aluI8 .q .add (.reg .rsp) 0x08#8, 4) := by decide
theorem dec_add_rax : Silmaril.X86.Ext.decode [0x48, 0x83, 0xc0, 0x01] =
    some (.aluI8 .q .add (.reg .rax) 0x01#8, 4) := by decide

theorem sext8 : (0x08#8 : BitVec 8).signExtend 64 = 8#64 := by decide
theorem sext1 : (0x01#8 : BitVec 8).signExtend 64 = 1#64 := by decide

/-- **`len1`'s code, against any callee spec**, on every machine that extends the open
machine. -/
theorem plusOne_safe {step : MState → Option MState} [Silmaril.Machine.X86.Safe.ExtendsOpen step]
    {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image} {n a f : Nat}
    {rel : BitVec 32} (ha : a + 18 ≤ 2 ^ 64)
    (hcode : ∀ i (hi : i < (plusOneCode rel).length), ContainsX ctx (a + i) (plusOneCode rel)[i])
    (htarget : BitVec.ofNat 64 (a + 4) + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hf : SafeOn step n f S ctx) : SafeOn step (n + 1) a (plusOneSpec S) ctx := by
  intro D bs hc x sp ret hA hst
  have hD : ∀ i (hi : i < (plusOneCode rel).length), D (a + i) ∧ bs (a + i) =
      (plusOneCode rel)[i] := fun i hi => hc _ _ (hcode i hi)
  -- addresses
  have t0 := toNat_ofNat_lt (k := a) (by omega)
  have t4 := toNat_ofNat_lt (k := a + 4) (by omega)
  have t9 := toNat_ofNat_lt (k := a + 9) (by omega)
  have t13 := toNat_ofNat_lt (k := a + 13) (by omega)
  have t17 := toNat_ofNat_lt (k := a + 17) (by omega)
  have h04 : BitVec.ofNat 64 a + 4#64 = BitVec.ofNat 64 (a + 4) := by
    apply BitVec.eq_of_toNat_eq; rw [t4, BitVec.toNat_add, t0]; simp; omega
  have h49 : BitVec.ofNat 64 (a + 4) + 5#64 = BitVec.ofNat 64 (a + 9) := by
    apply BitVec.eq_of_toNat_eq; rw [t9, BitVec.toNat_add, t4]; simp; omega
  have h913 : BitVec.ofNat 64 (a + 9) + 4#64 = BitVec.ofNat 64 (a + 13) := by
    apply BitVec.eq_of_toNat_eq; rw [t13, BitVec.toNat_add, t9]; simp; omega
  have h1317 : BitVec.ofNat 64 (a + 13) + 4#64 = BitVec.ofNat 64 (a + 17) := by
    apply BitVec.eq_of_toNat_eq; rw [t17, BitVec.toNat_add, t13]; simp; omega
  -- code pieces
  have c1 := cov_at (o := 0) (piece := [0x48, 0x83, 0xec, 0x08]) (by rw [t0]; rfl) (piece_cov hD
    (fun i hi => match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl))
  have c2 := cov_at (o := 4) (piece := Insn.encode (.call rel)) t4 (piece_cov hD
    (fun i hi => match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl))
  have c3 := cov_at (o := 9) (piece := [0x48, 0x83, 0xc4, 0x08]) t9 (piece_cov hD
    (fun i hi => match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl))
  have c4 := cov_at (o := 13) (piece := [0x48, 0x83, 0xc0, 0x01]) t13 (piece_cov hD
    (fun i hi => match i, hi with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl))
  have c5 := cov_at (o := 17) (piece := Insn.encode .ret) t17 (piece_cov hD
    (fun i hi => match i, hi with | 0, _ => rfl))
  -- stack
  have hst' : S.stack + 16 ≤ sp.toNat := hst
  have hA' : sp.toNat % 16 = 8 := hA
  have es1 : (sp - 8#64).toNat = sp.toNat - 8 := toNat_sub_eight' (by omega)
  have eback : sp - 8#64 + 8#64 = sp := by bv_omega
  have hA2 : FnSpec.EntryAligned (sp - 8#64 - 8#64) := by
    unfold FnSpec.EntryAligned; rw [toNat_sub_eight' (by omega), es1]; omega
  -- the instructions
  have TA := code_triple c1 (aluI8_step (v := sp) dec_sub rfl (by decide) h04)
  rw [show Silmaril.X86.Ext.AluOp.resultN .sub sp ((0x08#8 : BitVec 8).signExtend 64) =
    sp - 8#64 by rw [sext8]; rfl] at TA
  have SB := scall_rule (pc := BitVec.ofNat 64 (a + 4)) (s := sp - 8#64) hc hf c2 htarget hA2
    (by rw [es1]; omega) x
  rw [h49] at SB
  have TC1 := code_triple c3 (aluI8_step (v := sp - 8#64) dec_add_rsp rfl (by decide) h913)
  rw [show Silmaril.X86.Ext.AluOp.resultN .add (sp - 8#64) ((0x08#8 : BitVec 8).signExtend 64) =
    sp by rw [sext8]; exact eback] at TC1
  have TC3 := code_triple c5 (ret_step (BitVec.ofNat 64 (a + 17)) sp ret)
  -- assembly
  have blk : ∀ k, blockAny (sp.toNat - (S.stack + 16)) (S.stack + 8 + 8 + k) =
      (blockAny (sp.toNat - 8 - 8 - S.stack) (S.stack + 8) ∗ blockAny (sp.toNat - 8) (8 + k)) := by
    intro k
    rw [show S.stack + 8 + 8 + k = (S.stack + 8) + (8 + k) by omega, blockAny_add,
      show sp.toNat - (S.stack + 16) + (S.stack + 8) = sp.toNat - 8 by omega,
      show sp.toNat - (S.stack + 16) = sp.toNat - 8 - 8 - S.stack by omega]
  refine STriple.triple_seq (Triple.conseq ?_ (Triple.frame TA
      (SysVRegs (S.args x) ∗ blockAny (sp.toNat - 8 - 8 - S.stack) (S.stack + 8) ∗ S.pre x ∗
        wordPt sp.toNat ret ∗ blockAny (sp.toNat - 8) 8)) (entails_refl _))
    (STriple.seq_triple (STriple.conseq ?_ (STriple.frame SB
      (wordPt sp.toNat ret ∗ blockAny (sp.toNat - 8) 8)) (entails_refl _)) ?_)
  · -- entry
    apply entails_of_eq
    simp only [FnSpec.SysVPre, FnSpec.SysVEntry, plusOneSpec]
    rw [show S.stack + 16 = S.stack + 8 + 8 + 0 by omega, blk 0]
    ac_rfl
  · apply entails_of_eq
    rw [es1]
    ac_rfl
  · -- after the call: add, add, ret
    rw [sep_sexists, sexists_sep]
    refine Triple.sexists fun v => ?_
    have TC2 := code_triple c4 (aluI8_step (v := v) dec_add_rax rfl (by decide) h1317)
    rw [show Silmaril.X86.Ext.AluOp.resultN .add v ((0x01#8 : BitVec 8).signExtend 64) =
      v + 1#64 by rw [sext1]; rfl] at TC2
    have R1 := Triple.frame TC1 (regPt .rax v ∗ regsAny clobberedRegs ∗
      blockAny (sp.toNat - 8 - 8 - S.stack) (S.stack + 8) ∗ S.post x v ∗
      wordPt sp.toNat ret ∗ blockAny (sp.toNat - 8) 8)
    have R2 := Triple.frame TC2 (regPt .rsp sp ∗ regsAny clobberedRegs ∗
      blockAny (sp.toNat - 8 - 8 - S.stack) (S.stack + 8) ∗ S.post x v ∗
      wordPt sp.toNat ret ∗ blockAny (sp.toNat - 8) 8)
    have R3 := Triple.frame TC3 (regPt .rax (v + 1#64) ∗ regsAny clobberedRegs ∗ flagsAny ∗
      blockAny (sp.toNat - 8 - 8 - S.stack) (S.stack + 8) ∗ S.post x v ∗
      blockAny (sp.toNat - 8) 8)
    refine Triple.trans (Triple.pre ?_ R1) (Triple.trans (Triple.pre ?_ R2)
      (Triple.post (Triple.pre ?_ R3) ?_))
    · apply entails_of_eq
      simp only [SysVRet]
      rw [es1]
      ac_rfl
    · apply entails_of_eq; ac_rfl
    · apply entails_of_eq; ac_rfl
    · simp only [FnSpec.SysVPost, FnSpec.SysVExit, plusOneSpec, SysVRet]
      rw [sep_sexists]
      refine sexists_intro (v + 1#64) ?_
      rw [show S.stack + 16 + 8 = S.stack + 8 + 8 + 8 by omega, blk 8, blockAny_add (sp.toNat - 8) 8 8,
        show sp.toNat - 8 + 8 = sp.toNat by omega]
      refine entails_trans ?_ (sep_mono_right _ (sep_mono_right _
        (sexists_intro v (spure_sep_intro rfl (entails_refl _)))))
      refine entails_trans (sep_mono_left _ (sep_mono_right _ (sep_mono_right _
        (sep_mono_right _ (wordPt_blockAny _ _))))) (entails_of_eq ?_)
      ac_rfl

end Silmaril.Proofs.Machine.Link.LibMiniClient
