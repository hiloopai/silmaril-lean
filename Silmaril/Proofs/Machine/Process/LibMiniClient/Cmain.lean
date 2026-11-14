module

public import Silmaril.Machine.Link.BackedSpec.Thms
public import Silmaril.Proofs.Machine.Process.LibMiniClient.Insn
public import Silmaril.Machine.Link.Examples.LibMiniClient.Thms

/-!
# Proofs: `cmain` of ladder rung 12 meets a backed-stack `FnSpec`

```
cmain: sub $0x18,%rsp; mov $5,%edx; mov $0x78,%esi; mov %rsp,%rdi; call memset
       mov %rsp,%rsi; lea 8(%rsp),%rdi; mov $6,%edx; movb $0,5(%rsp); call memcpy
       lea 8(%rsp),%rdi; call len1; add $0x18,%rsp; ret
```

`cmain` passes two buffers in its own frame (`a` at `rsp`, `b` at `rsp + 8`) to `memset`
(`fillSpec`), `memcpy` (`copySpec`) and `len1` (`len1Spec`). The callee specs ask for backed
buffers (`bytesPt`), which the System V template's `blockAny` budget does not give (R8's
finding). `cmainSpec` is therefore proved against the **backed-stack template** `SafeB`
(`Silmaril.Machine.Link.BackedSpec`): a 48-byte backed budget, no arguments, `rax = 6` at
return.

`cmain_safeB`: if the image holds `cmainCode` at `0x401020` and `memset`, `memcpy` and
`len1` are `Safe n` at `0x4010b0`, `0x401080` and `0x401060` (their linked addresses), then
`cmain` is `SafeB (n + 1)` for `cmainSpec`. The callees are used only through their `Safe`
assumptions; the proof is instruction triples (`Insn`, R1's `aluI8_step`, A's `ret_step`),
the step-indexed call rule `scall_rule` three times, and frame bookkeeping.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient

open Silmaril.X86 (MState Word Byte Reg Insn)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.BackedSpec
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Proofs.Machine.Link.FnSpec
open Silmaril.Proofs.Machine.Link.BackedSpec
open Silmaril.Proofs.Machine.Link.LibMiniClient (piece_cov cov_at toNat_ofNat_lt)
open Silmaril.Machine.Link.Unit (Contains)

/-- The bytes of `cmain` (`main.o`'s `.text.cmain`, linked at `0x401020`, with its three
`call` displacements resolved). -/
def cmainCode : List Byte :=
  [0x48, 0x83, 0xec, 0x18, 0xba, 0x05, 0x00, 0x00, 0x00, 0xbe, 0x78, 0x00, 0x00, 0x00,
   0x48, 0x89, 0xe7, 0xe8, 0x7a, 0x00, 0x00, 0x00, 0x48, 0x89, 0xe6, 0x48, 0x8d, 0x7c,
   0x24, 0x08, 0xba, 0x06, 0x00, 0x00, 0x00, 0xc6, 0x44, 0x24, 0x05, 0x00, 0xe8, 0x33,
   0x00, 0x00, 0x00, 0x48, 0x8d, 0x7c, 0x24, 0x08, 0xe8, 0x09, 0x00, 0x00, 0x00, 0x48,
   0x83, 0xc4, 0x18, 0xc3]

/-- **`cmain`'s spec** (backed-stack template): no arguments, a 48-byte backed budget
(its 24-byte frame and the 24 bytes `len1` needs below it), returns `6`. -/
def cmainSpec : FnSpec where
  Arg := Unit
  args _ := []
  stack := 48
  pre _ := emp
  post _ v := ⌜v = 6#64⌝

/-- The address of `cmain`'s byte `k`. -/
def pcm (k : Nat) : Word := BitVec.ofNat 64 (0x401020 + k)

variable {D : Nat → Prop} {bs : Nat → Byte}

theorem cpiece
    (hD : ∀ i (hi : i < cmainCode.length), D (0x401020 + i) ∧ bs (0x401020 + i) = cmainCode[i])
    (o : Nat) (piece : List Byte)
    (hp : ∀ i (hi : i < piece.length), cmainCode[o + i]? = some piece[i])
    (ho : 0x401020 + o < 2 ^ 64) :
    ∀ i (hi : i < piece.length), D ((pcm o).toNat + i) ∧ bs ((pcm o).toNat + i) = piece[i] :=
  cov_at (toNat_ofNat_lt ho) (piece_cov hD hp)

/-- Eliminate a backed block in a precondition. -/
theorem STriple.blockB_elim {n a k : Nat} {P Q : SProp}
    (h : ∀ zs : List Byte, zs.length = k → STriple n (bytesPt a zs ∗ P) Q) :
    STriple n (blockB a k ∗ P) Q := by
  unfold blockB
  rw [sexists_sep]
  exact STriple.sexists_pre fun zs => by rw [sep_assoc]; exact STriple.spure_pre (h zs)

theorem weaken_rax_pure {φ : Prop} {v : Word} {L R : SProp}
    (h : L = (⌜φ⌝ ∗ regPt .rax v ∗ R)) : L ⊢ₛ (regAny .rax ∗ R) :=
  entails_trans (entails_of_eq h)
    (spure_sep_elim fun _ => sep_mono_left _ (sexists_intro v (entails_refl _)))

theorem pure2_rax {φ ψ : Prop} {v w : Word} {L R : SProp}
    (h : L = (⌜φ⌝ ∗ ⌜ψ⌝ ∗ regPt .rax v ∗ R)) (hv : φ → ψ → v = w) :
    L ⊢ₛ (regPt .rax w ∗ R) :=
  entails_trans (entails_of_eq h)
    (spure_sep_elim fun h1 => spure_sep_elim fun h2 => by rw [hv h1 h2]; exact entails_refl _)

/-! ## Decoding -/

theorem dec_sub18 : Silmaril.X86.Ext.decode [0x48, 0x83, 0xec, 0x18] =
    some (.aluI8 .q .sub (.reg .rsp) 0x18#8, 4) := by decide
theorem dec_add18 : Silmaril.X86.Ext.decode [0x48, 0x83, 0xc4, 0x18] =
    some (.aluI8 .q .add (.reg .rsp) 0x18#8, 4) := by decide
theorem dec_edx5 : Silmaril.X86.Ext.decode [0xba, 0x05, 0x00, 0x00, 0x00] =
    some (.movI32 .rdx 5#32, [0xba, 0x05, 0x00, 0x00, 0x00].length) := by decide
theorem dec_esi78 : Silmaril.X86.Ext.decode [0xbe, 0x78, 0x00, 0x00, 0x00] =
    some (.movI32 .rsi 0x78#32, [0xbe, 0x78, 0x00, 0x00, 0x00].length) := by decide
theorem dec_edx6 : Silmaril.X86.Ext.decode [0xba, 0x06, 0x00, 0x00, 0x00] =
    some (.movI32 .rdx 6#32, [0xba, 0x06, 0x00, 0x00, 0x00].length) := by decide
theorem dec_rdi_rsp : Silmaril.X86.Ext.decode [0x48, 0x89, 0xe7] =
    some (.mov .q (.reg .rdi) .rsp, [0x48, 0x89, 0xe7].length) := by decide
theorem dec_rsi_rsp : Silmaril.X86.Ext.decode [0x48, 0x89, 0xe6] =
    some (.mov .q (.reg .rsi) .rsp, [0x48, 0x89, 0xe6].length) := by decide
theorem dec_lea8 : Silmaril.X86.Ext.decode [0x48, 0x8d, 0x7c, 0x24, 0x08] =
    some (.lea .q .rdi (rspMem 8#32), [0x48, 0x8d, 0x7c, 0x24, 0x08].length) := by decide
theorem dec_store5 : Silmaril.X86.Ext.decode [0xc6, 0x44, 0x24, 0x05, 0x00] =
    some (.movI8 (.mem (rspMem 5#32)) 0#8, [0xc6, 0x44, 0x24, 0x05, 0x00].length) := by decide

/-! ## `cmain` -/

theorem fill_eqs {s c : Word} {old : List Byte} (hl : old.length = 5) :
    fillSpec.args ⟨s, c, old⟩ = [s, c, 5#64] ∧ fillSpec.pre ⟨s, c, old⟩ = bytesPt s.toNat old ∧
    ∀ v, fillSpec.post ⟨s, c, old⟩ v = (⌜v = s⌝ ∗
        bytesPt s.toNat (List.replicate 5 (c.setWidth 8))) := by
  refine ⟨by show [_, _, _] = _; rw [hl], ?_, fun v => by show (⌜_⌝ ∗ _) = _; rw [hl]⟩
  show (⌜_⌝ ∗ _) = _
  rw [eq_true (show old.length < 2 ^ 64 by omega), spure_true_emp, emp_sep]

theorem copy_eqs {d s : Word} {src old : List Byte} (hs : src.length = 6) (hl : old.length = 6) :
    copySpec.args ⟨d, s, src, old⟩ = [d, s, 6#64] ∧
    copySpec.pre ⟨d, s, src, old⟩ = (bytesPt d.toNat old ∗ bytesPtRO s.toNat src) ∧
    ∀ v, copySpec.post ⟨d, s, src, old⟩ v =
      (⌜v = d⌝ ∗ (bytesPt d.toNat src ∗ bytesPtRO s.toNat src)) := by
  refine ⟨by show [_, _, _] = _; rw [hs], ?_, fun v => rfl⟩
  show (⌜_⌝ ∗ _) = _
  rw [eq_true (show old.length = src.length ∧ src.length < 2 ^ 64 by omega), spure_true_emp,
    emp_sep]

theorem len1_eqs {s : Word} {str : List Byte} (h0 : (0 : Byte) ∉ str) :
    len1Spec.args ⟨s, str⟩ = [s] ∧ len1Spec.pre ⟨s, str⟩ = bytesPtRO s.toNat (str ++ [0]) ∧
    ∀ v, len1Spec.post ⟨s, str⟩ v = sexists fun w => ⌜v = w + 1#64⌝ ∗
      (⌜w = BitVec.ofNat 64 str.length⌝ ∗ bytesPtRO s.toNat (str ++ [0])) := by
  refine ⟨rfl, ?_, fun v => rfl⟩
  show (⌜_⌝ ∗ _) = _
  rw [eq_true h0, spure_true_emp, emp_sep]


/-- `cmain`'s 48-byte backed budget, split into the pieces the body uses. -/
theorem budget_split (t : Nat) : blockB t 48 ⊢ₛ
    (blockAny t 16 ∗ blockAny (t + 16) 8 ∗ blockB (t + 24) 5 ∗ blockAny (t + 29) 1 ∗
      blockAny (t + 30) 2 ∗ blockB (t + 32) 6 ∗ blockAny (t + 38) 2 ∗ blockAny (t + 40) 8) := by
  refine entails_trans (blockB_split t 16 32) (sep_mono (blockB_blockAny _ _) ?_)
  refine entails_trans (blockB_split (t + 16) 8 24) (sep_mono (blockB_blockAny _ _) ?_)
  rw [show t + 16 + 8 = t + 24 by omega]
  refine entails_trans (blockB_split (t + 24) 5 19) (sep_mono_right _ ?_)
  rw [show t + 24 + 5 = t + 29 by omega]
  refine entails_trans (blockB_split (t + 29) 1 18) (sep_mono (blockB_blockAny _ _) ?_)
  rw [show t + 29 + 1 = t + 30 by omega]
  refine entails_trans (blockB_split (t + 30) 2 16) (sep_mono (blockB_blockAny _ _) ?_)
  rw [show t + 30 + 2 = t + 32 by omega]
  refine entails_trans (blockB_split (t + 32) 6 10) (sep_mono_right _ ?_)
  rw [show t + 32 + 6 = t + 38 by omega]
  refine entails_trans (blockB_split (t + 38) 2 8) (sep_mono (blockB_blockAny _ _) ?_)
  rw [show t + 38 + 2 = t + 40 by omega]
  exact blockB_blockAny _ _

/-- The pieces `cmain` gives back, joined into the readable budget of the template. -/
theorem rd_join (t : Nat) (b1 b2 : List Byte) (h1 : b1.length = 6) (h2 : b2.length = 6)
    (w : Word) :
    (blockAny t 16 ∗ blockAny (t + 16) 8 ∗ bytesPtRO (t + 24) b1 ∗ blockAny (t + 30) 2 ∗
      bytesPtRO (t + 32) b2 ∗ blockAny (t + 38) 2 ∗ blockAny (t + 40) 8 ∗ wordPt (t + 48) w) ⊢ₛ
      blockRd t 56 := by
  rw [show (56 : Nat) = 16 + (8 + (6 + (2 + (6 + (2 + (8 + 8)))))) from rfl,
    blockRd_add t 16, blockRd_add (t + 16) 8, blockRd_add (t + 16 + 8) 6,
    blockRd_add (t + 16 + 8 + 6) 2, blockRd_add (t + 16 + 8 + 6 + 2) 6,
    blockRd_add (t + 16 + 8 + 6 + 2 + 6) 2, blockRd_add (t + 16 + 8 + 6 + 2 + 6 + 2) 8]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  have r1 := bytesAt_blockRd ro_ro (t + 24) b1
  have r2 := bytesAt_blockRd ro_ro (t + 32) b2
  rw [h1] at r1
  rw [h2] at r2
  exact sep_mono (blockAny_blockRd _ _) (sep_mono (blockAny_blockRd _ _) (sep_mono r1
    (sep_mono (blockAny_blockRd _ _) (sep_mono r2 (sep_mono (blockAny_blockRd _ _)
      (sep_mono (blockAny_blockRd _ _) (wordPt_blockRd _ _)))))))

/-- `memset`'s five bytes and the stored NUL, read-only. -/
theorem ro_join {a : Nat} :
    (bytesPt a (List.replicate 5 (0x78#8 : Byte)) ∗ bytesPt (a + 5) [0#8]) ⊢ₛ
      bytesPtRO a (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) := by
  rw [bytesPtRO, bytesAt_append, List.length_replicate]
  exact sep_mono (bytesAt_mono rw_ro _ _) (bytesAt_mono rw_ro _ _)

/-- **`cmain` meets `cmainSpec`** (backed-stack template), from the `Safe` contracts of its
three callees at their linked addresses. -/
theorem cmain_safeB {ctx : Silmaril.Machine.Link.Contract.Image} {n : Nat}
    (hcode : ∀ i (hi : i < cmainCode.length), ContainsX ctx (0x401020 + i) cmainCode[i])
    (hset : Safe n 0x4010b0 fillSpec ctx) (hcpy : Safe n 0x401080 copySpec ctx)
    (hlen : Safe n 0x401060 len1Spec ctx) : SafeB (n + 1) 0x401020 cmainSpec ctx := by
  intro D bs hc _ sp ret hA hst
  have hD : ∀ i (hi : i < cmainCode.length), D (0x401020 + i) ∧ bs (0x401020 + i) =
      cmainCode[i] := fun i hi => hc _ _ (hcode i hi)
  have hA' : sp.toNat % 16 = 8 := hA
  have hst' : 48 ≤ sp.toNat := hst
  have hlim : sp.toNat < 2 ^ 64 := sp.isLt
  obtain ⟨s, hsdef⟩ : ∃ s, s = sp - 24#64 := ⟨_, rfl⟩
  have es : s.toNat = sp.toNat - 24 := by subst hsdef; bv_omega
  have hsp : s + 24#64 = sp := by subst hsdef; bv_omega
  have e8 : (s + 8#64).toNat = s.toNat + 8 := by bv_omega
  have e5 : (s + (5#32 : BitVec 32).signExtend 64).toNat = s.toNat + 5 := by
    rw [show (5#32 : BitVec 32).signExtend 64 = 5#64 by decide]; bv_omega
  have hAl : FnSpec.EntryAligned (s - 8#64) := by
    unfold FnSpec.EntryAligned; rw [toNat_sub_eight' (by omega)]; omega
  -- the straight-line instructions
  have T1 := code_triple (cpiece hD 0 _ (by decide) (by decide))
    (aluI8_step (v := sp) (pc := pcm 0) (pc' := pcm 4) dec_sub18 rfl (by decide) (by decide))
  rw [show Silmaril.X86.Ext.AluOp.resultN .sub sp ((0x18#8 : BitVec 8).signExtend 64) = s by
    rw [hsdef]; rfl] at T1
  have T2 := code_triple (cpiece hD 4 _ (by decide) (by decide))
    (movI32_step (pc := pcm 4) (pc' := pcm 9) dec_edx5 (by decide))
  have T3 := code_triple (cpiece hD 9 _ (by decide) (by decide))
    (movI32_step (pc := pcm 9) (pc' := pcm 14) dec_esi78 (by decide))
  have T4 := code_triple (cpiece hD 14 _ (by decide) (by decide))
    (mov_step (v := s) (pc := pcm 14) (pc' := pcm 17) (by decide) dec_rdi_rsp (by decide))
  have T6 := code_triple (cpiece hD 22 _ (by decide) (by decide))
    (mov_step (v := s) (pc := pcm 22) (pc' := pcm 25) (by decide) dec_rsi_rsp (by decide))
  have T7 := code_triple (cpiece hD 25 _ (by decide) (by decide))
    (leaRsp_step (s := s) (pc := pcm 25) (pc' := pcm 30) (by decide) dec_lea8 (by decide))
  have T8 := code_triple (cpiece hD 30 _ (by decide) (by decide))
    (movI32_step (pc := pcm 30) (pc' := pcm 35) dec_edx6 (by decide))
  have T9 := code_triple (cpiece hD 35 _ (by decide) (by decide))
    (storeI8Rsp_step (s := s) (pc := pcm 35) (pc' := pcm 40) e5 dec_store5 (by decide))
  have T11 := code_triple (cpiece hD 45 _ (by decide) (by decide))
    (leaRsp_step (s := s) (pc := pcm 45) (pc' := pcm 50) (by decide) dec_lea8 (by decide))
  have T13 := code_triple (cpiece hD 55 _ (by decide) (by decide))
    (aluI8_step (v := s) (pc := pcm 55) (pc' := pcm 59) dec_add18 rfl (by decide) (by decide))
  rw [show Silmaril.X86.Ext.AluOp.resultN .add s ((0x18#8 : BitVec 8).signExtend 64) = sp by
    rw [← hsp]; rfl] at T13
  have T14 := code_triple (cpiece hD 59 (Insn.encode .ret) (by decide) (by decide))
    (ret_step (pcm 59) sp ret)
  simp only [Silmaril.X86.Ext.Sz.bits, BitVec.setWidth_eq] at T4 T6
  rw [show (5#32 : BitVec 32).setWidth 64 = 5#64 by decide] at T2
  rw [show (0x78#32 : BitVec 32).setWidth 64 = 0x78#64 by decide] at T3
  rw [show (6#32 : BitVec 32).setWidth 64 = 6#64 by decide] at T8
  rw [show (8#32 : BitVec 32).signExtend 64 = 8#64 by decide] at T7 T11
  have hb := budget_split (sp.toNat - 48)
  have hrd := rd_join (sp.toNat - 48) (List.replicate 5 (0x78#8 : Byte) ++ [0#8])
    (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) rfl rfl ret
  rw [show sp.toNat - 48 + 16 = s.toNat - 8 by omega, show sp.toNat - 48 + 24 = s.toNat by omega,
    show sp.toNat - 48 + 29 = s.toNat + 5 by omega, show sp.toNat - 48 + 30 = s.toNat + 6 by omega,
    show sp.toNat - 48 + 32 = (s + 8#64).toNat by omega,
    show sp.toNat - 48 + 38 = (s + 8#64).toNat + 6 by omega,
    show sp.toNat - 48 + 40 = s.toNat + 16 by omega] at hb
  rw [show sp.toNat - 48 + 16 = s.toNat - 8 by omega, show sp.toNat - 48 + 24 = s.toNat by omega,
    show sp.toNat - 48 + 30 = s.toNat + 6 by omega,
    show sp.toNat - 48 + 32 = (s + 8#64).toNat by omega,
    show sp.toNat - 48 + 38 = (s + 8#64).toNat + 6 by omega,
    show sp.toNat - 48 + 40 = s.toNat + 16 by omega,
    show sp.toNat - 48 + 48 = sp.toNat by omega] at hrd
  refine STriple.conseq (P := blockB s.toNat 5 ∗ blockB (s + 8#64).toNat 6 ∗ Code D bs ∗
      ripPt (pcm 0) ∗ regPt .rsp sp ∗ regAny .rdi ∗ regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗
      regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
      wordPt sp.toNat ret ∗ blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗
      blockAny (s.toNat - 8) 8 ∗ blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
      blockAny ((s + 8#64).toNat + 6) 2) ?_ ?_ (entails_refl _)
  · simp only [FnSpecB.SysVPreB, cmainSpec, SysVRegs, regsAny, regsWith, argRegs, scratchRegs]
    rw [show BitVec.ofNat 64 0x401020 = pcm 0 from rfl]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_right _ (sep_mono_right _ (sep_mono_left _ hb))))))) (entails_of_eq ?_)
    ac_rfl
  refine STriple.blockB_elim fun old5 hl5 => ?_
  rw [sep_left_comm]
  refine STriple.blockB_elim fun old6 hl6 => ?_
  obtain ⟨fa, fp, fq⟩ := fill_eqs (s := s) (c := 0x78#64) hl5
  obtain ⟨ca, cp, cq⟩ := copy_eqs (d := s + 8#64) (s := s)
    (src := (List.replicate 5 (0x78#8 : Byte) ++ [0#8])) (by rfl) hl6
  obtain ⟨la, lp, lq⟩ := len1_eqs (s := s + 8#64) (str := List.replicate 5 (0x78#8 : Byte))
    (by decide)
  have S5 := scall_rule (S := fillSpec) (pc := pcm 17) (s := s) hc hset
    (cpiece hD 17 (Insn.encode (.call 0x7a#32)) (by decide) (by decide)) (by decide) hAl
    (by show 0 + 8 ≤ s.toNat; omega) ⟨s, 0x78#64, old5⟩
  rw [fa, fp, show fillSpec.stack = 0 from rfl, Nat.sub_zero, Nat.zero_add,
    show pcm 17 + 5#64 = pcm 22 by decide] at S5
  simp only [fq, show ((0x78#64 : Word).setWidth 8) = (0x78#8 : Byte) by decide, SysVRegs,
    SysVRet, regsAny, regsWith, argRegs, scratchRegs, clobberedRegs] at S5
  have S10 := scall_rule (S := copySpec) (pc := pcm 40) (s := s) hc hcpy
    (cpiece hD 40 (Insn.encode (.call 0x33#32)) (by decide) (by decide)) (by decide) hAl
    (by show 0 + 8 ≤ s.toNat; omega)
    ⟨s + 8#64, s, (List.replicate 5 (0x78#8 : Byte) ++ [0#8]), old6⟩
  rw [ca, cp, show copySpec.stack = 0 from rfl, Nat.sub_zero, Nat.zero_add,
    show pcm 40 + 5#64 = pcm 45 by decide] at S10
  simp only [cq, SysVRegs, SysVRet, regsAny, regsWith, argRegs, scratchRegs, clobberedRegs] at S10
  have S12 := scall_rule (S := len1Spec) (pc := pcm 50) (s := s) hc hlen
    (cpiece hD 50 (Insn.encode (.call 0x09#32)) (by decide) (by decide)) (by decide) hAl
    (by show 16 + 8 ≤ s.toNat; omega) ⟨s + 8#64, List.replicate 5 (0x78#8 : Byte)⟩
  rw [la, lp, show len1Spec.stack = 16 from rfl, show s.toNat - 8 - 16 = sp.toNat - 48 by omega,
    blockAny_add (sp.toNat - 48) 16 8, show sp.toNat - 48 + 16 = s.toNat - 8 by omega,
    show pcm 50 + 5#64 = pcm 55 by decide] at S12
  have S12w := STriple.conseq (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (show bytesPt _ _ ⊢ₛ bytesPtRO _ _ from
        bytesAt_mono rw_ro (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))))))))
    S12 (entails_refl _)
  simp only [lq, SysVRegs, SysVRet, regsAny, regsWith, argRegs, scratchRegs, clobberedRegs] at S12w
  have T9' : Triple (Code D bs ∗ ripPt (pcm 35) ∗ regPt .rsp s ∗ blockAny (s.toNat + 5) 1 ∗
      bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)))
      ((Code D bs ∗ ripPt (pcm 40) ∗ regPt .rsp s) ∗
          bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8])) :=
    Triple.conseq (entails_of_eq (by ac_rfl))
      (Triple.frame T9 (bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte))))
      (entails_trans (entails_of_eq (by ac_rfl : _ = ((Code D bs ∗ ripPt (pcm 40) ∗ regPt .rsp s) ∗
        (bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗
            bytesPt (s.toNat + 5) [0#8])))) (sep_mono_right _ ro_join))
  refine STriple.triple_seq ?U1 (STriple.seq (R := regAny .rax ∗ (Code D bs ∗ ripPt (pcm 22) ∗
      regPt .rsp s ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗
          regAny .r9 ∗
      regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
      bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
      blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
      bytesPt (s + 8#64).toNat old6)))
    (STriple.conseq (entails_refl _) (STriple.frame S5 (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
        blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPt (s + 8#64).toNat old6)) ?E5) ?_)
  case U1 =>
    exact Triple.trans (Triple.pre (entails_of_eq (by ac_rfl))
        (Triple.frame T1 (regAny .rdi ∗ regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗ regAny .r8 ∗
            regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗ wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5)))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl))
        (Triple.frame T2 (regPt .rsp s ∗ flagsAny ∗ regAny .rdi ∗ regAny .rsi ∗ regAny .rcx ∗
            regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗
                wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5)))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl))
        (Triple.frame T3 (regPt .rsp s ∗ flagsAny ∗ regAny .rdi ∗ regPt .rdx 5#64 ∗ regAny .rcx ∗
            regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗
                wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5)))
      (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame T4 (flagsAny ∗ regPt .rdx 5#64 ∗ regPt .rsi 0x78#64 ∗ regAny .rcx ∗
            regAny .r8 ∗
            regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗ wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5))
        (entails_of_eq (by ac_rfl)))))
  case E5 =>
    rw [sep_sexists, sexists_sep]
    exact sexists_elim fun v => weaken_rax_pure (by ac_rfl)
  refine STriple.triple_seq ?U2 (STriple.seq (R := regAny .rax ∗ (Code D bs ∗ ripPt (pcm 45) ∗
      regPt .rsp s ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗
          regAny .r9 ∗
      regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
      (bytesPt (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
      bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8])) ∗ (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
      blockAny ((s + 8#64).toNat + 6) 2)))
    (STriple.conseq (entails_refl _) (STriple.frame S10 (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
        blockAny ((s + 8#64).toNat + 6) 2)) ?E10) ?_)
  case U2 =>
    exact Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T6 (regAny .rax ∗
        regAny .rcx ∗ regAny .rdx ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗
        regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
        bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
        blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPt (s + 8#64).toNat old6))))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T7 (regPt .rsi s ∗
          regAny .rax ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗
          regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
          bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
          blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
          blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
          bytesPt (s + 8#64).toNat old6))))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T8 (regPt .rsp s ∗
          regPt .rdi (s + 8#64) ∗ regPt .rsi s ∗ regAny .rax ∗ regAny .rcx ∗ regAny .r8 ∗
              regAny .r9 ∗
          regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
          bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
          blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
          blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
          bytesPt (s + 8#64).toNat old6))))
      (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame T9' (regPt .rdx 6#64 ∗
          regPt .rdi (s + 8#64) ∗ regPt .rsi s ∗ regAny .rax ∗ regAny .rcx ∗ regAny .r8 ∗
              regAny .r9 ∗
          regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗ wordPt sp.toNat ret ∗
          blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
          blockAny ((s + 8#64).toNat + 6) 2 ∗ bytesPt (s + 8#64).toNat old6))
        (entails_of_eq (by ac_rfl)))))
  case E10 =>
    rw [sep_sexists, sexists_sep]
    exact sexists_elim fun v => weaken_rax_pure (by ac_rfl)
  refine STriple.triple_seq ?U3 (STriple.seq_triple (R := regPt .rax 6#64 ∗ (Code D bs ∗
      ripPt (pcm 55) ∗ regPt .rsp s ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗
      regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
          (blockAny (sp.toNat - 48) 16 ∗
      blockAny (s.toNat - 8) 8) ∗
      bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
          (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
      bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))))
    (STriple.conseq (entails_refl _) (STriple.frame S12w (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))) ?E12) ?_)
  case U3 =>
    exact Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame T11 (regAny .rax ∗ regAny .rcx ∗
        regAny .rdx ∗ regAny .rsi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
        blockAny (s.toNat - 8) 8 ∗
        bytesPt (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
        bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗ (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
        blockAny ((s + 8#64).toNat + 6) 2)))
      (entails_of_eq (by ac_rfl))
  case E12 =>
    simp only [sep_sexists, sexists_sep]
    exact sexists_elim fun v => sexists_elim fun w => pure2_rax (by ac_rfl)
      (fun h1 h2 => by subst h1; subst h2; decide)
  refine Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T13 (regPt .rax 6#64 ∗
      regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗
          regAny .r10 ∗
      regAny .r11 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
      bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
          (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
      bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8])))))
    (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame T14 (flagsAny ∗ regPt .rax 6#64 ∗
        regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗
        regAny .r10 ∗ regAny .r11 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
        bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))) ?_)
  simp only [FnSpecB.SysVPostB, cmainSpec, SysVRet, regsAny, regsWith, clobberedRegs]
  rw [sep_sexists]
  refine sexists_intro 6#64 ?_
  rw [show (⌜(6#64 : Word) = 6#64⌝ : SProp) = emp by rw [eq_true rfl, spure_true_emp]]
  refine entails_trans (entails_of_eq (by ac_rfl : _ = ((blockAny (sp.toNat - 48) 16 ∗
      blockAny (s.toNat - 8) 8 ∗ bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
      blockAny (s.toNat + 6) 2 ∗
      bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
      blockAny ((s + 8#64).toNat + 6) 2 ∗ blockAny (s.toNat + 16) 8 ∗ wordPt sp.toNat ret) ∗
      (Code D bs ∗ ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ regPt .rax 6#64 ∗ regAny .rcx ∗
          regAny .rdx ∗
      regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny))))
    (entails_trans (sep_mono_left _ hrd) (entails_of_eq (by ac_rfl)))


/-- Eliminate a backed block in a total precondition. -/
theorem Triple.blockB_elim {a k : Nat} {P Q : SProp}
    (h : ∀ zs : List Byte, zs.length = k → Triple (bytesPt a zs ∗ P) Q) :
    Triple (blockB a k ∗ P) Q := by
  unfold blockB
  rw [sexists_sep]
  exact Triple.sexists fun zs => by rw [sep_assoc]; exact Triple.spure (h zs)

/-- **`cmain` meets `cmainSpec`, totally** (backed-stack template): from the total contracts of
its callees, `cmain` returns. -/
theorem cmain_safeTB {ctx : Silmaril.Machine.Link.Contract.Image}
    (hcode : ∀ i (hi : i < cmainCode.length), ContainsX ctx (0x401020 + i) cmainCode[i])
    (hset : SafeT 0x4010b0 fillSpec ctx) (hcpy : SafeT 0x401080 copySpec ctx)
    (hlen : SafeT 0x401060 len1Spec ctx) : SafeTB 0x401020 cmainSpec ctx := by
  intro D bs hc _ sp ret hA hst
  have hD : ∀ i (hi : i < cmainCode.length), D (0x401020 + i) ∧ bs (0x401020 + i) =
      cmainCode[i] := fun i hi => hc _ _ (hcode i hi)
  have hA' : sp.toNat % 16 = 8 := hA
  have hst' : 48 ≤ sp.toNat := hst
  have hlim : sp.toNat < 2 ^ 64 := sp.isLt
  obtain ⟨s, hsdef⟩ : ∃ s, s = sp - 24#64 := ⟨_, rfl⟩
  have es : s.toNat = sp.toNat - 24 := by subst hsdef; bv_omega
  have hsp : s + 24#64 = sp := by subst hsdef; bv_omega
  have e8 : (s + 8#64).toNat = s.toNat + 8 := by bv_omega
  have e5 : (s + (5#32 : BitVec 32).signExtend 64).toNat = s.toNat + 5 := by
    rw [show (5#32 : BitVec 32).signExtend 64 = 5#64 by decide]; bv_omega
  have hAl : FnSpec.EntryAligned (s - 8#64) := by
    unfold FnSpec.EntryAligned; rw [toNat_sub_eight' (by omega)]; omega
  -- the straight-line instructions
  have T1 := code_triple (cpiece hD 0 _ (by decide) (by decide))
    (aluI8_step (v := sp) (pc := pcm 0) (pc' := pcm 4) dec_sub18 rfl (by decide) (by decide))
  rw [show Silmaril.X86.Ext.AluOp.resultN .sub sp ((0x18#8 : BitVec 8).signExtend 64) = s by
    rw [hsdef]; rfl] at T1
  have T2 := code_triple (cpiece hD 4 _ (by decide) (by decide))
    (movI32_step (pc := pcm 4) (pc' := pcm 9) dec_edx5 (by decide))
  have T3 := code_triple (cpiece hD 9 _ (by decide) (by decide))
    (movI32_step (pc := pcm 9) (pc' := pcm 14) dec_esi78 (by decide))
  have T4 := code_triple (cpiece hD 14 _ (by decide) (by decide))
    (mov_step (v := s) (pc := pcm 14) (pc' := pcm 17) (by decide) dec_rdi_rsp (by decide))
  have T6 := code_triple (cpiece hD 22 _ (by decide) (by decide))
    (mov_step (v := s) (pc := pcm 22) (pc' := pcm 25) (by decide) dec_rsi_rsp (by decide))
  have T7 := code_triple (cpiece hD 25 _ (by decide) (by decide))
    (leaRsp_step (s := s) (pc := pcm 25) (pc' := pcm 30) (by decide) dec_lea8 (by decide))
  have T8 := code_triple (cpiece hD 30 _ (by decide) (by decide))
    (movI32_step (pc := pcm 30) (pc' := pcm 35) dec_edx6 (by decide))
  have T9 := code_triple (cpiece hD 35 _ (by decide) (by decide))
    (storeI8Rsp_step (s := s) (pc := pcm 35) (pc' := pcm 40) e5 dec_store5 (by decide))
  have T11 := code_triple (cpiece hD 45 _ (by decide) (by decide))
    (leaRsp_step (s := s) (pc := pcm 45) (pc' := pcm 50) (by decide) dec_lea8 (by decide))
  have T13 := code_triple (cpiece hD 55 _ (by decide) (by decide))
    (aluI8_step (v := s) (pc := pcm 55) (pc' := pcm 59) dec_add18 rfl (by decide) (by decide))
  rw [show Silmaril.X86.Ext.AluOp.resultN .add s ((0x18#8 : BitVec 8).signExtend 64) = sp by
    rw [← hsp]; rfl] at T13
  have T14 := code_triple (cpiece hD 59 (Insn.encode .ret) (by decide) (by decide))
    (ret_step (pcm 59) sp ret)
  simp only [Silmaril.X86.Ext.Sz.bits, BitVec.setWidth_eq] at T4 T6
  rw [show (5#32 : BitVec 32).setWidth 64 = 5#64 by decide] at T2
  rw [show (0x78#32 : BitVec 32).setWidth 64 = 0x78#64 by decide] at T3
  rw [show (6#32 : BitVec 32).setWidth 64 = 6#64 by decide] at T8
  rw [show (8#32 : BitVec 32).signExtend 64 = 8#64 by decide] at T7 T11
  have hb := budget_split (sp.toNat - 48)
  have hrd := rd_join (sp.toNat - 48) (List.replicate 5 (0x78#8 : Byte) ++ [0#8])
    (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) rfl rfl ret
  rw [show sp.toNat - 48 + 16 = s.toNat - 8 by omega, show sp.toNat - 48 + 24 = s.toNat by omega,
    show sp.toNat - 48 + 29 = s.toNat + 5 by omega, show sp.toNat - 48 + 30 = s.toNat + 6 by omega,
    show sp.toNat - 48 + 32 = (s + 8#64).toNat by omega,
    show sp.toNat - 48 + 38 = (s + 8#64).toNat + 6 by omega,
    show sp.toNat - 48 + 40 = s.toNat + 16 by omega] at hb
  rw [show sp.toNat - 48 + 16 = s.toNat - 8 by omega, show sp.toNat - 48 + 24 = s.toNat by omega,
    show sp.toNat - 48 + 30 = s.toNat + 6 by omega,
    show sp.toNat - 48 + 32 = (s + 8#64).toNat by omega,
    show sp.toNat - 48 + 38 = (s + 8#64).toNat + 6 by omega,
    show sp.toNat - 48 + 40 = s.toNat + 16 by omega,
    show sp.toNat - 48 + 48 = sp.toNat by omega] at hrd
  refine Triple.conseq (P := blockB s.toNat 5 ∗ blockB (s + 8#64).toNat 6 ∗ Code D bs ∗
      ripPt (pcm 0) ∗ regPt .rsp sp ∗ regAny .rdi ∗ regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗
      regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
      wordPt sp.toNat ret ∗ blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗
      blockAny (s.toNat - 8) 8 ∗ blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
      blockAny ((s + 8#64).toNat + 6) 2) ?_ ?_ (entails_refl _)
  · simp only [FnSpecB.SysVPreB, cmainSpec, SysVRegs, regsAny, regsWith, argRegs, scratchRegs]
    rw [show BitVec.ofNat 64 0x401020 = pcm 0 from rfl]
    refine entails_trans (sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (sep_mono_right _ (sep_mono_right _ (sep_mono_left _ hb))))))) (entails_of_eq ?_)
    ac_rfl
  refine Triple.blockB_elim fun old5 hl5 => ?_
  rw [sep_left_comm]
  refine Triple.blockB_elim fun old6 hl6 => ?_
  obtain ⟨fa, fp, fq⟩ := fill_eqs (s := s) (c := 0x78#64) hl5
  obtain ⟨ca, cp, cq⟩ := copy_eqs (d := s + 8#64) (s := s)
    (src := (List.replicate 5 (0x78#8 : Byte) ++ [0#8])) (by rfl) hl6
  obtain ⟨la, lp, lq⟩ := len1_eqs (s := s + 8#64) (str := List.replicate 5 (0x78#8 : Byte))
    (by decide)
  have S5 := tcall_rule (S := fillSpec) (pc := pcm 17) (s := s) hc hset
    (cpiece hD 17 (Insn.encode (.call 0x7a#32)) (by decide) (by decide)) (by decide) hAl
    (by show 0 + 8 ≤ s.toNat; omega) ⟨s, 0x78#64, old5⟩
  rw [fa, fp, show fillSpec.stack = 0 from rfl, Nat.sub_zero, Nat.zero_add,
    show pcm 17 + 5#64 = pcm 22 by decide] at S5
  simp only [fq, show ((0x78#64 : Word).setWidth 8) = (0x78#8 : Byte) by decide, SysVRegs,
    SysVRet, regsAny, regsWith, argRegs, scratchRegs, clobberedRegs] at S5
  have S10 := tcall_rule (S := copySpec) (pc := pcm 40) (s := s) hc hcpy
    (cpiece hD 40 (Insn.encode (.call 0x33#32)) (by decide) (by decide)) (by decide) hAl
    (by show 0 + 8 ≤ s.toNat; omega)
    ⟨s + 8#64, s, (List.replicate 5 (0x78#8 : Byte) ++ [0#8]), old6⟩
  rw [ca, cp, show copySpec.stack = 0 from rfl, Nat.sub_zero, Nat.zero_add,
    show pcm 40 + 5#64 = pcm 45 by decide] at S10
  simp only [cq, SysVRegs, SysVRet, regsAny, regsWith, argRegs, scratchRegs, clobberedRegs] at S10
  have S12 := tcall_rule (S := len1Spec) (pc := pcm 50) (s := s) hc hlen
    (cpiece hD 50 (Insn.encode (.call 0x09#32)) (by decide) (by decide)) (by decide) hAl
    (by show 16 + 8 ≤ s.toNat; omega) ⟨s + 8#64, List.replicate 5 (0x78#8 : Byte)⟩
  rw [la, lp, show len1Spec.stack = 16 from rfl, show s.toNat - 8 - 16 = sp.toNat - 48 by omega,
    blockAny_add (sp.toNat - 48) 16 8, show sp.toNat - 48 + 16 = s.toNat - 8 by omega,
    show pcm 50 + 5#64 = pcm 55 by decide] at S12
  have S12w := Triple.conseq (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
      (show bytesPt _ _ ⊢ₛ bytesPtRO _ _ from
        bytesAt_mono rw_ro (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))))))))
    S12 (entails_refl _)
  simp only [lq, SysVRegs, SysVRet, regsAny, regsWith, argRegs, scratchRegs, clobberedRegs] at S12w
  have T9' : Triple (Code D bs ∗ ripPt (pcm 35) ∗ regPt .rsp s ∗ blockAny (s.toNat + 5) 1 ∗
      bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)))
      ((Code D bs ∗ ripPt (pcm 40) ∗ regPt .rsp s) ∗
          bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8])) :=
    Triple.conseq (entails_of_eq (by ac_rfl))
      (Triple.frame T9 (bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte))))
      (entails_trans (entails_of_eq (by ac_rfl : _ = ((Code D bs ∗ ripPt (pcm 40) ∗ regPt .rsp s) ∗
        (bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗
            bytesPt (s.toNat + 5) [0#8])))) (sep_mono_right _ ro_join))
  refine Triple.trans ?U1 (Triple.trans (Q := regAny .rax ∗ (Code D bs ∗ ripPt (pcm 22) ∗
      regPt .rsp s ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗
          regAny .r9 ∗
      regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
      bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
      blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
      bytesPt (s + 8#64).toNat old6)))
    (Triple.conseq (entails_refl _) (Triple.frame S5 (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
        blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPt (s + 8#64).toNat old6)) ?E5) ?_)
  case U1 =>
    exact Triple.trans (Triple.pre (entails_of_eq (by ac_rfl))
        (Triple.frame T1 (regAny .rdi ∗ regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗ regAny .r8 ∗
            regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗ wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5)))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl))
        (Triple.frame T2 (regPt .rsp s ∗ flagsAny ∗ regAny .rdi ∗ regAny .rsi ∗ regAny .rcx ∗
            regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗
                wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5)))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl))
        (Triple.frame T3 (regPt .rsp s ∗ flagsAny ∗ regAny .rdi ∗ regPt .rdx 5#64 ∗ regAny .rcx ∗
            regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗
                wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5)))
      (Triple.conseq (entails_of_eq (by ac_rfl))
        (Triple.frame T4 (flagsAny ∗ regPt .rdx 5#64 ∗ regPt .rsi 0x78#64 ∗ regAny .rcx ∗
            regAny .r8 ∗
            regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗ wordPt sp.toNat ret ∗
            blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
            blockAny (s.toNat + 5) 1 ∗ blockAny (s.toNat + 6) 2 ∗
                blockAny ((s + 8#64).toNat + 6) 2 ∗
            bytesPt (s + 8#64).toNat old6 ∗ bytesPt s.toNat old5))
        (entails_of_eq (by ac_rfl)))))
  case E5 =>
    rw [sep_sexists, sexists_sep]
    exact sexists_elim fun v => weaken_rax_pure (by ac_rfl)
  refine Triple.trans ?U2 (Triple.trans (Q := regAny .rax ∗ (Code D bs ∗ ripPt (pcm 45) ∗
      regPt .rsp s ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗
          regAny .r9 ∗
      regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
      (bytesPt (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
      bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8])) ∗ (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
      blockAny ((s + 8#64).toNat + 6) 2)))
    (Triple.conseq (entails_refl _) (Triple.frame S10 (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
        blockAny ((s + 8#64).toNat + 6) 2)) ?E10) ?_)
  case U2 =>
    exact Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T6 (regAny .rax ∗
        regAny .rcx ∗ regAny .rdx ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗
        regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
        bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
        blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPt (s + 8#64).toNat old6))))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T7 (regPt .rsi s ∗
          regAny .rax ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗
          regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
          bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
          blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
          blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
          bytesPt (s + 8#64).toNat old6))))
      (Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T8 (regPt .rsp s ∗
          regPt .rdi (s + 8#64) ∗ regPt .rsi s ∗ regAny .rax ∗ regAny .rcx ∗ regAny .r8 ∗
              regAny .r9 ∗
          regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗
          bytesPt s.toNat (List.replicate 5 (0x78#8 : Byte)) ∗ (wordPt sp.toNat ret ∗
          blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 5) 1 ∗
          blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
          bytesPt (s + 8#64).toNat old6))))
      (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame T9' (regPt .rdx 6#64 ∗
          regPt .rdi (s + 8#64) ∗ regPt .rsi s ∗ regAny .rax ∗ regAny .rcx ∗ regAny .r8 ∗
              regAny .r9 ∗
          regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockAny (s.toNat - 8) 8 ∗ wordPt sp.toNat ret ∗
          blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
          blockAny ((s + 8#64).toNat + 6) 2 ∗ bytesPt (s + 8#64).toNat old6))
        (entails_of_eq (by ac_rfl)))))
  case E10 =>
    rw [sep_sexists, sexists_sep]
    exact sexists_elim fun v => weaken_rax_pure (by ac_rfl)
  refine Triple.trans ?U3 (Triple.trans (Q := regPt .rax 6#64 ∗ (Code D bs ∗
      ripPt (pcm 55) ∗ regPt .rsp s ∗ regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗
      regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
          (blockAny (sp.toNat - 48) 16 ∗
      blockAny (s.toNat - 8) 8) ∗
      bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
          (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
      bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))))
    (Triple.conseq (entails_refl _) (Triple.frame S12w (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))) ?E12) ?_)
  case U3 =>
    exact Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame T11 (regAny .rax ∗ regAny .rcx ∗
        regAny .rdx ∗ regAny .rsi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
        blockAny (s.toNat - 8) 8 ∗
        bytesPt (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
        bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗ (wordPt sp.toNat ret ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat + 6) 2 ∗
        blockAny ((s + 8#64).toNat + 6) 2)))
      (entails_of_eq (by ac_rfl))
  case E12 =>
    simp only [sep_sexists, sexists_sep]
    exact sexists_elim fun v => sexists_elim fun w => pure2_rax (by ac_rfl)
      (fun h1 h2 => by subst h1; subst h2; decide)
  refine Triple.trans (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T13 (regPt .rax 6#64 ∗
      regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗
          regAny .r10 ∗
      regAny .r11 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
      bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
          (wordPt sp.toNat ret ∗
      blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
      bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8])))))
    (Triple.conseq (entails_of_eq (by ac_rfl)) (Triple.frame T14 (flagsAny ∗ regPt .rax 6#64 ∗
        regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗
        regAny .r10 ∗ regAny .r11 ∗ blockAny (sp.toNat - 48) 16 ∗ blockAny (s.toNat - 8) 8 ∗
        bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
        blockAny (s.toNat + 16) 8 ∗ blockAny (s.toNat + 6) 2 ∗ blockAny ((s + 8#64).toNat + 6) 2 ∗
        bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]))) ?_)
  simp only [FnSpecB.SysVPostB, cmainSpec, SysVRet, regsAny, regsWith, clobberedRegs]
  rw [sep_sexists]
  refine sexists_intro 6#64 ?_
  rw [show (⌜(6#64 : Word) = 6#64⌝ : SProp) = emp by rw [eq_true rfl, spure_true_emp]]
  refine entails_trans (entails_of_eq (by ac_rfl : _ = ((blockAny (sp.toNat - 48) 16 ∗
      blockAny (s.toNat - 8) 8 ∗ bytesPtRO s.toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
      blockAny (s.toNat + 6) 2 ∗
      bytesPtRO (s + 8#64).toNat (List.replicate 5 (0x78#8 : Byte) ++ [0#8]) ∗
      blockAny ((s + 8#64).toNat + 6) 2 ∗ blockAny (s.toNat + 16) 8 ∗ wordPt sp.toNat ret) ∗
      (Code D bs ∗ ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ regPt .rax 6#64 ∗ regAny .rcx ∗
          regAny .rdx ∗
      regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny))))
    (entails_trans (sep_mono_left _ hrd) (entails_of_eq (by ac_rfl)))

end Silmaril.Proofs.Machine.Process.LibMiniClient
