module

public import Silmaril.Proofs.Machine.Process.LibMiniClient.Cmain
public import Silmaril.Machine.Process.LibMiniClient.Defs

/-!
# Proofs: `_start` of ladder rung 12 runs to `exit(6)`

```
_start: xor %ebp,%ebp; and $-16,%rsp; call cmain; mov %eax,%edi; mov $60,%eax; syscall
```

* `start_run`: a code-level step-indexed triple. From `rip = 0x401000`, a 16-aligned `rsp`,
  the caller-saved registers and `rbp` (any values), the eight bytes below `rsp` and a
  48-byte **backed** block below them, the machine does not get stuck before it reaches
  `rip = 0x401012` (the `syscall`) with `rax = 60` and `rdi = 6`, provided `cmain` is
  `SafeB n` for `cmainSpec` (`Cmain.cmain_safeB`).
* `exitAt_of`: such a state, with the image's `0f 05` at `0x401012` in the code region, is
  `ExitAt` (the predicate of `Task.startRun`).
* `and_neg16`: `x &&& -16 = x` for a 16-aligned `x` (the `and $-16,%rsp`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient

open Silmaril.X86 (MState Word Byte Reg Insn)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.BackedSpec
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Machine.Process.LpsBridge (AtSyscall)
open Silmaril.Proofs.Machine.Link.FnSpec
open Silmaril.Proofs.Machine.Link.BackedSpec
open Silmaril.Proofs.Machine.Link.LibMiniClient (piece_cov cov_at toNat_ofNat_lt)
open Silmaril.Machine.Link.Unit (Contains)

/-- The bytes of `_start` (`start.o`'s `.text._start`, linked at `0x401000`). -/
def startCode : List Byte :=
  [0x31, 0xed, 0x48, 0x83, 0xe4, 0xf0, 0xe8, 0x15, 0x00, 0x00, 0x00, 0x89, 0xc7, 0xb8, 0x3c,
   0x00, 0x00, 0x00, 0x0f, 0x05, 0x0f, 0x0b]

/-- The address of `_start`'s byte `k`. -/
def pcs (k : Nat) : Word := BitVec.ofNat 64 (0x401000 + k)

/-- Any fragment. -/
def anyFrag : SProp := fun _ => True

theorem to_any (P : SProp) : P ⊢ₛ anyFrag := fun _ _ => trivial

/-- **`_start`'s precondition** at a 16-aligned `sp`. -/
def startPre (sp : Word) : SProp :=
  ripPt (pcs 0) ∗ regPt .rsp sp ∗ regAny .rbp ∗ flagsAny ∗ regAny .rdi ∗ regAny .rsi ∗
    regAny .rdx ∗ regAny .rcx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗
    regAny .r11 ∗ blockAny (sp.toNat - 8) 8 ∗ blockB (sp.toNat - 56) 48

/-- **`_start`'s postcondition**: at the `syscall`, requesting `exit(6)`. -/
def startPost : SProp :=
  ripPt (pcs 18) ∗ regPt .rax 60#64 ∗ regPt .rdi 6#64 ∗ anyFrag

variable {D : Nat → Prop} {bs : Nat → Byte}

theorem spiece
    (hD : ∀ i (hi : i < startCode.length), D (0x401000 + i) ∧ bs (0x401000 + i) = startCode[i])
    (o : Nat) (piece : List Byte)
    (hp : ∀ i (hi : i < piece.length), startCode[o + i]? = some piece[i])
    (ho : 0x401000 + o < 2 ^ 64) :
    ∀ i (hi : i < piece.length), D ((pcs o).toNat + i) ∧ bs ((pcs o).toNat + i) = piece[i] :=
  cov_at (toNat_ofNat_lt ho) (piece_cov hD hp)

theorem and_neg16 (x : BitVec 64) (h : x.toNat % 16 = 0) : x &&& 0xfffffffffffffff0#64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hx := x.isLt
  rcases Nat.lt_or_ge i 4 with hi | hi
  · have : x.toNat.testBit i = false := by
      have e := Nat.testBit_mod_two_pow x.toNat 4 i
      rw [show x.toNat % 2 ^ 4 = 0 by omega, Nat.zero_testBit] at e
      simp [hi] at e; exact e
    simp [this]
  · rcases Nat.lt_or_ge i 64 with hi' | hi'
    · have key : ∀ j, j < 64 → 4 ≤ j → (18446744073709551600 : Nat).testBit j = true := by
        decide
      simp [key i hi' hi]
    · have : x.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi'))
      simp [this]

theorem pure1_rax {v w : Word} {L R : SProp} (h : L = (⌜v = w⌝ ∗ regPt .rax v ∗ R)) :
    L ⊢ₛ (regPt .rax w ∗ R) :=
  entails_trans (entails_of_eq h) (spure_sep_elim fun e => by rw [e]; exact entails_refl _)

theorem dec_xor_ebp : Silmaril.X86.Ext.decode [0x31, 0xed] =
    some (.alu .d .xor (.reg .rbp) .rbp, [0x31, 0xed].length) := by decide
theorem dec_and_rsp : Silmaril.X86.Ext.decode [0x48, 0x83, 0xe4, 0xf0] =
    some (.aluI8 .q .and (.reg .rsp) 0xf0#8, 4) := by decide
theorem dec_edi_eax : Silmaril.X86.Ext.decode [0x89, 0xc7] =
    some (.mov .d (.reg .rdi) .rax, [0x89, 0xc7].length) := by decide
theorem dec_eax60 : Silmaril.X86.Ext.decode [0xb8, 0x3c, 0x00, 0x00, 0x00] =
    some (.movI32 .rax 0x3c#32, [0xb8, 0x3c, 0x00, 0x00, 0x00].length) := by decide

/-- **`_start` runs to the `exit(6)` request**, given `cmain`'s backed-stack contract. -/
theorem start_run {ctx : Silmaril.Machine.Link.Contract.Image} {n : Nat}
    (hcode : ∀ i (hi : i < startCode.length), ContainsX ctx (0x401000 + i) startCode[i])
    (hcm : SafeB n 0x401020 cmainSpec ctx) (hc : Covers ctx D bs) {sp : Word}
    (hal : sp.toNat % 16 = 0) (hlow : 64 ≤ sp.toNat) :
    STriple (n + 1) (Code D bs ∗ startPre sp) (Code D bs ∗ startPost) := by
  have hD : ∀ i (hi : i < startCode.length), D (0x401000 + i) ∧ bs (0x401000 + i) =
      startCode[i] := fun i hi => hc _ _ (hcode i hi)
  have T1 : Triple (Code D bs ∗ ripPt (pcs 0) ∗ regAny .rbp ∗ flagsAny)
      (Code D bs ∗ ripPt (pcs 2) ∗ regPt .rbp 0 ∗ flagsAny) := by
    rw [show (Code D bs ∗ ripPt (pcs 0) ∗ regAny .rbp ∗ flagsAny) =
      sexists fun v => Code D bs ∗ ripPt (pcs 0) ∗ regPt .rbp v ∗ flagsAny by
        simp only [regAny, sexists_sep, sep_sexists]]
    exact Triple.sexists fun v => code_triple (spiece hD 0 _ (by decide) (by decide))
      (xorSelf_step (v := v) (pc := pcs 0) (pc' := pcs 2) dec_xor_ebp (by decide))
  have T2 := code_triple (spiece hD 2 _ (by decide) (by decide))
    (aluI8_step (v := sp) (pc := pcs 2) (pc' := pcs 6) dec_and_rsp rfl (by decide) (by decide))
  rw [show Silmaril.X86.Ext.AluOp.resultN .and sp ((0xf0#8 : BitVec 8).signExtend 64) = sp by
    rw [show (0xf0#8 : BitVec 8).signExtend 64 = 0xfffffffffffffff0#64 by decide]
    exact and_neg16 sp hal] at T2
  have hA : FnSpec.EntryAligned (sp - 8#64) := by
    unfold FnSpec.EntryAligned; rw [toNat_sub_eight' (by omega)]; omega
  have S3 := scallB_rule (S := cmainSpec) (pc := pcs 6) (s := sp) hc hcm
    (spiece hD 6 (Insn.encode (.call 0x15#32)) (by decide) (by decide)) (by decide) hA
    (by show 48 + 8 ≤ sp.toNat; omega) ()
  rw [show cmainSpec.stack = 48 from rfl, show sp.toNat - 8 - 48 = sp.toNat - 56 by omega,
    show pcs 6 + 5#64 = pcs 11 by decide] at S3
  simp only [cmainSpec, SysVRegs, SysVRet, regsAny, regsWith, argRegs, scratchRegs,
    clobberedRegs] at S3
  have T5 := code_triple (spiece hD 13 _ (by decide) (by decide))
    (movI32_step (pc := pcs 13) (pc' := pcs 18) dec_eax60 (by decide))
  rw [show (0x3c#32 : BitVec 32).setWidth 64 = 60#64 by decide] at T5
  have T4 := code_triple (spiece hD 11 _ (by decide) (by decide))
    (mov_step (v := 6#64) (pc := pcs 11) (pc' := pcs 13) (by decide) dec_edi_eax (by decide))
  rw [show ((6#64 : Word).setWidth (Silmaril.X86.Ext.Sz.d.bits)).setWidth 64 = 6#64 by decide]
    at T4
  have T45 : Triple (Code D bs ∗ ripPt (pcs 11) ∗ regPt .rax 6#64 ∗ regAny .rdi)
      (Code D bs ∗ ripPt (pcs 18) ∗ regPt .rax 60#64 ∗ regPt .rdi 6#64) :=
    Triple.trans T4 (Triple.conseq (entails_of_eq (by ac_rfl : _ =
        ((Code D bs ∗ ripPt (pcs 13) ∗ regPt .rax 6#64) ∗ regPt .rdi 6#64)))
      (Triple.frame (Triple.pre (sep_mono_right _ (sep_mono_right _
        (sexists_intro 6#64 (entails_refl _)))) T5) (regPt .rdi 6#64))
      (entails_of_eq (by ac_rfl)))
  refine STriple.triple_seq (Triple.trans (Triple.pre (entails_of_eq (by
      unfold startPre; ac_rfl))
      (Triple.frame T1 (regPt .rsp sp ∗ regAny .rdi ∗ regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗
        regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗
        blockAny (sp.toNat - 8) 8 ∗ blockB (sp.toNat - 56) 48)))
    (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T2 (regPt .rbp 0 ∗ regAny .rdi ∗
      regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗
      regAny .r10 ∗ regAny .r11 ∗ blockAny (sp.toNat - 8) 8 ∗ blockB (sp.toNat - 56) 48))))
    (STriple.seq_triple (STriple.conseq (entails_of_eq (by ac_rfl))
      (STriple.frame S3 (regPt .rbp 0)) ?_)
      (Triple.post (Triple.frame T45 (regPt .rsp sp ∗ regPt .rbp 0 ∗ regAny .rcx ∗ regAny .rdx ∗
        regAny .rsi ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗
        blockRd (sp.toNat - 56) (48 + 8)))
        (entails_trans (sep_mono_right _ (to_any _))
          (entails_of_eq (by unfold startPost; ac_rfl)))))
  rw [sep_sexists, sexists_sep]
  refine sexists_elim fun v => ?_
  refine entails_trans (pure1_rax (w := 6#64) (R := Code D bs ∗ ripPt (pcs 11) ∗ regPt .rsp sp ∗
    regAny .rcx ∗ regAny .rdx ∗ regAny .rsi ∗ regAny .rdi ∗ regAny .r8 ∗ regAny .r9 ∗
    regAny .r10 ∗ regAny .r11 ∗ flagsAny ∗ blockRd (sp.toNat - 56) (48 + 8) ∗ regPt .rbp 0)
    (by ac_rfl)) (entails_of_eq ?_)
  ac_rfl

/-- **The `exit(6)` request.** A state holding `_start`'s postcondition, with the image's
`0f 05` at `0x401012` in its code region, is `ExitAt`. -/
theorem exitAt_of
    (hD : ∀ i (hi : i < startCode.length), D (0x401000 + i) ∧ bs (0x401000 + i) = startCode[i])
    {F : SProp} {m : MState} (h : ((Code D bs ∗ startPost) ∗ F) (toFrag m)) : ExitAt m := by
  have hs := spiece hD 18 [0x0f, 0x05] (by decide) (by decide)
  rw [code_split _ _ hs] at h
  have H0 : Holds _ m := ⟨_, h, fun _ _ e => e⟩
  obtain ⟨H1, -⟩ := holds_sep H0
  obtain ⟨H2, H3⟩ := holds_sep H1
  obtain ⟨hcode, -⟩ := holds_sep H2
  unfold startPost at H3
  obtain ⟨hrip, H4⟩ := holds_sep H3
  obtain ⟨hrax, H5⟩ := holds_sep H4
  obtain ⟨hrdi, -⟩ := holds_sep H5
  obtain ⟨_, hc1, hl1⟩ := hcode
  obtain ⟨_, hr1, hl2⟩ := hrip
  obtain ⟨_, hr2, hl3⟩ := hrax
  obtain ⟨_, hr3, hl4⟩ := hrdi
  have erip := ripPt_le hr1 hl2
  refine ⟨?_, ?_, ?_⟩
  · unfold AtSyscall
    rw [erip]
    have := fetchBytes_of_codePt (bs := [0x0f, 0x05]) (List.cons_ne_nil _ _) hc1 hl1
    exact this
  · rw [regPt_le hr2 hl3]; rfl
  · rw [regPt_le hr3 hl4]; rfl

end Silmaril.Proofs.Machine.Process.LibMiniClient
