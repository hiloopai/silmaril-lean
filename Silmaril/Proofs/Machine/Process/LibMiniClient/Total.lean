module

public import Silmaril.Proofs.Machine.Process.LibMiniClient.StartRun
public import Silmaril.Machine.X86.Ladder.LibMini.Thms
public import Silmaril.Machine.Process.LpsBridge.Thms

/-!
# Proofs: rung 12 terminates (total correctness of the open run)

R1's link logic (`Safe`) is step-indexed, so it proves only partial correctness: the run never
gets stuck before the postcondition, but may run forever. For rung 12 the call graph is
acyclic (`_start → cmain → {memset, memcpy, len1 → strlen}`), so total triples compose
directly, without `link_compose`:

* libmini: the separation-logic layer's **total** `exports_sat` (`Export.Holds`, a `FnSpec.Sat`, i.e. `SPEC`)
  gives `SafeT` at the linked addresses (`safeT_of_sat`, the code bytes checked in the link by
  kernel evaluation: `memset_in_linked`, `memcpy_in_linked`, `strlen_in_linked`);
* `len1`: `plusOne_safeT` (R1's `plusOne_safe` proof with the total call rule `tcall_rule`);
* `cmain`: `Cmain.cmain_safeTB`;
* `_start`: `start_total`;
* `startRun_total`: from the launch state of every valid launch, the open machine **reaches**
  an `ExitAt` state (some finite run).

This bypasses `validated_compose`/`link_compose` for the total result: the link is still the
validated one (the same `linked` sections), but the composition is by hand, along the acyclic
call graph. A total variant of the general link theorem (for acyclic import graphs) is not
done.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient

open Silmaril.X86 (MState Reg Insn)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Formats.ELF.Link (LinkedSection)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.BackedSpec
open Silmaril.Machine.Link.Unit (Contains TU)
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Machine.Link.Fixtures.LibMiniClientBfd
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Proofs.Machine.Link.FnSpec
open Silmaril.Proofs.Machine.Link.BackedSpec
open Silmaril.Proofs.Machine.Link.LibMiniClient
open Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity

/-- **`len1`'s code, totally, against any callee spec** (R1's `plusOne_safe` with the total
call rule; the proof script is R1's with `Triple` combinators). -/
theorem plusOne_safeT {S : FnSpec} {ctx : Silmaril.Machine.Link.Contract.Image} {a f : Nat}
    {rel : BitVec 32} (ha : a + 18 ≤ 2 ^ 64)
    (hcode : ∀ i (hi : i < (plusOneCode rel).length), ContainsX ctx (a + i) (plusOneCode rel)[i])
    (htarget : BitVec.ofNat 64 (a + 4) + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hf : SafeT f S ctx) : SafeT a (plusOneSpec S) ctx := by
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
  have SB := tcall_rule (pc := BitVec.ofNat 64 (a + 4)) (s := sp - 8#64) hc hf c2 htarget hA2
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
  refine Triple.trans (Triple.conseq ?_ (Triple.frame TA
      (SysVRegs (S.args x) ∗ blockAny (sp.toNat - 8 - 8 - S.stack) (S.stack + 8) ∗ S.pre x ∗
        wordPt sp.toNat ret ∗ blockAny (sp.toNat - 8) 8)) (entails_refl _))
    (Triple.trans (Triple.conseq ?_ (Triple.frame SB
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

variable {D : Nat → Prop} {bs : Nat → Byte}

/-- **`_start` reaches the `exit(6)` request**, given `cmain`'s total backed-stack contract. -/
theorem start_total {ctx : Silmaril.Machine.Link.Contract.Image}
    (hcode : ∀ i (hi : i < startCode.length), ContainsX ctx (0x401000 + i) startCode[i])
    (hcm : SafeTB 0x401020 cmainSpec ctx) (hc : Covers ctx D bs) {sp : Word}
    (hal : sp.toNat % 16 = 0) (hlow : 64 ≤ sp.toNat) :
    Triple (Code D bs ∗ startPre sp) (Code D bs ∗ startPost) := by
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
  have S3 := tcallB_rule (S := cmainSpec) (pc := pcs 6) (s := sp) hc hcm
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
  refine Triple.trans (Triple.trans (Triple.pre (entails_of_eq (by
      unfold startPre; ac_rfl))
      (Triple.frame T1 (regPt .rsp sp ∗ regAny .rdi ∗ regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗
        regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗ regAny .r10 ∗ regAny .r11 ∗
        blockAny (sp.toNat - 8) 8 ∗ blockB (sp.toNat - 56) 48)))
    (Triple.pre (entails_of_eq (by ac_rfl)) (Triple.frame T2 (regPt .rbp 0 ∗ regAny .rdi ∗
      regAny .rsi ∗ regAny .rdx ∗ regAny .rcx ∗ regAny .r8 ∗ regAny .r9 ∗ regAny .rax ∗
      regAny .r10 ∗ regAny .r11 ∗ blockAny (sp.toNat - 8) 8 ∗ blockB (sp.toNat - 56) 48))))
    (Triple.trans (Triple.conseq (entails_of_eq (by ac_rfl))
      (Triple.frame S3 (regPt .rbp 0)) ?_)
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


/-! ## The total callees at their linked addresses -/

open Silmaril.Machine.X86.Ladder.LibMini (memsetCode memcpyCode strlenCode exports exports_sat)

set_option maxRecDepth 100000 in
theorem memset_in_linked : ∀ i (hi : i < memsetCode.length), ∃ s ∈ linked,
    s.address ≤ 0x4010b0 + i ∧ s.data[0x4010b0 + i - s.address]? = some memsetCode[i] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem memcpy_in_linked : ∀ i (hi : i < memcpyCode.length), ∃ s ∈ linked,
    s.address ≤ 0x401080 + i ∧ s.data[0x401080 + i - s.address]? = some memcpyCode[i] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem strlen_in_linked : ∀ i (hi : i < strlenCode.length), ∃ s ∈ linked,
    s.address ≤ 0x4010f0 + i ∧ s.data[0x4010f0 + i - s.address]? = some strlenCode[i] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem len1_in_linked : ∀ i (hi : i < (plusOneCode 0x87#32).length), ∃ s ∈ linked,
    s.address ≤ 0x401060 + i ∧
      s.data[0x401060 + i - s.address]? = some (plusOneCode 0x87#32)[i] := by
  decide +kernel

/-- **The callees of `cmain`, totally**: in the validated link, `memset`, `memcpy` (the separation-logic layer's
total `exports_sat`) and `len1` (`plusOne_safeT` over `strlen`) are `SafeT`. -/
theorem rung12_link_total {out : List LinkedSection}
    (h : Silmaril.X86.Linking.Relocation.link prepared witness.layout witness.absolute =
      some out) :
    SafeT 0x4010b0 fillSpec out ∧ SafeT 0x401080 copySpec out ∧ SafeT 0x401060 len1Spec out := by
  have e := out_eq h
  have hstr : SafeT 0x4010f0 scanSpec out := safeT_of_sat (by decide)
    (by rw [e]; exact fun i hi => containsX_linked (strlen_in_linked i hi)) (exports_sat ⟨"strlen", strlenCode, scanSpec⟩
      (by simp [exports]))
  refine ⟨safeT_of_sat (by decide) (by rw [e]; exact fun i hi => containsX_linked (memset_in_linked i hi))
      (exports_sat ⟨"memset", memsetCode, fillSpec⟩ (by simp [exports])),
    safeT_of_sat (by decide) (by rw [e]; exact fun i hi => containsX_linked (memcpy_in_linked i hi))
      (exports_sat ⟨"memcpy", memcpyCode, copySpec⟩ (by simp [exports])), ?_⟩
  exact plusOne_safeT (by decide) (by rw [e]; exact fun i hi => containsX_linked (len1_in_linked i hi)) (by decide) hstr

/-- **The open run terminates at `exit(6)`**: from the launch state of every valid launch of
the rung-12 image, the open machine reaches an `ExitAt` state in finitely many steps. -/
theorem startRun_total (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput)
    (himg : snapshot.image = image) (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ∃ k m', run Silmaril.Machine.X86.Open.step k (launchState snapshot en inp) = some m' ∧
      ExitAt m' := by
  obtain ⟨out, hlink, hcov, hal, hlow, F, hm⟩ := launch_setup himg hv
  obtain ⟨hset, hcpy, hlen⟩ := rung12_link_total hlink
  have hDs : ∀ i (hi : i < startCode.length), Dom out (0x401000 + i) ∧
      byteOf (launchState snapshot en inp) (0x401000 + i) = startCode[i] :=
    fun i hi => hcov _ _ (start_contains hlink i hi)
  have T := start_total (start_contains hlink)
    (cmain_safeTB (cmain_contains hlink) hset hcpy hlen) hcov hal hlow
  obtain ⟨m', ⟨k, hk⟩, hq⟩ := T F _ hm
  exact ⟨k, m', hk, exitAt_of hDs hq⟩

/-! ## The process must exit with status 6 -/

open Silmaril.Proofs.Machine.Process.LpsBridge in
/-- **Ladder rung 12 must exit with status 6** (LPS's must-exit tier). For every valid launch
of the rung-12 executable, every flag oracle and every refusal configuration, every LPS
execution of the launched process exits normally with status `6`, never reaches an error and
never stalls. -/
theorem rung12_mustExit (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) (oracle : Oracle) :
    MustExitInAt snapshot.image.segments spec (NativeX86.defaultRefusalFilter refusals) [6]
      (X86Launch.init (machine oracle) snapshot en limit inp) := by
  obtain ⟨k, m', hr, ht, hrax, hrdi⟩ := startRun_total snapshot en inp himg hv
  have := mustExit_of_launch (limit := limit) hr ht (.inl hrax) oracle
    (NativeX86.defaultRefusalFilter refusals)
  rwa [hrdi] at this

/-- **Ladder rung 12, end to end.** For every valid LPS launch of the validated, linked
rung-12 executable: every finite execution produces the trace `[]` or `[exit 6]` and no error
(`ProcessSafe`, the `lps-partial` shape), and every execution exits with status `6`
(`MustExitInAt`, the must-exit tier), for every flag oracle and refusal configuration. -/
theorem rung12_complete (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafe snapshot refusals limit en inp (exitAllowed inp.fs) ∧
      ∀ oracle : Oracle, MustExitInAt snapshot.image.segments spec
        (NativeX86.defaultRefusalFilter refusals) [6]
        (X86Launch.init (machine oracle) snapshot en limit inp) :=
  ⟨rung12_processSafe_unconditional snapshot refusals limit en inp himg hv,
    rung12_mustExit snapshot refusals limit en inp himg hv⟩

end Silmaril.Proofs.Machine.Process.LibMiniClient
