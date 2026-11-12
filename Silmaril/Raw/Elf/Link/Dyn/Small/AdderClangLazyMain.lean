-- variant-of: glibc.adder.clang-lazy | style: small-direct | see-also: Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangMain
module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangLazyCall

/-! # The adder (clang) under lazy binding: `main` meets `MainOk`

As `adderClang_main`, with each first call of an import going through `PLT0` and the resolver
(`lazy_scanf`, `lazy_printf`) instead of straight to the import. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt
open Silmaril.Elf.Link.Dyn.Stdio

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **`main` of `adderClang` under lazy binding.** -/
theorem adderClangL_main {b lb gate res : Word} {rel : Bool} (P : AdderPlacedL b lb gate res) :
    MainOk (adderClangWorldL b lb gate res rel) adderClangLayout b (lsmAt lb) (cxaAt lb)
      (fun _ m => PltL b res m) (fun g => scanDD g.inp ≠ .ub) (adderPost rel) := by
  have hb := P.base.base.hb
  have hsc_out := P.base.sc_out
  have hpf_out := P.base.pf_out
  have hsc_gate := P.base.sc_gate
  have hpf_gate := P.base.pf_gate
  have hlt0 := (P.base.base.hb)
  intro Q t hd hrip hal hret hroom hm hx hpre kk
  have hlt := (t.m.core.read .rsp).isLt
  have hin : ∀ n, n < 0x4028 → (adderClangWorldL b lb gate res rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => img_add (L := adderClangLayout) hb hn
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (t.m.core.read .rsp - 8#64).toNat = (t.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (t.m.core.read .rsp - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have eR4 : (t.m.core.read .rsp - 8#64 + 4#64).toNat = (t.m.core.read .rsp).toNat - 4 := by
    rw [add_toNat (k := 4) (by rw [e8]; omega), e8]; omega
  have p1 : t.m.memory.Permitted .write (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have hmain : Loaded t.m.memory (b + BitVec.ofNat 64 0x1150) adderClangLayout.cMain := hm.main
  have hrip0 : t.m.core.rip = b + BitVec.ofNat 64 0x1150 := hrip
  refine must_listed (o := 0) adderClang_mainL rfl hd (by rw [hrip0]; exact hin _ (by decide)) hmain
    (by rw [hrip0]; simp) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep [hrip0]
  have hm1 := hm.keep adderClang_ok' hb (keeps_push (L := adderClangLayout) (W := adderClangWorldL b lb gate res rel)
    rfl hroom (v := t.m.core.read .rax) (sp' := t.m.core.read .rsp) (by omega) (by omega))
  refine must_listed (o := 1) adderClang_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep [addrK b (x := 0x1150 + 1 + 7) (y := 0x2004) (d := 0x00000eac#32) (by decide)]
  refine must_listed (o := 8) adderClang_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep [ofReg_addr]
  refine must_listed (o := 13) adderClang_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep []
  refine must_listed (o := 16) adderClang_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep []
  -- `call __isoc99_scanf@plt`
  have p2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax)).Permitted .write
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have r2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax)).Permitted .read
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inl rfl) (by omega) (by omega)
  have k1 := keeps_push (L := adderClangLayout) (W := adderClangWorldL b lb gate res rel) rfl hroom
    (v := t.m.core.read .rax) (sp' := t.m.core.read .rsp) (by omega) (by omega)
  have k2 := keeps_push (L := adderClangLayout) (W := adderClangWorldL b lb gate res rel) rfl hroom.pushMem
    (m := pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
    (v := b + 4455#64) (sp' := t.m.core.read .rsp - 8#64) (by omega) (by omega)
  have hm2 := hm1.keep adderClang_ok' hb k2
  have hx2 := hx.keep hb (k1.trans k2)
  refine must_listed (o := 18) adderClang_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep [addrK b (x := 4455) (y := 0x1040) (d := 0xfffffed9#32) (by decide)]
  -- `__isoc99_scanf@plt`, first call: `push $1; jmp PLT0; push GOT[1]; jmp *GOT[2]`, resolver
  refine lazy_scanf P hd rfl hx2 (by simp; omega) (fun a h1 h2 => ?_) ?_
  · simp at h1 h2
    exact hroom.2.2 a (by omega) (by omega)
  intro u hurip hursp huregs hug hukeep hupg
  have hd' : u.g.done = none := by rw [hug]; exact hd
  have hsU : u.m.core.read .rsp = t.m.core.read .rsp - 8#64 - 8#64 := by rw [hursp]; simp
  have notHole : ∀ a, (t.m.core.read .rsp).toNat - 4096 ≤ a → a < (t.m.core.read .rsp).toNat + 8 →
      ¬ (b.toNat + 0x4000 ≤ a ∧ a < b.toNat + 0x4010) := fun a h1 h2 h =>
    (hroom.2.2 a h1 h2).2.2 (Or.inl (show Img adderClangLayout b a from
      ⟨by omega, by simp [adderClangLayout] at hb ⊢; omega⟩))
  have hkU : ∀ a, (t.m.core.read .rsp).toNat - 16 ≤ a → a < (t.m.core.read .rsp).toNat + 8 →
      u.m.memory.bytes.get? a = (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 4455#64)).bytes.get? a ∧
      ∀ acc, u.m.memory.permits acc a = t.m.memory.permits acc a := fun a h1 h2 =>
    hukeep a ⟨fun h => notHole a (by omega) h2 ⟨by omega, by omega⟩, Or.inr (by simp; omega)⟩
  have hroomU : StackRoom (adderClangWorldL b lb gate res rel) u.m.memory (t.m.core.read .rsp) := by
    refine ⟨hsp, hsp2, fun a h1 h2 => ?_⟩
    have hp : ∀ acc, u.m.memory.permits acc a = t.m.memory.permits acc a := by
      intro acc
      by_cases ha : a < (t.m.core.read .rsp).toNat - 16
      · exact hupg a acc (by simp; omega) (by simp; omega)
      · exact (hkU a (by omega) h2).2 acc
    rw [hp, hp]; exact hroom.2.2 a h1 h2
  have hrdU : ∀ {a len : Nat}, (t.m.core.read .rsp).toNat - 16 ≤ a → a + len ≤ (t.m.core.read .rsp).toNat + 8 →
      u.m.memory.readBytes a len = (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 4455#64)).readBytes a len := fun {a len} h1 h2 =>
    hukeep.readBytes (fun k hk => ⟨fun h => notHole (a + k) (by omega) (by omega) ⟨by omega, h.2⟩,
      Or.inr (by simp; omega)⟩)
  have hkI : Keeps (ImgH adderClangLayout b 0x4008 0x4010)
      (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 4455#64)) u.m.memory :=
    hukeep.mono fun a h => ⟨h.2, Or.inl (Or.inl h.1)⟩
  have hmU := hm2.keepH adderClang_ok' hb adderClang_avoids
    (hkI.mono fun a h => ⟨h.1, fun h' => h.2 ⟨by omega, h'.2⟩⟩)
  have hro := hmU.rodata
  have hfmt : u.m.memory.readBytes (b + 8196#64).toNat 6 = some (fmtDD ++ [0]) := by
    have := readBytes_sub' hro (k := 4) (j := 6) (by decide) (by decide)
    rw [show (b + 8196#64).toNat = (b + BitVec.ofNat 64 adderClangLayout.ro).toNat + 4 by
      rw [addr_toNat (by simp [adderClangLayout] at hb ⊢; omega),
        addr_toNat (by simp [adderClangLayout] at hb ⊢; omega)]; rfl, this]
    decide
  have hr2U : u.m.memory.readBytes (u.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 4455#64]) := by
    rw [hsU, hrdU (by rw [e16]) (by rw [e16]; omega)]; exact pushMem_read r2 p2
  refine must_contract hd' (show ¬ Img adderClangLayout b u.m.core.rip.toNat by rw [hurip]; exact hsc_out)
    (fun r => (extStep_fn (f := .named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf"))
      (by rw [hurip]; simpa [scanfAt, adderClangWorldL, crtWorld] using hsc_gate)
      (fun _ _ h => by
        simp only [adderClangWorldL, crtWorld, Option.some.injEq, Prod.mk.injEq] at h
        rw [hurip, ← h.1]; exact Ne.symm P.res_sc)
      (by rw [hurip]; simp [adderClangWorldL, crtWorld]) r).trans
      (adderClangL_scanf b lb gate res rel _ r)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · exact abiEntry_of' (v := b + 4455#64) (by rw [hsU, e16]; omega) hr2U
  · rw [huregs .rdi (by simp)]; exact ⟨by decide, hfmt⟩
  · rw [huregs .rsi (by simp)]
    show u.m.memory.Permitted .write (t.m.core.read .rsp - 8#64 + 4#64).toNat 4
    rw [eR4]; exact perm_room hroomU (Or.inr rfl) (by omega) (by omega)
  · rw [huregs .rdx (by simp)]
    show u.m.memory.Permitted .write (t.m.core.read .rsp - 8#64).toNat 4
    rw [e8]; exact perm_room hroomU (Or.inr rfl) (by omega) (by omega)
  · rw [huregs .rsi (by simp)]
    show u.m.memory.Permitted .read (t.m.core.read .rsp - 8#64 + 4#64).toNat 4
    rw [eR4]; exact perm_room hroomU (Or.inl rfl) (by omega) (by omega)
  · rw [huregs .rdx (by simp)]
    show u.m.memory.Permitted .read (t.m.core.read .rsp - 8#64).toNat 4
    rw [e8]; exact perm_room hroomU (Or.inl rfl) (by omega) (by omega)
  · rw [huregs .rsi (by simp), huregs .rdx (by simp)]
    show (t.m.core.read .rsp - 8#64 + 4#64).toNat + 4 ≤ (t.m.core.read .rsp - 8#64).toNat ∨
      (t.m.core.read .rsp - 8#64).toNat + 4 ≤ (t.m.core.read .rsp - 8#64 + 4#64).toNat
    rw [eR4, e8]; omega
  intro t2 hpost
  rw [huregs .rsi (by simp), huregs .rdx (by simp), hug] at hpost
  have hpost' : (match scanDD t.g.inp with
      | .ub => True
      | .ok a b' rest =>
        StdioFrame (Img adderClangLayout b) _ t2 (fun x => In4 (t.m.core.read .rsp - 8#64 + 4#64) x ∨
          In4 (t.m.core.read .rsp - 8#64) x) ∧
        low32 (t2.m.core.read .rax) = 2#32 ∧ t2.g = { t.g with inp := rest } ∧
        t2.m.memory.readBytes (t.m.core.read .rsp - 8#64 + 4#64).toNat 4 = some (le32 a) ∧
        t2.m.memory.readBytes (t.m.core.read .rsp - 8#64).toNat 4 = some (le32 b')
      | .fail =>
        StdioFrame (Img adderClangLayout b) _ t2 (fun x => In4 (t.m.core.read .rsp - 8#64 + 4#64) x ∨
          In4 (t.m.core.read .rsp - 8#64) x) ∧
        low32 (t2.m.core.read .rax) ≠ 2#32 ∧ t2.g.jobs = t.g.jobs ∧ t2.g.atexit = t.g.atexit ∧
        t2.g.done = none ∧ t2.g.out = t.g.out) := hpost
  have hr2 : (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)).readBytes (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 4455#64]) := pushMem_read r2 p2
  cases hsc : scanDD t.g.inp with
  | ub => exact absurd hsc hpre
  | ok a b' rest =>
    rw [hsc] at hpost'
    obtain ⟨⟨hab, hfs, hkeep, hex, htls, hpg2⟩, hrax, hg2, ha, hb'⟩ := hpost'
    have hpc : t2.m.core.rip = b + 4455#64 := by
      rw [hab.pc]; exact retOf_of' hr2U
    have hsp2' : t2.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
      rw [hab.stack, hsU]; simp
    have hd2 : t2.g.done = none := by rw [hg2]; exact hd
    have hk2' : Keeps (ImgH adderClangLayout b 0x4008 0x4010) (pushMem (pushMem t.m.memory
        (t.m.core.read .rsp) (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 4455#64)) t2.m.memory :=
      hkI.trans (Keeps.mono hkeep (fun x hx' => ⟨Or.inl hx'.1, fun h => by
        rcases h with h | h <;> (have := (hroom.2.2 x (by simp [In4] at h; omega)
          (by simp [In4] at h; omega)).2.2; exact this (Or.inl hx'.1))⟩))
    have hk2 : Keeps (ImgH adderClangLayout b 0x4000 0x4010) (pushMem (pushMem t.m.memory
        (t.m.core.read .rsp) (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 4455#64)) t2.m.memory :=
      hk2'.mono fun a h => ⟨h.1, fun h' => h.2 ⟨by omega, h'.2⟩⟩
    have hm3 := hm2.keepH adderClang_ok' hb adderClang_avoids hk2
    have hx3 := Plt0.keepH hb hx2.toPlt0 hk2'
    refine must_listed (o := 23) adderClang_mainL rfl hd2 (by rw [hpc]; exact hin _ (by decide))
      hm3.main (by rw [hpc, ripadd]; rfl) ?_
    xstep [hpc]
    have hrax' : (t2.m.core.read .rax).setWidth 32 = 2#32 := hrax
    refine must_listed (o := 25) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    refine must_listed (o := 30) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hrax', Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    refine must_listed (o := 33) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    have hlb := loadN_of_readBytes hb'
    have hla := loadN_of_readBytes ha
    refine must_listed (o := 35) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp2', hlb, le32_val']
    refine must_listed (o := 38) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp2', hla, le32_val', le32_val, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.AluOp.resultN]
    refine must_listed (o := 42) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [addrK b (x := 4481) (y := 0x200a) (d := 0x00000e89#32) (by decide)]
    refine must_listed (o := 49) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    -- `call printf@plt`
    have hroom3 : StackRoom (adderClangWorldL b lb gate res rel) t2.m.memory (t.m.core.read .rsp) := by
      refine ⟨hsp, hsp2, fun a h1 h2 => ?_⟩
      have hp : ∀ acc, t2.m.memory.permits acc a = u.m.memory.permits acc a := by
        intro acc
        by_cases ha : a < (t.m.core.read .rsp).toNat - 16
        · exact hpg2 a acc (by rw [hsU, e16]; omega) (by rw [hsU, e16]; omega)
        · by_cases hx : In4 (t.m.core.read .rsp - 8#64 + 4#64) a ∨ In4 (t.m.core.read .rsp - 8#64) a
          · exact (hex a hx).2 acc
          · exact (hkeep a ⟨Or.inr (by rw [hsU, e16]; omega), hx⟩).2 acc
      rw [hp, hp]; exact hroomU.2.2 a h1 h2
    have p3 : t2.m.memory.Permitted .write (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 := by
      rw [e16]; exact perm_room hroom3 (Or.inr rfl) (by omega) (by omega)
    have r3 : t2.m.memory.Permitted .read (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 := by
      rw [e16]; exact perm_room hroom3 (Or.inl rfl) (by omega) (by omega)
    have hout3 : ∀ x, (t.m.core.read .rsp - 8#64 - 8#64).toNat ≤ x →
        x < (t.m.core.read .rsp - 8#64 - 8#64).toNat + 8 → ¬ Img adderClangLayout b x := by
      rw [e16]; intro x h1 h2
      exact fun h => (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl h)
    have k4 := keeps_push_of (L := adderClangLayout) (b := b) (m := t2.m.memory)
      (sp := t.m.core.read .rsp - 8#64) (v := b + 4488#64) (by simpa using hout3)
    have hm4 := hm3.keep adderClang_ok' hb k4
    have hx4 := Plt0.keepH hb hx3 (Keeps.imgH k4)
    refine must_listed (o := 51) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
    rw [pushWord_mem (by simpa [hsp2'] using p3)]
    xstep [hsp2', addrK b (x := 4488) (y := 0x1030) (d := 0xfffffea8#32) (by decide)]
    -- `printf@plt`, first call: through the resolver
    refine lazy_printf P hd2 rfl hx4 (by simp; omega) (fun a h1 h2 => ?_) ?_
    · simp at h1 h2
      exact hroom3.2.2 a (by omega) (by omega)
    intro u' hurip' hursp' huregs' hug' hukeep' hupg'
    have hd2' : u'.g.done = none := by rw [hug']; exact hd2
    have hsU' : u'.m.core.read .rsp = t.m.core.read .rsp - 8#64 - 8#64 := by
      rw [hursp']; simp
    have hkU' : Keeps (ImgH adderClangLayout b 0x4000 0x4010)
        (pushMem t2.m.memory (t.m.core.read .rsp - 8#64) (b + 4488#64)) u'.m.memory :=
      hukeep'.mono fun a h => ⟨fun h' => h.2 ⟨h'.1, by omega⟩, Or.inl (Or.inl h.1)⟩
    have hrdU' : ∀ {a len : Nat}, (t.m.core.read .rsp).toNat - 16 ≤ a →
        a + len ≤ (t.m.core.read .rsp).toNat + 8 → u'.m.memory.readBytes a len =
          (pushMem t2.m.memory (t.m.core.read .rsp - 8#64) (b + 4488#64)).readBytes a len := fun h1 h2 =>
      hukeep'.readBytes (fun k hk => ⟨fun h => notHole _ (by omega) (by omega) ⟨h.1, by omega⟩,
        Or.inr (by simp; omega)⟩)
    have hmU' := hm4.keepH adderClang_ok' hb adderClang_avoids hkU'
    have hro4 := hmU'.rodata
    have hfmt2 : u'.m.memory.readBytes (b + 8202#64).toNat 4 = some (fmtDN ++ [0]) := by
      have := readBytes_sub' hro4 (k := 10) (j := 4) (by decide) (by decide)
      rw [show (b + 8202#64).toNat = (b + BitVec.ofNat 64 adderClangLayout.ro).toNat + 10 by
        rw [addr_toNat (by simp [adderClangLayout] at hb ⊢; omega),
          addr_toNat (by simp [adderClangLayout] at hb ⊢; omega)]; rfl, this]
      decide
    have hr3 := pushMem_read (v := b + 4488#64) r3 p3
    have hr3U : u'.m.memory.readBytes (u'.m.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [b + 4488#64]) := by
      rw [hsU', hrdU' (by rw [e16]) (by rw [e16]; omega)]; exact hr3
    refine must_contract hd2' (show ¬ Img adderClangLayout b u'.m.core.rip.toNat by
        rw [hurip']; exact hpf_out)
      (fun r => (extStep_fn (f := .named (Silmaril.Elf.Link.DynElf.nm "printf"))
        (by rw [hurip']; simpa [printfAt, adderClangWorldL, crtWorld] using hpf_gate)
        (fun _ _ h => by
          simp only [adderClangWorldL, crtWorld, Option.some.injEq, Prod.mk.injEq] at h
          rw [hurip', ← h.1]; exact Ne.symm P.res_pf)
        (by rw [hurip']; simp [adderClangWorldL, crtWorld]) r).trans
        (adderClangL_printf b lb gate res rel _ r)) ⟨?_, ?_⟩ ?_
    · exact abiEntry_of' (v := b + 4488#64) (by rw [hsU', e16]; omega) hr3U
    · rw [huregs' .rdi (by simp)]; exact ⟨by decide, hfmt2⟩
    rintro t3 ⟨⟨hab3, -, hk3, -, -, -⟩, hj3, hat3, hdn3, hin3, hout3⟩
    rw [hug'] at hj3 hat3 hin3
    rw [hug', huregs' .rsi (by simp)] at hout3
    have hpc3 : t3.m.core.rip = b + 4488#64 := by
      rw [hab3.pc]; exact retOf_of' hr3U
    have hsp3 : t3.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
      rw [hab3.stack, hsU']; simp
    have hd3 : t3.g.done = none := hdn3
    have hk3' : Keeps (ImgH adderClangLayout b 0x4000 0x4010)
        (pushMem t2.m.memory (t.m.core.read .rsp - 8#64) (b + 4488#64)) t3.m.memory :=
      hkU'.trans (Keeps.mono hk3 (fun x hx' => ⟨Or.inl hx'.1, id⟩))
    have hm5 := hm4.keepH adderClang_ok' hb adderClang_avoids hk3'
    -- the slots `pop` and `ret` read
    have hb'' := hb'; rw [e8] at hb''
    have ha' := ha; rw [eR4] at ha'
    have c8 := Memory.readBytes_append hb''
      (by rw [show (t.m.core.read .rsp).toNat - 8 + 4 = (t.m.core.read .rsp).toNat - 4 by omega]; exact ha')
    have c8m4 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4488#64) c8
      (Or.inr (by rw [e16]; omega))
    have c8u := slot_keeps hukeep' c8m4 (fun k hk => ⟨fun h => notHole _ (by omega) (by omega)
      ⟨h.1, by omega⟩, Or.inr (by simp; omega)⟩)
    have c8t3 := slot_keeps hk3 c8u (fun k hk => ⟨Or.inr (by rw [hsU']; simp; omega), id⟩)
    have d1 := slot_push (sp := t.m.core.read .rsp) (v := t.m.core.read .rax) hret
      (Or.inr (by rw [e8]; omega))
    have d2 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4455#64) d1
      (Or.inr (by rw [e16]; omega))
    have d2u := slot_keeps hukeep d2 (fun k hk => ⟨fun h => notHole _ (by omega) (by omega)
      ⟨by omega, h.2⟩, Or.inr (by simp; omega)⟩)
    have d3 := slot_keeps hkeep d2u (fun k hk => ⟨Or.inr (by rw [hsU]; simp; omega),
      fun h => by rcases h with h | h <;> simp only [In4] at h <;> (try rw [eR4] at h) <;>
        (try rw [e8] at h) <;> omega⟩)
    have d4 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4488#64) d3
      (Or.inr (by rw [e16]; omega))
    have d4u := slot_keeps hukeep' d4 (fun k hk => ⟨fun h => notHole _ (by omega) (by omega)
      ⟨h.1, by omega⟩, Or.inr (by simp; omega)⟩)
    have d5 := slot_keeps hk3 d4u (fun k hk => ⟨Or.inr (by rw [hsU']; simp; omega), id⟩)
    have haddr8 : (18446744073709551608 + (t.m.core.read .rsp).toNat) % 18446744073709551616 =
        (t.m.core.read .rsp).toNat - 8 := by omega
    refine must_listed (o := 56) adderClang_mainL rfl hd3 (by rw [hpc3]; exact hin _ (by decide))
      hm5.main (by rw [hpc3, ripadd]; rfl) ?_
    xstep [hpc3]
    refine must_listed (o := 58) adderClang_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.popWord, hsp3, haddr8, c8t3]
    refine must_listed (o := 59) adderClang_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.popWord, BitVec.sub_add_cancel, d5]
    refine kk _ rfl (by rw [hj3]; simp [hg2]) (by rw [hat3]; simp [hg2]) hd3 hm5 ?_
    simp only [adderPost, hsc]
    refine ⟨by simp [low32, Silmaril.X86.Ext.AluOp.resultN], by rw [hin3]; simp [hg2], ?_⟩
    rcases hout3 with h | ⟨hr, p, hp, h⟩
    · have hv : low32 (BitVec.setWidth 64 (BitVec.ofInt 32 b' + BitVec.ofInt 32 a)) =
          BitVec.ofInt 32 a + BitVec.ofInt 32 b' := by simp [low32, BitVec.add_comm]
      left; rw [h, ← hv, hg2]; rfl
    · have hv : low32 (BitVec.setWidth 64 (BitVec.ofInt 32 b' + BitVec.ofInt 32 a)) =
          BitVec.ofInt 32 a + BitVec.ofInt 32 b' := by simp [low32, BitVec.add_comm]
      right; refine ⟨hr, p, ?_, by rw [h, hg2]⟩
      rw [← hv]; exact hp
  | fail =>
    rw [hsc] at hpost'
    obtain ⟨⟨hab, hfs, hkeep, hex, htls, -⟩, hrax, hj2, hat2, hdn2, hout2⟩ := hpost'
    have hpc : t2.m.core.rip = b + 4455#64 := by
      rw [hab.pc]; exact retOf_of' hr2U
    have hsp2' : t2.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
      rw [hab.stack, hsU]; simp
    have hd2 : t2.g.done = none := hdn2
    have hk2' : Keeps (ImgH adderClangLayout b 0x4008 0x4010) (pushMem (pushMem t.m.memory
        (t.m.core.read .rsp) (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 4455#64)) t2.m.memory :=
      hkI.trans (Keeps.mono hkeep (fun x hx' => ⟨Or.inl hx'.1, fun h => by
        rcases h with h | h <;> (have := (hroom.2.2 x (by simp [In4] at h; omega)
          (by simp [In4] at h; omega)).2.2; exact this (Or.inl hx'.1))⟩))
    have hk2 : Keeps (ImgH adderClangLayout b 0x4000 0x4010) (pushMem (pushMem t.m.memory
        (t.m.core.read .rsp) (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 4455#64)) t2.m.memory :=
      hk2'.mono fun a h => ⟨h.1, fun h' => h.2 ⟨by omega, h'.2⟩⟩
    have hm3 := hm2.keepH adderClang_ok' hb adderClang_avoids hk2
    refine must_listed (o := 23) adderClang_mainL rfl hd2 (by rw [hpc]; exact hin _ (by decide))
      hm3.main (by rw [hpc, ripadd]; rfl) ?_
    xstep [hpc]
    refine must_listed (o := 25) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    refine must_listed (o := 30) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    refine must_listed (o := 33) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    split
    · rename_i heq; simp at heq
    rotate_left
    · rename_i heq
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_false] at heq
      exact absurd (sub_eq_zero.mp (of_decide_eq_true heq)) hrax
    simp only [WP_ok]
    obtain ⟨l8, hlen8, hl8⟩ := readBytes_of_backed (m := t2.m.memory) (a := (t.m.core.read .rsp).toNat - 8)
      (n := 8) (by omega) (by omega) (fun k hk => by
        have hx' := hex ((t.m.core.read .rsp).toNat - 8 + k) (by
          by_cases hk4 : k < 4
          · right; simp only [In4]; rw [e8]; omega
          · left; simp only [In4]; rw [eR4]; omega)
        refine ⟨?_, hx'.1⟩
        rw [hx'.2]
        exact (hroomU.2.2 _ (by omega) (by omega)).1)
    have d1 := slot_push (sp := t.m.core.read .rsp) (v := t.m.core.read .rax) hret
      (Or.inr (by rw [e8]; omega))
    have d2 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4455#64) d1
      (Or.inr (by rw [e16]; omega))
    have d2u := slot_keeps hukeep d2 (fun k hk => ⟨fun h => notHole _ (by omega) (by omega)
      ⟨by omega, h.2⟩, Or.inr (by simp; omega)⟩)
    have d3 := slot_keeps hkeep d2u (fun k hk => ⟨Or.inr (by rw [hsU]; simp; omega),
      fun h => by rcases h with h | h <;> simp only [In4] at h <;> (try rw [eR4] at h) <;>
        (try rw [e8] at h) <;> omega⟩)
    have haddr8 : (18446744073709551608 + (t.m.core.read .rsp).toNat) % 18446744073709551616 =
        (t.m.core.read .rsp).toNat - 8 := by omega
    refine must_listed (o := 58) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    obtain ⟨w8, hw8⟩ := wordOfBytes?_of_length hlen8
    xstep [Silmaril.X86.popWord, hsp2', haddr8, hl8, hw8]
    refine must_listed (o := 59) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.popWord, hsp2', BitVec.sub_add_cancel, d3]
    refine kk _ rfl hj2 hat2 hd2 hm3 ?_
    simp only [adderPost, hsc]
    exact ⟨by simp [low32], hout2⟩


/-- **`Task.adderClangLazyMain` holds.** -/
theorem adderClangLazyMain_holds : Task.adderClangLazyMain :=
  fun _ _ _ _ _ P => adderClangL_main P

/-- **The adder (clang) under lazy binding, end to end**: under the loader relation, from every documented initial
state whose `stdin` does not overflow `int` in `scanf`, every run ends as `adderPost` says. -/
theorem adderClangL_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn true res s.m.memory)
    (P : AdderPlacedL b lb gate res)
    (hs : AtEntry adderClangLayout (adderClangWorldL b lb gate res rel) b s)
    (hin : scanDD s.g.inp ≠ .ub) :
    MustQ (adderClangWorldL b lb gate res rel) (Ends s.g (adderPost rel) rel) s :=
  adderClangL_run adderClangLazyMain_holds hc hl hload P hs hin

/-- **The adder (clang) on the text `"a b\n"`**: with `a`, `b` and `a + b` in `int` and an
empty `stdout`, every run ends with exit status `0` and `stdout` = the decimal text of
`a + b` and a newline (a prefix of it if writes to fd 1 may fail). -/
theorem adderClangL_sum {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn true res s.m.memory)
    (P : AdderPlacedL b lb gate res)
    (hs : AtEntry adderClangLayout (adderClangWorldL b lb gate res rel) b s)
    {x y : Int} (hx : inInt32 x = true) (hy : inInt32 y = true) (hxy : inInt32 (x + y) = true)
    (hin : s.g.inp = decStr x ++ [32#8] ++ decStr y ++ [10#8]) (hout : s.g.out = []) :
    MustQ (adderClangWorldL b lb gate res rel)
      (fun u => ∃ w, u.g.done = some (0, w) ∧ w <+: decStr (x + y) ++ [10#8] ∧
        (rel = true → w = decStr (x + y) ++ [10#8])) s := by
  have hsc := scanDD_text hx hy
  rw [← hin] at hsc
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderClangL_exits hc hl hload P hs (by rw [hsc]; simp))
  rintro u ⟨g', e, w, hp, hd, hw, hrel⟩
  simp only [adderPost, hsc] at hp
  obtain ⟨rfl, -, ho⟩ := hp
  rw [int32_add hxy hx hy, hout] at ho
  refine ⟨w, by rw [hd]; rfl, ?_, ?_⟩
  · rcases ho with ho | ⟨-, p, hp, ho⟩
    · rw [ho] at hw; simpa using hw
    · rw [ho] at hw; simp at hw; exact hw.trans hp
  · intro hr; rw [hrel hr]
    rcases ho with ho | ⟨hr', -⟩
    · rw [ho]; simp
    · rw [hr] at hr'; cases hr'

end Silmaril.Elf.Link.Dyn.Small
