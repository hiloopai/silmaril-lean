-- variant-of: glibc.adder.gcc | style: small-direct | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.AdderGcc
module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderGcc

/-! # The adder (gcc): `main` meets `MainOk`, the stack guard check passes -/

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

theorem StackRoom.of_regions {W : World} {m m' : Memory} {sp : Word} (h : StackRoom W m sp)
    (hr : m'.regions = m.regions) : StackRoom W m' sp :=
  ⟨h.1, h.2.1, fun a h1 h2 => by
    have := h.2.2 a h1 h2
    simp only [Memory.permits, hr]; exact this⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`main` of `adderGcc`.** -/
theorem adderGcc_main {b lb gate fs : Word} {rel : Bool}
    (hb : b.toNat + adderGccLayout.size < 2 ^ 64)
    (hsc_out : ¬ Img adderGccLayout b (scanfAt lb).toNat)
    (hpf_out : ¬ Img adderGccLayout b (printfChkAt lb).toNat)
    (hsc_gate : scanfAt lb ≠ gate) (hpf_gate : printfChkAt lb ≠ gate) :
    MainOk (adderGccWorld b lb gate fs rel) adderGccLayout b (lsmAt lb) (cxaAt lb)
      (GccX b lb fs) (fun g => scanDD g.inp ≠ .ub) (adderPost rel) := by
  intro Q t hd hrip hal hret hroom hm hx hpre kk
  obtain ⟨hx, hfs, hfsb, c, hc⟩ := hx
  have hin : ∀ n, n < 0x4018 → (adderGccWorld b lb gate fs rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => img_add (L := adderGccLayout) hb (by simpa [adderGccLayout] using hn)
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hrip0 : t.m.core.rip = b + BitVec.ofNat 64 0x10a0 := hrip
  have hmain : Loaded t.m.memory (b + BitVec.ofNat 64 0x10a0) adderGccLayout.cMain := hm.main
  have hc0 : loadN t.m.memory (t.m.core.fsBase + 40#64) 8 = some c := by rw [hfs]; exact hc
  refine must_listed (o := 0) adderGcc_mainL rfl hd (by rw [hrip0]; exact hin _ (by decide)) hmain
    (by rw [hrip0]; simp) ?_
  xstep [hrip0]
  refine must_listed (o := 4) adderGcc_mainL rfl hd (hin _ (by decide)) hmain (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.AluOp.resultN]
  refine must_listed (o := 8) adderGcc_mainL rfl hd (hin _ (by decide)) hmain (by rw [ripadd]) ?_
  xstep [addrK b (x := 4271) (y := 0x2004) (d := 0x00000f55#32) (by decide)]
  refine must_listed (o := 15) adderGcc_mainL rfl hd (hin _ (by decide)) hmain (by rw [ripadd]) ?_
  xstep [memFs_addr, hc0]
  -- the guard copy at `rsp + 8`
  have e24 : (t.m.core.read .rsp - 24#64).toNat = (t.m.core.read .rsp).toNat - 24 :=
    sub_toNat (k := 24) (by omega) (by decide)
  have e16 : (t.m.core.read .rsp - 24#64 + 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := by
    rw [add_toNat (k := 8) (by rw [e24]; omega), e24]; omega
  have pw16 : t.m.memory.Permitted .write (t.m.core.read .rsp - 24#64 + 8#64).toNat 8 := by
    rw [e16]; exact perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have pr16 : t.m.memory.Permitted .read (t.m.core.read .rsp - 24#64 + 8#64).toNat 8 := by
    rw [e16]; exact perm_room hroom (Or.inl rfl) (by omega) (by omega)
  obtain ⟨m1, hs1, hS1⟩ := Silmaril.X86.Ext.storeN_isSome (v := c) pw16
  refine must_listed (o := 24) adderGcc_mainL rfl hd (hin _ (by decide)) hmain (by rw [ripadd]) ?_
  xstep [ofReg_addr]
  erw [hs1]
  simp only [Option.map_some, WP_ok]
  have hroom1 : StackRoom (adderGccWorld b lb gate fs rel) m1 (t.m.core.read .rsp) :=
    StackRoom.of_regions hroom hS1.regions
  have hk1 : Keeps (adderGccWorld b lb gate fs rel).Kept t.m.memory m1 :=
    keeps_of_writesOnly hS1.frame (fun x hx' => by
      rw [e16]
      simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]
      by_contra hc
      exact (hroom.2.2 x (by omega) (by omega)).2.2 hx')
  have hm1 := hm.keep adderGcc_ok' hb (keeps_img rfl hk1)
  have hx1 := hx.keep (L := adderGccLayout) hb (by decide)
    (by simp [adderGccGotAt, adderGccGot, adderGccLayout]) (keeps_img rfl hk1)
  have hfs40 : (fs + 40#64).toNat = fs.toNat + 40 := add_toNat (k := 40) (by omega)
  have hgk : ∀ {m m' : Memory}, Keeps (adderGccWorld b lb gate fs rel).Kept m m' →
      loadN m' (fs + 40#64) 8 = loadN m (fs + 40#64) 8 := fun h =>
    loadN_keeps h (fun i hi => Or.inr (Or.inr (by
      show Guard fs ((fs + 40#64).toNat + i); rw [hfs40]; simp only [Guard]; omega)))
  have hc1 : loadN m1 (fs + 40#64) 8 = some c := (hgk hk1).trans hc
  have hcopy1 : loadN m1 (t.m.core.read .rsp - 24#64 + 8#64) 8 = some c :=
    Silmaril.X86.Ext.loadN_storeN_eight hs1 pr16
  refine must_listed (o := 29) adderGcc_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep []
  refine must_listed (o := 31) adderGcc_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep [ofReg_addr]
  refine must_listed (o := 36) adderGcc_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  xstep []
  -- `call __isoc99_scanf@plt`
  have e32 : (t.m.core.read .rsp - 24#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 32 := by
    rw [sub_toNat (k := 8) (by rw [e24]; omega) (by decide), e24]; omega
  have p2 : m1.Permitted .write (t.m.core.read .rsp - 24#64 - 8#64).toNat 8 := by
    rw [e32]; exact perm_room hroom1 (Or.inr rfl) (by omega) (by omega)
  have r2 : m1.Permitted .read (t.m.core.read .rsp - 24#64 - 8#64).toNat 8 := by
    rw [e32]; exact perm_room hroom1 (Or.inl rfl) (by omega) (by omega)
  have k2 := keeps_push_kept (m := m1) (v := b + 4300#64) hroom1 (sp' := t.m.core.read .rsp - 24#64)
    (by rw [e24]; omega) (by rw [e24]; omega)
  have hm2 := hm1.keep adderGcc_ok' hb (keeps_img rfl k2)
  have hx2 := hx1.keep (L := adderGccLayout) hb (by decide)
    (by simp [adderGccGotAt, adderGccGot, adderGccLayout]) (keeps_img rfl k2)
  refine must_listed (o := 39) adderGcc_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by exact p2)]
  xstep [addrK b (x := 4300) (y := 0x1090) (d := 0xffffffc4#32) (by decide)]
  -- the `.plt.sec` stub
  have hst1 := hx2.code (0x1090, [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x36, 0x2f, 0x00, 0x00])
    (by simp [adderGccStubs])
  have hslot : loadN (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)) (b + 16336#64) 8 =
      some (lb + 392720#64) := by
    simpa using hx2.slot (0x3fd0, lb + BitVec.ofNat 64 0x5fe10)
      (by simp [adderGccGotAt, adderGccGot])
  refine must_listed (o := 0) adderGcc_stubScanf rfl hd (hin _ (by decide)) hst1 (by simp) ?_
  xstep []
  refine must_listed (o := 4) adderGcc_stubScanf rfl hd (hin _ (by decide)) hst1 (by rw [ripadd]) ?_
  xstep [addrK b (x := 0x1090 + 4 + 6) (y := 0x3fd0) (d := 0x2f36#32) (by decide)]
  erw [hslot]
  simp only [WP_ok]
  -- `__isoc99_scanf`
  have hro := hm2.rodata
  have hfmt : (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).readBytes (b + 8196#64).toNat 6 =
      some (fmtDD ++ [0]) := by
    have := readBytes_sub' hro (k := 4) (j := 6) (by decide) (by decide)
    rw [show (b + 8196#64).toNat = (b + BitVec.ofNat 64 adderGccLayout.ro).toNat + 4 by
      rw [addr_toNat (by simp [adderGccLayout] at hb ⊢; omega),
        addr_toNat (by simp [adderGccLayout] at hb ⊢; omega)]; rfl, this]
    decide
  have hroom2 : StackRoom (adderGccWorld b lb gate fs rel)
      (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)) (t.m.core.read .rsp) :=
    StackRoom.pushMem hroom1
  have e20 : (t.m.core.read .rsp - 24#64 + 4#64).toNat = (t.m.core.read .rsp).toNat - 20 := by
    rw [add_toNat (k := 4) (by rw [e24]; omega), e24]; omega
  have hr2 : (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).readBytes
      (t.m.core.read .rsp - 24#64 - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 4300#64]) := pushMem_read r2 p2
  refine must_contract hd (show ¬ Img adderGccLayout b (lb + 392720#64).toNat from hsc_out)
    (fun r => (extStep_fn (f := .named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf"))
      (by simpa [scanfAt, adderGccWorld, crtWorld] using hsc_gate)
      (fun _ _ h => by simp [adderGccWorld, crtWorld] at h)
      (by simp [adderGccWorld, crtWorld]) r).trans (adderGcc_scanf b lb gate fs rel _ r)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · exact abiEntry_of' (v := b + 4300#64)
      (by show (t.m.core.read .rsp - 24#64 - 8#64).toNat % 16 = 8; rw [e32]; omega) (by exact hr2)
  · exact ⟨by decide, hfmt⟩
  · show (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).Permitted .write
      (t.m.core.read .rsp - 24#64).toNat 4
    rw [e24]; exact perm_room hroom2 (Or.inr rfl) (by omega) (by omega)
  · show (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).Permitted .write
      (t.m.core.read .rsp - 24#64 + 4#64).toNat 4
    rw [e20]; exact perm_room hroom2 (Or.inr rfl) (by omega) (by omega)
  · show (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).Permitted .read
      (t.m.core.read .rsp - 24#64).toNat 4
    rw [e24]; exact perm_room hroom2 (Or.inl rfl) (by omega) (by omega)
  · show (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).Permitted .read
      (t.m.core.read .rsp - 24#64 + 4#64).toNat 4
    rw [e20]; exact perm_room hroom2 (Or.inl rfl) (by omega) (by omega)
  · show (t.m.core.read .rsp - 24#64).toNat + 4 ≤ (t.m.core.read .rsp - 24#64 + 4#64).toNat ∨
      (t.m.core.read .rsp - 24#64 + 4#64).toNat + 4 ≤ (t.m.core.read .rsp - 24#64).toNat
    rw [e24, e20]; omega
  intro t2 hpost
  have hpost' : (match scanDD t.g.inp with
      | .ub => True
      | .ok a b' rest =>
        StdioFrame (Img adderGccLayout b) _ t2 (fun x => In4 (t.m.core.read .rsp - 24#64) x ∨
          In4 (t.m.core.read .rsp - 24#64 + 4#64) x) ∧
        low32 (t2.m.core.read .rax) = 2#32 ∧ t2.g = { t.g with inp := rest } ∧
        t2.m.memory.readBytes (t.m.core.read .rsp - 24#64).toNat 4 = some (le32 a) ∧
        t2.m.memory.readBytes (t.m.core.read .rsp - 24#64 + 4#64).toNat 4 = some (le32 b')
      | .fail =>
        StdioFrame (Img adderGccLayout b) _ t2 (fun x => In4 (t.m.core.read .rsp - 24#64) x ∨
          In4 (t.m.core.read .rsp - 24#64 + 4#64) x) ∧
        low32 (t2.m.core.read .rax) ≠ 2#32 ∧ t2.g.jobs = t.g.jobs ∧ t2.g.atexit = t.g.atexit ∧
        t2.g.done = none ∧ t2.g.out = t.g.out) := hpost
  have hc2 : loadN (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)) (fs + 40#64) 8 = some c :=
    (hgk k2).trans hc1
  have hcp2 : loadN (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64))
      (t.m.core.read .rsp - 24#64 + 8#64) 8 = some c := by
    rw [loadN_keeps (P := fun a => (t.m.core.read .rsp).toNat - 16 ≤ a ∧ a < (t.m.core.read .rsp).toNat - 8)
      (pushMem_keeps (by intro x hx'; rw [e32]; omega)) (fun i hi => by rw [e16]; omega)]
    exact hcopy1
  have hoex : ∀ x, (t.m.core.read .rsp).toNat - 16 ≤ x → x < (t.m.core.read .rsp).toNat + 8 →
      ¬ (In4 (t.m.core.read .rsp - 24#64) x ∨ In4 (t.m.core.read .rsp - 24#64 + 4#64) x) := by
    intro x h1 h2 h; rcases h with h | h <;> simp only [In4] at h <;> (try rw [e24] at h) <;>
      (try rw [e20] at h) <;> omega
  cases hsc : scanDD t.g.inp with
  | ub => exact absurd hsc hpre
  | ok a b' rest =>
    rw [hsc] at hpost'
    obtain ⟨⟨hab, hfs2, hkeep, hex, htls, -⟩, hrax, hg2, ha, hb'⟩ := hpost'
    have hpc : t2.m.core.rip = b + 4300#64 := by
      rw [hab.pc]; exact retOf_of' (by exact hr2)
    have hsp2' : t2.m.core.read .rsp = t.m.core.read .rsp - 24#64 := by
      rw [hab.stack]; exact BitVec.sub_add_cancel _ _
    have hfs2' : t2.m.core.fsBase = fs := by rw [hfs2]; exact hfs
    have hd2 : t2.g.done = none := by rw [hg2]; exact hd
    have hk2 : Keeps (Img adderGccLayout b) (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64))
        t2.m.memory :=
      Keeps.mono hkeep (fun x hx' => ⟨Or.inl hx', fun h => by
        rcases h with h | h <;> simp only [In4] at h <;> (try rw [e24] at h) <;> (try rw [e20] at h) <;>
          exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl hx')⟩)
    have hm3 := hm2.keep adderGcc_ok' hb hk2
    have hx3 := hx2.keep (L := adderGccLayout) hb (by decide)
      (by simp [adderGccGotAt, adderGccGot, adderGccLayout]) hk2
    have hc3 : loadN t2.m.memory (fs + 40#64) 8 = some c := by
      rw [loadN_keeps htls (fun i hi => ⟨by
        show t.m.core.fsBase.toNat + 0x28 ≤ (fs + 40#64).toNat + i ∧
          (fs + 40#64).toNat + i < t.m.core.fsBase.toNat + 0x30
        rw [hfs, hfs40]; omega, fun h => by
          have hg : Guard fs ((fs + 40#64).toNat + i) := by rw [hfs40]; simp only [Guard]; omega
          rcases h with h | h <;> simp only [In4] at h <;> (try rw [e24] at h) <;>
            (try rw [e20] at h) <;>
            exact (hroom.2.2 _ (by omega) (by omega)).2.2 (Or.inr (Or.inr hg))⟩)]
      exact hc2
    have hcp3 : loadN t2.m.memory (t.m.core.read .rsp - 24#64 + 8#64) 8 = some c := by
      rw [loadN_keeps hkeep (fun i hi => ⟨Or.inr (by
        show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32, e16]; omega),
        hoex _ (by rw [e16]; omega) (by rw [e16]; omega)⟩)]
      exact hcp2
    have hrax' : (t2.m.core.read .rax).setWidth 32 = 2#32 := hrax
    refine must_listed (o := 44) adderGcc_mainL rfl hd2 (by rw [hpc]; exact hin _ (by decide))
      hm3.main (by rw [hpc, ripadd]; rfl) ?_
    xstep [hpc]
    refine must_listed (o := 46) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    refine must_listed (o := 51) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hrax', Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    refine must_listed (o := 54) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    have hlb := loadN_of_readBytes hb'
    have hla := loadN_of_readBytes ha
    refine must_listed (o := 77) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp2', hlb, le32_val']
    refine must_listed (o := 81) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [addrK b (x := 4344) (y := 0x200a) (d := 0x00000f12#32) (by decide)]
    refine must_listed (o := 88) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp2', hla, le32_val', le32_val, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.AluOp.resultN]
    refine must_listed (o := 91) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    refine must_listed (o := 93) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    -- `call __printf_chk@plt`
    have hpk : ∀ k < 8, ∀ acc, t2.m.memory.permits acc ((t.m.core.read .rsp).toNat - 32 + k) =
        (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64)).permits acc
          ((t.m.core.read .rsp).toNat - 32 + k) := by
      intro k hk acc
      exact ((hkeep _ ⟨Or.inr (by show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32]; omega),
        fun h => by rcases h with h | h <;> simp only [In4] at h <;> (try rw [e24] at h) <;>
          (try rw [e20] at h) <;> omega⟩).2 acc)
    have p3 : t2.m.memory.Permitted .write (t.m.core.read .rsp - 24#64 - 8#64).toNat 8 := by
      rw [e32]
      exact permitted_congr (fun k hk => hpk k hk _)
        (perm_room (acc := .write) hroom2 (Or.inr rfl) (by omega) (by omega))
    have r3 : t2.m.memory.Permitted .read (t.m.core.read .rsp - 24#64 - 8#64).toNat 8 := by
      rw [e32]
      exact permitted_congr (fun k hk => hpk k hk _)
        (perm_room (acc := .read) hroom2 (Or.inl rfl) (by omega) (by omega))
    have hout3 : ∀ x, (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ x →
        x < (t.m.core.read .rsp - 24#64 - 8#64).toNat + 8 → ¬ Img adderGccLayout b x := by
      rw [e32]; intro x h1 h2
      exact fun h => (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl h)
    have hout3k : ∀ x, (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ x →
        x < (t.m.core.read .rsp - 24#64 - 8#64).toNat + 8 →
        ¬ (adderGccWorld b lb gate fs rel).Kept x := by
      rw [e32]; intro x h1 h2
      exact (hroom.2.2 x (by omega) (by omega)).2.2
    have k4 : Keeps (adderGccWorld b lb gate fs rel).Kept t2.m.memory
        (pushMem t2.m.memory (t.m.core.read .rsp - 24#64) (b + 4359#64)) := by
      apply pushMem_keeps; intro x hx'
      by_contra hc
      exact hout3k x (by omega) (by omega) hx'
    have hm4 := hm3.keep adderGcc_ok' hb (keeps_img rfl k4)
    have hx4 := hx3.keep (L := adderGccLayout) hb (by decide)
      (by simp [adderGccGotAt, adderGccGot, adderGccLayout]) (keeps_img rfl k4)
    refine must_listed (o := 98) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
    rw [pushWord_mem (by
      show t2.m.memory.Permitted .write (t2.m.core.read .rsp - 8#64).toNat 8
      rw [hsp2']; exact p3)]
    xstep [hsp2', addrK b (x := 4359) (y := 0x1080) (d := 0xffffff79#32) (by decide)]
    have hst0 := hx4.code (0x1080, [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x3e, 0x2f, 0x00, 0x00])
      (by simp [adderGccStubs])
    have hslot2 : loadN (pushMem t2.m.memory (t.m.core.read .rsp - 24#64) (b + 4359#64)) (b + 16328#64) 8 =
        some (lb + 1276912#64) := by
      simpa using hx4.slot (0x3fc8, lb + BitVec.ofNat 64 0x137bf0)
        (by simp [adderGccGotAt, adderGccGot])
    refine must_listed (o := 0) adderGcc_stubChk rfl hd2 (hin _ (by decide)) hst0 (by simp) ?_
    xstep []
    refine must_listed (o := 4) adderGcc_stubChk rfl hd2 (hin _ (by decide)) hst0 (by rw [ripadd]) ?_
    xstep [addrK b (x := 0x1080 + 4 + 6) (y := 0x3fc8) (d := 0x2f3e#32) (by decide)]
    erw [hslot2]
    simp only [WP_ok]
    -- `__printf_chk`
    have hro4 := hm4.rodata
    have hfmt2 : (pushMem t2.m.memory (t.m.core.read .rsp - 24#64) (b + 4359#64)).readBytes
        (b + 8202#64).toNat 4 = some (fmtDN ++ [0]) := by
      have := readBytes_sub' hro4 (k := 10) (j := 4) (by decide) (by decide)
      rw [show (b + 8202#64).toNat = (b + BitVec.ofNat 64 adderGccLayout.ro).toNat + 10 by
        rw [addr_toNat (by simp [adderGccLayout] at hb ⊢; omega),
          addr_toNat (by simp [adderGccLayout] at hb ⊢; omega)]; rfl, this]
      decide
    have hr3 := pushMem_read (v := b + 4359#64) r3 p3
    refine must_contract hd2 (show ¬ Img adderGccLayout b (lb + 1276912#64).toNat from hpf_out)
      (fun r => (extStep_fn (f := .named (Silmaril.Elf.Link.DynElf.nm "__printf_chk"))
        (by simpa [printfChkAt, adderGccWorld, crtWorld] using hpf_gate)
        (fun _ _ h => by simp [adderGccWorld, crtWorld] at h)
        (by simp [adderGccWorld, crtWorld]) r).trans (adderGcc_printfChk b lb gate fs rel _ r)) ⟨?_, ?_⟩ ?_
    · exact abiEntry_of' (v := b + 4359#64)
        (by show (t.m.core.read .rsp - 24#64 - 8#64).toNat % 16 = 8; rw [e32]; omega) (by exact hr3)
    · exact ⟨by decide, hfmt2⟩
    rintro t3 ⟨⟨hab3, hfs3, hk3, -, htls3, -⟩, hj3, hat3, hdn3, hin3, hout3⟩
    have hpc3 : t3.m.core.rip = b + 4359#64 := by
      rw [hab3.pc]; exact retOf_of' (by exact hr3)
    have hsp3 : t3.m.core.read .rsp = t.m.core.read .rsp - 24#64 := by
      rw [hab3.stack]; exact BitVec.sub_add_cancel _ _
    have hd3 : t3.g.done = none := hdn3
    have hk3' : Keeps (Img adderGccLayout b)
        (pushMem t2.m.memory (t.m.core.read .rsp - 24#64) (b + 4359#64)) t3.m.memory :=
      Keeps.mono hk3 (fun x hx' => ⟨Or.inl hx', id⟩)
    have hm5 := hm4.keep adderGcc_ok' hb hk3'
    have hfs3' : t3.m.core.fsBase = fs := by rw [hfs3]; exact hfs2'
    have hc5 : loadN t3.m.memory (fs + 40#64) 8 = some c := by
      rw [loadN_keeps htls3 (fun i hi => ⟨by
        show t2.m.core.fsBase.toNat + 0x28 ≤ (fs + 40#64).toNat + i ∧
          (fs + 40#64).toNat + i < t2.m.core.fsBase.toNat + 0x30
        rw [hfs2', hfs40]; omega, id⟩), hgk k4]
      exact hc3
    have hcp5 : loadN t3.m.memory (t.m.core.read .rsp - 24#64 + 8#64) 8 = some c := by
      rw [loadN_keeps hk3 (fun i hi => ⟨Or.inr (by
          show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32, e16]; omega), id⟩),
        loadN_keeps (P := fun a => (t.m.core.read .rsp).toNat - 16 ≤ a ∧ a < (t.m.core.read .rsp).toNat - 8)
          (pushMem_keeps (by intro x hx'; rw [e32]; omega)) (fun i hi => by rw [e16]; omega)]
      exact hcp3
    refine must_listed (o := 103) adderGcc_mainL rfl hd3 (by rw [hpc3]; exact hin _ (by decide))
      hm5.main (by rw [hpc3, ripadd]; rfl) ?_
    xstep [hpc3]
    refine must_listed (o := 105) adderGcc_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    refine must_listed (o := 56) adderGcc_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp3, hcp5]
    refine must_listed (o := 61) adderGcc_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep [memFs_addr, hfs3', hc5, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    refine must_listed (o := 70) adderGcc_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    split
    · rename_i heq; simp at heq
    · rename_i heq
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true] at heq
      exact absurd (sub_self c) (of_decide_eq_false heq)
    simp only [WP_ok]
    -- `add $0x18,%rsp; ret`, back at the gate
    have d0 := hret
    have d1 : m1.readBytes (t.m.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by
      rw [Memory.readBytes, hS1.readWith_disjoint _ _ _ (by
        simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]; rw [e16]; omega)]
      exact d0
    have d2 := slot_push (sp := t.m.core.read .rsp - 24#64) (v := b + 4300#64) d1
      (Or.inr (by rw [e32]; omega))
    have d3 := slot_keeps hkeep d2 (fun k hk => ⟨Or.inr (by
      show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32]; omega),
      hoex _ (by omega) (by omega)⟩)
    have d4 := slot_push (sp := t.m.core.read .rsp - 24#64) (v := b + 4359#64) d3
      (Or.inr (by rw [e32]; omega))
    have d5 := slot_keeps hk3 d4 (fun k hk => ⟨Or.inr (by
      show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32]; omega), id⟩)
    refine must_listed (o := 72) adderGcc_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp3, Silmaril.X86.Ext.AluOp.resultN, BitVec.sub_add_cancel]
    refine must_listed (o := 76) adderGcc_mainL rfl hd3 (hin _ (by decide)) hm5.main
      (by rw [ripadd]; rfl) ?_
    have key : ∀ x : Word, x = t.m.core.read .rsp → t3.m.memory.readBytes x.toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by rintro x rfl; exact d5
    xstep [Silmaril.X86.popWord]
    rw [key _ (by exact BitVec.sub_add_cancel _ _), Option.bind_some,
      Silmaril.X86.wordOfBytes?_encodeWords, Option.bind_some]
    refine kk _ rfl (by rw [hj3]; simp [hg2]) (by rw [hat3]; simp [hg2]) hd3 hm5 ?_
    simp only [adderPost, hsc]
    refine ⟨by simp [low32], by rw [hin3]; simp [hg2], ?_⟩
    have hv : low32 (BitVec.setWidth 64 (BitVec.ofInt 32 b' + BitVec.ofInt 32 a)) =
        BitVec.ofInt 32 a + BitVec.ofInt 32 b' := by simp [low32, BitVec.add_comm]
    rcases hout3 with h | ⟨hr, p, hp, h⟩
    · left; rw [h, ← hv, hg2]; rfl
    · right; refine ⟨hr, p, ?_, by rw [h, hg2]⟩
      rw [← hv]; exact hp
  | fail =>
    rw [hsc] at hpost'
    obtain ⟨⟨hab, hfs2, hkeep, hex, htls, -⟩, hrax, hj2, hat2, hdn2, hout2⟩ := hpost'
    have hpc : t2.m.core.rip = b + 4300#64 := by
      rw [hab.pc]; exact retOf_of' (by exact hr2)
    have hsp2' : t2.m.core.read .rsp = t.m.core.read .rsp - 24#64 := by
      rw [hab.stack]; exact BitVec.sub_add_cancel _ _
    have hfs2' : t2.m.core.fsBase = fs := by rw [hfs2]; exact hfs
    have hd2 : t2.g.done = none := hdn2
    have hk2 : Keeps (Img adderGccLayout b) (pushMem m1 (t.m.core.read .rsp - 24#64) (b + 4300#64))
        t2.m.memory :=
      Keeps.mono hkeep (fun x hx' => ⟨Or.inl hx', fun h => by
        rcases h with h | h <;> simp only [In4] at h <;> (try rw [e24] at h) <;> (try rw [e20] at h) <;>
          exact (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl hx')⟩)
    have hm3 := hm2.keep adderGcc_ok' hb hk2
    have hc3 : loadN t2.m.memory (fs + 40#64) 8 = some c := by
      rw [loadN_keeps htls (fun i hi => ⟨by
        show t.m.core.fsBase.toNat + 0x28 ≤ (fs + 40#64).toNat + i ∧
          (fs + 40#64).toNat + i < t.m.core.fsBase.toNat + 0x30
        rw [hfs, hfs40]; omega, fun h => by
          have hg : Guard fs ((fs + 40#64).toNat + i) := by rw [hfs40]; simp only [Guard]; omega
          rcases h with h | h <;> simp only [In4] at h <;> (try rw [e24] at h) <;>
            (try rw [e20] at h) <;>
            exact (hroom.2.2 _ (by omega) (by omega)).2.2 (Or.inr (Or.inr hg))⟩)]
      exact hc2
    have hcp3 : loadN t2.m.memory (t.m.core.read .rsp - 24#64 + 8#64) 8 = some c := by
      rw [loadN_keeps hkeep (fun i hi => ⟨Or.inr (by
        show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32, e16]; omega),
        hoex _ (by rw [e16]; omega) (by rw [e16]; omega)⟩)]
      exact hcp2
    refine must_listed (o := 44) adderGcc_mainL rfl hd2 (by rw [hpc]; exact hin _ (by decide))
      hm3.main (by rw [hpc, ripadd]; rfl) ?_
    xstep [hpc]
    refine must_listed (o := 46) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep []
    refine must_listed (o := 51) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    refine must_listed (o := 54) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    split
    · rename_i heq; simp at heq
    · rename_i heq
      simp only [Option.some.injEq] at heq
      exact absurd (sub_eq_zero.mp (of_decide_eq_true heq)) hrax
    simp only [WP_ok]
    refine must_listed (o := 56) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp2', hcp3]
    refine must_listed (o := 61) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [memFs_addr, hfs2', hc3, Silmaril.X86.Ext.aluStepR, Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    refine must_listed (o := 70) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.AluOp.flagsN, Silmaril.X86.Ext.isZeroN, Silmaril.X86.Ext.subFlagsN, Option.map_some, Silmaril.X86.Ext.Narrow.bits, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.kNot]
    split
    · rename_i heq; simp at heq
    · rename_i heq
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true] at heq
      exact absurd (sub_self c) (of_decide_eq_false heq)
    simp only [WP_ok]
    have d1 : m1.readBytes (t.m.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by
      rw [Memory.readBytes, hS1.readWith_disjoint _ _ _ (by
        simp only [Silmaril.X86.Ext.leBytes, List.length_ofFn]; rw [e16]; omega)]
      exact hret
    have d2 := slot_push (sp := t.m.core.read .rsp - 24#64) (v := b + 4300#64) d1
      (Or.inr (by rw [e32]; omega))
    have d3 := slot_keeps hkeep d2 (fun k hk => ⟨Or.inr (by
      show (t.m.core.read .rsp - 24#64 - 8#64).toNat ≤ _; rw [e32]; omega),
      hoex _ (by omega) (by omega)⟩)
    refine must_listed (o := 72) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    xstep [hsp2', Silmaril.X86.Ext.AluOp.resultN, BitVec.sub_add_cancel]
    refine must_listed (o := 76) adderGcc_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    have key : ∀ x : Word, x = t.m.core.read .rsp → t2.m.memory.readBytes x.toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by rintro x rfl; exact d3
    xstep [Silmaril.X86.popWord]
    rw [key _ (by exact BitVec.sub_add_cancel _ _), Option.bind_some,
      Silmaril.X86.wordOfBytes?_encodeWords, Option.bind_some]
    refine kk _ rfl hj2 hat2 hd2 hm3 ?_
    simp only [adderPost, hsc]
    exact ⟨by simp [low32], hout2⟩

/-- Where the loader put things, for `adderGcc`. -/
structure AdderGccPlaced (b lb gate : Word) : Prop where
  base : Placed adderGccLayout b lb gate 0x2a200 0x472c0
  sc_out : ¬ Img adderGccLayout b (scanfAt lb).toNat
  pf_out : ¬ Img adderGccLayout b (printfChkAt lb).toNat
  sc_gate : scanfAt lb ≠ gate
  pf_gate : printfChkAt lb ≠ gate

theorem adderGcc_env {b lb gate fs : Word} {rel : Bool} (P : AdderGccPlaced b lb gate) :
    CrtEnv adderGccLayout (adderGccWorld b lb gate fs rel) b (lsmAt lb) (cxaAt lb) where
  hW := rfl
  hb := P.base.hb
  gate_out := P.base.gate_out
  cxa_out := P.base.cxa_out
  cxa_gate := P.base.cxa_gate
  cxa_res := fun _ _ h => by simp [adderGccWorld, crtWorld] at h
  cxa_fn := by simp [adderGccWorld, crtWorld]
  cxa_ne := P.base.cxa_ne
  lsm_out := P.base.lsm_out
  lsm_gate := P.base.lsm_gate
  lsm_res := fun _ _ h => by simp [adderGccWorld, crtWorld] at h
  lsm_fn := by simp [adderGccWorld, crtWorld]

/-- **The thread pointer at the entry**: `fsBase` is `fs`, and the guard word `%fs:0x28` is
readable (set up by `ld.so`, before `_start`). -/
structure TlsAt (fs : Word) (s : PState) : Prop where
  base : s.m.core.fsBase = fs
  wrap : fs.toNat + 0x30 ≤ 2 ^ 64
  guard : ∃ c : Word, loadN s.m.memory (fs + 40#64) 8 = some c

/-- **The adder (gcc), end to end**: under the loader relation, from every documented initial
state with the guard set up, whose `stdin` does not overflow `int` in `scanf`, every run ends
as `adderPost` says: in particular the stack protector's check passes (`__stack_chk_fail`
is never called). -/
theorem adderGcc_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate fs : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderGccFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderGccPlaced b lb gate)
    (hs : AtEntry adderGccLayout (adderGccWorld b lb gate fs rel) b s) (ht : TlsAt fs s)
    (hin : scanDD s.g.inp ≠ .ub) :
    MustQ (adderGccWorld b lb gate fs rel) (Ends s.g (adderPost rel) rel) s := by
  have F := Layout.facts adderGcc_ok
  obtain ⟨argc, hargc⟩ := hs.argc
  have hD := adderGcc_slots hc hl
  have hfs40 : (fs + 40#64).toNat = fs.toNat + 40 := add_toNat (k := 40) (by have := ht.wrap; omega)
  refine crt_run F (adderGcc_env P) rfl rfl (X := GccX b lb fs)
    (fun f m m' hk hx => ⟨hx.1.keep (L := adderGccLayout) P.base.hb (by decide)
      (by simp [adderGccGotAt, adderGccGot, adderGccLayout]) (keeps_img rfl hk), hx.2.1, hx.2.2.1, by
        obtain ⟨c, hc'⟩ := hx.2.2.2
        refine ⟨c, ?_⟩
        rw [loadN_keeps hk (fun i hi => Or.inr (Or.inr (by
          show Guard fs ((fs + 40#64).toNat + i); rw [hfs40]; simp only [Guard]; omega)))]
        exact hc'⟩)
    (adderGcc_main P.base.hb P.sc_out P.pf_out P.sc_gate P.pf_gate) hs.done
    ⟨extra_of_loaded adderGcc_info hD adderGcc_extra hload, ht.base, ht.wrap, ht.guard⟩ hs.atexit
    (crtMem_of_loaded adderGcc_info hD adderGcc_img hload) hs.rip hs.al hs.room hargc hin

/-- **The adder (gcc) on the text `"a b\n"`**: exit status `0`, `stdout` = the decimal text of
`a + b` and a newline (a prefix of it if writes to fd 1 may fail). -/
theorem adderGcc_sum {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate fs : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderGccFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderGccPlaced b lb gate)
    (hs : AtEntry adderGccLayout (adderGccWorld b lb gate fs rel) b s) (ht : TlsAt fs s)
    {x y : Int} (hx : inInt32 x = true) (hy : inInt32 y = true) (hxy : inInt32 (x + y) = true)
    (hin : s.g.inp = decStr x ++ [32#8] ++ decStr y ++ [10#8]) (hout : s.g.out = []) :
    MustQ (adderGccWorld b lb gate fs rel)
      (fun u => ∃ w, u.g.done = some (0, w) ∧ w <+: decStr (x + y) ++ [10#8] ∧
        (rel = true → w = decStr (x + y) ++ [10#8])) s := by
  have hsc := scanDD_text hx hy
  rw [← hin] at hsc
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderGcc_exits hc hl hload P hs ht (by rw [hsc]; simp))
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

/-- **The adder (gcc) on input `scanf` cannot convert**: exit status `1`, nothing written. -/
theorem adderGcc_bad {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate fs : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderGccFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderGccPlaced b lb gate)
    (hs : AtEntry adderGccLayout (adderGccWorld b lb gate fs rel) b s) (ht : TlsAt fs s)
    (hin : scanDD s.g.inp = .fail) (hout : s.g.out = []) :
    MustQ (adderGccWorld b lb gate fs rel) (fun u => u.g.done = some (1, [])) s := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderGcc_exits hc hl hload P hs ht (by rw [hin]; simp))
  rintro u ⟨g', e, w, hp, hd, hw, -⟩
  simp only [adderPost, hin] at hp
  obtain ⟨rfl, ho⟩ := hp
  rw [ho, hout, List.prefix_nil] at hw
  rw [hd, hw]; rfl

end Silmaril.Elf.Link.Dyn.Small
