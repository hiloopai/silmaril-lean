-- variant-of: glibc.adder.clang | style: small-direct | see-also: Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangLazyMain
module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClang
public import Silmaril.Elf.Link.Dyn.Stdio.Thms

/-! # The adder (clang): `main` meets `MainOk` -/

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

theorem le32_val (x : Int) :
    (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue (le32 x))).setWidth 32 = BitVec.ofInt 32 x := by
  apply BitVec.eq_of_toNat_eq
  have hw := (BitVec.ofInt 32 x).isLt
  simp only [le32, Silmaril.X86.Ext.leValue, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  generalize (BitVec.ofInt 32 x).toNat = w at hw ⊢
  omega

theorem le32_val' (x : Int) :
    BitVec.ofNat 32 (Silmaril.X86.Ext.leValue (le32 x)) = BitVec.ofInt 32 x := by
  have := le32_val x
  rw [BitVec.setWidth_ofNat_of_le (by decide)] at this
  exact this

theorem readBytes_of_backed {m : Memory} {a n : Nat} (hw : a + n ≤ 2 ^ 64) (ha : a < 2 ^ 64)
    (h : ∀ k < n, m.permits .read (a + k) = true ∧ (m.bytes.get? (a + k)).isSome) :
    ∃ l, l.length = n ∧ m.readBytes a n = some l := by
  refine ⟨(List.range n).map fun k => (m.bytes.get? (a + k)).getD 0, by simp, ?_⟩
  have := readWith_of_points (mem := m) (acc := .read)
    (l := (List.range n).map fun k => (m.bytes.get? (a + k)).getD 0) (a := a) (by simpa using hw) ha
    (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      refine ⟨(h k hk).1, ?_⟩
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (h k hk).2
      simp only [List.getElem_map, List.getElem_range]
      rw [hx]; rfl)
  simpa [Memory.readBytes] using this

theorem wordOfBytes?_of_length {l : List Byte} (h : l.length = 8) :
    ∃ w, Silmaril.X86.wordOfBytes? l = some w :=
  match l, h with
  | [_, _, _, _, _, _, _, _], _ => ⟨_, rfl⟩

theorem loadN_of_readBytes {m : Memory} {a : Word} {k : Nat} {l : List Byte}
    (h : m.readBytes a.toNat k = some l) :
    loadN m a k = some (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue l)) := by
  simp [loadN, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`main` of `adderClang`.** -/
theorem adderClang_main {b lb gate : Word} {rel : Bool}
    (hb : b.toNat + adderClangLayout.size < 2 ^ 64)
    (hsc_out : ¬ Img adderClangLayout b (scanfAt lb).toNat)
    (hpf_out : ¬ Img adderClangLayout b (printfAt lb).toNat)
    (hsc_gate : scanfAt lb ≠ gate) (hpf_gate : printfAt lb ≠ gate) :
    MainOk (adderClangWorld b lb gate rel) adderClangLayout b (lsmAt lb) (cxaAt lb)
      (fun _ => Extra b adderClangStubs (adderClangGotAt lb)) (fun g => scanDD g.inp ≠ .ub)
      (adderPost rel) := by
  intro Q t hd hrip hal hret hroom hm hx hpre kk
  have hin : ∀ n, n < 0x4028 → (adderClangWorld b lb gate rel).InImage (b + BitVec.ofNat 64 n).toNat :=
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
  have hm1 := hm.keep adderClang_ok' hb (keeps_push (L := adderClangLayout) (W := adderClangWorld b lb gate rel)
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
  have k1 := keeps_push (L := adderClangLayout) (W := adderClangWorld b lb gate rel) rfl hroom
    (v := t.m.core.read .rax) (sp' := t.m.core.read .rsp) (by omega) (by omega)
  have k2 := keeps_push (L := adderClangLayout) (W := adderClangWorld b lb gate rel) rfl hroom.pushMem
    (m := pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
    (v := b + 4455#64) (sp' := t.m.core.read .rsp - 8#64) (by omega) (by omega)
  have hm2 := hm1.keep adderClang_ok' hb k2
  have hx2 := hx.keep (L := adderClangLayout) hb (by decide)
    (by simp [adderClangGotAt, adderClangGot, adderClangLayout]) (k1.trans k2)
  refine must_listed (o := 18) adderClang_mainL rfl hd (hin _ (by decide)) hm1.main (by rw [ripadd]; rfl) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep [addrK b (x := 4455) (y := 0x1040) (d := 0xfffffed9#32) (by decide)]
  -- the `.plt` stub
  have hst1 := hx2.code (0x1040, [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00]) (by simp [adderClangStubs])
  have hslot : loadN (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)) (b + 16392#64) 8 = some (lb + 392720#64) := by
    simpa using hx2.slot (0x4008, lb + BitVec.ofNat 64 0x5fe10)
      (by simp [adderClangGotAt, adderClangGot])
  refine must_listed (o := 0) adderClang_stub1 rfl hd (hin _ (by decide)) hst1 (by simp) ?_
  xstep [addrK b (x := 0x1040 + 6) (y := 0x4008) (d := 0x2fc2#32) (by decide), hslot]
  -- `__isoc99_scanf`
  have hro := hm2.rodata
  have hfmt : (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)).readBytes (b + 8196#64).toNat 6 =
      some (fmtDD ++ [0]) := by
    have := readBytes_sub' hro (k := 4) (j := 6) (by decide) (by decide)
    rw [show (b + 8196#64).toNat = (b + BitVec.ofNat 64 adderClangLayout.ro).toNat + 4 by
      rw [addr_toNat (by simp [adderClangLayout] at hb ⊢; omega),
        addr_toNat (by simp [adderClangLayout] at hb ⊢; omega)]; rfl, this]
    decide
  have hroom2 : StackRoom (adderClangWorld b lb gate rel)
      (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 4455#64)) (t.m.core.read .rsp) := hroom.pushMem.pushMem
  refine must_contract hd (show ¬ Img adderClangLayout b (lb + 392720#64).toNat from hsc_out)
    (fun r => (extStep_fn (f := .named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf"))
      (by simpa [scanfAt, adderClangWorld, crtWorld] using hsc_gate)
      (fun _ _ h => by simp [adderClangWorld, crtWorld] at h)
      (by simp [adderClangWorld, crtWorld]) r).trans (adderClang_scanf b lb gate rel _ r)) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · exact abiEntry_of' (v := b + 4455#64) (by simp [e16]; omega) (by simpa using pushMem_read r2 p2)
  · exact ⟨by decide, hfmt⟩
  · show (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)).Permitted .write
      (t.m.core.read .rsp - 8#64 + 4#64).toNat 4
    rw [eR4]; exact perm_room hroom2 (Or.inr rfl) (by omega) (by omega)
  · show (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)).Permitted .write
      (t.m.core.read .rsp - 8#64).toNat 4
    rw [e8]; exact perm_room hroom2 (Or.inr rfl) (by omega) (by omega)
  · show (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)).Permitted .read
      (t.m.core.read .rsp - 8#64 + 4#64).toNat 4
    rw [eR4]; exact perm_room hroom2 (Or.inl rfl) (by omega) (by omega)
  · show (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 4455#64)).Permitted .read
      (t.m.core.read .rsp - 8#64).toNat 4
    rw [e8]; exact perm_room hroom2 (Or.inl rfl) (by omega) (by omega)
  · show (t.m.core.read .rsp - 8#64 + 4#64).toNat + 4 ≤ (t.m.core.read .rsp - 8#64).toNat ∨
      (t.m.core.read .rsp - 8#64).toNat + 4 ≤ (t.m.core.read .rsp - 8#64 + 4#64).toNat
    rw [eR4, e8]; omega
  intro t2 hpost
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
    obtain ⟨⟨hab, hfs, hkeep, hex, htls, -⟩, hrax, hg2, ha, hb'⟩ := hpost'
    have hpc : t2.m.core.rip = b + 4455#64 := by
      rw [hab.pc]; exact retOf_of' (by simpa using hr2)
    have hsp2' : t2.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
      rw [hab.stack]; simp
    have hd2 : t2.g.done = none := by rw [hg2]; exact hd
    have hk2 : Keeps (Img adderClangLayout b) (pushMem (pushMem t.m.memory (t.m.core.read .rsp)
        (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 4455#64)) t2.m.memory :=
      Keeps.mono hkeep (fun x hx' => ⟨Or.inl hx', fun h => by
        rcases h with h | h <;> (have := (hroom.2.2 x (by simp [In4] at h; omega)
          (by simp [In4] at h; omega)).2.2; exact this (Or.inl hx'))⟩)
    have hm3 := hm2.keep adderClang_ok' hb hk2
    have hx3 := hx2.keep (L := adderClangLayout) hb (by decide)
      (by simp [adderClangGotAt, adderClangGot, adderClangLayout]) hk2
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
    have hpk : ∀ k < 8, ∀ acc, t2.m.memory.permits acc ((t.m.core.read .rsp).toNat - 16 + k) =
        t.m.memory.permits acc ((t.m.core.read .rsp).toNat - 16 + k) := by
      intro k hk acc
      have := hkeep ((t.m.core.read .rsp).toNat - 16 + k) ⟨Or.inr (by simp; omega),
        fun h => by rcases h with h | h <;> simp only [In4] at h <;> (try rw [eR4] at h) <;> (try rw [e8] at h) <;> omega⟩
      exact (this.2 acc).trans rfl
    have p3 : t2.m.memory.Permitted .write (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 := by
      rw [e16]
      exact permitted_congr (fun k hk => hpk k hk _)
        (perm_room (acc := .write) hroom (Or.inr rfl) (by omega) (by omega))
    have r3 : t2.m.memory.Permitted .read (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 := by
      rw [e16]
      exact permitted_congr (fun k hk => hpk k hk _)
        (perm_room (acc := .read) hroom (Or.inl rfl) (by omega) (by omega))
    have hout3 : ∀ x, (t.m.core.read .rsp - 8#64 - 8#64).toNat ≤ x →
        x < (t.m.core.read .rsp - 8#64 - 8#64).toNat + 8 → ¬ Img adderClangLayout b x := by
      rw [e16]; intro x h1 h2
      exact fun h => (hroom.2.2 x (by omega) (by omega)).2.2 (Or.inl h)
    have k4 := keeps_push_of (L := adderClangLayout) (b := b) (m := t2.m.memory)
      (sp := t.m.core.read .rsp - 8#64) (v := b + 4488#64) (by simpa using hout3)
    have hm4 := hm3.keep adderClang_ok' hb k4
    have hx4 := hx3.keep (L := adderClangLayout) hb (by decide)
      (by simp [adderClangGotAt, adderClangGot, adderClangLayout]) k4
    refine must_listed (o := 51) adderClang_mainL rfl hd2 (hin _ (by decide)) hm3.main
      (by rw [ripadd]; rfl) ?_
    simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
    rw [pushWord_mem (by simpa [hsp2'] using p3)]
    xstep [hsp2', addrK b (x := 4488) (y := 0x1030) (d := 0xfffffea8#32) (by decide)]
    have hst0 := hx4.code (0x1030, [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00]) (by simp [adderClangStubs])
    have hslot2 : loadN (pushMem t2.m.memory (t.m.core.read .rsp - 8#64) (b + 4488#64)) (b + 16384#64) 8 =
        some (lb + 393472#64) := by
      simpa using hx4.slot (0x4000, lb + BitVec.ofNat 64 0x60100)
        (by simp [adderClangGotAt, adderClangGot])
    refine must_listed (o := 0) adderClang_stub0 rfl hd2 (hin _ (by decide)) hst0 (by simp) ?_
    xstep [addrK b (x := 0x1030 + 6) (y := 0x4000) (d := 0x2fca#32) (by decide), hslot2]
    -- `printf`
    have hro4 := hm4.rodata
    have hfmt2 : (pushMem t2.m.memory (t.m.core.read .rsp - 8#64) (b + 4488#64)).readBytes
        (b + 8202#64).toNat 4 = some (fmtDN ++ [0]) := by
      have := readBytes_sub' hro4 (k := 10) (j := 4) (by decide) (by decide)
      rw [show (b + 8202#64).toNat = (b + BitVec.ofNat 64 adderClangLayout.ro).toNat + 10 by
        rw [addr_toNat (by simp [adderClangLayout] at hb ⊢; omega),
          addr_toNat (by simp [adderClangLayout] at hb ⊢; omega)]; rfl, this]
      decide
    have hr3 := pushMem_read (v := b + 4488#64) r3 p3
    refine must_contract hd2 (show ¬ Img adderClangLayout b (lb + 393472#64).toNat from hpf_out)
      (fun r => (extStep_fn (f := .named (Silmaril.Elf.Link.DynElf.nm "printf"))
        (by simpa [printfAt, adderClangWorld, crtWorld] using hpf_gate)
        (fun _ _ h => by simp [adderClangWorld, crtWorld] at h)
        (by simp [adderClangWorld, crtWorld]) r).trans (adderClang_printf b lb gate rel _ r)) ⟨?_, ?_⟩ ?_
    · exact abiEntry_of' (v := b + 4488#64) (by simp [e16]; omega) (by simpa [hsp2'] using hr3)
    · exact ⟨by decide, hfmt2⟩
    rintro t3 ⟨⟨hab3, -, hk3, -, -, -⟩, hj3, hat3, hdn3, hin3, hout3⟩
    have hpc3 : t3.m.core.rip = b + 4488#64 := by
      rw [hab3.pc]; exact retOf_of' (by simpa [hsp2'] using hr3)
    have hsp3 : t3.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
      rw [hab3.stack]; simp
    have hd3 : t3.g.done = none := hdn3
    have hk3' : Keeps (Img adderClangLayout b)
        (pushMem t2.m.memory (t.m.core.read .rsp - 8#64) (b + 4488#64)) t3.m.memory :=
      Keeps.mono hk3 (fun x hx' => ⟨Or.inl hx', id⟩)
    have hm5 := hm4.keep adderClang_ok' hb hk3'
    -- the slots `pop` and `ret` read
    have hb'' := hb'; rw [e8] at hb''
    have ha' := ha; rw [eR4] at ha'
    have c8 := Memory.readBytes_append hb''
      (by rw [show (t.m.core.read .rsp).toNat - 8 + 4 = (t.m.core.read .rsp).toNat - 4 by omega]; exact ha')
    have c8m4 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4488#64) c8
      (Or.inr (by rw [e16]; omega))
    have c8t3 := slot_keeps hk3 c8m4 (fun k hk => ⟨Or.inr (by simp; omega), id⟩)
    have d1 := slot_push (sp := t.m.core.read .rsp) (v := t.m.core.read .rax) hret
      (Or.inr (by rw [e8]; omega))
    have d2 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4455#64) d1
      (Or.inr (by rw [e16]; omega))
    have d3 := slot_keeps hkeep d2 (fun k hk => ⟨Or.inr (by simp; omega),
      fun h => by rcases h with h | h <;> simp only [In4] at h <;> (try rw [eR4] at h) <;>
        (try rw [e8] at h) <;> omega⟩)
    have d4 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4488#64) d3
      (Or.inr (by rw [e16]; omega))
    have d5 := slot_keeps hk3 d4 (fun k hk => ⟨Or.inr (by simp; omega), id⟩)
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
      rw [hab.pc]; exact retOf_of' (by simpa using hr2)
    have hsp2' : t2.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
      rw [hab.stack]; simp
    have hd2 : t2.g.done = none := hdn2
    have hk2 : Keeps (Img adderClangLayout b) (pushMem (pushMem t.m.memory (t.m.core.read .rsp)
        (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 4455#64)) t2.m.memory :=
      Keeps.mono hkeep (fun x hx' => ⟨Or.inl hx', fun h => by
        rcases h with h | h <;> (have := (hroom.2.2 x (by simp [In4] at h; omega)
          (by simp [In4] at h; omega)).2.2; exact this (Or.inl hx'))⟩)
    have hm3 := hm2.keep adderClang_ok' hb hk2
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
        exact (hroom.2.2 _ (by omega) (by omega)).1)
    have d1 := slot_push (sp := t.m.core.read .rsp) (v := t.m.core.read .rax) hret
      (Or.inr (by rw [e8]; omega))
    have d2 := slot_push (sp := t.m.core.read .rsp - 8#64) (v := b + 4455#64) d1
      (Or.inr (by rw [e16]; omega))
    have d3 := slot_keeps hkeep d2 (fun k hk => ⟨Or.inr (by simp; omega),
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

/-- **`Task.adderClangMain` holds.** -/
theorem adderClangMain_holds : Task.adderClangMain :=
  fun _ _ _ _ hb h1 h2 h3 h4 => adderClang_main hb h1 h2 h3 h4

/-- **The adder (clang), end to end**: under the loader relation, from every documented initial
state whose `stdin` does not overflow `int` in `scanf`, every run ends as `adderPost` says. -/
theorem adderClang_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderPlaced adderClangLayout b lb gate)
    (hs : AtEntry adderClangLayout (adderClangWorld b lb gate rel) b s)
    (hin : scanDD s.g.inp ≠ .ub) :
    MustQ (adderClangWorld b lb gate rel) (Ends s.g (adderPost rel) rel) s :=
  adderClang_run adderClangMain_holds hc hl hload P hs hin

theorem int32_add {a b : Int} (h : inInt32 (a + b) = true) (ha : inInt32 a = true)
    (hb : inInt32 b = true) : (BitVec.ofInt 32 a + BitVec.ofInt 32 b).toInt = a + b := by
  simp only [inInt32, Bool.and_eq_true, decide_eq_true_eq] at h ha hb
  rw [BitVec.toInt_add, BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  have h1 : a.bmod (2 ^ 32) = a := Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have h2 : b.bmod (2 ^ 32) = b := Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  rw [h1, h2]
  exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)

/-- **The adder (clang) on the text `"a b\n"`**: with `a`, `b` and `a + b` in `int` and an
empty `stdout`, every run ends with exit status `0` and `stdout` = the decimal text of
`a + b` and a newline (a prefix of it if writes to fd 1 may fail). -/
theorem adderClang_sum {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderPlaced adderClangLayout b lb gate)
    (hs : AtEntry adderClangLayout (adderClangWorld b lb gate rel) b s)
    {x y : Int} (hx : inInt32 x = true) (hy : inInt32 y = true) (hxy : inInt32 (x + y) = true)
    (hin : s.g.inp = decStr x ++ [32#8] ++ decStr y ++ [10#8]) (hout : s.g.out = []) :
    MustQ (adderClangWorld b lb gate rel)
      (fun u => ∃ w, u.g.done = some (0, w) ∧ w <+: decStr (x + y) ++ [10#8] ∧
        (rel = true → w = decStr (x + y) ++ [10#8])) s := by
  have hsc := scanDD_text hx hy
  rw [← hin] at hsc
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderClang_exits hc hl hload P hs (by rw [hsc]; simp))
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

/-- **The adder (clang) on input `scanf` cannot convert**: exit status `1`, nothing written. -/
theorem adderClang_bad {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderPlaced adderClangLayout b lb gate)
    (hs : AtEntry adderClangLayout (adderClangWorld b lb gate rel) b s)
    (hin : scanDD s.g.inp = .fail) (hout : s.g.out = []) :
    MustQ (adderClangWorld b lb gate rel) (fun u => u.g.done = some (1, [])) s := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderClang_exits hc hl hload P hs (by rw [hin]; simp))
  rintro u ⟨g', e, w, hp, hd, hw, -⟩
  simp only [adderPost, hin] at hp
  obtain ⟨rfl, ho⟩ := hp
  rw [ho, hout, List.prefix_nil] at hw
  rw [hd, hw]; rfl

/-- For example, the input `"x\n"`. -/
example : scanDD [0x78#8, 10#8] = .fail := by rfl

end Silmaril.Elf.Link.Dyn.Small
