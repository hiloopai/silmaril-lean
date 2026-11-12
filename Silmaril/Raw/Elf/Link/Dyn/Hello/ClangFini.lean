module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.ClangInit
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccFini

/-! # hello-clang: `__do_global_dtors_aux` -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn.Proc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`__do_global_dtors_aux`** (`0x1120`): `completed.0` is 0, `__cxa_finalize` is bound
(non-null), so it calls `__cxa_finalize(__dso_handle)`, then `deregister_tm_clones` (which
returns at once), sets `completed.0` and returns. -/
theorem clang_dtors {b lb gate res ps : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res) {Q : PState → Prop}
    {t : PState} (hc : CCb (clangWorld b lb gate res lazy rel) b lb ps t (b + 0x10f0#64)) (hbss : ClangBss b t.m.memory)
    (hat : t.g.atexit = [])
    (k : ∀ u : PState, u.m.core.rip = gate → u.g = t.g → ClangMem b lb ps u.m.memory →
      MustQ (clangWorld b lb gate res lazy rel) Q u) :
    MustQ (clangWorld b lb gate res lazy rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4020 → (clangWorld b lb gate res lazy rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => clang_in E.hb hn
  have hd := hc.done
  have hroom := hc.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (t.m.core.read .rsp - 8#64).toNat = (t.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (t.m.core.read .rsp - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  -- push rbp
  have p1 : t.m.memory.Permitted .write (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have q1 : t.m.memory.Permitted .read (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inl rfl) (by omega) (by omega)
  have hk1 : Keeps (ClangImg b) t.m.memory
      (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp)) :=
    ckeeps_push rfl hroom (by omega) (by omega)
  have hm1 := hc.mem.keep E.hb (keepsI' hk1)
  -- call __cxa_finalize@plt
  have p2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp)).Permitted .write
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have q2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp)).Permitted .read
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inl rfl) (by omega) (by omega)
  have hk2 : Keeps (ClangImg b) t.m.memory (pushMem (pushMem t.m.memory (t.m.core.read .rsp)
      (t.m.core.read .rbp)) (t.m.core.read .rsp - 8#64) (b + 0x1117#64)) :=
    hk1.trans (ckeeps_push rfl hroom.pushMem (by omega) (by omega))
  have hm2 := hc.mem.keep E.hb (keepsI' hk2)
  have hret2 := pushMem_read (v := b + 0x1117#64) q2 p2
  have hz1 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN (BitVec.setWidth 8 (0#64)) 0#8)
      Silmaril.X86.Ext.Cond.ne = some false := by decide
  have hz2 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp
      (lb + 0x472c0#64) 0#64) Silmaril.X86.Ext.Cond.e = some false := by
    show Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN _ _) _ = _
    rw [eval_e_sub]; simpa using E.cxa_ne
  refine must_listed (o := 0xf0) clang_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 0xf4) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hbss.val, Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits]
  refine must_listed (o := 0xfb) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [hz1]
  refine must_listed (o := 0xfd) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 0xfe) clang_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  xstep [hm1.cxa]
  refine must_listed (o := 0x106) clang_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x109) clang_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  xstep [hz2]
  refine must_listed (o := 0x10b) clang_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  xstep [hm1.dso]
  refine must_listed (o := 0x112) clang_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 0x40) clang_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep [hm2.cxa]
  have hsp' : (t.m.core.read .rsp - 8#64 - 8#64).toNat % 16 = 8 := by rw [e16]; have := hc.al; omega
  refine must_fn' hd (by simpa [clangWorld_inImage] using E.cxa_out)
    (by simpa [clangWorld] using (Ne.symm E.gate_cxa))
    (clang_res_ne E.res_cxa) (f := .cxaFinalize) (by simp [clangWorld]) (fun r => Iff.rfl)
    ⟨abiEntry_of (v := b + 0x1117#64) (by simpa using hsp') (by simpa using hret2), by simpa using hat⟩ ?_
  rintro u ⟨⟨habi, hkeep⟩, hg, -⟩
  simp only at habi hkeep hg
  -- the memories: m2 (before `__cxa_finalize`), u, m3 (after `call deregister_tm_clones`)
  have hrsp_c : (t.m.core.read .rsp - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := e16
  have hrip_u : u.m.core.rip = b + 0x1117#64 := by
    rw [habi.pc]; exact retOf_of (by simpa using hret2)
  have hrsp_u : u.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
    rw [habi.stack]; simp
  have hkU : Keeps (fun a => (clangWorld b lb gate res lazy rel).Kept a ∨
      (t.m.core.read .rsp - 8#64 - 8#64).toNat ≤ a)
      (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rbp))
        (t.m.core.read .rsp - 8#64) (b + 0x1117#64)) u.m.memory := by simpa using hkeep
  have hkUi : Keeps (ClangImg b) t.m.memory u.m.memory :=
    hk2.trans (hkU.mono (fun a ha => Or.inl (Or.inl (by simpa [clangWorld_inImage] using ha))))
  have hmu := hc.mem.keep E.hb (keepsI' hkUi)
  -- permissions on the stack and on `completed.0` in `u`
  have pU : ∀ acc, acc = Access.read ∨ acc = Access.write →
      u.m.memory.Permitted acc (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 := by
    intro acc hacc
    rw [hkU.permitted (fun k hk => Or.inr (by omega))]
    exact perm_room hroom.pushMem.pushMem hacc (by omega) (by omega)
  have hk3 : Keeps (ClangImg b) u.m.memory (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64)) := by
    apply pushMem_keeps
    intro x hx
    have := (hroom.2.2 x)
    by_contra hc'
    have h' := this (by rw [e16] at hc'; omega) (by rw [e16] at hc'; omega)
    exact h'.2.2 (Or.inl (by simpa [clangWorld_inImage] using hx))
  have hm3 := hmu.keep E.hb (keepsI' hk3)
  have hret3 := pushMem_read (m := u.m.memory) (sp := t.m.core.read .rsp - 8#64) (v := b + 0x111c#64)
    (pU _ (Or.inl rfl)) (pU _ (Or.inr rfl))
  have hz3 : Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.AluOp.flagsN Silmaril.X86.AluOp.cmp
      (b + 16408#64) (b + 16408#64)) Silmaril.X86.Ext.Cond.e = some true := by
    show Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.subFlagsN _ _) _ = _
    rw [eval_e_sub]; simp
  have hwb : (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64)).Permitted .write
      (b + 0x4018#64).toNat 1 := by
    rw [pushMem_permitted]
    rw [hkU.permitted (fun k hk => Or.inl (Or.inl <| by
      have := clang_in E.hb (n := 0x4018) (by decide)
      rw [addr_toNat (by have := E.hb; omega)] at this ⊢
      simp only [clangWorld_inImage, ClangImg] at this ⊢; omega))]
    rw [pushMem_permitted, pushMem_permitted]
    exact hbss.wr
  have hdu : u.g.done = none := by rw [hg]; exact hd
  refine must_listed (o := 0x117) clang_listing_ok rfl hdu (by rw [hrip_u]; exact hin _ (by decide))
    hmu.code (by rw [hrip_u, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa [hrsp_u] using pU _ (Or.inr rfl))]
  xstep [hrip_u, hrsp_u]
  refine must_listed (o := 0x80) clang_listing_ok rfl hdu (hin _ (by decide)) hm3.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x87) clang_listing_ok rfl hdu (hin _ (by decide)) hm3.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x8e) clang_listing_ok rfl hdu (hin _ (by decide)) hm3.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x91) clang_listing_ok rfl hdu (hin _ (by decide)) hm3.code (by rw [ripadd]) ?_
  xstep [hz3]
  refine must_listed (o := 0xa8) clang_listing_ok rfl hdu (hin _ (by decide)) hm3.code (by rw [ripadd]) ?_
  have hA : (18446744073709551608 + (18446744073709551608 + (t.m.core.read .rsp).toNat)) %
      18446744073709551616 = (t.m.core.read .rsp - 8#64 - 8#64).toNat := by rw [e16]; omega
  xstep [Silmaril.X86.popWord]
  rw [hA, hret3]
  simp only [obind_some, Silmaril.X86.wordOfBytes?_encodeWords, WP_ok, st_write_regs]
  refine must_listed (o := 0x11c) clang_listing_ok rfl hdu (hin _ (by decide)) hm3.code (by rw [ripadd]) ?_
  xstep [Silmaril.X86.Ext.writeRM8]
  rw [storeN_ok hwb]
  xstep []
  -- the stack below `completed.0`'s store: the saved `rbp` and the gate
  have hstk : ∀ x, (t.m.core.read .rsp).toNat - 16 ≤ x → x < (t.m.core.read .rsp).toNat + 8 →
      ¬ ClangImg b x := fun x h1 h2 => by
    have := (hroom.2.2 x (by omega) h2).2.2
    exact fun h => this (Or.inl (by simpa [clangWorld_inImage] using h))
  have hbssA : (b + 0x4018#64).toNat = b.toNat + 0x4018 := addr_toNat (by have := E.hb; omega)
  have hbssI : ClangImg b (b.toNat + 0x4018) := ⟨by omega, by have := E.hb; omega⟩
  have hk4 : Keeps (fun x => (t.m.core.read .rsp).toNat - 16 ≤ x ∧ x < (t.m.core.read .rsp).toNat + 8)
      (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64))
      (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64)) (b + 16408#64) 1
        1#64) := by
    apply storeMem_keeps
    intro x ⟨h1, h2⟩
    have := hstk x h1 h2
    rw [show (b + 16408#64) = b + 0x4018#64 from rfl, hbssA]
    by_contra hc'
    exact this (by rw [show x = b.toNat + 0x4018 by omega]; exact hbssI)
  have hRbp : (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64)) (b + 16408#64) 1
        1#64).readBytes (t.m.core.read .rsp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rbp]) := by
    rw [hk4.readBytes (fun k hk => ⟨by omega, by omega⟩)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 8 ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [hkU.readBytes (fun k hk => Or.inr (by omega))]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 8 ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    exact pushMem_read q1 p1
  have hRgate : (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64)) (b + 16408#64) 1
        1#64).readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by
    rw [hk4.readBytes (fun k hk => ⟨by omega, by omega⟩)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [hkU.readBytes (fun k hk => Or.inr (by omega))]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e8]; omega))).readBytes (fun k hk => by omega)]
    exact hc.ret
  have hm4 : ClangMem b lb ps (storeMem (pushMem u.m.memory (t.m.core.read .rsp - 8#64) (b + 0x111c#64))
      (b + 16408#64) 1 1#64) := by
    refine hm3.keep E.hb (storeMem_keeps (fun x hx => ?_))
    rw [show (b + 16408#64) = b + 0x4018#64 from rfl, hbssA]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    omega
  have hB : (18446744073709551608 + (t.m.core.read .rsp).toNat) % 18446744073709551616 =
      (t.m.core.read .rsp - 8#64).toNat := by rw [e8]; omega
  refine must_listed (o := 0x123) clang_listing_ok rfl hdu (hin _ (by decide)) hm4.code (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord]
  rw [hB, hRbp]
  simp only [obind_some, Silmaril.X86.wordOfBytes?_encodeWords, WP_ok, st_write_regs]
  refine must_listed (o := 0x124) clang_listing_ok rfl hdu (hin _ (by decide)) hm4.code (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hRgate]
  exact k _ rfl hg hm4

end Silmaril.Elf.Link.Dyn.Hello
