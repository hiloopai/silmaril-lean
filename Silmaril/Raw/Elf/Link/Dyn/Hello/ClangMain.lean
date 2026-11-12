module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.ClangFini

/-! # hello-clang: `main`, `puts@plt` and lazy binding -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn.Proc

theorem ClangBss.keepP {b : Word} (hb : b.toNat + 0x4020 < 2 ^ 64) {P : Nat → Prop}
    (hP : ∀ k < 1, P (b.toNat + 0x4018 + k)) {m m' : Memory} (h : ClangBss b m) (hk : Keeps P m m') :
    ClangBss b m' := by
  refine ⟨?_, ?_⟩
  · have := h.val
    simp only [loadN, Memory.readBytes] at this ⊢
    rw [ckeeps_range hb hk (off := 0x4018) (by decide) hP]; exact this
  · have hw := h.wr
    rw [addr_toNat (by omega)] at hw ⊢
    rw [hk.permitted hP]
    exact hw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The call of `puts("hello, world")` (at `puts`'s entry, with `main`'s frame below) and the
rest of `main`. -/
theorem clang_puts_tail {b lb gate res ps : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res)
    {Q : PState → Prop} {s : PState} {rsp0 v : Word} (hd : s.g.done = none)
    (hrip : s.m.core.rip = lb + 0x87cc0#64) (hrsp : s.m.core.read .rsp = rsp0 - 8#64 - 8#64)
    (hal : rsp0.toNat % 16 = 8) (hlo : 4096 ≤ rsp0.toNat) (hhi : rsp0.toNat + 8 < 2 ^ 64)
    (hret : s.m.memory.readBytes (rsp0 - 8#64 - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [b + 0x114d#64]))
    (hv : s.m.memory.readBytes (rsp0 - 8#64).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v]))
    (hgate : s.m.memory.readBytes rsp0.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [gate]))
    (hrdi : s.m.core.read .rdi = b + 0x2004#64) (hm : ClangMem b lb ps s.m.memory)
    (hbs : ClangBss b s.m.memory)
    (k : ∀ u : PState, u.m.core.rip = gate → u.g.jobs = s.g.jobs → u.g.atexit = s.g.atexit →
      u.g.done = none → OutStep rel s.g.out u.g.out → low32 (u.m.core.read .rax) = 0#32 →
      ClangMem b lb ps u.m.memory → ClangBss b u.m.memory →
      MustQ (clangWorld b lb gate res lazy rel) Q u) :
    MustQ (clangWorld b lb gate res lazy rel) Q s := by
  have hin : ∀ n, n < 0x4020 → (clangWorld b lb gate res lazy rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => clang_in E.hb hn
  have e8 : (rsp0 - 8#64).toNat = rsp0.toNat - 8 := sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (rsp0 - 8#64 - 8#64).toNat = rsp0.toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  refine must_fn' hd (by rw [hrip]; simpa [clangWorld_inImage] using E.puts_out)
    (by rw [hrip]; simpa [clangWorld] using (Ne.symm E.gate_puts))
    (by rw [hrip]; exact clang_res_ne E.res_puts) (f := .puts) (by rw [hrip]; simp [clangWorld])
    (fun r => Iff.rfl)
    ⟨abiEntry_of (v := b + 0x114d#64) (by rw [hrsp, e16]; omega) (by rw [hrsp]; exact hret),
      helloStr, by rw [hrdi]; exact helloStr_cstr' hm⟩ ?_
  rintro u ⟨⟨habi, hkeep⟩, str, hcs, hj, ha, hdn, -, hout⟩
  have hstr : str = helloStr := cstr_unique hcs (by rw [hrdi]; exact helloStr_cstr' hm)
  subst hstr
  have hrip_u : u.m.core.rip = b + 0x114d#64 := by
    rw [habi.pc]; exact retOf_of (by rw [hrsp]; exact hret)
  have hrsp_u : u.m.core.read .rsp = rsp0 - 8#64 := by
    rw [habi.stack, hrsp]; simp
  have hkI : Keeps (ClangImg b) s.m.memory u.m.memory :=
    hkeep.mono (fun a ha => Or.inl (Or.inl (by simpa [clangWorld_inImage] using ha)))
  have hmu := hm.keep E.hb (keepsI' hkI)
  have hbu := hbs.keep E.hb hkI
  have hv_u : u.m.memory.readBytes (rsp0 - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [v]) := by
    rw [hkeep.readBytes (fun k hk => Or.inr (by rw [hrsp, e16, e8]; omega))]; exact hv
  have hg_u : u.m.memory.readBytes rsp0.toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by
    rw [hkeep.readBytes (fun k hk => Or.inr (by rw [hrsp, e16]; omega))]; exact hgate
  refine must_listed (o := 0x14d) clang_listing_ok rfl hdn (by rw [hrip_u]; exact hin _ (by decide))
    hmu.code (by rw [hrip_u, ripadd]) ?_
  xstep [hrip_u]
  refine must_listed (o := 0x14f) clang_listing_ok rfl hdn (hin (0x1000 + 0x14f) (by decide)) hmu.code (by rw [ripadd]) ?_
  have hB : (18446744073709551608 + rsp0.toNat) % 18446744073709551616 = (rsp0 - 8#64).toNat := by
    rw [e8]; omega
  xstep [Silmaril.X86.popWord, hrsp_u]
  rw [hB, hv_u]
  simp only [obind_some, Silmaril.X86.wordOfBytes?_encodeWords, WP_ok, st_write_regs]
  refine must_listed (o := 0x150) clang_listing_ok rfl hdn (hin (0x1000 + 0x150) (by decide)) hmu.code (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hg_u]
  refine k _ rfl hj ha hdn (outStep_of rfl hout) ?_ hmu hbu
  simp [low32, Silmaril.X86.Ext.AluOp.resultN]

theorem loadN_of_word {m : Memory} {a v : Word}
    (h : m.readBytes a.toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    loadN m a 8 = some v := by
  rw [← Silmaril.X86.Ext.leBytes_eight] at h
  simp only [loadN, h, Option.map_some, Silmaril.X86.Ext.leValue_leBytes]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt v.isLt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`main`** (`0x1140`), in both binding modes: `puts@plt` jumps through `puts`'s slot, either
straight to `puts` (eager) or, on this first call, through `PLT0` to the resolver, which binds
the slot and enters `puts` (lazy). -/
theorem clang_main {b lb gate res : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res)
    {Q : PState → Prop} {t : PState}
    (hc : CCb (clangWorld b lb gate res lazy rel) b lb (clangPs b lb lazy) t (b + 0x1140#64))
    (hplt : ClangPlt b (clangPs b lb lazy) res lazy t.m.memory) (hbss : ClangBss b t.m.memory)
    (k : ∀ u : PState, u.m.core.rip = gate → u.g.jobs = t.g.jobs → u.g.atexit = t.g.atexit →
      u.g.done = none → OutStep rel t.g.out u.g.out → low32 (u.m.core.read .rax) = 0#32 →
      ClangMem b lb (clangPs b lb lazy) u.m.memory → ClangBss b u.m.memory →
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
  have e24 : (t.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have e32 : (t.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat =
      (t.m.core.read .rsp).toNat - 32 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e24]; omega
  -- push rax; call puts@plt
  have p1 : t.m.memory.Permitted .write (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have q1 : t.m.memory.Permitted .read (t.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inl rfl) (by omega) (by omega)
  have hk1 : Keeps (ClangImg b) t.m.memory
      (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax)) :=
    ckeeps_push rfl hroom (by omega) (by omega)
  have p2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax)).Permitted .write
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have q2 : (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax)).Permitted .read
      (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inl rfl) (by omega) (by omega)
  have hk2 : Keeps (ClangImg b) t.m.memory (pushMem (pushMem t.m.memory (t.m.core.read .rsp)
      (t.m.core.read .rax)) (t.m.core.read .rsp - 8#64) (b + 0x114d#64)) :=
    hk1.trans (ckeeps_push rfl hroom.pushMem (by omega) (by omega))
  have hm2 := hc.mem.keep E.hb (keepsI' hk2)
  have hb2 := hbss.keep E.hb hk2
  have hp2 := hplt.keep E.hb hk2
  -- the stack after the call
  have hret2 := pushMem_read (v := b + 0x114d#64) q2 p2
  have hv2 : (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 0x114d#64)).readBytes (t.m.core.read .rsp - 8#64).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [t.m.core.read .rax]) := by
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 8 ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by rw [e8]; omega)]
    exact pushMem_read q1 p1
  have hg2 : (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
      (t.m.core.read .rsp - 8#64) (b + 0x114d#64)).readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e16]; omega))).readBytes (fun k hk => by omega)]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x)
      (fun x hx => Or.inr (by rw [e8]; omega))).readBytes (fun k hk => by omega)]
    exact hc.ret
  refine must_listed (o := 0x140) clang_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep [hc.rip]
  refine must_listed (o := 0x141) clang_listing_ok rfl hd (hin (0x1000 + 0x141) (by decide))
    (hc.mem.keep E.hb (keepsI' hk1)).code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x148) clang_listing_ok rfl hd (hin (0x1000 + 0x148) (by decide))
    (hc.mem.keep E.hb (keepsI' hk1)).code (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 0x30) clang_listing_ok rfl hd (hin (0x1000 + 0x30) (by decide))
    hm2.code (by rw [ripadd]) ?_
  xstep [hp2.slot]
  cases lazy
  · -- eager binding: straight to `puts`
    exact clang_puts_tail E hd (rsp0 := t.m.core.read .rsp) (v := t.m.core.read .rax)
      (by simp [clangPs]) (by simp) hc.al hsp hsp2 (by simpa using hret2) (by simpa using hv2)
      (by simpa using hg2) (by simp) (by simpa using hm2) (by simpa using hb2)
      (fun u h1 h2 h3 h4 h5 h6 h7 h8 => k u h1 h2 h3 h4 h5 h6 h7 h8)
  · -- lazy binding: `push $0; jmp PLT0; push GOT[1]; jmp *GOT[2]`
    rw [show clangPs b lb true = b + 0x1036#64 from rfl]
    have p3 : (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 0x114d#64)).Permitted .write
        (t.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
      perm_room hroom.pushMem.pushMem (Or.inr rfl) (by omega) (by omega)
    have q3 : (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 0x114d#64)).Permitted .read
        (t.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
      perm_room hroom.pushMem.pushMem (Or.inl rfl) (by omega) (by omega)
    have hk3 := hk2.trans (ckeeps_push (sp' := t.m.core.read .rsp - 8#64 - 8#64) (v := 0#64) rfl
      hroom.pushMem.pushMem (by omega) (by omega))
    have hp3 := hplt.keep E.hb hk3
    obtain ⟨w, hw⟩ := hp3.got1
    have p4 : (pushMem (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 0x114d#64)) (t.m.core.read .rsp - 8#64 - 8#64) 0#64).Permitted
        .write (t.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64).toNat 8 :=
      perm_room hroom.pushMem.pushMem.pushMem (Or.inr rfl) (by omega) (by omega)
    have hk4 := hk3.trans (ckeeps_push (sp' := t.m.core.read .rsp - 8#64 - 8#64 - 8#64) (v := w) rfl
      hroom.pushMem.pushMem.pushMem (by omega) (by omega))
    have hp4 := hplt.keep E.hb hk4
    have hm4 := hc.mem.keep E.hb (keepsI' hk4)
    have hb4 := hbss.keep E.hb hk4
    refine must_listed (o := 0x36) clang_listing_ok rfl hd (hin (0x1000 + 0x36) (by decide))
      hm2.code (by rw [ripadd]) ?_
    simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext9.execNew]
    rw [pushWord_mem (by simpa using p3)]
    xstep []
    refine must_listed (o := 0x3b) clang_listing_ok rfl hd (hin (0x1000 + 0x3b) (by decide))
      (hc.mem.keep E.hb (keepsI' hk3)).code (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 0x20) clang_listing_ok rfl hd (hin (0x1000 + 0x20) (by decide))
      (hc.mem.keep E.hb (keepsI' hk3)).code (by rw [ripadd]) ?_
    simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.readRM, ofRip_addr, ripadd, Silmaril.X86.Ext.Sz.bytes]
    xstep [hw]
    rw [pushWord_mem (by simpa using p4)]
    xstep []
    refine must_listed (o := 0x26) clang_listing_ok rfl hd (hin (0x1000 + 0x26) (by decide))
      hm4.code (by rw [ripadd]) ?_
    xstep [hp4.got2 rfl]
    have hj : (pushMem (pushMem (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 0x114d#64)) (t.m.core.read .rsp - 8#64 - 8#64) 0#64)
        (t.m.core.read .rsp - 8#64 - 8#64 - 8#64) w).readBytes
        (t.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [0#64]) := by
      rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 24 ≤ x)
        (fun x hx => Or.inr (by rw [e32]; omega))).readBytes (fun k hk => by rw [e24]; omega)]
      exact pushMem_read q3 p3
    refine must_resolve hd (by simpa [clangWorld_inImage] using E.res_out)
      (by simpa [clangWorld] using Ne.symm E.gate_res) (res := res) (e := (0x4000, lb + 0x87cc0#64))
      rfl rfl (loadN_of_word (by simpa using hj)) hp4.slotRW ?_
    rintro t' ⟨hrip', hrsp', hregs, -, hkeep, -, hg', -⟩
    simp only [st_read_mk, Silmaril.Machine.RegisterFile.write_same] at hrip' hrsp' hregs hkeep hg'
    have hsp16 : t.m.core.read .rsp - 8#64 - 8#64 - 8#64 - 8#64 + 16#64 = t.m.core.read .rsp - 8#64 - 8#64 := by
      bv_omega
    rw [hsp16] at hrsp' hkeep
    have hA : (b + BitVec.ofNat 64 0x4000).toNat = b.toNat + 0x4000 := addr_toNat (by have := E.hb; omega)
    have hnslot : ∀ x, (t.m.core.read .rsp).toNat - 16 ≤ x → x < (t.m.core.read .rsp).toNat + 8 →
        ¬ (((clangWorld b lb gate res true rel).base + BitVec.ofNat 64 16384).toNat ≤ x ∧
          x < ((clangWorld b lb gate res true rel).base + BitVec.ofNat 64 16384).toNat + 8) := by
      intro x h1 h2 hx
      rw [show (clangWorld b lb gate res true rel).base = b from rfl, show (16384 : Nat) = 0x4000 from rfl,
        hA] at hx
      have := (hroom.2.2 x (by omega) h2).2.2
      apply this; left
      simp only [clangWorld_inImage, ClangImg]
      have := E.hb
      omega
    have hkS : ∀ {a len : Nat}, (t.m.core.read .rsp).toNat - 16 ≤ a →
        a + len ≤ (t.m.core.read .rsp).toNat + 8 → t'.m.memory.readBytes a len = (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
          (t.m.core.read .rsp - 8#64) (b + 0x114d#64)).readBytes a len := by
      intro a len ha ha2
      rw [hkeep.readBytes (fun k hk => ⟨hnslot _ (by omega) (by omega), Or.inr (by rw [e16]; omega)⟩)]
      rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 16 ≤ x)
        (fun x hx => Or.inr (by rw [e32]; omega))).readBytes (fun k hk => by omega)]
      rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat - 16 ≤ x)
        (fun x hx => Or.inr (by rw [e24]; omega))).readBytes (fun k hk => by omega)]
    have hkI : Keeps (ClangImg' b)
        (pushMem (pushMem (pushMem (pushMem t.m.memory (t.m.core.read .rsp) (t.m.core.read .rax))
        (t.m.core.read .rsp - 8#64) (b + 0x114d#64)) (t.m.core.read .rsp - 8#64 - 8#64) 0#64)
        (t.m.core.read .rsp - 8#64 - 8#64 - 8#64) w) t'.m.memory :=
      hkeep.mono (fun a ha => ⟨by simp only [clangWorld, hA]; exact ha.2.1,
        Or.inl (Or.inl (by simpa [clangWorld_inImage] using ha.1))⟩)
    refine clang_puts_tail E (s := t') (rsp0 := t.m.core.read .rsp) (v := t.m.core.read .rax)
      (by rw [hg']; exact hd) hrip' hrsp' hc.al hsp hsp2 ?_ ?_ ?_ ?_ (hm4.keep E.hb hkI)
      (hb4.keepP E.hb (fun k hk => by
        refine ⟨?_, Or.inl (Or.inl ?_)⟩
        · simp only [clangWorld, hA]; omega
        · simp only [clangWorld_inImage, ClangImg]; have := E.hb; omega) hkeep) ?_
    · rw [hkS (by rw [e16]) (by rw [e16]; omega)]; exact hret2
    · rw [hkS (by rw [e8]; omega) (by rw [e8]; omega)]; exact hv2
    · rw [hkS (by omega) (by omega)]; exact hg2
    · rw [hregs .rdi (by simp)]; simp
    · intro u h1 h2 h3 h4 h5 h6 h7 h8
      rw [hg'] at h2 h3 h5
      exact k u h1 h2 h3 h4 h5 h6 h7 h8

end Silmaril.Elf.Link.Dyn.Hello
