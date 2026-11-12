module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.ClangMem
public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccStart

/-! # hello-clang: world, layout, `_start` -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

/-- The process world of hello-clang. Under lazy binding (`lazy`), `res` is the resolver and
`puts`'s slot (`0x4000`) is bound on its first call. -/
def clangWorld (b lb gate res : Word) (lazy rel : Bool) : World where
  base := b
  size := 0x4020
  inits := [b + 0x1000#64, b + 0x1130#64]
  finis := [b + 0x10f0#64, b + 0x1154#64]
  gate := gate
  lazy := if lazy then some (res, [(0x4000, lb + 0x87cc0#64)]) else none
  fns := [(lb + 0x87cc0#64, .puts), (lb + 0x2a200#64, .libcStartMain),
    (lb + 0x472c0#64, .cxaFinalize)]
  reliable := rel

theorem clangWorld_inImage (b lb gate res : Word) (lazy rel : Bool) :
    (clangWorld b lb gate res lazy rel).InImage = ClangImg b := rfl

/-- The layout facts the loader guarantees for hello-clang. -/
structure ClangEnv (b lb gate res : Word) : Prop where
  hb : b.toNat + 0x4020 < 2 ^ 64
  puts_out : ¬ ClangImg b (lb + 0x87cc0#64).toNat
  lsm_out : ¬ ClangImg b (lb + 0x2a200#64).toNat
  cxa_out : ¬ ClangImg b (lb + 0x472c0#64).toNat
  gate_out : ¬ ClangImg b gate.toNat
  res_out : ¬ ClangImg b res.toNat
  gate_puts : gate ≠ lb + 0x87cc0#64
  gate_lsm : gate ≠ lb + 0x2a200#64
  gate_cxa : gate ≠ lb + 0x472c0#64
  gate_res : gate ≠ res
  res_puts : res ≠ lb + 0x87cc0#64
  res_lsm : res ≠ lb + 0x2a200#64
  res_cxa : res ≠ lb + 0x472c0#64
  cxa_ne : lb + 0x472c0#64 ≠ 0#64

theorem clang_in {b : Word} (hb : b.toNat + 0x4020 < 2 ^ 64) {n : Nat} (hn : n < 0x4020) :
    ClangImg b (b + BitVec.ofNat 64 n).toNat := by
  rw [addr_toNat (by omega)]; simp only [ClangImg]; omega

theorem clang_listing_ok : listingOk clangText clangListing = true := by decide +kernel

theorem ckeeps_push {b : Word} {W : World} (hW : W.InImage = ClangImg b) {m : Memory} {sp v : Word}
    (hroom : StackRoom W m sp) {sp' : Word} (hlo : sp.toNat - 4096 + 8 ≤ sp'.toNat)
    (hhi : sp'.toNat ≤ sp.toNat + 8) : Keeps (ClangImg b) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hroom
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  have := (h3 (x) (by omega) (by omega)).2.2
  exact this (Or.inl (by rw [hW]; exact hx))

theorem keepsI' {b : Word} {m m' : Memory} (h : Keeps (ClangImg b) m m') : Keeps (ClangImg' b) m m' :=
  h.mono fun _ h => h.1

/-- The lazy-binding hypothesis of `extStep_fn` at a library entry point. -/
theorem clang_res_ne {b lb gate res : Word} {lazy rel : Bool} {a : Word} (h : res ≠ a) :
    ∀ r s, (clangWorld b lb gate res lazy rel).lazy = some (r, s) → a ≠ r := by
  intro r s hl
  cases lazy
  · simp [clangWorld] at hl
  · simp [clangWorld] at hl; rw [← hl.1]; exact Ne.symm h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_start`** (`0x1080`): to `__libc_start_main` with `rdi = main`, `rsi = argc`,
`rdx = argv`, a System V entry and the image intact. -/
theorem clang_start {b lb gate res ps : Word} {lazy rel : Bool} (E : ClangEnv b lb gate res) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : ClangMem b lb ps s.m.memory)
    (hrip : s.m.core.rip = b + 0x1050#64) (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom (clangWorld b lb gate res lazy rel) s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = lb + 0x2a200#64 → ClangMem b lb ps t.m.memory →
      Keeps (ClangImg b) s.m.memory t.m.memory → AbiEntry t.m.core t.m.memory → t.m.core.read .rdi = b + 0x1140#64 →
      t.m.core.read .rsi = argc → t.m.core.read .rdx = s.m.core.read .rsp + 8#64 →
      MustQ (clangWorld b lb gate res lazy rel) Q t) :
    MustQ (clangWorld b lb gate res lazy rel) Q s := by
  have hl := hm.code
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hin : ∀ n, n < 0x4020 → (clangWorld b lb gate res lazy rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => clang_in E.hb hn
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have hm1 : ClangMem b lb ps (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)) :=
    (hm.keep E.hb ∘ keepsI') (ckeeps_push rfl hroom (by omega) (by omega))
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have hm2 : ClangMem b lb ps (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)) :=
    (hm1.keep E.hb ∘ keepsI') (ckeeps_push rfl hroom.pushMem (by omega) (by omega))
  have p3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inr rfl) (by omega) (by omega)
  have r3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .read
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inl rfl) (by omega) (by omega)
  have hm3 : ClangMem b lb ps (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
      (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
      (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x1075#64)) :=
    (hm2.keep E.hb ∘ keepsI') (ckeeps_push rfl hroom.pushMem.pushMem (by omega) (by omega))
  have hret := pushMem_read (v := b + 0x1075#64) r3 p3
  refine must_listed (o := 0x50) clang_listing_ok rfl hd (by rw [hrip]; exact hin _ (by decide)) hl
    (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 0x54) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x56) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x59) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hargc]
  refine must_listed (o := 0x5a) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x5d) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  simp only [and16 hal (by omega)]
  refine must_listed (o := 0x61) clang_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 0x62) clang_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 0x63) clang_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x66) clang_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x68) clang_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x6f) clang_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  rw [pushWord_mem (by simpa using p3)]
  simp only [hm2.lsm, WP_ok, st_write_regs, st_read_mk]
  refine k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hm3
  · have hk : Keeps (ClangImg b) s.m.memory (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
        (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
        (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x1075#64)) :=
      (ckeeps_push (sp' := s.m.core.read .rsp) rfl hroom (by omega) (by omega)).trans
        ((ckeeps_push (sp' := s.m.core.read .rsp - 8#64) rfl hroom.pushMem (by omega) (by omega)).trans
          (ckeeps_push (sp' := s.m.core.read .rsp - 8#64 - 8#64) rfl hroom.pushMem.pushMem (by omega) (by omega)))
    simpa using hk
  · refine abiEntry_of (v := b + 0x1075#64) ?_ ?_
    · simp [e24]; omega
    · simpa using hret
  all_goals simp

end Silmaril.Elf.Link.Dyn.Hello
