module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccMem
public import Silmaril.X86.BlockCert9.Thms

/-! # hello-gcc: `_start` up to the call of `__libc_start_main` -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

/-- The process world of hello-gcc: executable at `b`, `libc.so.6` at `lb`, callbacks
returning to `gate`. -/
def gccWorld (b lb gate : Word) (rel : Bool) : World where
  base := b
  size := 0x4018
  inits := [b + 0x1000#64, b + 0x1160#64]
  finis := [b + 0x1120#64, b + 0x116c#64]
  gate := gate
  lazy := none
  fns := [(lb + 0x87cc0#64, .puts), (lb + 0x2a200#64, .libcStartMain),
    (lb + 0x472c0#64, .cxaFinalize)]
  reliable := rel

theorem gccWorld_inImage (b lb gate : Word) (rel : Bool) :
    (gccWorld b lb gate rel).InImage = GccImg b := rfl

/-- What the loader guarantees about the layout: the image does not wrap, and libc's entry
points and the callback gate lie outside it. -/
structure GccEnv (b lb gate : Word) : Prop where
  hb : b.toNat + 0x4018 < 2 ^ 64
  puts_out : ¬ GccImg b (lb + 0x87cc0#64).toNat
  lsm_out : ¬ GccImg b (lb + 0x2a200#64).toNat
  cxa_out : ¬ GccImg b (lb + 0x472c0#64).toNat
  gate_out : ¬ GccImg b gate.toNat
  gate_puts : gate ≠ lb + 0x87cc0#64
  gate_lsm : gate ≠ lb + 0x2a200#64
  gate_cxa : gate ≠ lb + 0x472c0#64
  cxa_ne : lb + 0x472c0#64 ≠ 0#64

theorem gcc_in {b : Word} (hb : b.toNat + 0x4018 < 2 ^ 64) {n : Nat} (hn : n < 0x4018) :
    GccImg b (b + BitVec.ofNat 64 n).toNat := by
  rw [addr_toNat (by omega)]; simp only [GccImg]; omega

theorem gcc_listing_ok : listingOk gccText gccListing = true := by decide +kernel

/-- A push below a stack room keeps the image. -/
theorem keeps_push {b : Word} {W : World} (hW : W.InImage = GccImg b) {m : Memory} {sp v : Word}
    (hroom : StackRoom W m sp) {sp' : Word} (hlo : sp.toNat - 4096 + 8 ≤ sp'.toNat)
    (hhi : sp'.toNat ≤ sp.toNat + 8) : Keeps (GccImg b) m (pushMem m sp' v) := by
  apply pushMem_keeps
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hroom
  have h8 : (sp' - 8#64).toNat = sp'.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  rw [h8]
  by_contra hc
  have := (h3 (x) (by omega) (by omega)).2.2
  exact this (Or.inl (by rw [hW]; exact hx))

theorem retOf_of {c : State} {m : Memory} {v : Word}
    (h : m.readBytes (c.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    Silmaril.X86.FnContract.retOf c m = v := by
  simp [Silmaril.X86.FnContract.retOf, h]

theorem abiEntry_of {c : State} {m : Memory} {v : Word} (ha : (c.read .rsp).toNat % 16 = 8)
    (h : m.readBytes (c.read .rsp).toNat 8 = some (Silmaril.Machine.LittleEndian.encodeWords [v])) :
    AbiEntry c m := ⟨ha, by rw [h, retOf_of h]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`_start`** (`0x1080`): to `__libc_start_main` with `rdi = main`, `rsi = argc`,
`rdx = argv`, a System V entry and the image intact. -/
theorem gcc_start {b lb gate : Word} {rel : Bool} (E : GccEnv b lb gate) {Q : PState → Prop}
    {s : PState} (hd : s.g.done = none) (hm : GccMem b lb s.m.memory)
    (hrip : s.m.core.rip = b + 0x1080#64) (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom (gccWorld b lb gate rel) s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (k : ∀ t : PState, t.g = s.g → t.m.core.rip = lb + 0x2a200#64 → GccMem b lb t.m.memory →
      Keeps (GccImg b) s.m.memory t.m.memory → AbiEntry t.m.core t.m.memory → t.m.core.read .rdi = b + 0x1060#64 →
      t.m.core.read .rsi = argc → t.m.core.read .rdx = s.m.core.read .rsp + 8#64 →
      MustQ (gccWorld b lb gate rel) Q t) :
    MustQ (gccWorld b lb gate rel) Q s := by
  have hl := hm.code
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have hin : ∀ n, n < 0x4018 → (gccWorld b lb gate rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => gcc_in E.hb hn
  have e8 : (s.m.core.read .rsp - 8#64).toNat = (s.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (s.m.core.read .rsp - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have e24 : (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat = (s.m.core.read .rsp).toNat - 24 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e16]; omega
  have p1 : s.m.memory.Permitted .write (s.m.core.read .rsp - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have hm1 : GccMem b lb (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)) :=
    hm.keep E.hb (keeps_push rfl hroom (by omega) (by omega))
  have p2 : (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem (Or.inr rfl) (by omega) (by omega)
  have hm2 : GccMem b lb (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)) :=
    hm1.keep E.hb (keeps_push rfl hroom.pushMem (by omega) (by omega))
  have p3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .write
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inr rfl) (by omega) (by omega)
  have r3 : (pushMem (pushMem s.m.memory (s.m.core.read .rsp) (s.m.core.read .rax))
      (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64)).Permitted .read
      (s.m.core.read .rsp - 8#64 - 8#64 - 8#64).toNat 8 :=
    perm_room hroom.pushMem.pushMem (Or.inl rfl) (by omega) (by omega)
  have hm3 : GccMem b lb (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
      (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
      (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x10a5#64)) :=
    hm2.keep E.hb (keeps_push rfl hroom.pushMem.pushMem (by omega) (by omega))
  have hret := pushMem_read (v := b + 0x10a5#64) r3 p3
  refine must_listed (o := 0x80) gcc_listing_ok rfl hd (by rw [hrip]; exact hin _ (by decide)) hl
    (by rw [hrip, ripadd]) ?_
  xstep [hrip]
  refine must_listed (o := 0x84) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x86) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x89) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hargc]
  refine must_listed (o := 0x8a) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x8d) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  simp only [and16 hal (by omega)]
  refine must_listed (o := 0x91) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 0x92) gcc_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p2)]
  xstep []
  refine must_listed (o := 0x93) gcc_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x96) gcc_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x98) gcc_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x9f) gcc_listing_ok rfl hd (hin _ (by decide)) hm2.code (by rw [ripadd]) ?_
  xstep []
  rw [pushWord_mem (by simpa using p3)]
  simp only [hm2.lsm, WP_ok, st_write_regs, st_read_mk]
  refine k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using hm3
  · have hk : Keeps (GccImg b) s.m.memory (pushMem (pushMem (pushMem s.m.memory (s.m.core.read .rsp)
        (s.m.core.read .rax)) (s.m.core.read .rsp - 8#64) (s.m.core.read .rsp - 8#64))
        (s.m.core.read .rsp - 8#64 - 8#64) (b + 0x10a5#64)) :=
      (keeps_push (sp' := s.m.core.read .rsp) rfl hroom (by omega) (by omega)).trans
        ((keeps_push (sp' := s.m.core.read .rsp - 8#64) rfl hroom.pushMem (by omega) (by omega)).trans
          (keeps_push (sp' := s.m.core.read .rsp - 8#64 - 8#64) rfl hroom.pushMem.pushMem (by omega) (by omega)))
    simpa using hk
  · refine abiEntry_of (v := b + 0x10a5#64) ?_ ?_
    · simp [e24]; omega
    · simpa using hret
  all_goals simp

end Silmaril.Elf.Link.Dyn.Hello
