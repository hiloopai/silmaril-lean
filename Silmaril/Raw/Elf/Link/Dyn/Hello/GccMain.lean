module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccInit

/-! # hello-gcc: `main` and its call of `puts` through the PLT -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn.Proc

/-- `"hello, world\n"` -/
def helloNL : List Byte := helloStr ++ [10#8]

/-- What `puts` may have done to the stream. -/
def OutStep (rel : Bool) (o o' : List Byte) : Prop :=
  o' = o ++ helloNL ∨ (rel = false ∧ ∃ p, p <+: helloNL ∧ o' = o ++ p)

theorem outStep_of {rel : Bool} {o o' : List Byte} {r : Word} {W : World} (hW : W.reliable = rel)
    (h : (o' = o ++ helloStr ++ [10] ∧ (low32 r).msb = false) ∨
      (W.reliable = false ∧ ∃ p, p <+: helloStr ++ [10] ∧ o' = o ++ p ∧ low32 r = 0xffffffff#32)) :
    OutStep rel o o' := by
  rcases h with ⟨h1, -⟩ | ⟨h1, p, h2, h3, -⟩
  · left; rw [h1, helloNL, List.append_assoc]; rfl
  · right; exact ⟨hW ▸ h1, p, by simpa [helloNL] using h2, h3⟩

theorem helloStr_cstr {m : Memory} {b lb : Word} (hm : GccMem b lb m) :
    CStr m (b + 0x2004#64) helloStr := ⟨by decide, hm.str⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`main`** (`0x1060`): `puts("hello, world")` through `puts@plt`, then `return 0`. -/
theorem gcc_main {b lb gate : Word} {rel : Bool} (E : GccEnv b lb gate) {Q : PState → Prop}
    {t : PState} (hc : Cb (gccWorld b lb gate rel) b lb t (b + 0x1060#64))
    (k : ∀ u : PState, u.m.core.rip = gate → u.g.jobs = t.g.jobs → u.g.atexit = t.g.atexit →
      u.g.done = none → OutStep rel t.g.out u.g.out → low32 (u.m.core.read .rax) = 0#32 →
      Keeps (GccImg b) t.m.memory u.m.memory → MustQ (gccWorld b lb gate rel) Q u) :
    MustQ (gccWorld b lb gate rel) Q t := by
  have hl := hc.mem.code
  have hin : ∀ n, n < 0x4018 → (gccWorld b lb gate rel).InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => gcc_in E.hb hn
  have hd := hc.done
  have hroom := hc.room
  have hsp := hroom.1
  have hsp2 := hroom.2.1
  have e8 : (t.m.core.read .rsp - 8#64).toNat = (t.m.core.read .rsp).toNat - 8 :=
    sub_toNat (k := 8) (by omega) (by decide)
  have e16 : (t.m.core.read .rsp - 8#64 - 8#64).toNat = (t.m.core.read .rsp).toNat - 16 := by
    rw [sub_toNat (k := 8) (by omega) (by decide), e8]; omega
  have p1 : t.m.memory.Permitted .write (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom (Or.inr rfl) (by omega) (by omega)
  have r1 : t.m.memory.Permitted .read (t.m.core.read .rsp - 8#64 - 8#64).toNat 8 :=
    perm_room hroom (Or.inl rfl) (by omega) (by omega)
  have hk1 : Keeps (GccImg b) t.m.memory
      (pushMem t.m.memory (t.m.core.read .rsp - 8#64) (b + 0x1074#64)) :=
    keeps_push rfl hroom (by omega) (by omega)
  have hm1 := hc.mem.keep E.hb hk1
  have hret := pushMem_read (v := b + 0x1074#64) r1 p1
  refine must_listed (o := 0x60) gcc_listing_ok rfl hd (by rw [hc.rip]; exact hin _ (by decide)) hl
    (by rw [hc.rip, ripadd]) ?_
  xstep [hc.rip]
  refine must_listed (o := 0x64) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x68) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x6f) gcc_listing_ok rfl hd (hin _ (by decide)) hl (by rw [ripadd]) ?_
  simp only [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec]
  rw [pushWord_mem (by simpa using p1)]
  xstep []
  refine must_listed (o := 0x50) gcc_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  xstep []
  refine must_listed (o := 0x54) gcc_listing_ok rfl hd (hin _ (by decide)) hm1.code (by rw [ripadd]) ?_
  xstep [hm1.puts]
  have hsp' : (t.m.core.read .rsp - 8#64 - 8#64).toNat % 16 = 8 := by rw [e16]; have := hc.al; omega
  refine must_fn hd (by simpa [gccWorld_inImage] using E.puts_out) (by simpa [gccWorld] using (Ne.symm E.gate_puts))
    rfl (f := .puts) (by simp [gccWorld]) (fun r => Iff.rfl)
    ⟨abiEntry_of (v := b + 0x1074#64) (by simpa using hsp') (by simpa using hret), helloStr,
      by simpa using helloStr_cstr hm1⟩ ?_
  rintro u ⟨⟨habi, hkeep⟩, str, hcs, hj, ha, hdn, -, hout⟩
  simp only at hcs hj ha hdn hout habi hkeep
  have hstr : str = helloStr := cstr_unique hcs (by simpa using helloStr_cstr hm1)
  subst hstr
  have hrip_u : u.m.core.rip = b + 0x1074#64 := by
    rw [habi.pc]; exact retOf_of (by simpa using hret)
  have hrsp_u : u.m.core.read .rsp = t.m.core.read .rsp - 8#64 := by
    rw [habi.stack]; simp
  have hku : Keeps (GccImg b) t.m.memory u.m.memory :=
    hk1.trans (hkeep.mono (fun a ha => Or.inl (Or.inl (by simpa [gccWorld_inImage] using ha))))
  have hmu := hc.mem.keep E.hb hku
  have hgate_u : u.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [gate]) := by
    rw [hkeep.readBytes (fun k hk => Or.inr (by simp [e16]; omega))]
    rw [(pushMem_keeps (P := fun x => (t.m.core.read .rsp).toNat ≤ x) (m := t.m.memory)
      (sp := t.m.core.read .rsp - 8#64) (v := b + 0x1074#64) (fun x hx => Or.inr (by rw [e16]; omega))).readBytes
      (fun k hk => by omega)]
    exact hc.ret
  refine must_listed (o := 0x74) gcc_listing_ok rfl hdn (by rw [hrip_u]; exact hin _ (by decide))
    hmu.code (by rw [hrip_u, ripadd]) ?_
  xstep [hrip_u]
  refine must_listed (o := 0x76) gcc_listing_ok rfl hdn (hin _ (by decide)) hmu.code (by rw [ripadd]) ?_
  xstep [hrsp_u]
  refine must_listed (o := 0x7a) gcc_listing_ok rfl hdn (hin _ (by decide)) hmu.code (by rw [ripadd]) ?_
  xstep [Silmaril.X86.popWord, hgate_u]
  refine k _ rfl hj ha hdn (outStep_of rfl hout) ?_ hku
  simp [low32, Silmaril.X86.Ext.AluOp.resultN]
