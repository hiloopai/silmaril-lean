module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Start
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Init
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Gate

/-! # The C runtime: a whole run, around `main`

`crt_run`: from the executable's entry (`_start`, after the loader), through
`__libc_start_main`, `_init`, `frame_dummy`, **`main`** (a hypothesis, `MainOk`), `exit`,
`__do_global_dtors_aux` and `_fini`, every run ends with the exit status `main` returned
(modulo 256) and the bytes `main` handed to `stdout` (a prefix of them if writes to fd 1 may
fail). This is the part of every proof about a gcc/clang executable that does not depend on
the program: per executable only `MainOk` remains. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry)
open Silmaril.Elf.Link.Dyn.Proc

/-- **What `main` must do**, entered as the library's callback: from a System V entry with
the image facts, an invariant `X` of `fsBase` and memory, and `pre` of the library state, it returns to the gate with the image facts
kept, the library's jobs, handlers and liveness unchanged, and `post` of the library states
before and after and of its `eax`. -/
def MainOk (W : World) (L : Layout) (b lsmA cxaA : Word) (X : Word → Memory → Prop)
    (pre : Ghost → Prop)
    (post : Ghost → Ghost → BitVec 32 → Prop) : Prop :=
  ∀ (Q : PState → Prop) (t : PState), t.g.done = none →
    t.m.core.rip = b + BitVec.ofNat 64 L.main → (t.m.core.read .rsp).toNat % 16 = 8 →
    t.m.memory.readBytes (t.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [W.gate]) →
    StackRoom W t.m.memory (t.m.core.read .rsp) → CrtMem L b lsmA cxaA 0#8 t.m.memory →
    X t.m.core.fsBase t.m.memory → pre t.g →
    (∀ u : PState, u.m.core.rip = W.gate → u.g.jobs = t.g.jobs → u.g.atexit = t.g.atexit →
      u.g.done = none → CrtMem L b lsmA cxaA 0#8 u.m.memory →
      post t.g u.g (low32 (u.m.core.read .rax)) → MustQ W Q u) →
    MustQ W Q t

/-- How a run ends: `main` returned `e` with library state `g'` (`post` of the state it was
entered with), and the process ended with status `e mod 256` and `w` on `stdout`. -/
def Ends (g0 : Ghost) (post : Ghost → Ghost → BitVec 32 → Prop) (rel : Bool) (u : PState) : Prop :=
  ∃ (g' : Ghost) (e : BitVec 32) (w : List Byte), post { g0 with jobs := [.exitRax] } g' e ∧
    u.g.done = some ((e.setWidth 64).toNat % 256, w) ∧ w <+: g'.out ∧ (rel = true → w = g'.out)

set_option maxHeartbeats 4000000 in
/-- **A whole run of the C runtime around `main`.** -/
theorem crt_run {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {W : World}
    (E : CrtEnv L W b lsmA cxaA)
    (hinits : W.inits = [b + BitVec.ofNat 64 L.init, b + BitVec.ofNat 64 L.fdummy])
    (hfinis : W.finis = [b + BitVec.ofNat 64 L.dtors, b + BitVec.ofNat 64 L.fini])
    {X : Word → Memory → Prop} (hX : ∀ f m m', Keeps W.Kept m m' → X f m → X f m')
    {pre : Ghost → Prop} {post : Ghost → Ghost → BitVec 32 → Prop}
    (hmain : MainOk W L b lsmA cxaA X pre post) {s : PState} (hd : s.g.done = none)
    (hX0 : X s.m.core.fsBase s.m.memory)
    (hat : s.g.atexit = []) (hm : CrtMem L b lsmA cxaA 0#8 s.m.memory)
    (hrip : s.m.core.rip = b + BitVec.ofNat 64 L.start) (hal : (s.m.core.read .rsp).toNat % 16 = 0)
    (hroom : StackRoom W s.m.memory (s.m.core.read .rsp)) {argc : Word}
    (hargc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [argc]))
    (hpre : pre { s.g with jobs := [.exitRax] })
    (hpend : ∀ s p, W.pending s p → p = [] := by intro _ _ h; exact h) :
    MustQ W (Ends s.g post W.reliable) s := by
  have hb := E.hb
  have gout : ¬ W.InImage W.gate.toNat := by rw [E.hW]; exact E.gate_out
  refine crt_start F E hd hm hrip hal hroom hargc fun t1 hg1 hrip1 hm1 hk1 hf1 habi hrdi1 _ _ => ?_
  have hx1 : X t1.m.core.fsBase t1.m.memory := hf1 ▸ hX _ _ _ hk1 hX0
  have hd1 : t1.g.done = none := by rw [hg1]; exact hd
  refine must_contract hd1 (by rw [hrip1, E.hW]; exact E.lsm_out)
    (fun r => extStep_fn (f := .libcStartMain) (by rw [hrip1]; exact E.lsm_gate)
      (fun res slots h => by rw [hrip1]; exact E.lsm_res res slots h)
      (by rw [hrip1]; exact E.lsm_fn) r) habi ?_
  rintro t2 ⟨⟨hrip2, hk2, hf2⟩, hg2⟩
  have hm2 := hm1.keep F hb (keeps_img E.hW hk2)
  have hx2 : X t2.m.core.fsBase t2.m.memory := hf2 ▸ hX _ _ _ hk2 hx1
  -- `_init`
  refine must_gate_call (by rw [hg2]; exact hd1) hrip2 gout (by rw [hg2, hinits]; rfl)
    fun t3 hen_t3 _ _ _ hg3 => ?_
  obtain ⟨hrip3, hal3, hret3, hroom3, hk3, hf3⟩ := hen_t3
  have hm3 := hm2.keep F hb (keeps_img E.hW hk3)
  have hx3 : X t3.m.core.fsBase t3.m.memory := hf3 ▸ hX _ _ _ hk3 hx2
  have hd3 : t3.g.done = none := by rw [hg3, hg2]; exact hd1
  refine crt_init F E.hW hb hd3 hm3 hrip3 hret3 fun t4 hg4 hrip4 hmem4 _ hf4 => ?_
  have hm4 : CrtMem L b lsmA cxaA 0#8 t4.m.memory := hmem4 ▸ hm3
  have hx4 : X t4.m.core.fsBase t4.m.memory := hf4 ▸ hmem4 ▸ hx3
  -- `frame_dummy`
  refine must_gate_call (by rw [hg4]; exact hd3) hrip4 gout (by rw [hg4, hg3]; rfl)
    fun t5 hen_t5 _ _ _ hg5 => ?_
  obtain ⟨hrip5, hal5, hret5, hroom5, hk5, hf5⟩ := hen_t5
  have hm5 := hm4.keep F hb (keeps_img E.hW hk5)
  have hx5 : X t5.m.core.fsBase t5.m.memory := hf5 ▸ hX _ _ _ hk5 hx4
  have hd5 : t5.g.done = none := by rw [hg5, hg4]; exact hd3
  refine crt_fdummy F E.hW hb hd5 hm5 hrip5 hret5 fun t6 hg6 hrip6 hmem6 _ hf6 => ?_
  have hm6 : CrtMem L b lsmA cxaA 0#8 t6.m.memory := hmem6 ▸ hm5
  have hx6 : X t6.m.core.fsBase t6.m.memory := hf6 ▸ hmem6 ▸ hx5
  -- `main`
  refine must_gate_main (by rw [hg6]; exact hd5) hrip6 gout (by rw [hg6, hg5]; rfl)
    fun t7 hen_t7 _ _ _ hg7 => ?_
  obtain ⟨hrip7, hal7, hret7, hroom7, hk7, hf7⟩ := hen_t7
  have hm7 := hm6.keep F hb (keeps_img E.hW hk7)
  have hx7 : X t7.m.core.fsBase t7.m.memory := hf7 ▸ hX _ _ _ hk7 hx6
  have hg7' : t7.g = { s.g with jobs := [.exitRax] } := by
    rw [hg7, hg6, hg5, hg4, hg3, hg2, hg1]
  refine hmain _ t7 (by rw [hg7']; exact hd) (hrip7.trans hrdi1) hal7 hret7 hroom7 hm7 hx7 (hg7' ▸ hpre)
    fun u hripu hju hatu hdu hmu hpost => ?_
  -- `exit (main's eax)`
  refine must_gate_exitRax (hpend := hpend) hdu hripu gout (by rw [hju, hg7']) fun t8 hen_t8 hg8 => ?_
  obtain ⟨hrip8, hk8, -⟩ := hen_t8
  have hm8 := hmu.keep F hb (keeps_img E.hW hk8)
  refine must_gate_exit (by rw [hg8]; exact hdu) hrip8 gout (by rw [hg8]) fun t9 hen_t9 hg9 => ?_
  obtain ⟨hrip9, hk9, -⟩ := hen_t9
  have hm9 := hm8.keep F hb (keeps_img E.hW hk9)
  have hat8 : t8.g.atexit = [] := by rw [hg8, hatu, hg7']; exact hat
  -- `__do_global_dtors_aux`
  refine must_gate_call0 (f := b + BitVec.ofNat 64 L.dtors)
    (js := [.call0 (b + BitVec.ofNat 64 L.fini), .halt ((low32 (u.m.core.read .rax)).setWidth 64)])
    (by rw [hg9, hg8]; exact hdu) hrip9 gout
    (by rw [hg9]; simp [exitJobs, hat8, hfinis]) fun t10 hen_t10 hg10 => ?_
  obtain ⟨hrip10, hal10, hret10, hroom10, hk10, -⟩ := hen_t10
  have hm10 := hm9.keep F hb (keeps_img E.hW hk10)
  have hd10 : t10.g.done = none := by rw [hg10, hg9, hg8]; exact hdu
  refine crt_dtors F E hd10 hm10 hrip10 hal10 hroom10 hret10
    (by rw [hg10, hg9]) fun t11 hg11 hrip11 hm11 => ?_
  -- `_fini`
  refine must_gate_call0 (by rw [hg11]; exact hd10) hrip11 gout (by rw [hg11, hg10])
    fun t12 hen_t12 hg12 => ?_
  obtain ⟨hrip12, hal12, hret12, hroom12, hk12, -⟩ := hen_t12
  have hm12 := hm11.keep F hb (keeps_img E.hW hk12)
  have hd12 : t12.g.done = none := by rw [hg12, hg11]; exact hd10
  refine crt_fini F E.hW hb hd12 hm12 hrip12 hret12 fun t13 hg13 hrip13 _ _ _ => ?_
  -- the end
  refine must_gate_halt (by rw [hg13]; exact hd12) hrip13 gout (by rw [hg13, hg12, hg11])
    fun t14 w hw hrel hg14 => must_done ?_
  have hout : t13.g.out = u.g.out := by rw [hg13, hg12, hg11, hg10, hg9, hg8]
  refine ⟨u.g, low32 (u.m.core.read .rax), w, hg7' ▸ hpost, by rw [hg14], hout ▸ hw,
    fun h => hout ▸ hrel h⟩

end Silmaril.Elf.Link.Dyn.Crt
