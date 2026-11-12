-- variant-of: glibc.hello.gcc | style: hello-direct | see-also: Silmaril.Raw.Elf.Link.Dyn.Program.Examples.Hello, Silmaril.Raw.Elf.Link.Dyn.Program.StdExe.Examples.HelloGcc
module

public import Silmaril.Raw.Elf.Link.Dyn.Hello.GccFini

/-! # hello-gcc: the whole process -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Hello

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Proc

/-- The kernel's part of the initial state (System V process entry): `rip` at `e_entry`, an
aligned stack with `argc` on top and room below it, and the library's initial state. -/
structure GccStartState (W : World) (b : Word) (s : PState) (argc : Word) : Prop where
  rip : s.m.core.rip = b + 0x1080#64
  al : (s.m.core.read .rsp).toNat % 16 = 0
  room : StackRoom W s.m.memory (s.m.core.read .rsp)
  argc : s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [argc])
  ghost : s.g = { jobs := [], out := [], atexit := [], done := none }

/-- What the run must end with: exit status 0, and `"hello, world\n"` written to fd 1 (a
prefix of it if writes may fail). -/
def HelloDone (rel : Bool) : PState → Prop :=
  Ended 0 fun w => w <+: helloNL ∧ (rel = true → w = helloNL)

/-- Enters → `Cb`. -/
theorem cb_of_enters {b lb gate : Word} {rel : Bool} (E : GccEnv b lb gate) {s t : PState} {f : Word}
    (h : Enters (gccWorld b lb gate rel) s t f) (hm : GccMem b lb s.m.memory)
    (hd : t.g.done = none) : Cb (gccWorld b lb gate rel) b lb t f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hm.keep E.hb (by simpa [gccWorld_inImage] using keeps_img h.2.2.2.2.1), hd⟩

theorem keepsImg {b lb gate : Word} {rel : Bool} {m m' : Memory}
    (h : Keeps (gccWorld b lb gate rel).Kept m m') : Keeps (GccImg b) m m' := by
  simpa [gccWorld_inImage] using keeps_img h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **hello-gcc, the whole run**: from the kernel's entry state with the loaded image, every
run of the process (with glibc's imports as their loose contracts) terminates, with exit
status 0 and `"hello, world\n"` written to fd 1 (a prefix of it if writes may fail). -/
theorem gcc_run {b lb gate : Word} {rel : Bool} (E : GccEnv b lb gate) {s : PState} {argc : Word}
    (hm : GccMem b lb s.m.memory) (hbs : GccBss b s.m.memory)
    (hs : GccStartState (gccWorld b lb gate rel) b s argc) :
    MustQ (gccWorld b lb gate rel) (HelloDone rel) s := by
  have hd0 : s.g.done = none := by rw [hs.ghost]
  have hgo : ¬ (gccWorld b lb gate rel).InImage gate.toNat := by
    simpa [gccWorld_inImage] using E.gate_out
  refine gcc_start E hd0 hm hs.rip hs.al hs.room hs.argc ?_
  intro t1 hg1 hrip1 hm1 hk1 habi1 hrdi1 hrsi1 hrdx1
  have hbs1 := hbs.keep E.hb hk1
  have hd1 : t1.g.done = none := by rw [hg1]; exact hd0
  -- __libc_start_main
  refine must_fn hd1 (by rw [hrip1]; simpa [gccWorld_inImage] using E.lsm_out)
    (by rw [hrip1]; simpa [gccWorld] using Ne.symm E.gate_lsm) rfl (f := .libcStartMain)
    (by rw [hrip1]; simp [gccWorld]) (fun r => Iff.rfl) habi1 ?_
  rintro t2 ⟨⟨hrip2, hk2, -⟩, hg2⟩
  have hm2 := hm1.keep E.hb (keepsImg hk2)
  have hbs2 := hbs1.keep E.hb (keepsImg hk2)
  simp only [gccWorld, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hrdi1] at hg2
  have hd2 : t2.g.done = none := by rw [hg2]; exact hd1
  -- _init
  refine gate_call hd2 (by rw [hrip2]; exact hgo) hrip2 (by rw [hg2]) ?_
  intro t3 he3 _ _ _ hg3
  have hd3 : t3.g.done = none := by rw [hg3]; exact hd2
  have hm3 := hm2.keep E.hb (keepsImg he3.2.2.2.2.1)
  have hbs3 := hbs2.keep E.hb (keepsImg he3.2.2.2.2.1)
  refine gcc_init E (cb_of_enters E he3 hm2 hd3) ?_
  intro u3 hru3 hgu3 hmu3
  have hdu3 : u3.g.done = none := by rw [hgu3]; exact hd3
  -- frame_dummy
  refine gate_call hdu3 (by rw [hru3]; exact hgo) hru3 (by rw [hgu3, hg3]) ?_
  intro t4 he4 _ _ _ hg4
  have hd4 : t4.g.done = none := by rw [hg4]; exact hdu3
  have hm4 := (hmu3 ▸ hm3).keep E.hb (keepsImg he4.2.2.2.2.1)
  have hbs4 := (hmu3 ▸ hbs3).keep E.hb (keepsImg he4.2.2.2.2.1)
  refine gcc_frameDummy E (cb_of_enters E he4 (hmu3 ▸ hm3) hd4) ?_
  intro u4 hru4 hgu4 hmu4
  have hdu4 : u4.g.done = none := by rw [hgu4]; exact hd4
  -- main
  refine gate_main hdu4 (by rw [hru4]; exact hgo) hru4 (by rw [hgu4, hg4]) ?_
  intro t5 he5 _ _ _ hg5
  have hd5 : t5.g.done = none := by rw [hg5]; exact hdu4
  have hm5 := (hmu4 ▸ hm4).keep E.hb (keepsImg he5.2.2.2.2.1)
  have hbs5 := (hmu4 ▸ hbs4).keep E.hb (keepsImg he5.2.2.2.2.1)
  refine gcc_main E (cb_of_enters E he5 (hmu4 ▸ hm4) hd5) ?_
  intro u5 hru5 hju5 hau5 hdu5 hout5 hrax5 hku5
  have hmu5 := hm5.keep E.hb hku5
  have hbsu5 := hbs5.keep E.hb hku5
  -- exit (eax = 0)
  refine gate_exitRax hdu5 (by rw [hru5]; exact hgo) hru5 (by rw [hju5, hg5]) ?_
  rintro t6 ⟨hrip6, hk6, -⟩ hg6
  rw [hrax5] at hg6
  have hd6 : t6.g.done = none := by rw [hg6]; exact hdu5
  have hm6 := hmu5.keep E.hb (keepsImg hk6)
  have hbs6 := hbsu5.keep E.hb (keepsImg hk6)
  refine gate_exit hd6 (by rw [hrip6]; exact hgo) hrip6 (by rw [hg6]) ?_
  rintro t7 ⟨hrip7, hk7, -⟩ hg7
  have hat : u5.g.atexit = [] := by
    rw [hau5, hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  simp only [exitJobs, hg6, hat, gccWorld, List.reverse_nil, List.map_nil, List.map_cons,
    List.nil_append, List.cons_append] at hg7
  have hd7 : t7.g.done = none := by rw [hg7]; exact hdu5
  have hm7 := hm6.keep E.hb (keepsImg hk7)
  have hbs7 := hbs6.keep E.hb (keepsImg hk7)
  -- __do_global_dtors_aux
  refine gate_call0 hd7 (by rw [hrip7]; exact hgo) hrip7 (by rw [hg7]) ?_
  intro t8 he8 hg8
  have hd8 : t8.g.done = none := by rw [hg8]; exact hd7
  have hbs8 := hbs7.keep E.hb (keepsImg he8.2.2.2.2.1)
  have hat8 : t8.g.atexit = [] := by rw [hg8, hg7]
  refine gcc_dtors E (cb_of_enters E he8 hm7 hd8) hbs8 hat8 ?_
  intro u8 hru8 hgu8 hmu8
  have hdu8 : u8.g.done = none := by rw [hgu8]; exact hd8
  -- _fini
  refine gate_call0 hdu8 (by rw [hru8]; exact hgo) hru8 (by rw [hgu8, hg8]) ?_
  intro t9 he9 hg9
  have hd9 : t9.g.done = none := by rw [hg9]; exact hdu8
  refine gcc_fini E (cb_of_enters E he9 hmu8 hd9) ?_
  intro u9 hru9 hgu9
  have hdu9 : u9.g.done = none := by rw [hgu9]; exact hd9
  -- the end
  refine gate_halt hdu9 (by rw [hru9]; exact hgo) hru9 (by rw [hgu9, hg9]) ?_
  intro t10 w hw hwr hg10
  refine must_done ⟨w, by rw [hg10]; rfl, ?_⟩
  have hout : u9.g.out = u5.g.out := by
    rw [hgu9, hg9, hgu8, hg8, hg7]
  have hout0 : t5.g.out = [] := by
    rw [hg5, hgu4, hg4, hgu3, hg3, hg2, hg1, hs.ghost]
  rw [hout] at hw hwr
  rw [hout0] at hout5
  rcases hout5 with h | ⟨hrel, p, hp, h⟩
  · rw [h, List.nil_append] at hw hwr
    exact ⟨hw, fun hr => hwr (by simpa [gccWorld] using hr)⟩
  · rw [h, List.nil_append] at hw
    exact ⟨hw.trans hp, fun hr => by rw [hrel] at hr; cases hr⟩

theorem gcc_not_lazy {Fs : List Blob} {bases : List Word} {ifn : Word → Option Word} {lazy : Bool}
    {res : Word} {mem : Memory} (h : ExeLoaded (gccFile :: Fs) bases ifn lazy res mem) :
    lazy = false := by
  obtain ⟨f, b', i, D, T, hf, -, hi, hlz, -⟩ := h
  simp only [List.head?_cons, Option.some.injEq] at hf
  subst hf
  rw [gcc_info_f, Option.some.injEq] at hi
  subst hi
  cases lazy
  · rfl
  · exact absurd (hlz rfl) (by rw [gcc_bindNow]; decide)

/-- **hello-gcc, from the loader relation.** For every `libc.so.6` and `ld.so` that agree with
the pinned chunks (`ChunksOf`), every load base of the three objects, every ifunc choice,
every lazy-binding resolver address, either binding mode the environment may pick (only eager
is possible: `DF_BIND_NOW`), every callback gate and I/O environment: if the memory is what the
loader relation says and the entry state is the kernel's, then every run ends with status 0
having written `"hello, world\n"` (or, if writes may fail, a prefix of it). -/
theorem hello_gcc {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res gate : Word} {ifn : Word → Option Word} {lazy rel : Bool}
    (E : GccEnv b lb gate) {s : PState} {argc : Word}
    (hload : ExeLoaded [gccFile, Fc, Fl] [b, lb, ldb] ifn lazy res s.m.memory)
    (hs : GccStartState (gccWorld b lb gate rel) b s argc) :
    MustQ (gccWorld b lb gate rel) (HelloDone rel) s := by
  have := gcc_not_lazy hload
  subst this
  exact gcc_run E (gccMem_of_loaded hc hl hload) (gccBss_of_loaded hc hl hload) hs

end Silmaril.Elf.Link.Dyn.Hello
