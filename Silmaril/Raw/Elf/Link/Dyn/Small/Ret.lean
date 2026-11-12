module

public import Silmaril.Elf.Link.Dyn.Small.Defs
public import Silmaril.Elf.Link.Dyn.Hello.Cert
public import Silmaril.Raw.Elf.Link.Dyn.Crt.ConstMain

/-! # `return 0` and `return 42`, dynamically linked, gcc and clang: verified

For each of the four executables (`ret0Gcc`, `ret0Clang`, `ret42Gcc`, `ret42Clang`):

* the per-binary checks, each one `decide +kernel`: the headers (`_info`), the references
  (`_refs`), **the binding certificate** against the cached glibc lookup tables (`_slots_K`),
  the C runtime's placement (`_ok`), the image facts (`_img`) and `main`'s listing (`_main`);
* **`_exits`**: under the loader relation (eager binding, any bases, any `libc.so.6`/`ld.so`
  agreeing with the pinned chunks), from every documented initial state with an empty
  `stdout`, every run of the process ends with exit status `0` (resp. `42`) and nothing written
  to `stdout`.

Everything else is the generic C runtime proof (`Crt.exe_const`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Hello
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt

/-! ## `ret0Gcc` -/

theorem ret0Gcc_info : finfo ret0GccFile = some ret0GccInfo := by decide +kernel
theorem ret0Gcc_refs : refsHold ret0GccFile ret0GccInfo ret0GccRefs = true := by decide +kernel
theorem ret0Gcc_slots_K :
    slotsWith (resolveK [exeFacts ret0GccRefs, libcFacts, ldFacts]) false ret0GccFile ret0GccInfo =
      some ret0GccSlots := by decide +kernel
theorem ret0Gcc_ok : ret0GccLayout.ok = true := by decide +kernel
theorem ret0Gcc_img : ret0GccLayout.imageOk ret0GccFile ret0GccInfo ret0GccTextPh ret0GccRoPh ret0GccRwPh ret0GccSlots 0x2a200 0x472c0 =
    true := by decide +kernel
theorem ret0Gcc_main : listingOk ret0GccLayout.cMain (constMainL true none) = true := by decide +kernel

theorem ret0Gcc_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks) :
    slots [ret0GccFile, Fc, Fl] false ret0GccFile ret0GccInfo = some ret0GccSlots := by
  have := slots_of_known (ks := [⟨ret0GccFile, ret0GccInfo, exeFacts ret0GccRefs⟩, libcKnown Fc, ldKnown Fl])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok ret0Gcc_info ret0Gcc_refs
      · exact libcKnown_ok hc
      · exact ldKnown_ok hl) ret0Gcc_slots_K
  simpa [libcKnown, ldKnown] using this

/-- **`ret0Gcc` exits with status 0 and writes nothing.** -/
theorem ret0Gcc_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res gate : Word} {ifn : Word → Option Word} {rel : Bool} {s : PState}
    (hload : ExeLoaded [ret0GccFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : Placed ret0GccLayout b lb gate 0x2a200 0x472c0)
    (hs : AtEntry ret0GccLayout (smallWorld ret0GccLayout b lb gate 0x2a200 0x472c0 rel) b s)
    (hout : s.g.out = []) :
    MustQ (smallWorld ret0GccLayout b lb gate 0x2a200 0x472c0 rel) (fun u => u.g.done = some (0, [])) s := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (exe_const ret0Gcc_ok ret0Gcc_info (ret0Gcc_slots hc hl) ret0Gcc_img ret0Gcc_main hload P hs)
  rintro u ⟨w, hd, hw, -⟩
  rw [hout, List.prefix_nil] at hw
  rw [hd, hw]; rfl

/-! ## `ret0Clang` -/

theorem ret0Clang_info : finfo ret0ClangFile = some ret0ClangInfo := by decide +kernel
theorem ret0Clang_refs : refsHold ret0ClangFile ret0ClangInfo ret0ClangRefs = true := by decide +kernel
theorem ret0Clang_slots_K :
    slotsWith (resolveK [exeFacts ret0ClangRefs, libcFacts, ldFacts]) false ret0ClangFile ret0ClangInfo =
      some ret0ClangSlots := by decide +kernel
theorem ret0Clang_ok : ret0ClangLayout.ok = true := by decide +kernel
theorem ret0Clang_img : ret0ClangLayout.imageOk ret0ClangFile ret0ClangInfo ret0ClangTextPh ret0ClangRoPh ret0ClangRwPh ret0ClangSlots 0x2a200 0x472c0 =
    true := by decide +kernel
theorem ret0Clang_main : listingOk ret0ClangLayout.cMain (constMainL false none) = true := by decide +kernel

theorem ret0Clang_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks) :
    slots [ret0ClangFile, Fc, Fl] false ret0ClangFile ret0ClangInfo = some ret0ClangSlots := by
  have := slots_of_known (ks := [⟨ret0ClangFile, ret0ClangInfo, exeFacts ret0ClangRefs⟩, libcKnown Fc, ldKnown Fl])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok ret0Clang_info ret0Clang_refs
      · exact libcKnown_ok hc
      · exact ldKnown_ok hl) ret0Clang_slots_K
  simpa [libcKnown, ldKnown] using this

/-- **`ret0Clang` exits with status 0 and writes nothing.** -/
theorem ret0Clang_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res gate : Word} {ifn : Word → Option Word} {rel : Bool} {s : PState}
    (hload : ExeLoaded [ret0ClangFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : Placed ret0ClangLayout b lb gate 0x2a200 0x472c0)
    (hs : AtEntry ret0ClangLayout (smallWorld ret0ClangLayout b lb gate 0x2a200 0x472c0 rel) b s)
    (hout : s.g.out = []) :
    MustQ (smallWorld ret0ClangLayout b lb gate 0x2a200 0x472c0 rel) (fun u => u.g.done = some (0, [])) s := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (exe_const ret0Clang_ok ret0Clang_info (ret0Clang_slots hc hl) ret0Clang_img ret0Clang_main hload P hs)
  rintro u ⟨w, hd, hw, -⟩
  rw [hout, List.prefix_nil] at hw
  rw [hd, hw]; rfl

/-! ## `ret42Gcc` -/

theorem ret42Gcc_info : finfo ret42GccFile = some ret42GccInfo := by decide +kernel
theorem ret42Gcc_refs : refsHold ret42GccFile ret42GccInfo ret42GccRefs = true := by decide +kernel
theorem ret42Gcc_slots_K :
    slotsWith (resolveK [exeFacts ret42GccRefs, libcFacts, ldFacts]) false ret42GccFile ret42GccInfo =
      some ret42GccSlots := by decide +kernel
theorem ret42Gcc_ok : ret42GccLayout.ok = true := by decide +kernel
theorem ret42Gcc_img : ret42GccLayout.imageOk ret42GccFile ret42GccInfo ret42GccTextPh ret42GccRoPh ret42GccRwPh ret42GccSlots 0x2a200 0x472c0 =
    true := by decide +kernel
theorem ret42Gcc_main : listingOk ret42GccLayout.cMain (constMainL true (some 0x2a#32)) = true := by decide +kernel

theorem ret42Gcc_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks) :
    slots [ret42GccFile, Fc, Fl] false ret42GccFile ret42GccInfo = some ret42GccSlots := by
  have := slots_of_known (ks := [⟨ret42GccFile, ret42GccInfo, exeFacts ret42GccRefs⟩, libcKnown Fc, ldKnown Fl])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok ret42Gcc_info ret42Gcc_refs
      · exact libcKnown_ok hc
      · exact ldKnown_ok hl) ret42Gcc_slots_K
  simpa [libcKnown, ldKnown] using this

/-- **`ret42Gcc` exits with status 42 and writes nothing.** -/
theorem ret42Gcc_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res gate : Word} {ifn : Word → Option Word} {rel : Bool} {s : PState}
    (hload : ExeLoaded [ret42GccFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : Placed ret42GccLayout b lb gate 0x2a200 0x472c0)
    (hs : AtEntry ret42GccLayout (smallWorld ret42GccLayout b lb gate 0x2a200 0x472c0 rel) b s)
    (hout : s.g.out = []) :
    MustQ (smallWorld ret42GccLayout b lb gate 0x2a200 0x472c0 rel) (fun u => u.g.done = some (42, [])) s := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (exe_const ret42Gcc_ok ret42Gcc_info (ret42Gcc_slots hc hl) ret42Gcc_img ret42Gcc_main hload P hs)
  rintro u ⟨w, hd, hw, -⟩
  rw [hout, List.prefix_nil] at hw
  rw [hd, hw]; rfl

/-! ## `ret42Clang` -/

theorem ret42Clang_info : finfo ret42ClangFile = some ret42ClangInfo := by decide +kernel
theorem ret42Clang_refs : refsHold ret42ClangFile ret42ClangInfo ret42ClangRefs = true := by decide +kernel
theorem ret42Clang_slots_K :
    slotsWith (resolveK [exeFacts ret42ClangRefs, libcFacts, ldFacts]) false ret42ClangFile ret42ClangInfo =
      some ret42ClangSlots := by decide +kernel
theorem ret42Clang_ok : ret42ClangLayout.ok = true := by decide +kernel
theorem ret42Clang_img : ret42ClangLayout.imageOk ret42ClangFile ret42ClangInfo ret42ClangTextPh ret42ClangRoPh ret42ClangRwPh ret42ClangSlots 0x2a200 0x472c0 =
    true := by decide +kernel
theorem ret42Clang_main : listingOk ret42ClangLayout.cMain (constMainL false (some 0x2a#32)) = true := by decide +kernel

theorem ret42Clang_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks) :
    slots [ret42ClangFile, Fc, Fl] false ret42ClangFile ret42ClangInfo = some ret42ClangSlots := by
  have := slots_of_known (ks := [⟨ret42ClangFile, ret42ClangInfo, exeFacts ret42ClangRefs⟩, libcKnown Fc, ldKnown Fl])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok ret42Clang_info ret42Clang_refs
      · exact libcKnown_ok hc
      · exact ldKnown_ok hl) ret42Clang_slots_K
  simpa [libcKnown, ldKnown] using this

/-- **`ret42Clang` exits with status 42 and writes nothing.** -/
theorem ret42Clang_exits {Fc Fl : Blob} (hc : ChunksOf Fc libcChunks) (hl : ChunksOf Fl ldChunks)
    {b lb ldb res gate : Word} {ifn : Word → Option Word} {rel : Bool} {s : PState}
    (hload : ExeLoaded [ret42ClangFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : Placed ret42ClangLayout b lb gate 0x2a200 0x472c0)
    (hs : AtEntry ret42ClangLayout (smallWorld ret42ClangLayout b lb gate 0x2a200 0x472c0 rel) b s)
    (hout : s.g.out = []) :
    MustQ (smallWorld ret42ClangLayout b lb gate 0x2a200 0x472c0 rel) (fun u => u.g.done = some (42, [])) s := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (exe_const ret42Clang_ok ret42Clang_info (ret42Clang_slots hc hl) ret42Clang_img ret42Clang_main hload P hs)
  rintro u ⟨w, hd, hw, -⟩
  rw [hout, List.prefix_nil] at hw
  rw [hd, hw]; rfl

end Silmaril.Elf.Link.Dyn.Small
