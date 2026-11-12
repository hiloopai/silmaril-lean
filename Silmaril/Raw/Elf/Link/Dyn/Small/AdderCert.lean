module

public import Silmaril.Elf.Link.Dyn.Small.Adder
public import Silmaril.Elf.Link.Dyn.Small.Libc
public import Silmaril.Elf.Link.Dyn.Hello.Cert
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Extra
public import Silmaril.Elf.Link.Dyn.Glibc.Thms

/-! # The adder: the per-binary checks

Each one `decide +kernel`: headers, references, the binding certificate against the glibc
lookup facts of `Small.Libc` (themselves checked on the sparse chunks), the runtime layout,
the image facts and the extra facts (PLT stubs and their slots). -/

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

/-! ## glibc, for these references -/

theorem libcS_info_sparse : dynInfo.run (sparseRead libcChunksS) = some libcInfo := by decide +kernel
theorem ldS_info_sparse : dynInfo.run (sparseRead ldChunksS) = some ldInfo := by decide +kernel
theorem libcS_facts_sparse : factsHold libcChunksS libcInfo libcFactsS = true := by decide +kernel
theorem ldS_facts_sparse : factsHold ldChunksS ldInfo ldFactsS = true := by decide +kernel

theorem libcKnownS_ok {Fc : Blob} (hc : ChunksOf Fc libcChunksS) :
    (Known.mk Fc libcInfo libcFactsS).Ok :=
  ⟨run_sparse hc libcS_info_sparse, fun e he => facts_of libcS_facts_sparse hc e he⟩

theorem ldKnownS_ok {Fl : Blob} (hl : ChunksOf Fl ldChunksS) :
    (Known.mk Fl ldInfo ldFactsS).Ok :=
  ⟨run_sparse hl ldS_info_sparse, fun e he => facts_of ldS_facts_sparse hl e he⟩

/-! ## `adderClang` -/

/-- `printf@plt` and `__isoc99_scanf@plt` (`.plt`, the `jmp` through the GOT). -/
def adderClangStubs : List (Nat × List Byte) :=
  [(0x1030, [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00]), (0x1040, [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00])]

/-- Their slots: `printf`, `__isoc99_scanf` in `libc.so.6`. -/
def adderClangGot : List (Nat × Nat) := [(0x4000, 0x60100), (0x4008, 0x5fe10)]

theorem adderClang_info : finfo adderClangFile = some adderClangInfo := by decide +kernel
theorem adderClang_refs : refsHold adderClangFile adderClangInfo adderClangRefs = true := by
  decide +kernel
theorem adderClang_slots_K :
    slotsWith (resolveK [exeFacts adderClangRefs, libcFactsS, ldFactsS]) false adderClangFile
      adderClangInfo = some adderClangSlots := by decide +kernel
theorem adderClang_ok : adderClangLayout.ok = true := by decide +kernel
theorem adderClang_img : adderClangLayout.imageOk adderClangFile adderClangInfo adderClangTextPh
    adderClangRoPh adderClangRwPh adderClangSlots 0x2a200 0x472c0 = true := by decide +kernel
theorem adderClang_extra : extraOk adderClangFile adderClangInfo adderClangTextPh adderClangRwPh
    adderClangSlots adderClangStubs adderClangGot = true := by decide +kernel

theorem adderClang_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS) (hl : ChunksOf Fl ldChunksS) :
    slots [adderClangFile, Fc, Fl] false adderClangFile adderClangInfo = some adderClangSlots := by
  have := slots_of_known (ks := [⟨adderClangFile, adderClangInfo, exeFacts adderClangRefs⟩,
      ⟨Fc, libcInfo, libcFactsS⟩, ⟨Fl, ldInfo, ldFactsS⟩])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok adderClang_info adderClang_refs
      · exact libcKnownS_ok hc
      · exact ldKnownS_ok hl) adderClang_slots_K
  simpa using this

end Silmaril.Elf.Link.Dyn.Small
