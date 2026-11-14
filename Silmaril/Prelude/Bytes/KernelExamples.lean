module

public import Silmaril.Prelude.Bytes.Elab.Defs

/-! # Kernel bytes: kernel-only examples

`hello` is the pinned `hello-gcc` (15,960 bytes; SHA-256
`6964f3f23e27cfd2b6c26bd469cb210ff000dd359fc9988138cadc96683065c7`), written out as the
canonical tree by `kbytes_def`. Every proof here is checked by the kernel (`decide +kernel`,
`rfl` or the theorems of `Silmaril.Prelude.Bytes.Thms`); nothing is evaluated natively.

The staged reads (header, then the program header table it locates, then the `PT_INTERP`
string that table points at) are examples of the byte interface, not an ELF parser
(`Silmaril.Elf` owns that). They are the kernel-only examples of hiloopai/silmaril-lean#125
(`Silmaril.Prelude.Bytes.Examples` there), without its native-edge and trust-profile examples.
-/

@[expose] public section

namespace Silmaril.KBytes.KernelExamples

open Silmaril.KBytes

kbytes_def hello from_file "../../../examples/dyn/pinned/hello-gcc"

example : hello.len = 15960 := hello.len_eq

/-! ## Stage 1: the ELF header -/

theorem magic : hello.readLE 0 4 = some 0x464c457f := by decide +kernel
theorem elfClass64 : hello.readLE 4 1 = some 2 := by decide +kernel
theorem typeDyn : hello.readLE 16 2 = some 3 := by decide +kernel
theorem machineX86_64 : hello.readLE 18 2 = some 62 := by decide +kernel
theorem phoff : hello.readLE 32 8 = some 64 := by decide +kernel
theorem shoff : hello.readLE 40 8 = some 13976 := by decide +kernel
theorem phentsize_phnum : hello.readLE 54 4 = some (56 + 13 * 65536) := by decide +kernel

/-- Out of range: one byte past the end. -/
theorem past_end : hello.readLE 15959 2 = none := by decide +kernel

/-! ## Stage 2: the program header table, as a slice -/

/-- The 13 program headers, sharing the file's leaves. -/
noncomputable def phdrs : KBytes := hello.slice 64 (13 * 56)

/-- The second program header is `PT_INTERP` (type 3) at file offset 792, 28 bytes long. -/
theorem interpHeader :
    phdrs.readLE 56 4 = some 3 ∧ phdrs.readLE (56 + 8) 8 = some 792 ∧
      phdrs.readLE (56 + 32) 8 = some 28 := by
  decide +kernel

/-- The slice holds what the file holds at the same place. -/
theorem phdrs_toList : phdrs.toList = (hello.toList.drop 64).take (13 * 56) :=
  toList_slice hello 64 _ hello.wf_true (by rw [hello.len_eq]; decide)

/-! ## Stage 3: the interpreter path, as one wide read -/

theorem interp :
    hello.readLE 792 28 = some (leVal "/lib64/ld-linux-x86-64.so.2\x00".toUTF8.data.toList) := by
  decide +kernel

/-! ## Ropes and canonical forms -/

/-- Cut at an unaligned offset and glued back: a rope with the file's bytes. -/
noncomputable def rope : KBytes := hello.slice 0 5000 ++ hello.slice 5000 (15960 - 5000)

/-- A canonicalised rope is the canonical tree itself: the kernel checks it by evaluation and
one structural comparison. -/
theorem canon_rope : (rope.canon 4096).beq hello = true := by decide +kernel

/-- Window-by-window comparison of differently shaped trees, in the kernel. -/
theorem rope_same : rope.sameBytes 65536 hello = true := by decide +kernel

theorem rope_toList : rope.toList = hello.toList :=
  toList_eq_of_sameBytes 65536 rope hello
    (wf_append (wf_slice _ _ _ hello.wf_true (by rw [hello.len_eq]; decide))
      (wf_slice _ _ _ hello.wf_true (by rw [hello.len_eq]; decide)))
    hello.wf_true rope_same

end Silmaril.KBytes.KernelExamples
