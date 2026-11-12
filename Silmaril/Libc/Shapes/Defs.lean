module

public import Silmaril.Libc.AllocElf.Defs
public import Silmaril.Libc.AllocLoad.Defs
public import Silmaril.Project.Defs

/-!
# Standard problem shapes: allocators in real ELF files

An **ELF allocator row** names a signature level `s` (`AllocSig.Sig`: `mf ⊂ mfc ⊂ mfcr ⊂ full`),
a strength (an abstract relation `T`, `AllocSig.loose` at the base), an ELF file `F` (its bytes:
a pinned shared object, by sha256), how its functions are named (`Syms`: prefix, versions) and a
loading model `LM` (`AllocElf.LoadModel`: the machine, the started process states, the client's
steps):

| name | statement |
|---|---|
| `silmaril.shapes.alloc.elf.contract` | `ElfAllocContract T LM s F S`: `F` binds the functions of `s` and, for some owned regions, invariant and ghost heap, the started image establishes the invariant and every valid POSIX call returns as `T` allows, in the invariant, within the frame (`AllocElf.Contract`) |
| `silmaril.shapes.alloc.elf.posix_safe` | `T := loose`: **POSIX-safe with invariant** (`AllocElf.PosixSafe`; `NULL`/`ENOMEM` always allowed, nothing promised after UB) |
| `….posix_safe.mf`, `.mfc`, `.mfcr`, `.full` | the four levels |
| `silmaril.shapes.alloc.elf.loaded` | `ElfAllocLoaded s F S`: `AllocLoad.Row`, **for every environment whose bound imports satisfy their named contracts, `F` is POSIX-safe at `s` in the concrete loading model** `AllocLoad.model` |
| `….loaded.mf`, `.mfc`, `.mfcr`, `.full` | the four levels |

A row at `s'` gives the row at every `s ≤ s'` (`AllocElf.Thms.reduct`), and a row at a stronger
relation the row at `loose` (`AllocElf.Thms.mono`).

Rows over pinned glibc, jemalloc and mimalloc files instantiate these shapes at the loading model
`Silmaril.Libc.AllocLoad.model` (bound imports with named contracts, `AllocLoad.Row`).
-/

@[expose] public section

namespace Silmaril.Libc.Shapes

open Silmaril.Libc.AllocSig (Rel Sig)
open Silmaril.Libc.AllocElf (LoadModel Syms)

/-- **An ELF file is an allocator at signature `s` and strength `T`** (module doc). -/
@[problem "silmaril.shapes.alloc.elf.contract"
  (title := "An ELF file's exported allocator meets the allocator contract of a signature level at a strength")]
def ElfAllocContract (T : Rel) (LM : LoadModel) (s : Sig) (F : Silmaril.X86.Link.Blob)
    (S : Syms) : Prop :=
  Silmaril.Libc.AllocElf.Contract T LM s F S

/-- **An ELF file is a POSIX-safe allocator at signature `s`** (module doc). -/
@[problem "silmaril.shapes.alloc.elf.posix_safe"
  (title := "An ELF file's exported allocator is POSIX-safe with invariant at a signature level")]
def ElfAllocPosixSafe (LM : LoadModel) (s : Sig) (F : Silmaril.X86.Link.Blob) (S : Syms) : Prop :=
  Silmaril.Libc.AllocElf.PosixSafe LM s F S

/-- **An ELF file is a POSIX-safe allocator at signature `s` in the concrete loading model**, for
every environment whose imports satisfy their named contracts (`AllocLoad.Row`). -/
@[problem "silmaril.shapes.alloc.elf.loaded"
  (title := "An ELF file's exported allocator, loaded with its imports bound to functions meeting named contracts, is POSIX-safe at a signature level")]
def ElfAllocLoaded (s : Sig) (F : Silmaril.X86.Link.Blob) (S : Syms) : Prop :=
  Silmaril.Libc.AllocLoad.Row s F S

end Silmaril.Libc.Shapes

end

silmaril instance silmaril.shapes.alloc.elf.posix_safe.mf
    (title := "POSIX-safe malloc and free") :=
  silmaril.shapes.alloc.elf.posix_safe (s := Silmaril.Libc.AllocSig.Sig.mf)
silmaril instance silmaril.shapes.alloc.elf.posix_safe.mfc
    (title := "POSIX-safe malloc, free and calloc") :=
  silmaril.shapes.alloc.elf.posix_safe (s := Silmaril.Libc.AllocSig.Sig.mfc)
silmaril instance silmaril.shapes.alloc.elf.posix_safe.mfcr
    (title := "POSIX-safe malloc, free, calloc and realloc") :=
  silmaril.shapes.alloc.elf.posix_safe (s := Silmaril.Libc.AllocSig.Sig.mfcr)
silmaril instance silmaril.shapes.alloc.elf.posix_safe.full
    (title := "POSIX-safe malloc, free, calloc, realloc, aligned_alloc, posix_memalign, malloc_usable_size") :=
  silmaril.shapes.alloc.elf.posix_safe (s := Silmaril.Libc.AllocSig.Sig.full)
silmaril instance silmaril.shapes.alloc.elf.loaded.mf
    (title := "POSIX-safe malloc and free, loaded with contracted imports") :=
  silmaril.shapes.alloc.elf.loaded (s := Silmaril.Libc.AllocSig.Sig.mf)
silmaril instance silmaril.shapes.alloc.elf.loaded.mfc
    (title := "POSIX-safe malloc, free and calloc, loaded with contracted imports") :=
  silmaril.shapes.alloc.elf.loaded (s := Silmaril.Libc.AllocSig.Sig.mfc)
silmaril instance silmaril.shapes.alloc.elf.loaded.mfcr
    (title := "POSIX-safe malloc, free, calloc and realloc, loaded with contracted imports") :=
  silmaril.shapes.alloc.elf.loaded (s := Silmaril.Libc.AllocSig.Sig.mfcr)
silmaril instance silmaril.shapes.alloc.elf.loaded.full
    (title := "POSIX-safe malloc, free, calloc, realloc, aligned_alloc, posix_memalign, malloc_usable_size, loaded with contracted imports") :=
  silmaril.shapes.alloc.elf.loaded (s := Silmaril.Libc.AllocSig.Sig.full)
