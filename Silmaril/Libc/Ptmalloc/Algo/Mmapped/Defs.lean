module

public import Silmaril.Libc.Ptmalloc.Algo.Step.Defs

/-!
# ptmalloc algorithm: `mmap`ed chunks

glibc 2.39 `sysmalloc_mmap (nb, pagesize, 0, av)` (a chunk of its own mapping: `size =
ALIGN_UP (nb + SIZE_SZ, pagesize)`, `prev_size` 0 since `MALLOC_ALIGNMENT == CHUNK_HDR_SZ`,
`mp_` counters), `munmap_chunk (p)` and `mremap_chunk (p, nb)`. These touch only the shared part
(`MmapSt`) and the kernel: no arena.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- **`sysmalloc_mmap (nb, pagesize, 0, av)`**: the payload, or `none` (the kernel refused, or the
size wrapped); the kernel's answer is consumed either way. -/
def sysmallocMmap (l : Local) (nb : Nat) : Option Nat × Local :=
  let size := alignUp (nb + C.sizeSz) C.page
  if size ≤ nb then (none, l) else
  match l.kernel.mmap C.page size with
  | (none, k) => (none, { l with kernel := k })
  | (some a, k) =>
    (some (a + C.hdr),
      { l with kernel := k, shared := { l.shared with mm := l.shared.mm.add ⟨a, size, .client⟩ } })

/-- The `mmap`ed chunk at `c`, if any. -/
def mmFind? (l : Local) (c : Nat) : Option Chunk := l.shared.mm.chunks.find? (·.addr = c)

/-- **`munmap_chunk (p)`** of the `mmap`ed chunk at `c`. -/
def munmapChunk (l : Local) (c : Nat) : Res Local :=
  match mmFind? l c with
  | none => .error .munmapInvalidPointer
  | some ch =>
    if c % C.page ≠ 0 ∨ ch.size % C.page ≠ 0 then .error .munmapInvalidPointer else
    .ok { l with
      kernel := l.kernel.munmap c ch.size
      shared := { l.shared with mm := l.shared.mm.remove ch } }

/-- **`mremap_chunk (p, nb)`** of the `mmap`ed chunk at `c`: the new chunk's address (0: refused). -/
def mremapChunk (l : Local) (c nb : Nat) : Res (Nat × Local) :=
  match mmFind? l c with
  | none => .error .mremapInvalidPointer
  | some ch =>
    if c % C.page ≠ 0 ∨ ch.size % C.page ≠ 0 then .error .mremapInvalidPointer else
    let newSize := alignUp (nb + C.sizeSz) C.page
    if newSize = ch.size then .ok (c, l) else
    match l.kernel.mremap C.page c ch.size newSize with
    | (none, k) => .ok (0, { l with kernel := k })
    | (some a, k) =>
      let mm := l.shared.mm
      let mem := mm.mp.mmappedMem + newSize - ch.size
      .ok (a, { l with
        kernel := k
        shared := { l.shared with mm :=
          { chunks := ⟨a, newSize, ch.use⟩ :: mm.chunks.erase ch
            mp := { mm.mp with mmappedMem := mem, maxMmappedMem := max mem mm.mp.maxMmappedMem } } } })

end Silmaril.Libc.Ptmalloc.Algo
