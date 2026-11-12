module

public import Silmaril.Proofs.Libc.Ptmalloc.X86sim.Gcc13.Hit
public import Silmaril.Proofs.Libc.Ptmalloc.Versions.V240.TcGet

/-!
# ptmalloc versions, glibc 2.40: `__libc_malloc`'s tcache hit, data only

glibc 2.40's `__libc_malloc` is 2.39's (identical normalised
listings), compiled by gcc 14 at other addresses: the three rip-relative displacements differ
and a longer `nop` moves the count test from offset 328 to 336. So the whole tcache-hit path is
x86sim's generic gcc 13/14 proof (`X86sim.Gcc13.mallocTcacheHitK'`) at the 2.40 data:

* `mallocData240`: the bytes (`V240.mallocCode`) and the path's parameters;
* `mallocSeq240`: the decode facts, by `decide` on the pinned bytes;
* `mallocPin240`: with `tcShape240` and three `rfl`s against `pin240`'s records.

No simulation proof in this module.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Versions.V240

open Silmaril.Libc.Ptmalloc.X86sim
open Silmaril.Libc.Ptmalloc.X86sim.Gcc13

set_option maxRecDepth 10000

/-- **glibc 2.40's `__libc_malloc` tcache-hit path**: `cmpb $0, 0x16550d(%rip)` (→ `+0x165528`,
`__malloc_initialized`), `mov 0x15e0f6(%rip), %r13` (→ `+0x15e140`, the GOT slot of `tcache`'s TLS
offset), `cmp 0x15e529(%rip), %r12` (→ `+0x15e588`, `mp_.tcache_bins`), the count test at 336. -/
def mallocData240 : MallocData :=
  ⟨mallocCode, 0x16550d#32, 0x15e0f6#32, 0x15e529#32, 0x165528, 0x15e140, 0x15e588, 336⟩

/-- The decode facts of the path in the 2.40 bytes. -/
theorem mallocSeq240 : MallocSeq mallocCode 0x16550d#32 0x15e0f6#32 0x15e529#32 0x165528 0x15e140
    0x15e588 336 where
  fit := by decide
  ge := by decide
  rInit := by decide
  rGot := by decide
  rBins := by decide
  d0 := by decide
  d4 := by decide
  d5 := by decide
  d8 := by decide
  d10 := by decide
  d12 := by decide
  d13 := by decide
  d16 := by decide
  d20 := by decide
  d27 := ⟨0x1ff#32, by decide⟩
  d33 := by decide
  d36 := ⟨0x204#32, by decide⟩
  d42 := by decide
  d46 := by decide
  d49 := by decide
  d53 := by decide
  d55 := by decide
  d59 := by decide
  d63 := by decide
  d67 := by decide
  d74 := by decide
  d79 := by decide
  d82 := ⟨0xb8#32, by decide⟩
  d88 := by decide
  d95 := ⟨0xeb#32, by decide, by decide⟩
  c0 := by decide
  c5 := by decide
  c8 := ⟨0xffffff07#32, by decide⟩
  get := mallocTcGet
  e0 := by decide
  e4 := by decide
  e5 := by decide
  e7 := by decide
  e9 := by decide
  e10 := by decide

/-- **What glibc 2.40 supplies to the generic tcache-hit proof.** -/
theorem mallocPin240 : MallocPin pin240 mallocData240 where
  seq := mallocSeq240
  shape := tcShape240
  bins64 := rfl
  init := rfl
  binsAt := rfl

end Silmaril.Libc.Ptmalloc.Versions.V240
