module

public import Silmaril.Libc.X86Alloc.Ladder.Boundary.Defs
public import Silmaril.Libc.X86Alloc.Pinned.Boundary
public import Silmaril.X86.Ladder.Pinned.Thms
public import Silmaril.Libc.X86Alloc.Spec.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryInit
import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryMalloc

/-!
# Rung 08 (`boundary`): results

* `malloc_sat`, `free_sat`: the code meets the loose interface `iface` on `Open.isa`.
* `init`: the loaded static data is the allocator state (one free block covering the arena).
* `code_loaded`, `data_loaded`: the pinned executable loads the layout (kernel evaluation).
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc

theorem malloc_sat : (mallocSpec iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary.malloc_sat

theorem free_sat : (freeSpec iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary.free_sat

theorem init : layout.Init ⊢ₛ iface.mm := Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary.init

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Boundary.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.Boundary.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

end Silmaril.Libc.X86Alloc.Ladder.Boundary
