module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Libc.X86Alloc.Pinned.FirstFit
public import Silmaril.Libc.X86Alloc.Spec.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitEntry
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitRel
import Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFreeRel

/-!
# Rung 05 (first-fit with splitting): results

* `malloc_sat`, `free_sat`: the gcc `-O2` code meets the **first-fit capacity model** `ffCap`
  (liveness: `malloc(n)` succeeds whenever `n ≤ 4096` and some block of the abstract free set has
  `roundUp 16 n` payload bytes) on `Open.isa`. `malloc`'s free-list walk is proved with the loop
  rule `SPEC.loop` (`Silmaril/Raw/Libc/X86Alloc/Ladder/FirstFit{Malloc,Body,TailA,TailB,
  TailC,Entry}.lean`).
* `init`: the loaded `.data` is the one-block free list `ffS0`.
* `code_loaded`, `data_loaded`: the pinned executable loads the layout.

* `malloc_sat_rel`, `free_sat_rel`, `initR`: **functional strength against the relational model
  `ffRel`**: the state is the exact free list; `malloc` returns its first fit (`ffFindB`) and
  leaves `ffTakeB`'s list; `free` pushes the block with the size its header holds. Same machine
  proof as `live` (`malloc_core` is generic in the spec; only the exits differ).

The deterministic `functional` strength stays open: `free` pushes the block with its real size,
held in the client's token, which `RefModel.dealloc` cannot see (see `FirstFit/Live.lean`).
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.FirstFit

open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

theorem malloc_sat :
    (mallocSpecL iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc.malloc_sat

theorem free_sat :
    (freeSpecL iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree.free_sat

theorem init : layout.Init ⊢ₛ iface.mmS ffS0 :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit.init

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.FirstFit.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.FirstFit.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

theorem malloc_sat_rel :
    (mallocSpecR ifaceR).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitMalloc.malloc_sat_rel_full

theorem free_sat_rel :
    (freeSpecR ifaceR).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitFree.free_sat_rel

theorem initR : layout.Init ⊢ₛ ifaceR.mmS relS0 :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit.initR

end Silmaril.Libc.X86Alloc.Ladder.FirstFit
