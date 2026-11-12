module

public import Silmaril.Libc.Ptmalloc.Algo.Realloc.Defs
public import Silmaril.Libc.Ptmalloc.Algo.Arena.Defs

/-!
# ptmalloc: the algorithm model `ptmalloc C`

`ptmalloc C : Ops C` assembles the bodies of `Silmaril.Libc.Ptmalloc.Algo.*` (one module each:
`Step`, `Consolidate`, `Trim`, `Free`, `Mmapped`, `Sys`, `Malloc`, `Realloc`, `Arena`) for a
configuration `C`. The world-level calls are `Ops.malloc`, `Ops.free`, `Ops.calloc`,
`Ops.realloc` of `Silmaril.Libc.Ptmalloc.Algo.Defs`. Everything is executable (`#eval`), with the
kernel's answers as data (`KOracle`); `initWorld` is the load-time state.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- **The algorithm model of ptmalloc** for the configuration `C`. -/
def ptmalloc : Ops C where
  ptmallocInit := ptmallocInit
  tcacheInit := tcacheInit C
  arenaGet := arenaGet C
  arenaRetry := arenaRetry C
  intMalloc := intMalloc C
  intFree := intFree C
  intRealloc := intRealloc C
  sysmalloc := sysmalloc C
  systrim := systrim C
  consolidate := consolidate C
  munmapChunk := munmapChunk C
  mremapChunk := mremapChunk C

/-- **The load-time state**: one thread `tid`, `main_arena` at `mainArena` with no heap, `mp_` at
its defaults, the break at `brk` (page-aligned, at least a page), the kernel's answers `o`.
The kernel's one mapping is libc's `main_arena` (`stateSize` bytes at `mainArena`): the kernel
never hands it out again (without it `_int_new_arena` could place an arena at `main_arena`). -/
def initWorld (mainArena tid brk : Nat) (o : KOracle) : World where
  mainArena := mainArena
  arenas := fun a => if a = mainArena then some
    { tiles := { start := 0, chunks := [], top := 0, topSize := 0, noncontig := false,
                 systemMem := 0, maxSystemMem := 0 }
      fast := { lists := fun _ => [], haveFast := false }
      bins := { lists := fun _ => [], binmap := fun _ => false }
      unsorted := { list := [], lastRem := 0 } } else none
  tids := [tid]
  threads := fun _ => {}
  shared := { init := false, key := 0,
              mm := { mp := { trimThreshold := C.trimThreshold, mmapThreshold := C.mmapThreshold } } }
  kernel := { brkStart := brk, brk := brk, maps := [(mainArena, C.stateSize)], oracle := o }

end Silmaril.Libc.Ptmalloc.Algo
