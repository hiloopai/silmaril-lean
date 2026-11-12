module

public import Silmaril.Libc.Ptmalloc.Algo.Step.Defs

/-!
# ptmalloc algorithm: `systrim` and `heap_trim`

glibc 2.39 `systrim (pad, av)` (main arena): release whole pages at the top of the break when
the top chunk has more than `pad + MINSIZE` spare bytes and the break is where malloc left it.
M7: callers only call it when `chunksize (top) ≥ mp_.trim_threshold` (`_int_free_maybe_consolidate`),
so `top_size - MINSIZE - 1` does not wrap; the model returns unchanged when it would.

`heap_trim (heap, pad)` (non-main arenas): the shrink part (`shrink_heap` of the current heap,
when `chunksize (top) ≥ mp_.trim_threshold`). **Model gap (documented):** glibc's first loop,
which deletes a whole heap whose only chunk is top and moves top to the previous heap, is not
modelled yet (multi-threaded paths only).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable (C : Config)

/-- **`systrim (pad, av)`**. -/
def systrim (l : Local) (pad : Nat) : Res Local :=
  let ts := l.av.tiles
  let topSize := ts.topSize
  if topSize < C.minSize + 1 then .ok l else
  let area := topSize - C.minSize - 1
  if area ≤ pad then .ok l else
  let extra := alignDown (area - pad) C.page
  if extra = 0 then .ok l else
  if l.kernel.brk ≠ ts.top + topSize then .ok l else
  match l.kernel.shrink extra with
  | (none, k) => .ok { l with kernel := k }
  | (some (), k) =>
    .ok { l with
      kernel := k
      av := { l.av with tiles := { ts with topSize := topSize - extra, systemMem := ts.systemMem - extra } } }

/-- **`heap_trim (heap, pad)`**, shrink part (see the module note). -/
def heapTrim (l : Local) (pad : Nat) : Res Local :=
  let ts := l.av.tiles
  let topSize := ts.topSize
  if topSize < l.shared.mm.mp.trimThreshold then .ok l else
  if topSize < C.minSize + 1 then .ok l else
  let area := topSize - C.minSize - 1
  if area ≤ pad then .ok l else
  let extra := alignDown (area - pad) C.page
  if extra = 0 then .ok l else
  match l.av.heaps with
  | [] => .error .internal
  | (h, hs) :: rest =>
    match l.kernel.mprotect with
    | (false, k) => .ok { l with kernel := k }
    | (true, k) =>
      .ok { l with
        kernel := k
        av := { l.av with
          heaps := (h, hs - extra) :: rest
          reserve := l.av.reserve + extra
          tiles := { ts with topSize := topSize - extra, systemMem := ts.systemMem - extra } } }

end Silmaril.Libc.Ptmalloc.Algo
