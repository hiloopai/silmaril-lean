module

public import Silmaril.Libc.Ptmalloc.Defs
public import Silmaril.Libc.Ptmalloc.Heap.Thms
public import Silmaril.Libc.Ptmalloc.Rep.Thms
public import Silmaril.Libc.Ptmalloc.Version.Thms
public import Silmaril.Libc.Ptmalloc.Algo.Thms

/-!
# ptmalloc: theorems

Proved so far (standard axioms only): the frame rule `Silmaril.Data.Frag.holds_frame` (with
`MemView.load_congr`, `Frag.holds_append`, `Frag.holds_sub`), the composition theorems
`ArenaWF.withFast`/`withBins`/`withUnsorted`/`withTiles`, `envFrag_frame`, `surrInv_step`, the
triple rules `Mach.Triple.conseq`/`seq`/`frame`/`cases`, and `pin239_ok`. Every other statement is a named
`Task` (see `Silmaril.Libc.Ptmalloc.Defs`).
-/
