module

public import Silmaril.Libc.Ptmalloc.Version.Defs
public import Silmaril.Libc.X86Alloc.Spec.Defs

/-!
# ptmalloc: the bridge to the allocator institution

Layer (a) is the allocator institution of `Silmaril.Libc.X86Alloc.Spec` /
`Silmaril.Libc.Shapes.Alloc`: `safe` (loose `Iface` with tokens), `live` (`CapModel`),
`functional`/`functional_rel` (`RefModel`/`RelModel`), and `model` (`HeapModel`: an
authoritative live set, which is what ptmalloc's header reads need, see the token finding in
`Silmaril.Libc.Shapes.Alloc.Defs`).

* `relModel C A tid`: the algorithm model as a `RelModel` (deterministic `malloc`, relational
  `free`), for one thread. Its `malloc` is a function of the `World` (the kernel's answers are
  part of the state), so this is the `functional_rel` strength **at the algorithm level**.
* `heapModel C repX`: the `HeapModel` whose live set is `World.live` and whose representation
  `repX` is the x86 separation-logic image of `LocalRep`/`envFrag` (built by `x86sim` in
  `Silmaril.Libc.Ptmalloc.Sim.Str9K`).
* `Task.bridge.model`: the target statement for one pin: glibc's `malloc`/`free` meet
  `mallocSpecH`/`freeSpecH` of `heapModel`. It follows from `Task.algo.wfWorld` (refinement at
  the algorithm level, proved once for every `Config`), the representation lemmas (`seplist`)
  and the block simulations (`x86sim`) for that pin; nothing in it is version-specific except
  `P` and the machine.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

open Silmaril.X86 (Word)
open Silmaril.X86.Sep
open Silmaril.X86.SegVC (Isa)

/-- **The algorithm model as a relational reference model**, for thread `tid` (an aborting call
counts as a refused `malloc`; `Task.algo.mallocTotal` excludes it on well-formed worlds). -/
def relModel (C : Config) (A : Ops C) (tid : Nat) : Silmaril.Libc.X86Alloc.RelModel where
  St := World
  malloc w n := match A.malloc w tid n with
    | .ok (p, _) => BitVec.ofNat 64 p
    | .error _ => 0
  alloc w n := match A.malloc w tid n with
    | .ok (_, w') => w'
    | .error _ => w
  dealloc w p _ w' := A.free w tid p.toNat = .ok w'

/-- **The algorithm model as a heap model**, with the x86 representation `repX`. -/
def heapModel (C : Config) (repX : World → SProp) : Silmaril.Libc.X86Alloc.HeapModel where
  Heap := World
  rep := repX
  live := World.live C

/-- **`Task.bridge.model`**: the pinned libc's `malloc` and `free` (at load layout `lay`) meet the
institution's heap-model specifications for the algorithm model of `P.config`, on the machine
`I`, with stack budget `stack`. -/
def Task.bridge.model (P : Pin) (repX : World → SProp) {σ : Type} (I : Isa σ)
    (lay : Silmaril.Libc.X86Alloc.Layout) (stack : Nat) : Prop :=
  (Silmaril.Libc.X86Alloc.mallocSpecH (heapModel P.config repX) P.config.align stack).Sat I lay.C
      lay.mallocAt ∧
    (Silmaril.Libc.X86Alloc.freeSpecH (heapModel P.config repX) stack).Sat I lay.C lay.freeAt

end Silmaril.Libc.Ptmalloc
