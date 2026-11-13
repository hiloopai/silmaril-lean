module

public import Silmaril.Libc.Ptmalloc.Algo.Thms
public import Silmaril.Libc.Ptmalloc.Version.Thms

/-!
# ptmalloc: `calloc` and `realloc` at the pins (algorithm level)

The algorithm-level `calloc`/`realloc` theorems (`Algo.wfCallocRealloc`, `Algo.calloc_refines`,
`Algo.realloc_refines`) are proved for every `C` with `C.Ok`; here they are instantiated at the
three pinned configurations (glibc 2.36, 2.39, 2.40: data only, `pin236_ok`, `pin239_ok`,
`pin240_ok`). These are statements about the model `ptmalloc pinXXX.config`; no x86 simulation
of `__libc_calloc` or `__libc_realloc` is part of them.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.E2e

open Silmaril.Libc Silmaril.Libc.Ptmalloc.Algo Silmaril.Libc.Ptmalloc.Versions

/-- **glibc 2.39's `calloc` refines the institution's `calloc`** (the model at `pin239`). -/
theorem calloc239 {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩)
    {k m p : Nat} {w' : World} (hc : (ptmalloc pin239.config).calloc w tid k m = .ok (p, w')) :
    RefInv pin239.config tid ⟨w', if p = 0 then h else h.add p (k * m)⟩ ∧
      allocLoose h (.calloc k m) (.ok (if p = 0 then h else h.add p (k * m)) p) :=
  calloc_refines pin239_ok hI hc

/-- **glibc 2.39's `realloc` of a token refines the institution's `realloc`** (the model at
`pin239`). -/
theorem realloc239 {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin239.config tid ⟨w, h⟩)
    {p n q : Nat} {w' : World} (hp : (h p).isSome)
    (hr : (ptmalloc pin239.config).realloc w tid p n = .ok (q, w')) :
    RefInv pin239.config tid ⟨w', if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n⟩ ∧
      allocLoose h (.realloc p n)
        (.ok (if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n) q) :=
  realloc_refines pin239_ok hI hp hr

/-- glibc 2.36 (data only). -/
theorem calloc236 {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin236.config tid ⟨w, h⟩)
    {k m p : Nat} {w' : World} (hc : (ptmalloc pin236.config).calloc w tid k m = .ok (p, w')) :
    RefInv pin236.config tid ⟨w', if p = 0 then h else h.add p (k * m)⟩ ∧
      allocLoose h (.calloc k m) (.ok (if p = 0 then h else h.add p (k * m)) p) :=
  calloc_refines pin236_ok hI hc

/-- glibc 2.36 (data only). -/
theorem realloc236 {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin236.config tid ⟨w, h⟩)
    {p n q : Nat} {w' : World} (hp : (h p).isSome)
    (hr : (ptmalloc pin236.config).realloc w tid p n = .ok (q, w')) :
    RefInv pin236.config tid ⟨w', if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n⟩ ∧
      allocLoose h (.realloc p n)
        (.ok (if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n) q) :=
  realloc_refines pin236_ok hI hp hr

/-- glibc 2.40 (data only). -/
theorem calloc240 {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin240.config tid ⟨w, h⟩)
    {k m p : Nat} {w' : World} (hc : (ptmalloc pin240.config).calloc w tid k m = .ok (p, w')) :
    RefInv pin240.config tid ⟨w', if p = 0 then h else h.add p (k * m)⟩ ∧
      allocLoose h (.calloc k m) (.ok (if p = 0 then h else h.add p (k * m)) p) :=
  calloc_refines pin240_ok hI hc

/-- glibc 2.40 (data only). -/
theorem realloc240 {tid : Nat} {w : World} {h : Heap} (hI : RefInv pin240.config tid ⟨w, h⟩)
    {p n q : Nat} {w' : World} (hp : (h p).isSome)
    (hr : (ptmalloc pin240.config).realloc w tid p n = .ok (q, w')) :
    RefInv pin240.config tid ⟨w', if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n⟩ ∧
      allocLoose h (.realloc p n)
        (.ok (if n = 0 then h.remove p else if q = 0 then h else (h.remove p).add q n) q) :=
  realloc_refines pin240_ok hI hp hr

end Silmaril.Libc.Ptmalloc.E2e
