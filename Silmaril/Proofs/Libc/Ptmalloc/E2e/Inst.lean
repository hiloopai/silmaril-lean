module

public import Silmaril.Libc.Ptmalloc.Algo.Thms
public import Silmaril.Libc.Ptmalloc.Sim.Defs

/-!
# ptmalloc end to end, version-generic part: a body-level path step is an institution step

Everything here is parametric in the `Config` `C` (no version, no machine). It is the glue a
pinned block simulation needs to reach the allocator institution (layer a) through the
algorithm model (layer b):

* `malloc_tcacheHit`: when thread `tid`'s tcache bin `C.utidx n` is non-empty, the model's
  world-level `malloc` (`Ops.malloc` of `ptmalloc C`) is exactly the leaf `Local.tcacheGet` on the
  thread's home arena, put back (`World.put`);
* `free_intFree`: for a heap chunk with an initialised tcache, the model's `free` is exactly
  `intFree` (the body) on the chunk's arena, put back;
* `malloc_inst`, `free_inst`: any world-level `malloc`/`free` step of any `A : Ops C` that has a
  `SafeMF` invariant (`AbsAlloc.SatOn Frag.mf … allocLoose`, ghost tokens) keeps the invariant and
  meets `allocLoose` (the institution's `safe` relation);
* `mallocTcache_post`, `freeTcache_post`: the two composed, i.e. what a block simulation's
  post-state (`x.1.tcacheGet C i = some (p, l')`, resp. `intFree C x.1 c = .ok l'`) means for the
  institution.

A new glibc version reuses all of this; it only supplies its machine triple (layer d).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Libc.Ptmalloc.E2e

open Silmaril.Libc.Ptmalloc.Algo
open Silmaril.Libc

/-- The arena a thread's body sees, viewed from the world: its thread and shared parts. -/
theorem local?_parts {w : World} {tid a : Nat} {l : Local} (h : w.local? tid a = some l) :
    l.thread = w.threads tid ∧ l.shared = w.shared ∧ l.kernel = w.kernel ∧ l.avAddr = a := by
  unfold World.local? at h
  cases ha : w.arenas a with
  | none => simp [ha] at h
  | some av =>
    simp only [ha, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The model's `malloc` on a tcache hit** is the leaf `tcache_get` on the thread's home arena
(no `ptmalloc_init`, no `tcache_init`, no body). -/
theorem malloc_tcacheHit (C : Config) {w : World} {tid n p : Nat} {l l' : Local}
    (hn : n < 2 ^ 63) (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some l)
    (hi : l.shared.init = true) (htc : l.thread.tcache.isSome = true)
    (hb : C.utidx n < C.tcacheBins) (hg : l.tcacheGet C (C.utidx n) = some (p, l')) :
    (ptmalloc C).malloc w tid n = .ok (p, w.put tid l') := by
  obtain ⟨ht, hs, -, -⟩ := local?_parts hl
  rw [ht] at htc
  rw [hs] at hi
  have hcr : C.checkedRequest2size n = some (C.request2size n) := by
    unfold Config.checkedRequest2size
    split
    · omega
    · rfl
  have hti : (ptmalloc C).tcacheInit w tid = .ok w := by
    simp [ptmalloc, tcacheInit, htc, pure, Except.pure]
  unfold Config.utidx at hb hg
  simp only [Ops.malloc, Ops.init, hi, ite_true, hcr, hti, Ops.localAt, hl, hb, hg, bind, Except.bind,
    pure, Except.pure]

/-- **The model's `free` of a heap chunk** (thread with a tcache) is `_int_free` on the chunk's
arena (no `tcache_init`, no `munmap_chunk`). -/
theorem free_intFree (C : Config) {w : World} {tid p a : Nat} {l l' : Local}
    (hp : p ≠ 0) (hmm : Ops.mmapped? w (p - C.hdr) = none)
    (htc : (w.threads tid).tcache.isSome = true) (ha : Ops.arenaOf w (p - C.hdr) = some a)
    (hl : w.local? tid a = some l) (hf : intFree C l (p - C.hdr) = .ok l') :
    (ptmalloc C).free w tid p = .ok (w.put tid l') := by
  have hti : (ptmalloc C).tcacheInit w tid = .ok w := by
    simp [ptmalloc, tcacheInit, htc, pure, Except.pure]
  simp only [Ops.free, hp, ite_false, hmm, hti, ha, Ops.localAt, hl, bind, Except.bind, pure,
    Except.pure]
  simp [ptmalloc, hf, Except.bind, pure, Except.pure]

/-- **A `malloc` step is an institution step**: for any `A` with a `SafeMF` invariant, the
token state after a successful `malloc` keeps the invariant and meets `allocLoose`. -/
theorem malloc_inst {C : Config} {A : Ops C} {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF C A tid w0 Inv) {w : World} {h : Heap} (hI : Inv ⟨w, h⟩) {n p : Nat} {w' : World}
    (hm : A.malloc w tid n = .ok (p, w')) :
    Inv ⟨w', if p = 0 then h else h.add p n⟩ ∧
      allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p) := by
  have hst : absStep C A tid ⟨w, h⟩ (.malloc n) (some (⟨w', if p = 0 then h else h.add p n⟩, p)) :=
    ⟨p, w', hm, rfl⟩
  exact ⟨hS.inv _ (.malloc n) _ _ hI trivial hst, hS.rel _ (.malloc n) _ hI trivial hst⟩

/-- **A `free` step of a token is an institution step**. -/
theorem free_inst {C : Config} {A : Ops C} {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF C A tid w0 Inv) {w : World} {h : Heap} (hI : Inv ⟨w, h⟩) {p : Nat} {w' : World}
    (hp : p ≠ 0) (hh : (h p).isSome = true) (hf : A.free w tid p = .ok w') :
    Inv ⟨w', h.remove p⟩ ∧ allocLoose h (.free p) (.ok (h.remove p) 0) := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hh
  have hst : absStep C A tid ⟨w, h⟩ (.free p) (some (⟨w', h.remove p⟩, 0)) := by
    simp only [absStep, hp, ite_false, hm]
    exact ⟨w', hf, rfl⟩
  exact ⟨hS.inv _ (.free p) _ _ hI trivial hst, hS.rel _ (.free p) _ hI trivial hst⟩

/-- **The meaning of a simulated tcache hit** (version-generic): a block simulation's post
`x.tcacheGet C (C.utidx n) = some (p, l')` on the thread's home arena is the model's `malloc`
returning `p`, and an institution step of the token state. -/
theorem mallocTcache_post {C : Config} {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF C (ptmalloc C) tid w0 Inv) {w : World} {h : Heap} (hI : Inv ⟨w, h⟩)
    {n p : Nat} {l l' : Local} (hn : n < 2 ^ 63)
    (hl : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some l)
    (hi : l.shared.init = true) (htc : l.thread.tcache.isSome = true)
    (hb : C.utidx n < C.tcacheBins) (hg : l.tcacheGet C (C.utidx n) = some (p, l')) :
    (ptmalloc C).malloc w tid n = .ok (p, w.put tid l') ∧
      Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
      allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p) :=
  have hm := malloc_tcacheHit C hn hl hi htc hb hg
  ⟨hm, malloc_inst hS hI hm⟩

/-- **The meaning of a simulated `_int_free`** (version-generic): a block simulation's post
`intFree C l (p - C.hdr) = .ok l'` on the chunk's arena is the model's `free`, and an institution
step of the token state. -/
theorem freeTcache_post {C : Config} {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF C (ptmalloc C) tid w0 Inv) {w : World} {h : Heap} (hI : Inv ⟨w, h⟩)
    {p a : Nat} {l l' : Local} (hp : p ≠ 0) (hh : (h p).isSome = true)
    (hmm : Ops.mmapped? w (p - C.hdr) = none) (htc : (w.threads tid).tcache.isSome = true)
    (ha : Ops.arenaOf w (p - C.hdr) = some a) (hl : w.local? tid a = some l)
    (hf : intFree C l (p - C.hdr) = .ok l') :
    (ptmalloc C).free w tid p = .ok (w.put tid l') ∧
      Inv ⟨w.put tid l', h.remove p⟩ ∧ allocLoose h (.free p) (.ok (h.remove p) 0) :=
  have hm := free_intFree C hp hmm htc ha hl hf
  ⟨hm, free_inst hS hI hp hh hm⟩

/-- **The tcache case of `_int_free` exists** under the conditions of glibc's `tcache_put`
branch (`Algo.intFree_tcache`, restated at the payload `p`): what a free-path block simulation
reaches. -/
theorem intFree_tcache_exists (C : Config) (hC : C.Ok) {l : Local} (hw : LocalWF C l) {ch : Chunk}
    (hch : ch ∈ l.av.chunks) (hcu : ch.use = .client) {tc : TcacheSt}
    (ht : l.thread.tcache = some tc) (hi : C.tidx ch.size < C.tcacheBins)
    (hnot : (ch.addr, ch.size) ∉ tc.bins (C.tidx ch.size))
    (hroom : (tc.bins (C.tidx ch.size)).length < C.tcacheCount)
    (hnp : (ch.addr + C.hdr, ch.size - C.sizeSz) ∉ l.thread.parked C) :
    ∃ l', intFree C l (ch.addr + C.hdr - C.hdr) = .ok l' ∧ LocalWF C l' ∧
      (l'.live C).Perm ((l.live C).erase (ch.addr + C.hdr, ch.size - C.sizeSz)) := by
  obtain ⟨l', hf, hw', -, hp⟩ := intFree_tcache hC hw hch hcu ht hi hnot hroom hnp
  exact ⟨l', by rw [Nat.add_sub_cancel]; exact hf, hw', hp⟩

/-! ## The small-bin hit of `malloc` -/

/-- **`_int_malloc`'s small-bin path**: a request of chunk size `nb` in small-bin range, whose
fastbin (if `nb` is a fastbin size) is empty, served by `mallocSmall` (`last (bin)` lent out,
then the tcache refill from the same bin). -/
theorem intMalloc_small (C : Config) {l l' : Local} {n nb p : Nat}
    (hcr : C.checkedRequest2size n = some nb)
    (hfast : nb ≤ C.maxFast → mallocFast C l nb = .ok none)
    (hsr : C.inSmallRange nb = true) (hs : mallocSmall C l nb = some (p, l')) :
    intMalloc C l n = .ok (p, l') := by
  unfold intMalloc
  by_cases hf : nb ≤ C.maxFast
  · simp [hcr, hf, hfast hf, hsr, hs, bind, Except.bind, pure, Except.pure]
  · simp [hcr, hf, hsr, hs, bind, Except.bind, pure, Except.pure]

/-- **The model's `malloc` on a tcache miss, single-threaded**: `_int_malloc` on `main_arena`, put
back (`SINGLE_THREAD_P`: no `arena_get`, no retry). -/
theorem malloc_miss_single (C : Config) {w : World} {tid n nb p : Nat} {l0 l l' : Local}
    (hi : w.shared.init = true) (htc : (w.threads tid).tcache.isSome = true)
    (hcr : C.checkedRequest2size n = some nb)
    (hl0 : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some l0)
    (hmiss : (if C.tidx nb < C.tcacheBins then l0.tcacheGet C (C.tidx nb) else none) = none)
    (hsingle : w.single = true) (hl : w.local? tid w.mainArena = some l)
    (hbody : intMalloc C l n = .ok (p, l')) :
    (ptmalloc C).malloc w tid n = .ok (p, w.put tid l') := by
  have hti : (ptmalloc C).tcacheInit w tid = .ok w := by
    simp [ptmalloc, tcacheInit, htc, pure, Except.pure]
  have hbody' : (ptmalloc C).intMalloc l n = .ok (p, l') := hbody
  simp only [Ops.malloc, Ops.init, hi, ite_true, hcr, hti, Ops.localAt, hl0, hmiss, Ops.withArena,
    hsingle, hl, hbody', bind, Except.bind, pure, Except.pure]

/-- **The meaning of a simulated small-bin hit** (version-generic): a machine run whose post is
`mallocSmall C x.1 nb = some (p, l')` on `main_arena`'s body view, for a single-threaded process
whose thread misses in its tcache, is the model's `malloc` returning `p`, and an institution step
of the token state. -/
theorem mallocSmall_post {C : Config} {tid : Nat} {w0 : World} {Inv : TokSt → Prop}
    (hS : SafeMF C (ptmalloc C) tid w0 Inv) {w : World} {h : Heap} (hI : Inv ⟨w, h⟩)
    {n nb p : Nat} {l0 l l' : Local} (hi : w.shared.init = true)
    (htc : (w.threads tid).tcache.isSome = true) (hcr : C.checkedRequest2size n = some nb)
    (hl0 : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some l0)
    (hmiss : (if C.tidx nb < C.tcacheBins then l0.tcacheGet C (C.tidx nb) else none) = none)
    (hsingle : w.single = true) (hl : w.local? tid w.mainArena = some l)
    (hfast : nb ≤ C.maxFast → mallocFast C l nb = .ok none) (hsr : C.inSmallRange nb = true)
    (hs : mallocSmall C l nb = some (p, l')) :
    (ptmalloc C).malloc w tid n = .ok (p, w.put tid l') ∧
      Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
      allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p) :=
  have hm := malloc_miss_single C hi htc hcr hl0 hmiss hsingle hl (intMalloc_small C hcr hfast hsr hs)
  ⟨hm, malloc_inst hS hI hm⟩

/-- **`malloc`'s small-bin hit, end to end, from any machine simulation of it** (any machine `M`,
any representation addresses `P`): a triple whose post is `mallocSmall C x.1 nb = some (p, l')`
with `LocalAt (l', surr, [p])` is a run of the model's `malloc` and an institution step. -/
theorem mallocSmall_of {C : Config} {M : Mach} {P : RepAt} {Pre R : M.St → Prop} {fp : Nat → Prop}
    (x : AState) (n nb : Nat)
    (hX : M.Triple Pre (fun s' => ∃ p l', mallocSmall C x.1 nb = some (p, l') ∧
      LocalAt C P M (l', x.2.1, [p]) s' ∧ R s') fp)
    {tid : Nat} {w0 : World} {Inv : TokSt → Prop} (hS : SafeMF C (ptmalloc C) tid w0 Inv)
    {w : World} {h : Heap} (hI : Inv ⟨w, h⟩) {l0 : Local} (hi : w.shared.init = true)
    (htc : (w.threads tid).tcache.isSome = true) (hcr : C.checkedRequest2size n = some nb)
    (hl0 : w.local? tid (((w.threads tid).arena).getD w.mainArena) = some l0)
    (hmiss : (if C.tidx nb < C.tcacheBins then l0.tcacheGet C (C.tidx nb) else none) = none)
    (hsingle : w.single = true) (hl : w.local? tid w.mainArena = some x.1)
    (hfast : nb ≤ C.maxFast → mallocFast C x.1 nb = .ok none) (hsr : C.inSmallRange nb = true) :
    M.Triple Pre
      (fun s' => ∃ p l', (ptmalloc C).malloc w tid n = .ok (p, w.put tid l') ∧
        LocalAt C P M (l', x.2.1, [p]) s' ∧ R s' ∧
        Inv ⟨w.put tid l', if p = 0 then h else h.add p n⟩ ∧
        allocLoose h (.malloc n) (.ok (if p = 0 then h else h.add p n) p)) fp :=
  hX.conseq (fun _ hs => hs)
    (fun _ ⟨p, l', hs, hL, hR⟩ =>
      have ⟨hm, hI', hrel⟩ := mallocSmall_post hS hI hi htc hcr hl0 hmiss hsingle hl hfast hsr hs
      ⟨p, l', hm, hL, hR, hI', hrel⟩)
    (fun _ ha => ha)

end Silmaril.Libc.Ptmalloc.E2e
