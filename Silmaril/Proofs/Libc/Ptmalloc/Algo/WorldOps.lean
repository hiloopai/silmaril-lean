module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldPut
public import Silmaril.Libc.Ptmalloc.Algo.Leaf.Thms
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Free

/-!
# ptmalloc algorithm: the world-level steps keep `WorldWF`

`ptmalloc_init`, `errno`, `thread_arena`, the kernel's answer counter, `tcache_get`,
`_int_new_arena`, `arena_get`, `arena_get_retry`, `tcache_init`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## Changes that touch no arena, `mmap`ed chunk, kernel region or tcache -/

theorem kernel_has_congr {k k' : KernelSt} (h1 : k'.brkStart = k.brkStart) (h2 : k'.brk = k.brk)
    (h3 : k'.maps = k.maps) {x : Nat} : k'.Has x ↔ k.Has x := by
  unfold KernelSt.Has; rw [h1, h2, h3]

theorem kernel_covers_congr {k k' : KernelSt} (h1 : k'.brkStart = k.brkStart) (h2 : k'.brk = k.brk)
    (h3 : k'.maps = k.maps) {r : Nat × Nat} : k'.Covers r ↔ k.Covers r := by
  unfold KernelSt.Covers; simp only [kernel_has_congr h1 h2 h3]

theorem parked_congr {t t' : ThreadSt} (h : t'.tcache = t.tcache) : t'.parked C = t.parked C := by
  unfold ThreadSt.parked; rw [h]

/-- `LocalWF` carries over to a view with the same arena, tcache, `mmap`ed chunks and break. -/
theorem localWF_transfer {l l' : Local} (h : LocalWF C l) (hav : l'.av = l.av)
    (htc : l'.thread.tcache = l.thread.tcache) (hmm : l'.shared.mm = l.shared.mm)
    (hsh : SharedWF C l'.shared) (hinit : l'.shared.init = false → l.shared.init = false)
    (hm : l'.isMain = l.isMain) (hk1 : l'.kernel.brkStart = l.kernel.brkStart)
    (hk2 : l'.kernel.brk = l.kernel.brk) (hk3 : l'.kernel.maps = l.kernel.maps) : LocalWF C l' where
  arena := hav ▸ h.arena
  shared := hsh
  tcache := fun tc htc' => h.tcache tc (htc ▸ htc')
  main := fun hm' => by
    have ⟨h1, h2⟩ := h.main (hm ▸ hm')
    unfold MainSbrk MainBrk at *
    rw [hav, hmm, hk1, hk2]; exact ⟨h1, h2⟩
  init := fun hi => by
    have := h.init (hinit hi); rw [hav, hmm, htc]; exact this
  apart := by unfold Local.spans; rw [hav, hmm]; exact h.apart
  mmSize := by rw [hmm]; exact h.mmSize
  heap := fun hm' => by rw [hav]; exact h.heap (hm ▸ hm')
  sysMain := fun hm' => by
    have := h.sysMain (hm ▸ hm')
    rw [hav, hmm, KernelSt.total_eq hk1 hk2 hk3]; exact this

/-- A world change that keeps the arenas, the `mmap`ed chunks, the arena list, the kernel's
regions and every tcache keeps `WorldWF` and the live set (`thread_arena`s must stay arenas, and
the init flag may only be set). -/
theorem worldWF_congr {w w' : World} (hw : WorldWF C w) (hma : w'.mainArena = w.mainArena)
    (har : w'.arenas = w.arenas) (htids : w'.tids = w.tids) (hmm : w'.shared.mm = w.shared.mm)
    (hsa : w'.shared.arenas = w.shared.arenas) (hfl : ∀ x ∈ w'.shared.freeList, x ∈ w.shared.freeList)
    (hna : w'.shared.narenas = w.shared.narenas) (hk1 : w'.kernel.brkStart = w.kernel.brkStart)
    (hk2 : w'.kernel.brk = w.kernel.brk) (hk3 : w'.kernel.maps = w.kernel.maps)
    (htc : ∀ t, (w'.threads t).tcache = (w.threads t).tcache)
    (hta : ∀ t ∈ w.tids, ∀ a, (w'.threads t).arena = some a → a ∈ w.arenaAddrs)
    (hinit : w'.shared.init = false → w.shared.init = false) :
    WorldWF C w' ∧ w'.live C = w.live C := by
  have hA : w'.arenaAddrs = w.arenaAddrs := by simp [World.arenaAddrs, hma, hsa]
  have hsp : w'.spans = w.spans := by simp [World.spans, hA, har, hmm]
  have hch : w'.chunks = w.chunks := by simp [World.chunks, hA, har]
  have hpk : ∀ t, (w'.threads t).parked C = (w.threads t).parked C := fun t => parked_congr (htc t)
  have hsh : SharedWF C w'.shared :=
    { mm := by rw [hmm]; exact hw.shared.mm
      narenas := by rw [hna, hsa]; exact hw.shared.narenas
      freeListSub := fun x hx => by rw [hsa]; exact hw.shared.freeListSub x (hfl x hx) }
  have hhas : ∀ x, w'.kernel.Has x ↔ w.kernel.Has x := fun x => kernel_has_congr hk1 hk2 hk3
  have hcov : ∀ r, w'.kernel.Covers r ↔ w.kernel.Covers r := fun r => kernel_covers_congr hk1 hk2 hk3
  refine ⟨
    { main := by rw [hma, har]; exact hw.main
      arenas := fun a => by rw [hA, har]; exact hw.arenas a
      arenaWF := fun a av h => hw.arenaWF a av (har ▸ h)
      shared := hsh
      locals := fun t a l ht hl => by
        rw [htids] at ht
        obtain ⟨av, hav, rfl⟩ := local?_some hl
        rw [har] at hav
        have hold := hw.locals t a _ ht (local?_of hav t)
        exact localWF_transfer hold rfl (htc t) hmm hsh hinit (by simp [hma]) hk1 hk2 hk3
      arenaNodup := by rw [hA]; exact hw.arenaNodup
      apart := by rw [hsp]; exact hw.apart
      mmSize := by rw [hmm]; exact hw.mmSize
      parked := fun t tc ht htc' i c hc => by
        rw [htids] at ht; rw [htc] at htc'; rw [hch]; exact hw.parked t tc ht htc' i c hc
      parkedOnce := by simp only [htids, hpk]; exact hw.parkedOnce
      tidsNodup := by rw [htids]; exact hw.tidsNodup
      threadArena := fun t a ht h => by rw [htids] at ht; rw [hA]; exact hta t ht a h
      covered := fun r hr => by rw [hsp] at hr; exact (hcov r).mpr (hw.covered r hr)
      structs := fun a ha => by
        rw [hA] at ha; rw [hsp, hhas]; exact hw.structs a ha
      heaps := fun a av h hne => hw.heaps a av (har ▸ h) (hma ▸ hne) }, ?_⟩
  simp [World.live, hA, har, htids, hpk, SharedSt.live, hmm]

/-! ## `ptmalloc_init`, `errno`, `thread_arena` -/

theorem ptmallocInit_eq (w : World) (tid : Nat) :
    ∃ key k, ptmallocInit w tid = .ok { w with
      shared := { w.shared with init := true, key }
      kernel := k
      threads := fun t => if t = tid then { w.threads t with arena := some w.mainArena } else w.threads t } ∧
      k.brkStart = w.kernel.brkStart ∧ k.brk = w.kernel.brk ∧ k.maps = w.kernel.maps := by
  unfold ptmallocInit KernelSt.ask
  cases w.kernel.oracle.answer w.kernel.asked with
  | ok v => exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | refuse =>
    simp only
    cases ({ w.kernel with asked := w.kernel.asked + 1 } : KernelSt).oracle.answer (w.kernel.asked + 1) with
    | ok v => exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    | refuse => exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem ptmallocInit_wf {w w' : World} {tid : Nat} (hw : WorldWF C w)
    (h : ptmallocInit w tid = .ok w') :
    WorldWF C w' ∧ w'.live C = w.live C ∧ w'.tids = w.tids ∧ w'.shared.init = true ∧
      w'.mainArena = w.mainArena ∧ ∀ t, (w'.threads t).tcache = (w.threads t).tcache := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  obtain ⟨key, k, he, h1, h2, h3⟩ := ptmallocInit_eq w tid
  rw [he] at h; cases h
  have htc : ∀ t, ((fun t => if t = tid then { w.threads t with arena := some w.mainArena }
      else w.threads t) t).tcache = (w.threads t).tcache := by
    intro t; show (if t = tid then _ else _ : ThreadSt).tcache = _; split <;> rfl
  have := worldWF_congr (C := C) (w' := { w with
      shared := { w.shared with init := true, key }
      kernel := k
      threads := fun t => if t = tid then { w.threads t with arena := some w.mainArena } else w.threads t })
    hw rfl rfl rfl rfl rfl (fun _ h => h) rfl h1 h2 h3 htc
    (fun t ht a h => by
      change (if t = tid then _ else _ : ThreadSt).arena = some a at h
      split at h
      · cases h; exact hmain
      · exact hw.threadArena t a ht h) (fun h => by cases h)
  exact ⟨this.1, this.2, rfl, rfl, rfl, htc⟩

theorem init_wf {w w' : World} {tid : Nat} (hw : WorldWF C w)
    (h : (ptmalloc C).init w tid = .ok w') :
    WorldWF C w' ∧ w'.live C = w.live C ∧ w'.tids = w.tids ∧ w'.shared.init = true ∧
      w'.mainArena = w.mainArena ∧ ∀ t, (w'.threads t).tcache = (w.threads t).tcache := by
  unfold Ops.init at h
  split at h
  · rename_i hi; cases h; exact ⟨hw, rfl, rfl, hi, rfl, fun _ => rfl⟩
  · exact ptmallocInit_wf hw h

theorem setErrno_wf {w : World} {tid e : Nat} (hw : WorldWF C w) :
    WorldWF C (Ops.setErrno w tid e) ∧ (Ops.setErrno w tid e).live C = w.live C :=
  worldWF_congr hw rfl rfl rfl rfl rfl (fun _ h => h) rfl rfl rfl rfl
    (fun t => by show (if t = tid then _ else _ : ThreadSt).tcache = _; split <;> rfl)
    (fun t ht a h => by
      change (if t = tid then _ else _ : ThreadSt).arena = some a at h; split at h
      · rename_i htt; subst htt; exact hw.threadArena _ a ht h
      · exact hw.threadArena t a ht h) id

theorem setArena_wf {w : World} {tid a : Nat} (hw : WorldWF C w) (ha : a ∈ w.arenaAddrs) :
    WorldWF C (setArena w tid a) ∧ (setArena w tid a).live C = w.live C :=
  worldWF_congr hw rfl rfl rfl rfl rfl (fun _ h => h) rfl rfl rfl rfl
    (fun t => by show (if t = tid then _ else _ : ThreadSt).tcache = _; split <;> rfl)
    (fun t ht x h => by
      change (if t = tid then _ else _ : ThreadSt).arena = some x at h; split at h
      · cases h; exact ha
      · exact hw.threadArena t x ht h) id

/-! ## A thread-only change, and `tcache_get` -/

/-- A change of the calling thread's state only, whose tcache entries were entries before. -/
theorem put_thread_wf (hC : C.Ok) {w : World} {tid a : Nat} {l : Local} (hw : WorldWF C w)
    (ht : tid ∈ w.tids) (hl : w.local? tid a = some l) (t' : ThreadSt)
    (hT : ∀ tc, t'.tcache = some tc → TcacheWF C tc)
    (hsub : ∀ tc' i e, t'.tcache = some tc' → e ∈ tc'.bins i →
      ∃ tc j, l.thread.tcache = some tc ∧ e ∈ tc.bins j)
    (har : t'.arena = l.thread.arena) (hinit : l.shared.init = false → t'.tcache = none) :
    WorldWF C (w.put tid { l with thread := t' }) := by
  have hsp := localSp hw ht hl
  refine worldWF_put (freed := []) hC hw ht hl ((hw.locals tid a l ht hl).withThread t' hT hinit) ?_ (by simp)
  exact
    { avAddr := rfl, isMain := rfl
      spatial := fun r _ hc haw => ⟨hc, haw⟩
      covered := hsp.covered
      brkStart := rfl
      nonMain := fun _ => ⟨rfl, rfl⟩
      acct := fun _ => Nat.le_refl _
      init := rfl
      arenas := ⟨rfl, rfl, rfl⟩
      arena := har
      heaps := id
      clients := fun c hc _ _ => hc
      fresh := fun tc' i e htc he => .inl (by
        obtain ⟨tc, j, h1, h2⟩ := hsub tc' i e htc he; exact ⟨tc, j, h1, h2⟩) }

/-- `tidx` is injective on aligned chunk sizes. -/
theorem tidx_inj (hC : C.Ok) {s s' : Nat} (h : C.tidx s = C.tidx s') (hs : s % C.align = 0)
    (hs' : s' % C.align = 0) (h1 : C.minSize ≤ s) (h2 : C.minSize ≤ s') : s = s' := by
  unfold Config.tidx at h
  rw [hC.align, hC.minSize] at *
  omega

theorem request2size_props (hC : C.Ok) (n : Nat) :
    C.request2size n % C.align = 0 ∧ C.minSize ≤ C.request2size n ∧ n + C.sizeSz ≤ C.request2size n := by
  unfold Config.request2size Config.alignMask
  rw [hC.align, hC.minSize, hC.sizeSz]
  split <;> refine ⟨?_, ?_, ?_⟩ <;> omega

/-- **The tcache path of `malloc`**, put back. -/
theorem tcacheGet_world (hC : C.Ok) {w : World} {tid a : Nat} {l0 l : Local} (hw : WorldWF C w)
    (ht : tid ∈ w.tids) (hl : w.local? tid a = some l0) {i p n nb : Nat}
    (hg : l0.tcacheGet C i = some (p, l)) (hnb : C.checkedRequest2size n = some nb)
    (hi : i = C.tidx nb) :
    WorldWF C (w.put tid l) ∧ MallocLive C n p (w.live C) ((w.put tid l).live C) := by
  obtain ⟨tc, tc', htc, hget, rfl⟩ := tcacheGet_eq hg
  obtain ⟨av, hav, hlav, hla, -, hlt, hls, -⟩ := local?_fields hl
  have hwl := hw.locals tid a l0 ht hl
  have htw := hwl.tcache tc htc
  have htw' := TcacheSt.wf_get htw hget
  obtain ⟨e, rest, hb, rfl, rfl⟩ := TcacheSt.get_eq hget
  have hsub : ∀ j x, x ∈ (if j = i then rest else tc.bins j) → x ∈ tc.bins j := by
    intro j x hx; by_cases hj : j = i
    · subst hj; simp only [ite_true] at hx; rw [hb]; exact List.mem_cons_of_mem _ hx
    · simpa [hj] using hx
  have hw' : WorldWF C (w.put tid { l0 with thread := { l0.thread with tcache := some _ } }) :=
    put_thread_wf hC hw ht hl _ (fun x hx => by cases hx; exact htw')
      (fun tc'' j x h hx => by cases h; exact ⟨tc, j, htc, hsub j x hx⟩) rfl
      (fun h0 => by have := (hwl.init h0).2.2; rw [htc] at this; cases this)
  refine ⟨hw', ?_⟩
  -- the popped entry
  have he : e ∈ tc.bins i := by rw [hb]; exact List.mem_cons_self ..
  have hei : i < C.tcacheBins := Nat.lt_of_not_le fun h => by rw [htw.bins i h] at he; cases he
  have hq : epay C e ∈ l0.thread.parked C := mem_parked_of htw htc he
  have hqP : epay C e ∈ allParked C w := mem_allParked.mpr ⟨tid, ht, by rw [← hlt]; exact hq⟩
  have hql : epay C e ∉ w.live C := fun h => parked_not_live hw hqP h
  -- the new thread's parked set: the old one without `epay e`
  have hPn : ∀ y, y ∈ ({ l0.thread with tcache := some { tc with
      bins := fun j => if j = i then rest else tc.bins j } } : ThreadSt).parked C ↔
      y ∈ l0.thread.parked C ∧ y ≠ epay C e := by
    intro y
    rw [mem_parked, mem_parked]
    constructor
    · rintro ⟨tc1, h1, j, hj, x, hx, rfl⟩
      cases h1
      refine ⟨⟨tc, htc, j, hj, x, hsub j x hx, rfl⟩, fun hxe => ?_⟩
      have hxs := (htw.size j x (hsub j x hx))
      have hes := htw.size i e he
      have := epay_inj hxe (by have := hC.minSize; have := hC.sizeSz; omega)
        (by have := hC.minSize; have := hC.sizeSz; omega)
      subst this
      by_cases hj' : j = i
      · subst hj'; simp only [ite_true] at hx
        have hnd0 := (htw.nodup j).1; rw [hb] at hnd0; exact (List.nodup_cons.mp hnd0).1 hx
      · exact hj' (hxs.1.symm.trans hes.1)
    · rintro ⟨⟨tc1, h1, j, hj, x, hx, rfl⟩, hne⟩
      rw [htc] at h1; cases h1
      refine ⟨_, rfl, j, hj, x, ?_, rfl⟩
      by_cases hj' : j = i
      · subst hj'; simp only [ite_true]; rw [hb] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl hne
        · exact hx
      · simpa [hj'] using hx
  have hmem : ∀ y, y ∈ (w.put tid { l0 with thread := { l0.thread with tcache := some { tc with
      bins := fun j => if j = i then rest else tc.bins j } } }).live C ↔ y = epay C e ∨ y ∈ w.live C := by
    intro y
    rw [mem_live, mem_live]
    have hA' : (w.put tid { l0 with thread := { l0.thread with tcache := some { tc with
      bins := fun j => if j = i then rest else tc.bins j } } }).arenaAddrs = w.arenaAddrs := by
      simp [World.arenaAddrs, World.put, hls]
    have harr : ∀ b, (w.put tid { l0 with thread := { l0.thread with tcache := some { tc with
      bins := fun j => if j = i then rest else tc.bins j } } }).arenas b = w.arenas b := by
      intro b; simp only [World.put]; split
      · rename_i hb'; rw [hb', hla, hav, hlav]
      · rfl
    simp only [hA', harr, put_allParked ht, old_allParked ht, hPn, ← hlt]
    have hsh : (w.put tid { l0 with thread := { l0.thread with tcache := some { tc with
      bins := fun j => if j = i then rest else tc.bins j } } }).shared = w.shared := by
      simp [World.put, hls]
    rw [hsh]
    constructor
    · rintro (⟨hy, hnp⟩ | hm)
      · by_cases hye : y = epay C e
        · exact .inl hye
        · right; left; refine ⟨hy, ?_⟩
          rintro (h | h)
          · exact hnp (.inl ⟨h, hye⟩)
          · exact hnp (.inr h)
      · exact .inr (.inr hm)
    · rintro (rfl | ⟨hy, hnp⟩ | hm)
      · left
        obtain ⟨b, avb, hab, d, hd, hdu, hde⟩ := parked_chunk hw hqP
        refine ⟨⟨b, hw.mem_addrs hab, avb, hab, mem_out.mpr ⟨d, hd, hdu, hde⟩⟩, ?_⟩
        rintro (⟨-, h⟩ | ⟨t, htt, hne, h⟩)
        · exact h rfl
        · exact disjoint_of_nodup_flatMap hw.parkedOnce htt ht hne h (by rw [← hlt]; exact hq)
      · left; refine ⟨hy, ?_⟩
        rintro (⟨h, -⟩ | h)
        · exact hnp (.inl h)
        · exact hnp (.inr h)
      · exact .inr hm
  -- `MallocLive`
  have hes := htw.size i e he
  have hnn := htw.nonNull i e he
  obtain ⟨hr1, hr2, hr3⟩ := request2size_props hC n
  have hnb' : nb = C.request2size n := by
    unfold Config.checkedRequest2size at hnb; split at hnb <;> simp_all
  have hsz : e.2 = nb := tidx_inj hC (hes.1.trans hi) hes.2.1 (hnb' ▸ hr1) hes.2.2 (hnb' ▸ hr2)
  have hnd := live_nodup hC hw
  have hnd' := live_nodup hC hw'
  refine .inr ⟨?_, ?_, e.2 - C.sizeSz, ?_, ?_, ?_⟩
  · have := hC.align; unfold Config.hdr; rw [hC.sizeSz]; omega
  · show (e.1 + C.hdr) % C.align = 0
    unfold Config.hdr; rw [hC.sizeSz, hC.align]; rw [hC.align] at hnn; omega
  · rw [hsz, hnb']; omega
  · refine (List.perm_ext_iff_of_nodup hnd' (List.nodup_cons.mpr ⟨hql, hnd⟩)).mpr fun y => ?_
    rw [hmem y]; simp [epay]
  · intro q hq
    have hap := (liveApart C hC _ hw').1
    have hq' := (hmem q).mpr (.inr hq)
    have hp' := (hmem (epay C e)).mpr (.inl rfl)
    exact pairwise_of_mem (fun h => h.symm) hap hq' hp' (fun h => hql (h ▸ hq))

/-! ## Quiet world steps: `WorldWF` kept, the live set and the threads' tcaches unchanged -/

/-- **A quiet world step** from `w` to `w'`. -/
structure Quiet (C : Config) (w w' : World) : Prop where
  wf : WorldWF C w'
  live : (w'.live C).Perm (w.live C)
  tids : w'.tids = w.tids
  init : w'.shared.init = w.shared.init
  tcache : ∀ t, (w'.threads t).tcache = (w.threads t).tcache
  main : w'.mainArena = w.mainArena
  arenasKept : ∀ b av, w.arenas b = some av → w'.arenas b = some av

theorem Quiet.refl {w : World} (hw : WorldWF C w) : Quiet C w w :=
  ⟨hw, List.Perm.refl _, rfl, rfl, fun _ => rfl, rfl, fun _ _ h => h⟩

theorem Quiet.trans {w₁ w₂ w₃ : World} (h₁ : Quiet C w₁ w₂) (h₂ : Quiet C w₂ w₃) : Quiet C w₁ w₃ :=
  ⟨h₂.wf, h₂.live.trans h₁.live, h₂.tids.trans h₁.tids, h₂.init.trans h₁.init,
    fun t => (h₂.tcache t).trans (h₁.tcache t), h₂.main.trans h₁.main,
    fun b av h => h₂.arenasKept b av (h₁.arenasKept b av h)⟩

theorem setArena_quiet {w : World} {tid a : Nat} (hw : WorldWF C w) (ha : a ∈ w.arenaAddrs) :
    Quiet C w (setArena w tid a) :=
  have h := setArena_wf (tid := tid) hw ha
  ⟨h.1, by rw [h.2], rfl, rfl, fun t => by show (if t = tid then _ else _ : ThreadSt).tcache = _; split <;> rfl, rfl,
    fun _ _ h => h⟩

/-- Only the kernel's answer counter (and, for a refusal, nothing else) changes. -/
theorem kernel_quiet {w : World} (hw : WorldWF C w) (k : KernelSt) (h1 : k.brkStart = w.kernel.brkStart)
    (h2 : k.brk = w.kernel.brk) (h3 : k.maps = w.kernel.maps) : Quiet C w { w with kernel := k } :=
  have h := worldWF_congr (w' := { w with kernel := k }) hw rfl rfl rfl rfl rfl (fun _ h => h) rfl
    h1 h2 h3 (fun _ => rfl) (fun t ht a h => hw.threadArena t a ht h) id
  ⟨h.1, by rw [h.2], rfl, rfl, fun _ => rfl, rfl, fun _ _ h => h⟩

/-! ## Fresh kernel memory -/

/-- A range the kernel may map is apart from every range of the process's memory. -/
theorem fresh_away {k : KernelSt} {al h n : Nat} (hp : k.Placeable al h n) (hn : 0 < n)
    {r : Nat × Nat} (hr : k.Covers r) (h0 : 0 < r.2) : r.1 + r.2 ≤ h ∨ h + n ≤ r.1 := by
  by_cases h1 : r.1 + r.2 ≤ h
  · exact .inl h1
  by_cases h2 : h + n ≤ r.1
  · exact .inr h2
  exfalso
  obtain ⟨-, -, -, hfree, hbrk, -⟩ := hp
  have key : ∀ x, r.1 ≤ x → x < r.1 + r.2 → h ≤ x → x < h + n → False := by
    intro x hx1 hx2 hx3 hx4
    rcases hr x hx1 hx2 with ⟨hb1, hb2⟩ | ⟨m, hm, hm1, hm2⟩
    · omega
    · have := hfree m hm; omega
  by_cases h3 : r.1 ≤ h
  · exact key h h3 (by omega) (Nat.le_refl _) (by omega)
  · exact key r.1 (Nat.le_refl _) (by omega) (by omega) (by omega)

theorem has_mono {k k' : KernelSt} (h1 : k'.brkStart = k.brkStart) (h2 : k'.brk = k.brk)
    (h3 : ∀ m ∈ k.maps, m ∈ k'.maps) {x : Nat} (h : k.Has x) : k'.Has x := by
  rcases h with ⟨a, b⟩ | ⟨m, hm, hm1, hm2⟩
  · exact .inl ⟨h1 ▸ a, h2 ▸ b⟩
  · exact .inr ⟨m, h3 m hm, hm1, hm2⟩

theorem covers_mono {k k' : KernelSt} (h1 : k'.brkStart = k.brkStart) (h2 : k'.brk = k.brk)
    (h3 : ∀ m ∈ k.maps, m ∈ k'.maps) {r : Nat × Nat} (h : k.Covers r) : k'.Covers r :=
  fun x hx1 hx2 => has_mono h1 h2 h3 (h x hx1 hx2)

/-! ## `_int_new_arena` -/

/-- A new arena: an empty heap from `p` with a top of `T` bytes, `sz` bytes of system memory. -/
def freshArena (p T sz : Nat) (hs : List (Nat × Nat)) (rv : Nat) : ArenaSt :=
  { tiles := { start := p, chunks := [], top := p, topSize := T, noncontig := true,
               systemMem := sz, maxSystemMem := sz }
    fast := { lists := fun _ => [], haveFast := false }
    bins := { lists := fun _ => [], binmap := fun _ => false }
    unsorted := { list := [], lastRem := 0 }
    attached := 1
    heaps := hs
    reserve := rv }

set_option linter.unusedSimpArgs false in
theorem freshArena_chunks (p T sz : Nat) (hs : List (Nat × Nat)) (rv : Nat) :
    (freshArena p T sz hs rv).chunks = [] := by
  simp [freshArena, ArenaSt.chunks, TopSt.heapChunks, layout]

set_option linter.unusedSimpArgs false in
theorem freshArena_spans {p T sz h rv : Nat} (hp : p ≠ 0) :
    (freshArena p T sz [(h, sz)] rv).spans =
      (p, T) :: (h, 1) :: (if rv = 0 then [] else [(h + sz, rv)]) := by
  rcases Nat.eq_zero_or_pos rv with rfl | hr
  · simp [freshArena, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans, TopSt.heapChunks, layout, hp]
  · simp [freshArena, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans, TopSt.heapChunks, layout, hp,
      Nat.pos_iff_ne_zero.mp hr]

set_option linter.unusedSimpArgs false in
theorem arenaWF_fresh (C : Config) {p T sz : Nat} (hs : List (Nat × Nat)) (rv : Nat) (hp0 : p ≠ 0)
    (hpa : p % C.align = 0) (hTa : T % C.align = 0) (hTm : C.minSize ≤ T) (hTs : T ≤ sz)
    (hsz : sz < 2 ^ 64) (hb : p + T < 2 ^ 64) : ArenaWF C (freshArena p T sz hs rv) where
  tiles :=
    { sizes := by simp [freshArena, TopSt.heapChunks, layout]
      aligned := by simp [freshArena, TopSt.heapChunks, layout]
      nonNull := by simp [freshArena, TopSt.heapChunks, layout]
      topAt := fun _ => by simp [freshArena]
      topAligned := ⟨hpa, hTa⟩
      topMin := fun _ => hTm
      coalesced := rfl
      lastUsed := by simp [freshArena]
      coalescedOld := by simp [freshArena]
      sysMem := by simp [freshArena, TopSt.heapChunks, layout]; exact hTs
      sysMemBound := hsz
      noHeap := fun h => absurd h hp0
      nodup := by simp [freshArena, TopSt.heapChunks, layout]
      bound := by simp [freshArena, TopSt.heapChunks, layout]
      topBound := fun _ => hb }
  fast :=
    { exact := fun i x => by
        simp [freshArena, ArenaSt.fastView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      nodup := fun _ => List.nodup_nil
      size := by simp [freshArena, ArenaSt.fastView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      flag := fun ⟨_, h⟩ => absurd rfl h }
  bins :=
    { exact := fun i _ x => by
        simp [freshArena, ArenaSt.sortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      outside := fun _ _ => rfl
      nodup := fun _ => List.nodup_nil
      size := by simp [freshArena, ArenaSt.sortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      sorted := fun _ _ => List.Pairwise.nil
      binmap := fun _ h => absurd rfl h }
  unsorted :=
    { exact := fun x => by
        simp [freshArena, ArenaSt.unsortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      nodup := List.nodup_nil
      size := by simp [freshArena, ArenaSt.unsortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      lastRemBound := by simp [freshArena] }
  internal := by simp [freshArena, ArenaSt.chunks, TopSt.heapChunks, layout]

theorem flatMap_insert {β : Type} {G G₁ : Nat → List β} {m a : Nat} {rest : List Nat}
    (hna : a ∉ m :: rest) (hG : ∀ b, b ≠ a → G₁ b = G b) :
    (m :: a :: rest).flatMap G₁ = G m ++ G₁ a ++ rest.flatMap G := by
  have hm : m ≠ a := fun h => hna (h ▸ List.mem_cons_self ..)
  simp only [List.flatMap_cons, hG m hm, List.append_assoc]
  congr 2
  exact flatMap_congr' fun b hb => hG b (fun h => hna (h ▸ List.mem_cons_of_mem _ hb))

/-- **Linking a new arena** at `a = h + heapInfoSize` on a fresh heap mapping `(h, HEAP_MAX_SIZE)`
of which `sz` bytes are used, its top from `p` (after the arena struct) to `h + sz`. -/
theorem addArena_quiet (hC : C.Ok) {w : World} {tid : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids)
    (hi : w.shared.init = true) {h sz p : Nat} (k₁ : KernelSt)
    (hk1 : k₁.brkStart = w.kernel.brkStart) (hk2 : k₁.brk = w.kernel.brk)
    (hk3 : k₁.maps = (h, C.heapMaxSize) :: w.kernel.maps)
    (hpl : w.kernel.Placeable C.heapMaxSize h C.heapMaxSize)
    (hszl : 0x8000 ≤ sz) (hszu : sz ≤ C.heapMaxSize) (hsza : sz % C.align = 0)
    (hp1 : h + C.heapInfoSize + C.stateSize ≤ p) (hp2 : p ≤ h + C.heapInfoSize + C.stateSize + 15)
    (hpa : p % C.align = 0) :
    Quiet C w { w with
      kernel := k₁
      arenas := fun x => if x = h + C.heapInfoSize then some (freshArena p (h + sz - p) sz [(h, sz)] (C.heapMaxSize - sz))
        else w.arenas x
      shared := { w.shared with arenas := (h + C.heapInfoSize) :: w.shared.arenas,
                                narenas := w.shared.narenas + 1 } } ∧
    h + C.heapInfoSize ∈ (h + C.heapInfoSize) :: w.shared.arenas := by
  refine ⟨?_, List.mem_cons_self ..⟩
  obtain ⟨hst, hhs, -, -⟩ := hC.arena
  have h16 := hC.align; have h32 := hC.minSize
  obtain ⟨hpl0, hpla, hplu, -, -, -⟩ := id hpl
  have hHMS : 0 < C.heapMaxSize := by have := hC.arena.2.2.2; rw [hC.page] at this; omega
  generalize ha : h + C.heapInfoSize = a
  generalize hT : h + sz - p = T
  generalize hw1 : ({ w with
      kernel := k₁
      arenas := fun x => if x = a then some (freshArena p T sz [(h, sz)] (C.heapMaxSize - sz)) else w.arenas x
      shared := { w.shared with arenas := a :: w.shared.arenas,
                                narenas := w.shared.narenas + 1 } } : World) = w₁
  have hfr : ∀ r, w.kernel.Covers r → 0 < r.2 → r.1 + r.2 ≤ h ∨ h + C.heapMaxSize ≤ r.1 :=
    fun r hr h0 => fresh_away hpl hHMS hr h0
  have hanot : a ∉ w.arenaAddrs := by
    intro hm
    have := hfr (a, 1) (covers_one.mpr (hw.structs a hm).1) Nat.one_pos
    simp only at this; omega
  have hama : a ≠ w.mainArena := fun h' => hanot (h' ▸ List.mem_cons_self ..)
  have hanone : w.arenas a = none := by
    have : ¬ (w.arenas a).isSome = true := fun h' => hanot ((hw.arenas a).mpr h')
    cases hx : w.arenas a with
    | none => rfl
    | some _ => rw [hx] at this; simp at this
  have hp0 : p ≠ 0 := by omega
  have hpT : p + T = h + sz := by omega
  have hTm : C.minSize ≤ T := by omega
  have hTa : T % C.align = 0 := by
    have : h % C.align = 0 := by
      have hd1 : C.heapMaxSize ∣ h := Nat.dvd_of_mod_eq_zero hpla
      have hd2 : 16 ∣ C.heapMaxSize := by
        have := hC.arena.2.2.1; rw [hC.page] at this
        exact Nat.dvd_trans ⟨256, rfl⟩ (Nat.dvd_of_mod_eq_zero this)
      rw [h16]; exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd2 hd1)
    rw [h16] at hsza hpa this ⊢; omega
  have hut : h + C.heapMaxSize ≤ 2 ^ 47 := hplu
  have hTs : T ≤ sz := by omega
  have hsz64 : sz < 2 ^ 64 := by omega
  have hb64 : p + T < 2 ^ 64 := by omega
  have hfa := arenaWF_fresh C [(h, sz)] (C.heapMaxSize - sz) hp0 hpa hTa hTm hTs hsz64 hb64
  have hA1 : w₁.arenaAddrs = w.mainArena :: a :: w.shared.arenas := by rw [← hw1]; rfl
  have harr : ∀ x, w₁.arenas x = if x = a then some (freshArena p T sz [(h, sz)] (C.heapMaxSize - sz)) else w.arenas x := by
    intro x; rw [← hw1]
  have hmm1 : w₁.shared.mm = w.shared.mm := by rw [← hw1]
  have hk : w₁.kernel = k₁ := by rw [← hw1]
  have hnot' : a ∉ w.mainArena :: w.shared.arenas := hanot
  -- spans, chunks, live
  generalize hN : (p, T) :: (h, 1) :: (if C.heapMaxSize - sz = 0 then [] else
    [(h + sz, C.heapMaxSize - sz)]) = N
  have hNin : ∀ n ∈ N, h ≤ n.1 ∧ n.1 + n.2 ≤ h + C.heapMaxSize ∧ 0 < n.2 := by
    intro n hn; rw [← hN] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · simp only; have := hC.arena.2.1; omega
    rcases List.mem_cons.mp hn with rfl | hn
    · simp only; omega
    split at hn
    · simp at hn
    · simp only [List.mem_singleton] at hn; subst hn; simp only; omega
  have hNap : Apart N := by
    rw [← hN]
    have hst0 := hC.arena.1
    refine ⟨?_, fun n hn => (hNin n (hN ▸ hn)).2.2⟩
    split
    · simp only [List.pairwise_cons, List.mem_cons, forall_eq, List.not_mem_nil, false_imp_iff,
        implies_true, List.Pairwise.nil, and_true, or_false]
      omega
    · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil,
        false_imp_iff, implies_true, List.Pairwise.nil, and_true, or_false]
      omega
  have hsp1 : w₁.spans = w.aspans w.mainArena ++ N ++
      (w.shared.arenas.flatMap w.aspans ++ w.mmSpans) := by
    rw [World.spans_eq, hA1, flatMap_insert hnot' (G := w.aspans) (fun b hb => by
      simp [World.aspans, harr, hb])]
    simp [World.aspans, harr, freshArena_spans hp0, World.mmSpans, hmm1, List.append_assoc, ← hN]
  have hsp0 : w.spans = w.aspans w.mainArena ++ (w.shared.arenas.flatMap w.aspans ++ w.mmSpans) := by
    rw [World.spans_eq]; simp [World.arenaAddrs, List.flatMap_cons, List.append_assoc]
  have hperm : w₁.spans.Perm (N ++ w.spans) := by
    rw [hsp1, hsp0, List.append_assoc]; exact List.perm_append_comm_assoc ..
  have hch : w₁.chunks = w.chunks := by
    unfold World.chunks
    rw [hA1, flatMap_insert hnot' (G := fun b => ((w.arenas b).map (·.chunks)).getD []) (fun b hb => by
      simp [harr, hb])]
    simp [harr, freshArena_chunks, World.arenaAddrs, List.flatMap_cons]
  have hout : (w₁.arenaAddrs.flatMap fun b => ((w₁.arenas b).map (·.out C)).getD []) =
      (w.arenaAddrs.flatMap fun b => ((w.arenas b).map (·.out C)).getD []) := by
    rw [hA1, flatMap_insert hnot' (G := fun b => ((w.arenas b).map (·.out C)).getD []) (fun b hb => by
      simp [harr, hb])]
    have : (freshArena p T sz [(h, sz)] (C.heapMaxSize - sz)).out C = [] := by
      simp [ArenaSt.out, Chunk.view, freshArena_chunks]
    simp [harr, this, World.arenaAddrs, List.flatMap_cons]
  have hthr : w₁.threads = w.threads := by rw [← hw1]
  have htids : w₁.tids = w.tids := by rw [← hw1]
  have hlive : w₁.live C = w.live C := by
    unfold World.live; rw [hout, hthr, htids]
    simp [SharedSt.live, hmm1]
  -- the new range is apart from the old process memory
  have hnew : ∀ n ∈ N, ∀ r ∈ w.spans, n.1 + n.2 ≤ r.1 ∨ r.1 + r.2 ≤ n.1 := by
    intro n hn r hr
    have := hfr r (hw.covered r hr) (hw.apart.2 r hr)
    have := hNin n hn; omega
  have hap1 : Apart w₁.spans := by
    refine Apart.perm ?_ hperm.symm
    refine ⟨List.pairwise_append.mpr ⟨hNap.1, hw.apart.1, hnew⟩, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hNap.2 r hr
    · exact hw.apart.2 r hr
  have hmaps : ∀ m ∈ w.kernel.maps, m ∈ k₁.maps := fun m hm => by rw [hk3]; exact List.mem_cons_of_mem _ hm
  have hcov1 : ∀ r ∈ w₁.spans, w₁.kernel.Covers r := by
    intro r hr
    rw [hk]
    rcases List.mem_append.mp (hperm.subset hr) with hr | hr
    · intro x hx1 hx2
      have := hNin r hr
      exact .inr ⟨(h, C.heapMaxSize), by rw [hk3]; exact List.mem_cons_self .., by simp only; omega,
        by simp only; omega⟩
    · exact covers_mono hk1 hk2 hmaps (hw.covered r hr)
  have harWF : ∀ x avx, w₁.arenas x = some avx → ArenaWF C avx := by
    intro x avx hx; rw [harr] at hx; split at hx
    · cases hx; exact hfa
    · exact hw.arenaWF x avx hx
  have har1 : ∀ x, x ∈ w₁.arenaAddrs ↔ (w₁.arenas x).isSome := by
    intro x; rw [hA1, harr]
    by_cases hx : x = a
    · subst hx; simp
    · simp only [hx, ite_false, List.mem_cons, false_or]
      rw [← hw.arenas x]; simp [World.arenaAddrs]
  have hsh1 : SharedWF C w₁.shared := by
    rw [← hw1]
    exact { mm := hw.shared.mm
            narenas := by simp [hw.shared.narenas]
            freeListSub := fun x hx => List.mem_cons_of_mem _ (hw.shared.freeListSub x hx) }
  have hmain1 : MainOK C w₁ := by
    intro avm hm
    have hmw : w₁.mainArena = w.mainArena := by rw [← hw1]
    rw [hmw, harr] at hm; simp only [Ne.symm hama, ite_false] at hm
    obtain ⟨h1, h2, h3⟩ := hw.mainOK ht avm hm
    have h12 : MainSbrk w.shared avm ∧ MainBrk C w.kernel avm := ⟨h1, h2⟩
    have h12' : MainSbrk w₁.shared avm ∧ MainBrk C w₁.kernel avm := by
      unfold MainSbrk MainBrk at h12 ⊢
      rw [show w₁.shared.mm = w.shared.mm from hmm1, hk, hk1, hk2]; exact h12
    refine ⟨h12'.1, h12'.2, ?_⟩
    have htot : k₁.total = w.kernel.total + C.heapMaxSize := by
      unfold KernelSt.total; rw [hk1, hk2, hk3]; simp only [List.map_cons, List.sum_cons]; omega
    rw [show w₁.shared.mm = w.shared.mm from hmm1, hk, htot]; omega
  have hheap1 : HeapOK C w₁ := by
    intro x avx hx hne
    rw [harr] at hx; split at hx
    · cases hx
      have hsz0 : sz ≤ C.heapMaxSize := hszu
      refine ⟨⟨h, sz, [], rfl, by simp only [freshArena]; have := hC.arena.1; omega,
        by simp only [freshArena]; omega, by simp only [freshArena]; omega⟩, ?_, ?_⟩
      · intro hp hm; simp only [freshArena, List.mem_singleton] at hm; subst hm
        exact ⟨hpla, hplu, hszu⟩
      · simp [freshArena]
    · exact hw.heapOK ht x avx hx (by rw [← hw1] at hne; exact hne)
  have hinit1 : InitOK w₁ := by
    intro h0; rw [show w₁.shared.init = w.shared.init by rw [← hw1], hi] at h0; cases h0
  refine ⟨?_, by rw [hlive], htids, by rw [← hw1], fun t => by rw [hthr], by rw [← hw1],
    fun b avb hb => by
      rw [harr]
      have hba : b ≠ a := fun h => hanot (h ▸ hw.mem_addrs hb)
      simp [hba, hb]⟩
  exact
    { main := by
        rw [show w₁.mainArena = w.mainArena by rw [← hw1], harr]; simp only [Ne.symm hama, ite_false]; exact hw.main
      arenas := har1
      arenaWF := harWF
      shared := hsh1
      locals := fun t x lx htt hlx => by
        rw [htids] at htt
        exact localWF_of harWF hsh1 hmain1 hinit1 hheap1 hap1 (by rw [hmm1]; exact hw.mmSize) har1
          (by rw [htids]; exact htt) (by rw [hthr]; exact hw.tcacheWF htt) hlx
      arenaNodup := by
        rw [hA1]
        have hn := hw.arenaNodup
        unfold World.arenaAddrs at hn
        rw [List.nodup_cons] at hn ⊢
        refine ⟨fun h' => ?_, List.nodup_cons.mpr ⟨fun h' => hanot (List.mem_cons_of_mem _ h'), hn.2⟩⟩
        rcases List.mem_cons.mp h' with h' | h'
        · exact hama h'.symm
        · exact hn.1 h'
      apart := hap1
      mmSize := by rw [hmm1]; exact hw.mmSize
      parked := fun t tc htt htc i c hc => by
        rw [hch]; rw [htids] at htt; rw [hthr] at htc; exact hw.parked t tc htt htc i c hc
      parkedOnce := by rw [htids, hthr]; exact hw.parkedOnce
      tidsNodup := by rw [htids]; exact hw.tidsNodup
      threadArena := fun t x htt hx => by
        rw [htids] at htt; rw [hthr] at hx; rw [hA1]
        rcases List.mem_cons.mp (hw.threadArena t x htt hx) with h' | h'
        · exact h' ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
      covered := hcov1
      structs := fun x hx => by
        rw [hA1] at hx
        rw [hk]
        have hxa : ∀ r ∈ w₁.spans, x = a ∨ x ∈ w.arenaAddrs → x + 1 ≤ r.1 ∨ r.1 + r.2 ≤ x := by
          intro r hr hxo
          rcases List.mem_append.mp (hperm.subset hr) with hr | hr
          · rcases hxo with rfl | hxo
            · have hhi := hC.heapInfoPos; have hst0 := hC.arena.1
              rw [← hN] at hr
              rcases List.mem_cons.mp hr with rfl | hr
              · simp only; omega
              rcases List.mem_cons.mp hr with rfl | hr
              · simp only; omega
              split at hr
              · simp at hr
              · simp only [List.mem_singleton] at hr; subst hr; simp only; omega
            · have := hfr (x, 1) (covers_one.mpr (hw.structs x hxo).1) Nat.one_pos
              have := hNin r hr
              omega
          · rcases hxo with rfl | hxo
            · have := hfr r (hw.covered r hr) (hw.apart.2 r hr); omega
            · exact (hw.structs x hxo).2 r hr
        have hxo : x = a ∨ x ∈ w.arenaAddrs := by
          rcases List.mem_cons.mp hx with h' | h'
          · exact .inr (h' ▸ List.mem_cons_self ..)
          · rcases List.mem_cons.mp h' with h'' | h''
            · exact .inl h''
            · exact .inr (List.mem_cons_of_mem _ h'')
        refine ⟨?_, fun r hr => hxa r hr hxo⟩
        rcases hxo with rfl | hxo
        · exact .inr ⟨(h, C.heapMaxSize), by rw [hk3]; exact List.mem_cons_self .., by omega, by omega⟩
        · exact has_mono hk1 hk2 hmaps (hw.structs x hxo).1
      heaps := fun x avx hx hne => by
        rw [harr] at hx; split at hx
        · cases hx; simp [freshArena]
        · exact hw.heaps x avx hx (by rw [← hw1] at hne; exact hne) }

theorem mmap_spec (k : KernelSt) (al n : Nat) :
    (k.mmap al n).2.brkStart = k.brkStart ∧ (k.mmap al n).2.brk = k.brk ∧
      (((k.mmap al n).1 = none ∧ (k.mmap al n).2.maps = k.maps) ∨
        ∃ a, (k.mmap al n).1 = some a ∧ (k.mmap al n).2.maps = (a, n) :: k.maps ∧
          k.Placeable al a n) := by
  unfold KernelSt.mmap KernelSt.ask
  cases k.oracle.answer k.asked with
  | refuse => simp
  | ok a =>
    simp only
    split
    · rename_i hp; exact ⟨rfl, rfl, .inr ⟨a, rfl, rfl, hp⟩⟩
    · exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩

theorem heapAttempt_spec (w : World) (sz : Nat) :
    ∃ k', (heapAttempt C w sz).2 = { w with kernel := k' } ∧ k'.brkStart = w.kernel.brkStart ∧
      k'.brk = w.kernel.brk ∧
      (((heapAttempt C w sz).1 = none ∧ k'.maps = w.kernel.maps) ∨
       ∃ h, (heapAttempt C w sz).1 = some (h, sz) ∧ sz ≤ C.heapMaxSize ∧
         k'.maps = (h, C.heapMaxSize) :: w.kernel.maps ∧
         w.kernel.Placeable C.heapMaxSize h C.heapMaxSize) := by
  unfold heapAttempt
  split
  · exact ⟨w.kernel, rfl, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  · rename_i hle
    have hs := mmap_spec w.kernel C.heapMaxSize C.heapMaxSize
    revert hs
    cases w.kernel.mmap C.heapMaxSize C.heapMaxSize with
    | mk r k =>
      cases r with
      | none =>
        rintro ⟨h1, h2, h3⟩
        refine ⟨k, rfl, h1, h2, .inl ⟨rfl, ?_⟩⟩
        rcases h3 with ⟨-, h⟩ | ⟨a, h, -⟩
        · exact h
        · cases h
      | some hh =>
        rintro ⟨h1, h2, h3⟩
        rcases h3 with ⟨h, -⟩ | ⟨a, ha, hmaps, hp⟩
        · cases h
        · cases ha
          exact ⟨k, rfl, h1, h2, .inr ⟨hh, rfl, by omega, hmaps, hp⟩⟩

theorem heapAttempt_none_quiet {w : World} (hw : WorldWF C w) {sz : Nat}
    (h : (heapAttempt C w sz).1 = none) : Quiet C w (heapAttempt C w sz).2 := by
  obtain ⟨k', he, h1, h2, h3⟩ := heapAttempt_spec (C := C) w sz
  rw [he]
  rcases h3 with ⟨-, h3⟩ | ⟨hh, h', -⟩
  · exact kernel_quiet hw k' h1 h2 h3
  · rw [h] at h'; cases h'

theorem alignUp_page (hC : C.Ok) (x : Nat) : alignUp x C.page % C.align = 0 := by
  unfold alignUp; rw [hC.page, hC.align]; omega

/-- **`_int_new_arena`** is quiet and returns an arena. -/
theorem newArena_quiet (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid : Nat} (ht : tid ∈ w.tids)
    (hi : w.shared.init = true) (nb : Nat) :
    Quiet C w (newArena C w tid nb).2 ∧
      ∀ a, (newArena C w tid nb).1 = some a → a ∈ (newArena C w tid nb).2.arenaAddrs := by
  have h16 := hC.align; have h8 := hC.sizeSz
  have hmin : ∀ x, max (alignUp x C.page) heapMinSize % C.align = 0 ∧ 0x8000 ≤ max (alignUp x C.page) heapMinSize := by
    intro x
    have := alignUp_page hC x
    unfold heapMinSize; rw [h16] at this ⊢
    constructor
    · rcases Nat.le_total (alignUp x C.page) 0x8000 with h | h
      · rw [Nat.max_eq_right h]
      · rw [Nat.max_eq_left h]; exact this
    · exact Nat.le_max_right ..
  -- the final step, from a world `wX` quiet from `w` and a granted heap
  have final : ∀ wX : World, Quiet C w wX → ∀ k₂ h sz, k₂.brkStart = wX.kernel.brkStart →
      k₂.brk = wX.kernel.brk → k₂.maps = (h, C.heapMaxSize) :: wX.kernel.maps →
      wX.kernel.Placeable C.heapMaxSize h C.heapMaxSize → sz ≤ C.heapMaxSize →
      sz % C.align = 0 → 0x8000 ≤ sz → ∀ p, h + C.heapInfoSize + C.stateSize ≤ p →
      p ≤ h + C.heapInfoSize + C.stateSize + 15 → p % C.align = 0 →
      Quiet C w (setArena { wX with
        kernel := k₂
        arenas := fun x => if x = h + C.heapInfoSize then some (freshArena p (h + sz - p) sz [(h, sz)] (C.heapMaxSize - sz))
          else wX.arenas x
        shared := { wX.shared with arenas := (h + C.heapInfoSize) :: wX.shared.arenas,
                                   narenas := wX.shared.narenas + 1 } } tid (h + C.heapInfoSize)) ∧
      h + C.heapInfoSize ∈ wX.mainArena :: (h + C.heapInfoSize) :: wX.shared.arenas := by
    intro wX hX k₂ h sz hk1 hk2 hk3 hpl hszu hsza hszl p hp1 hp2 hpa
    have ⟨hq, ha⟩ := addArena_quiet hC hX.wf (hX.tids ▸ ht) (hX.init.trans hi) k₂ hk1 hk2 hk3 hpl
      hszl hszu hsza hp1 hp2 hpa
    have hs := setArena_quiet (tid := tid) hq.wf (List.mem_cons_of_mem _ ha)
    exact ⟨hX.trans (hq.trans hs), List.mem_cons_of_mem _ ha⟩
  have hpx : ∀ q : Nat,
      q ≤ (if (q + C.hdr) % C.align ≠ 0 then q + (C.align - (q + C.hdr) % C.align) else q) ∧
      (if (q + C.hdr) % C.align ≠ 0 then q + (C.align - (q + C.hdr) % C.align) else q) ≤ q + 15 ∧
      (if (q + C.hdr) % C.align ≠ 0 then q + (C.align - (q + C.hdr) % C.align) else q) % C.align = 0 := by
    intro q
    have hh : C.hdr = 16 := by unfold Config.hdr; rw [h8]
    rw [hh, h16]
    split <;> refine ⟨?_, ?_, ?_⟩ <;> omega
  unfold newArena
  dsimp only
  have hm1 := hmin (nb + (C.heapInfoSize + C.stateSize + C.align) + C.topPad)
  have hm2 := hmin (C.heapInfoSize + C.stateSize + C.align)
  generalize max (alignUp (nb + (C.heapInfoSize + C.stateSize + C.align) + C.topPad) C.page) heapMinSize = t1 at hm1 ⊢
  generalize max (alignUp (C.heapInfoSize + C.stateSize + C.align) C.page) heapMinSize = t2 at hm2 ⊢
  obtain ⟨k1, he1, h11, h12, h13⟩ := heapAttempt_spec (C := C) w t1
  cases hA1 : heapAttempt C w t1 with
  | mk r1 w1 =>
    rw [hA1] at he1 h13
    simp only at he1 h13
    subst he1
    cases r1 with
    | some v =>
      obtain ⟨h, sz⟩ := v
      rcases h13 with ⟨h', -⟩ | ⟨hh, h', hszu, hmaps, hpl⟩
      · cases h'
      · simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        have hq := hpx (h + C.heapInfoSize + C.stateSize)
        exact (final w (Quiet.refl hw) k1 h sz h11 h12 hmaps hpl hszu hm1.1 hm1.2 _ hq.1 hq.2.1 hq.2.2) |>
          fun ⟨q, m⟩ => ⟨q, fun a ha => by simp only [Option.some.injEq] at ha; subst ha; exact m⟩
    | none =>
      rcases h13 with ⟨-, hmaps1⟩ | ⟨hh, h', -⟩
      · have hq1 : Quiet C w { w with kernel := k1 } := kernel_quiet hw k1 h11 h12 hmaps1
        simp only
        obtain ⟨k2, he2, h21, h22, h23⟩ := heapAttempt_spec (C := C) { w with kernel := k1 } t2
        cases hA2 : heapAttempt C { w with kernel := k1 } t2 with
        | mk r2 w2 =>
          rw [hA2] at he2 h23
          simp only at he2 h23
          subst he2
          cases r2 with
          | none =>
            rcases h23 with ⟨-, hmaps2⟩ | ⟨hh, h', -⟩
            · exact ⟨hq1.trans (kernel_quiet hq1.wf k2 h21 h22 hmaps2), fun a ha => by cases ha⟩
            · cases h'
          | some v =>
            obtain ⟨h, sz⟩ := v
            rcases h23 with ⟨h', -⟩ | ⟨hh, h', hszu, hmaps, hpl⟩
            · cases h'
            · simp only [Option.some.injEq, Prod.mk.injEq] at h'
              obtain ⟨rfl, rfl⟩ := h'
              have hq := hpx (h + C.heapInfoSize + C.stateSize)
              exact (final { w with kernel := k1 } hq1 k2 h sz h21 h22 hmaps hpl hszu hm2.1 hm2.2 _
                hq.1 hq.2.1 hq.2.2) |>
                fun ⟨q, m⟩ => ⟨q, fun a ha => by simp only [Option.some.injEq] at ha; subst ha; exact m⟩
      · cases h'

/-! ## `arena_get`, `arena_get2`, `arena_get_retry` -/

theorem arenaGet2_quiet (hC : C.Ok) {w w' : World} {tid nb a : Nat} (hw : WorldWF C w)
    (ht : tid ∈ w.tids) (hi : w.shared.init = true) (h : arenaGet2 C w tid nb = .ok (a, w')) :
    Quiet C w w' ∧ a ∈ w'.arenaAddrs := by
  have hmain : w.mainArena ∈ w.arenaAddrs := List.mem_cons_self ..
  unfold arenaGet2 at h
  split at h
  · rename_i b rest hfl
    cases h
    have hb : a ∈ w.arenaAddrs :=
      List.mem_cons_of_mem _ (hw.shared.freeListSub a (by rw [hfl]; exact List.mem_cons_self ..))
    have hc := worldWF_congr (C := C) (w' := { w with shared := { w.shared with freeList := rest } })
      hw rfl rfl rfl rfl rfl (fun x hx => by rw [hfl]; exact List.mem_cons_of_mem _ hx) rfl rfl rfl rfl
      (fun _ => rfl) (fun t ht x h => hw.threadArena t x ht h) id
    have hq : Quiet C w { w with shared := { w.shared with freeList := rest } } :=
      ⟨hc.1, by rw [hc.2], rfl, rfl, fun _ => rfl, rfl, fun _ _ h => h⟩
    exact ⟨hq.trans (setArena_quiet hq.wf hb), hb⟩
  · split at h
    · have hn := newArena_quiet hC hw ht hi (tid := tid) nb
      revert hn h
      cases newArena C w tid nb with
      | mk r w₁ =>
        cases r with
        | some b => intro h hn; cases h; exact ⟨hn.1, hn.2 _ rfl⟩
        | none =>
          intro h hn; cases h
          have hm1 : w₁.mainArena ∈ w₁.arenaAddrs := List.mem_cons_self ..
          exact ⟨hn.1.trans (setArena_quiet hn.1.wf hm1), by rw [← hn.1.main] at *; exact hm1⟩
    · cases h; exact ⟨setArena_quiet hw hmain, hmain⟩

theorem arenaGet_quiet (hC : C.Ok) {w w' : World} {tid nb a : Nat} (hw : WorldWF C w)
    (ht : tid ∈ w.tids) (hi : w.shared.init = true) (h : arenaGet C w tid nb = .ok (a, w')) :
    Quiet C w w' ∧ a ∈ w'.arenaAddrs := by
  unfold arenaGet at h
  split at h
  · rename_i b hb; cases h; exact ⟨Quiet.refl hw, hw.threadArena tid _ ht hb⟩
  · exact arenaGet2_quiet hC hw ht hi h

theorem arenaRetry_quiet (hC : C.Ok) {w w' : World} {tid a nb : Nat} {r : Option Nat}
    (hw : WorldWF C w) (ht : tid ∈ w.tids) (hi : w.shared.init = true)
    (h : arenaRetry C w tid a nb = .ok (r, w')) :
    Quiet C w w' ∧ ∀ b, r = some b → b ∈ w'.arenaAddrs := by
  unfold arenaRetry at h
  split at h
  · cases h; exact ⟨Quiet.refl hw, fun b hb => by cases hb; exact List.mem_cons_self ..⟩
  · cases h2 : arenaGet2 C w tid nb with
    | error e => rw [h2] at h; cases h
    | ok v =>
      obtain ⟨b, w''⟩ := v
      rw [h2] at h; cases h
      have := arenaGet2_quiet hC hw ht hi h2
      exact ⟨this.1, fun b' hb' => by cases hb'; exact this.2⟩

theorem local?_of_mem {w : World} (hw : WorldWF C w) {a : Nat} (ha : a ∈ w.arenaAddrs) (tid : Nat) :
    ∃ l, w.local? tid a = some l := by
  obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp ((hw.arenas a).mp ha)
  exact ⟨_, local?_of hav tid⟩

theorem localAt_ok {w : World} (hw : WorldWF C w) {tid a : Nat} (ha : a ∈ w.arenaAddrs) :
    ∃ l, Ops.localAt w tid a = .ok l ∧ w.local? tid a = some l := by
  obtain ⟨l, hl⟩ := local?_of_mem hw ha tid
  exact ⟨l, by simp [Ops.localAt, hl], hl⟩

theorem localAt_inv {w : World} {tid a : Nat} {l : Local} (h : Ops.localAt w tid a = .ok l) :
    w.local? tid a = some l := by
  unfold Ops.localAt at h
  split at h
  · cases h; assumption
  · cases h

/-! ## `tcache_init`'s `markInternal`: the new struct is held, not live -/

/-- Relabel the `mmap`ed chunk at `c` as `internal`. -/
def mmRelabel (l : Local) (c : Nat) : Local :=
  { l with shared := { l.shared with mm := { l.shared.mm with
      chunks := l.shared.mm.chunks.map fun d => if d.addr = c then { d with use := .internal } else d } } }

theorem mmRelabel_spans (l : Local) (c : Nat) : (mmRelabel l c).spans = l.spans := by
  simp only [Local.spans, mmRelabel, List.map_map]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp]; split <;> rfl

theorem mm_addr_inj {l : Local} (hw : LocalWF C l) {x y : Chunk} (hx : x ∈ l.shared.mm.chunks)
    (hy : y ∈ l.shared.mm.chunks) (he : x.addr = y.addr) : x = y := by
  refine Classical.byContradiction fun hne => ?_
  have hap := Apart.right hw.apart
  have hp := hap.1
  rw [List.pairwise_map] at hp
  have h1 : x.addr + x.size ≤ y.addr ∨ y.addr + y.size ≤ x.addr :=
    pairwise_of_mem (fun h => h.symm) hp hx hy hne
  have h2 : 0 < x.size := hap.2 _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have h3 : 0 < y.size := hap.2 _ (List.mem_map.mpr ⟨y, hy, rfl⟩)
  omega

theorem localWF_mmRelabel {l : Local} (hw : LocalWF C l) (c : Nat) : LocalWF C (mmRelabel l c) := by
  have hm := hw.shared.mm
  refine
    { arena := hw.arena
      shared :=
        { mm :=
            { mpBound := hm.mpBound
              trimMin := hm.trimMin
              use := fun d hd => by
                obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
                split
                · exact .inr rfl
                · exact hm.use d' hd'
              page := fun d hd hu => by
                obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
                split at hu
                · cases hu
                · rename_i h; simp only [h, ite_false] at hu ⊢; exact hm.page d' hd' hu
              nonNull := fun d hd => by
                obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
                split
                · exact hm.nonNull d' hd'
                · exact hm.nonNull d' hd'
              nodup := nodup_map_on (fun x hx y hy hxy => mm_addr_inj hw hx hy (by
                  have := congrArg Chunk.addr hxy
                  revert this; split <;> split <;> simp)) hm.nodup
              mem := by
                simp only [mmRelabel, List.map_map]
                rw [hm.mem]; congr 1
                apply List.map_congr_left; intro d _; simp only [Function.comp]; split <;> rfl }
          narenas := hw.shared.narenas
          freeListSub := hw.shared.freeListSub }
      tcache := hw.tcache
      main := hw.main
      init := fun hi => by
        have := hw.init hi
        refine ⟨this.1, ?_, this.2.2⟩
        show List.map _ l.shared.mm.chunks = []
        rw [this.2.1]; rfl
      apart := by rw [mmRelabel_spans]; exact hw.apart
      mmSize := fun d hd => by
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
        split
        · exact hw.mmSize d' hd'
        · exact hw.mmSize d' hd'
      heap := hw.heap
      sysMain := hw.sysMain }

theorem markInternal_of_mm {w : World} {a p : Nat}
    (h : (w.shared.mm.chunks.any fun x => decide (x.addr = p - C.hdr)) = true) :
    markInternal C w a p = { w with shared := { w.shared with mm := { w.shared.mm with
        chunks := w.shared.mm.chunks.map fun d => if d.addr = p - C.hdr then { d with use := .internal }
          else d } } } := by
  unfold markInternal; simp only [h, ite_true]

theorem markInternal_of_arena {w : World} {a p : Nat}
    (h : ¬ (w.shared.mm.chunks.any fun x => decide (x.addr = p - C.hdr)) = true) :
    markInternal C w a p = { w with arenas := fun x => if x = a then (w.arenas x).map fun av =>
        { av with tiles := av.tiles.relabel (p - C.hdr) .internal } else w.arenas x } := by
  unfold markInternal; simp only [Bool.not_eq_true] at h; simp only [h, Bool.false_eq_true, ite_false]

/-- **`markInternal`** of a live payload `(p, u)` (a chunk of arena `a`, or `mmap`ed): the world
stays well formed and `(p, u)` leaves the live set. -/
theorem markInternal_wf (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid a p u : Nat}
    (ht : tid ∈ w.tids) (ha : a ∈ w.arenaAddrs) (hpu : (p, u) ∈ w.live C)
    (hloc : (∃ av, w.arenas a = some av ∧ (p, u) ∈ av.out C) ∨ (p, u) ∈ w.shared.live C) :
    WorldWF C (markInternal C w a p) ∧
      ((markInternal C w a p).live C).Perm ((w.live C).erase (p, u)) ∧
      (markInternal C w a p).tids = w.tids ∧ (markInternal C w a p).shared.init = w.shared.init ∧
      (markInternal C w a p).threads = w.threads ∧ (markInternal C w a p).mainArena = w.mainArena := by
  obtain ⟨l, hl⟩ := local?_of_mem hw ha tid
  obtain ⟨av, hav, hlav, hla, hlm, hlt, hls, hlk⟩ := local?_fields hl
  have hwl := hw.locals tid a l ht hl
  have hsp := localSp hw ht hl
  have hpl : (p, u) ∈ l.live C := by
    rcases hloc with ⟨av', hav', hout⟩ | hm
    · rw [hav] at hav'; cases hav'
      refine mem_llive.mpr (.inl ⟨by rw [hlav]; exact hout, fun hp => ?_⟩)
      exact parked_not_live hw (mem_allParked.mpr ⟨tid, ht, by rw [← hlt]; exact hp⟩) hpu
    · exact mem_llive.mpr (.inr (by rw [hls]; exact hm))
  have harr : ∀ x, (if x = a then some l.av else w.arenas x) = w.arenas x := fun x => by
    by_cases hx : x = a
    · subst hx; rw [hav, hlav]; simp
    · simp [hx]
  have hthr : (fun t => if t = tid then w.threads tid else w.threads t) = w.threads := by
    funext t; by_cases h : t = tid
    · subst h; simp
    · simp [h]
  have hK : ∀ l'' : Local, l''.thread = l.thread → KeptAway l l'' := by
    intro l'' h tc i e htc he _; exact ⟨tc, by rw [h]; exact htc, he⟩
  by_cases hany : (w.shared.mm.chunks.any fun x => decide (x.addr = p - C.hdr)) = true
  · -- an `mmap`ed chunk
    rw [markInternal_of_mm hany]
    obtain ⟨m, hm, hma⟩ := List.any_eq_true.mp hany
    have hma' : m.addr = p - C.hdr := by simpa using hma
    -- `(p, u)` is `m`'s payload
    have hpm : (p, u) ∈ w.shared.live C := by
      rcases hloc with ⟨av', hav', hout⟩ | hm'
      · exfalso
        obtain ⟨d, hd, -, hde⟩ := mem_out.mp hout
        simp only [Prod.mk.injEq] at hde
        exact clash_mm hw hav' hd hm (by omega)
      · exact hm'
    obtain ⟨m', hm', hmu, hme⟩ := mem_shlive.mp hpm
    simp only [Prod.mk.injEq] at hme
    have hmm : m' = m := mm_addr_inj (l := l) hwl (by rw [hls]; exact hm') (by rw [hls]; exact hm)
      (by omega)
    subst hmm
    have heq : ({ w with shared := { w.shared with mm := { w.shared.mm with
        chunks := w.shared.mm.chunks.map fun d => if d.addr = p - C.hdr then { d with use := .internal }
          else d } } } : World) = w.put tid (mmRelabel l (p - C.hdr)) := by
      simp only [World.put, mmRelabel, hla, hlt, hls, hlk, harr, hthr]
    rw [heq]
    have hwl'' := localWF_mmRelabel hwl (p - C.hdr)
    have hF : Frame C l (mmRelabel l (p - C.hdr)) [(p, u)] :=
      { avAddr := rfl, isMain := rfl
        spatial := fun r _ hc haw => ⟨hc, by rw [mmRelabel_spans]; exact haw⟩
        covered := by rw [mmRelabel_spans]; exact hsp.covered
        brkStart := rfl
        nonMain := fun _ => ⟨rfl, rfl⟩
        acct := fun _ => Nat.le_refl _
        init := rfl
        arenas := ⟨rfl, rfl, rfl⟩
        arena := rfl
        heaps := id
        clients := fun c hc _ _ => hc
        fresh := fun tc' i e htc he => .inl ⟨tc', i, htc, he⟩ }
    have hperm : ((mmRelabel l (p - C.hdr)).live C).Perm ((l.live C).erase (p, u)) := by
      refine (List.perm_ext_iff_of_nodup (nodup_of_liveApart (llive_apart hC hwl''))
        ((nodup_of_liveApart (llive_apart hC hwl)).erase _)).mpr fun y => ?_
      rw [(nodup_of_liveApart (llive_apart hC hwl)).mem_erase_iff, mem_llive, mem_llive]
      have hsh : ∀ y, y ∈ (mmRelabel l (p - C.hdr)).shared.live C ↔
          y ∈ l.shared.live C ∧ y ≠ (p, u) := by
        intro y
        rw [mem_shlive, mem_shlive]
        constructor
        · rintro ⟨d, hd, hdu, rfl⟩
          obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
          by_cases hda : d'.addr = p - C.hdr
          · simp [hda] at hdu
          · simp only [hda, ite_false] at hdu ⊢
            refine ⟨⟨d', hd', hdu, rfl⟩, fun he => hda ?_⟩
            simp only [Prod.mk.injEq] at he; omega
        · rintro ⟨⟨d, hd, hdu, rfl⟩, hne⟩
          have hda : d.addr ≠ p - C.hdr := fun h => hne (by
            have := mm_addr_inj (l := l) hwl hd (by rw [hls]; exact hm') (by omega)
            subst this; simp only [Prod.mk.injEq]; omega)
          exact ⟨d, List.mem_map.mpr ⟨d, hd, by simp [hda]⟩, hdu, rfl⟩
      constructor
      · rintro (⟨hy, hnp⟩ | hy)
        · refine ⟨fun he => ?_, .inl ⟨hy, hnp⟩⟩
          subst he
          obtain ⟨d, hd, -, hde⟩ := mem_out.mp hy
          simp only [Prod.mk.injEq] at hde
          exact clash_mm hw hav (by rw [← hlav]; exact hd) hm' (by omega)
        · exact ⟨((hsh y).mp hy).2, .inr ((hsh y).mp hy).1⟩
      · rintro ⟨hne, (⟨hy, hnp⟩ | hy)⟩
        · exact .inl ⟨hy, hnp⟩
        · exact .inr ((hsh y).mpr ⟨hy, hne⟩)
    have := put_free hC hw ht hl hwl hwl'' hF (hK _ rfl) hpu hpl hperm
    refine ⟨this.1, this.2, rfl, ?_, ?_, rfl⟩
    · show l.shared.init = w.shared.init; rw [hls]
    · show (fun t => if t = tid then l.thread else w.threads t) = w.threads; rw [hlt]; exact hthr
  · -- an arena chunk
    rw [markInternal_of_arena hany]
    have hout : (p, u) ∈ av.out C := by
      rcases hloc with ⟨av', hav', hout⟩ | hm'
      · rw [hav] at hav'; cases hav'; exact hout
      · exfalso
        obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hm'
        simp only [Prod.mk.injEq] at hme
        exact hany (List.any_eq_true.mpr ⟨m, hm, by simp; omega⟩)
    obtain ⟨d, hd, hdu, hde⟩ := mem_out.mp hout
    simp only [Prod.mk.injEq] at hde
    obtain ⟨rfl, rfl⟩ := hde
    have hdl : d ∈ l.av.tiles.heapChunks := by rw [hlav]; exact hd
    obtain ⟨hwl'', hout''⟩ := relabelInternal_step hwl hdl hdu
    have hc : d.addr + C.hdr - C.hdr = d.addr := by omega
    have heq : ({ w with arenas := fun x => if x = a then (w.arenas x).map fun av =>
        { av with tiles := av.tiles.relabel (d.addr + C.hdr - C.hdr) .internal } else w.arenas x } : World) =
        w.put tid (l.relabel d.addr .internal) := by
      have harr' : ∀ x, (if x = a then some (l.relabel d.addr .internal).av else w.arenas x) =
          (if x = a then (w.arenas x).map fun av =>
            { av with tiles := av.tiles.relabel d.addr .internal } else w.arenas x) := fun x => by
        by_cases hx : x = a
        · subst hx; rw [hav]; simp [Local.relabel, hlav]
        · simp [hx]
      rw [hc]
      simp only [World.put, Local.relabel, hla, hlt, hls, hlk, hthr]
      simp only [← harr']
      rfl
    rw [heq]
    have hspr : (l.relabel d.addr .internal).spans = l.spans := by
      unfold Local.spans ArenaSt.spans
      rw [show (l.relabel d.addr .internal).av.heapSpans = l.av.heapSpans from rfl,
        show (l.relabel d.addr .internal).shared = l.shared from rfl,
        show (l.relabel d.addr .internal).av.tiles = l.av.tiles.relabel d.addr .internal from rfl,
        TopSt.spans_relabel]
    have hF : Frame C l (l.relabel d.addr .internal) [(d.addr + C.hdr, d.size - C.sizeSz)] :=
      { avAddr := rfl, isMain := rfl
        spatial := fun r _ hc haw => ⟨hc, by rw [hspr]; exact haw⟩
        covered := by rw [hspr]; exact hsp.covered
        brkStart := rfl
        nonMain := fun _ => ⟨rfl, rfl⟩
        acct := fun _ => Nat.le_refl _
        init := rfl
        arenas := ⟨rfl, rfl, rfl⟩
        arena := rfl
        heaps := id
        clients := fun c hc hcu hnf => by
          have hne : c.addr ≠ d.addr := fun h => hnf (by
            have := chunk_unique hwl.arena.tiles.nodup hc hdl h
            subst this; simp [usable])
          show c ∈ (l.av.tiles.relabel d.addr .internal).heapChunks
          rw [TopSt.heapChunks_relabel]
          exact List.mem_map.mpr ⟨c, hc, Chunk.relabelAt_of_ne hne⟩
        fresh := fun tc' i e htc he => .inl ⟨tc', i, htc, he⟩ }
    have hal : (d.addr + C.hdr, d.size - C.sizeSz) ∈ l.arenaLive C := by
      have := mem_llive.mp hpl
      rcases this with ⟨h1, h2⟩ | h3
      · exact List.mem_filter.mpr ⟨h1, by simpa [contains_false] using h2⟩
      · exfalso
        obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp h3
        simp only [Prod.mk.injEq] at hme
        exact clash_mm hw hav hd (by rw [← hls]; exact hm) (by omega)
    have hperm := live_of_out (C := C) (l := l) (l' := l.relabel d.addr .internal) rfl rfl
      (by rw [hout'']; simp [usable]) hal
    have := put_free hC hw ht hl hwl hwl'' hF (hK _ rfl) hpu hpl hperm
    refine ⟨this.1, this.2, rfl, ?_, ?_, rfl⟩
    · show l.shared.init = w.shared.init; rw [hls]
    · show (fun t => if t = tid then l.thread else w.threads t) = w.threads; rw [hlt]; exact hthr

end Silmaril.Libc.Ptmalloc.Algo
