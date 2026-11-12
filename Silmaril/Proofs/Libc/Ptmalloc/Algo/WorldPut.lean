module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.World
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Tiling
public import Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs

/-!
# ptmalloc algorithm: putting a body's result back into the world

* `Algo.localSp`: every view of a well-formed world has the spatial facts `LocalSp`.
* `Algo.worldWF_put`: a body run on a view, well formed after and with a `Frame`, gives a
  well-formed world back (`World.put`).
* `Algo.live_put`: the world's live set changes as the view's does.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## The world's spans, split at one arena -/

/-- The spans of arena `b` (none if there is no arena there). -/
def _root_.Silmaril.Libc.Ptmalloc.World.aspans (w : World) (b : Nat) : List (Nat × Nat) := ((w.arenas b).map (·.spans)).getD []

/-- The spans of the `mmap`ed chunks. -/
def _root_.Silmaril.Libc.Ptmalloc.World.mmSpans (w : World) : List (Nat × Nat) := w.shared.mm.chunks.map fun c => (c.addr, c.size)

/-- The spans of every arena but `a`. -/
def _root_.Silmaril.Libc.Ptmalloc.World.others (w : World) (a : Nat) : List (Nat × Nat) := (w.arenaAddrs.erase a).flatMap w.aspans

theorem _root_.Silmaril.Libc.Ptmalloc.World.spans_eq (w : World) : w.spans = w.arenaAddrs.flatMap w.aspans ++ w.mmSpans := rfl

theorem spans_perm {w : World} {a : Nat} (ha : a ∈ w.arenaAddrs) :
    w.spans.Perm (w.aspans a ++ w.mmSpans ++ w.others a) := by
  rw [World.spans_eq]
  have h1 : (w.arenaAddrs.flatMap w.aspans).Perm (w.aspans a ++ w.others a) := by
    have := (List.perm_cons_erase ha).flatMap_right w.aspans
    simpa [World.others] using this
  refine (h1.append_right _).trans ?_
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

theorem Apart.cross {X Y : List (Nat × Nat)} (h : Apart (X ++ Y)) {r s : Nat × Nat} (hr : r ∈ X)
    (hs : s ∈ Y) : r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 :=
  (List.pairwise_append.mp h.1).2.2 r hr s hs

theorem Apart.left {X Y : List (Nat × Nat)} (h : Apart (X ++ Y)) : Apart X :=
  h.sublist (List.sublist_append_left ..)

theorem Apart.right {X Y : List (Nat × Nat)} (h : Apart (X ++ Y)) : Apart Y :=
  h.sublist (List.sublist_append_right ..)

theorem Apart.append {X Y : List (Nat × Nat)} (hx : Apart X) (hy : Apart Y)
    (hxy : ∀ r ∈ X, ∀ s ∈ Y, r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1) : Apart (X ++ Y) :=
  ⟨List.pairwise_append.mpr ⟨hx.1, hy.1, hxy⟩, fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact hx.2 r h
    · exact hy.2 r h⟩

/-- The world split at arena `a` is apart. -/
theorem _root_.Silmaril.Libc.Ptmalloc.WorldWF.apart_at {w : World} (hw : WorldWF C w) {a : Nat} (ha : a ∈ w.arenaAddrs) :
    Apart (w.aspans a ++ w.mmSpans ++ w.others a) :=
  hw.apart.perm (spans_perm ha)

theorem local?_some {w : World} {tid a : Nat} {l : Local} (h : w.local? tid a = some l) :
    ∃ av, w.arenas a = some av ∧
      l = { avAddr := a, isMain := decide (a = w.mainArena), av, thread := w.threads tid,
            shared := w.shared, kernel := w.kernel } := by
  unfold World.local? at h
  cases ha : w.arenas a with
  | none => rw [ha] at h; cases h
  | some av => rw [ha] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨av, rfl, h.symm⟩

theorem aspans_of {w : World} {a : Nat} {av : ArenaSt} (h : w.arenas a = some av) :
    w.aspans a = av.spans := by simp [World.aspans, h]

theorem _root_.Silmaril.Libc.Ptmalloc.WorldWF.mem_addrs {w : World} (hw : WorldWF C w) {a : Nat} {av : ArenaSt}
    (h : w.arenas a = some av) : a ∈ w.arenaAddrs := (hw.arenas a).mpr (by simp [h])

theorem local_spans {w : World} {tid a : Nat} {l : Local} (h : w.local? tid a = some l) :
    l.spans = w.aspans a ++ w.mmSpans := by
  obtain ⟨av, hav, rfl⟩ := local?_some h
  simp [Local.spans, aspans_of hav, World.mmSpans]

theorem mem_world_chunks {w : World} {d : Chunk} (hd : d ∈ w.chunks) :
    ∃ b ∈ w.arenaAddrs, ∃ av, w.arenas b = some av ∧ d ∈ av.chunks := by
  unfold World.chunks at hd
  obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
  cases hab : w.arenas b with
  | none => rw [hab] at hdb; cases hdb
  | some av => rw [hab] at hdb; exact ⟨b, hb, av, hab, hdb⟩

theorem mem_world_chunks_of {w : World} {b : Nat} {av : ArenaSt} (hb : b ∈ w.arenaAddrs)
    (hab : w.arenas b = some av) {d : Chunk} (hd : d ∈ av.chunks) : d ∈ w.chunks := by
  unfold World.chunks
  exact List.mem_flatMap.mpr ⟨b, hb, by rw [hab]; exact hd⟩

theorem span_mem_spans {av : ArenaSt} {d : Chunk} (hd : d ∈ av.chunks) :
    (d.addr, d.size) ∈ av.spans := by
  unfold ArenaSt.spans TopSt.spans
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨d, hd, rfl⟩))

theorem mem_others {w : World} {a b : Nat} (hb : b ∈ w.arenaAddrs) (hne : b ≠ a) {av : ArenaSt}
    (hab : w.arenas b = some av) {r : Nat × Nat} (hr : r ∈ av.spans) : r ∈ w.others a := by
  unfold World.others
  exact List.mem_flatMap.mpr ⟨b, List.mem_erase_of_ne hne |>.mpr hb, by rw [aspans_of hab]; exact hr⟩

theorem mem_spans_of_others {w : World} {a : Nat} (ha : a ∈ w.arenaAddrs) {r : Nat × Nat}
    (hr : r ∈ w.others a) : r ∈ w.spans :=
  (spans_perm ha).symm.subset (List.mem_append_right _ hr)

theorem mem_spans_of_local {w : World} {tid a : Nat} {l : Local} (hl : w.local? tid a = some l)
    (ha : a ∈ w.arenaAddrs) {r : Nat × Nat} (hr : r ∈ l.spans) : r ∈ w.spans := by
  rw [local_spans hl] at hr
  exact (spans_perm ha).symm.subset (List.mem_append_left _ hr)

/-- A chunk of another arena is apart from the view. -/
theorem away_of_other {w : World} (hw : WorldWF C w) {tid a : Nat} {l : Local}
    (hl : w.local? tid a = some l) {b : Nat} (hb : b ∈ w.arenaAddrs) (hne : b ≠ a) {av : ArenaSt}
    (hab : w.arenas b = some av) {r : Nat × Nat} (hr : r ∈ av.spans) : Away l.spans r := by
  obtain ⟨av₀, hav₀, -⟩ := local?_some hl
  have ha := hw.mem_addrs hav₀
  intro s hs
  rw [local_spans hl] at hs
  exact (Apart.cross (hw.apart_at ha) hs (mem_others hb hne hab hr)).symm

/-- **Every view of a well-formed world has the spatial facts.** -/
theorem localSp {w : World} (hw : WorldWF C w) {tid a : Nat} {l : Local} (ht : tid ∈ w.tids)
    (hl : w.local? tid a = some l) : LocalSp C l := by
  obtain ⟨av, hav, hleq⟩ := local?_some hl
  have ha := hw.mem_addrs hav
  refine ⟨fun r hr => ?_, fun tc htc i e he => ?_, fun hm => ?_⟩
  · have := hw.covered r (mem_spans_of_local hl ha hr)
    rw [hleq]; exact this
  · rw [hleq] at htc
    obtain ⟨d, hd, hda, hds, hdu⟩ := hw.parked tid tc ht htc i e he
    obtain ⟨b, hb, avb, hab, hdb⟩ := mem_world_chunks hd
    by_cases hba : b = a
    · subst hba
      rw [hav] at hab; cases hab
      left; rw [hleq]; exact ⟨d, hdb, hda, hds, hdu⟩
    · right
      have hr : e = (d.addr, d.size) := by rw [hda, hds]
      rw [hr]
      refine ⟨away_of_other hw hl hb hba hab (span_mem_spans hdb), ?_⟩
      have := hw.covered _ (mem_spans_of_others ha (mem_others hb hba hab (span_mem_spans hdb)))
      rw [hleq]; exact this
  · rw [hleq] at hm ⊢
    exact hw.heaps a av hav (by simpa using hm)

/-! ## `WorldWF` from its parts -/

/-- The main arena agrees with `mp_` and the kernel. -/
def MainOK (C : Config) (w : World) : Prop :=
  ∀ av, w.arenas w.mainArena = some av → MainSbrk w.shared av ∧ MainBrk C w.kernel av ∧
    av.tiles.systemMem + w.shared.mm.mp.mmappedMem ≤ w.kernel.total

/-- Before `ptmalloc_init`: no heap, no `mmap`ed chunk, no tcache. -/
def InitOK (w : World) : Prop :=
  w.shared.init = false → (∀ b av, w.arenas b = some av → av.tiles.start = 0) ∧
    w.shared.mm.chunks = [] ∧ ∀ t ∈ w.tids, (w.threads t).tcache = none

theorem local?_of {w : World} {a : Nat} {av : ArenaSt} (h : w.arenas a = some av) (tid : Nat) :
    w.local? tid a =
      some ⟨a, decide (a = w.mainArena), av, w.threads tid, w.shared, w.kernel⟩ := by
  simp [World.local?, h]

theorem _root_.Silmaril.Libc.Ptmalloc.WorldWF.mainOK {w : World} (hw : WorldWF C w) {tid : Nat}
    (ht : tid ∈ w.tids) : MainOK C w := fun av hav =>
  have h := hw.locals tid _ _ ht (local?_of hav tid)
  ⟨(h.main (by simp)).1, (h.main (by simp)).2, h.sysMain (by simp)⟩

/-- Every non-main arena's heaps are well formed. -/
def HeapOK (C : Config) (w : World) : Prop :=
  ∀ a av, w.arenas a = some av → a ≠ w.mainArena → HeapWF C av

theorem _root_.Silmaril.Libc.Ptmalloc.WorldWF.heapOK {w : World} (hw : WorldWF C w) {tid : Nat}
    (ht : tid ∈ w.tids) : HeapOK C w := fun _ _ hav hne =>
  (hw.locals tid _ _ ht (local?_of hav tid)).heap (by simpa using hne)

theorem _root_.Silmaril.Libc.Ptmalloc.WorldWF.initOK {w : World} (hw : WorldWF C w) {tid : Nat}
    (ht : tid ∈ w.tids) : InitOK w := by
  intro hi
  obtain ⟨avm, havm⟩ := Option.isSome_iff_exists.mp hw.main
  have h0 := (hw.locals tid _ _ ht (local?_of havm tid)).init hi
  refine ⟨fun b av hav => ((hw.locals tid _ _ ht (local?_of hav tid)).init hi).1, h0.2.1,
    fun t htt => ((hw.locals t _ _ htt (local?_of havm t)).init hi).2.2⟩

theorem _root_.Silmaril.Libc.Ptmalloc.WorldWF.tcacheWF {w : World} (hw : WorldWF C w) {t : Nat}
    (ht : t ∈ w.tids) : ∀ tc, (w.threads t).tcache = some tc → TcacheWF C tc := by
  obtain ⟨avm, havm⟩ := Option.isSome_iff_exists.mp hw.main
  exact (hw.locals t _ _ ht (local?_of havm t)).tcache

/-- **A view of a world is well formed** when the world's parts are. -/
theorem localWF_of {w : World}
    (hA : ∀ a av, w.arenas a = some av → ArenaWF C av) (hS : SharedWF C w.shared)
    (hM : MainOK C w) (hI : InitOK w) (hH : HeapOK C w)
    (hap : Apart w.spans) (hmm : ∀ c ∈ w.shared.mm.chunks, C.hdr < c.size ∧ c.addr + c.size ≤ 2 ^ 64)
    (har : ∀ a, a ∈ w.arenaAddrs ↔ (w.arenas a).isSome)
    {t a : Nat} {l : Local} (ht : t ∈ w.tids)
    (hT : ∀ tc, (w.threads t).tcache = some tc → TcacheWF C tc)
    (hl : w.local? t a = some l) : LocalWF C l := by
  obtain ⟨av, hav, rfl⟩ := local?_some hl
  have ha : a ∈ w.arenaAddrs := (har a).mpr (by simp [hav])
  refine
    { arena := hA a av hav
      shared := hS
      tcache := hT
      main := fun hm => by
        have : a = w.mainArena := by simpa using hm
        subst this; exact ⟨(hM av hav).1, (hM av hav).2.1⟩
      sysMain := fun hm => by
        have : a = w.mainArena := by simpa using hm
        subst this; exact (hM av hav).2.2
      init := fun hi => ⟨(hI hi).1 a av hav, (hI hi).2.1, (hI hi).2.2 t ht⟩
      apart := ?_
      mmSize := hmm
      heap := fun hm => hH a av hav (by simpa using hm) }
  have := Apart.left (hap.perm (spans_perm ha))
  simpa [Local.spans, aspans_of hav, World.mmSpans] using this

/-! ## The world after a body: spans -/

section put

variable {w : World} {tid a : Nat} {l l' : Local} {freed : List (Nat × Nat)}

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.flatMap_cons]
    rw [h x (by simp), flatMap_congr' (fun y hy => h y (by simp [hy]))]

theorem put_addrs (hl : w.local? tid a = some l) (hF : Frame C l l' freed) :
    (w.put tid l').arenaAddrs = w.arenaAddrs := by
  obtain ⟨av, hav, rfl⟩ := local?_some hl
  simp [World.arenaAddrs, World.put, hF.arenas.1]

theorem put_arenas (hl : w.local? tid a = some l) (hF : Frame C l l' freed) (x : Nat) :
    (w.put tid l').arenas x = if x = a then some l'.av else w.arenas x := by
  obtain ⟨av, hav, rfl⟩ := local?_some hl
  simp [World.put, hF.avAddr]

theorem put_others (hw : WorldWF C w) (hl : w.local? tid a = some l) (hF : Frame C l l' freed) :
    (w.put tid l').others a = w.others a := by
  unfold World.others
  rw [put_addrs hl hF]
  refine flatMap_congr' fun b hb => ?_
  have hne : b ≠ a := ((hw.arenaNodup.mem_erase_iff).mp hb).1
  simp [World.aspans, put_arenas hl hF, hne]

theorem put_local_spans (hl : w.local? tid a = some l) (hF : Frame C l l' freed) :
    l'.spans = (w.put tid l').aspans a ++ (w.put tid l').mmSpans := by
  obtain ⟨av, hav, rfl⟩ := local?_some hl
  simp [Local.spans, World.aspans, World.mmSpans, World.put, hF.avAddr]

theorem put_spans_perm (hw : WorldWF C w) (hl : w.local? tid a = some l) (hF : Frame C l l' freed) :
    (w.put tid l').spans.Perm (l'.spans ++ w.others a) := by
  obtain ⟨av, hav, -⟩ := local?_some hl
  have ha : a ∈ (w.put tid l').arenaAddrs := by rw [put_addrs hl hF]; exact hw.mem_addrs hav
  have := spans_perm ha
  rwa [put_others hw hl hF, ← put_local_spans hl hF] at this

/-- The other arenas' spans are apart from the view's and the process's memory. -/
theorem others_facts (hw : WorldWF C w) (hl : w.local? tid a = some l) {r : Nat × Nat}
    (hr : r ∈ w.others a) : 0 < r.2 ∧ l.kernel.Covers r ∧ Away l.spans r := by
  obtain ⟨av, hav, hleq⟩ := local?_some hl
  have ha := hw.mem_addrs hav
  have hap := hw.apart_at ha
  refine ⟨hap.2 r (List.mem_append_right _ hr), ?_, fun s hs => ?_⟩
  · rw [hleq]; exact hw.covered r (mem_spans_of_others ha hr)
  · rw [local_spans hl] at hs
    exact (Apart.cross hap hs hr).symm

theorem put_apart (hw : WorldWF C w) (hl : w.local? tid a = some l) (hwf' : LocalWF C l')
    (hF : Frame C l l' freed) : Apart (l'.spans ++ w.others a) := by
  obtain ⟨av, hav, -⟩ := local?_some hl
  refine Apart.append hwf'.apart (Apart.right (hw.apart_at (hw.mem_addrs hav))) fun r hr s hs => ?_
  obtain ⟨h0, hc, haw⟩ := others_facts hw hl hs
  exact ((hF.spatial s h0 hc haw).2 r hr).symm

end put

/-! ## Membership in the live and parked sets -/

/-- A tcache entry's payload. -/
def epay (C : Config) (e : Nat × Nat) : Nat × Nat := (e.1 + C.hdr, e.2 - C.sizeSz)

/-- Every thread's parked payloads. -/
def allParked (C : Config) (w : World) : List (Nat × Nat) := w.tids.flatMap fun t => (w.threads t).parked C

theorem mem_parked {t : ThreadSt} {y : Nat × Nat} :
    y ∈ t.parked C ↔ ∃ tc, t.tcache = some tc ∧ ∃ i < C.tcacheBins, ∃ e ∈ tc.bins i, y = epay C e := by
  unfold ThreadSt.parked
  cases t.tcache with
  | none => simp
  | some tc =>
    simp only [Option.map_some, Option.getD_some, TcacheSt.payloads, List.mem_map, List.mem_flatMap,
      List.mem_range, Option.some.injEq, exists_eq_left', epay]
    constructor
    · rintro ⟨e, ⟨i, hi, he⟩, rfl⟩; exact ⟨i, hi, e, he, rfl⟩
    · rintro ⟨i, hi, e, he, rfl⟩; exact ⟨e, ⟨i, hi, he⟩, rfl⟩

theorem mem_parked_of {t : ThreadSt} {tc : TcacheSt} (hT : TcacheWF C tc) (h : t.tcache = some tc)
    {i : Nat} {e : Nat × Nat} (he : e ∈ tc.bins i) : epay C e ∈ t.parked C := by
  refine mem_parked.mpr ⟨tc, h, i, ?_, e, he, rfl⟩
  apply Nat.lt_of_not_le; intro hi; rw [hT.bins i hi] at he; cases he

theorem mem_allParked {w : World} {y : Nat × Nat} :
    y ∈ allParked C w ↔ ∃ t ∈ w.tids, y ∈ (w.threads t).parked C := by
  simp [allParked]

theorem mem_out {av : ArenaSt} {y : Nat × Nat} :
    y ∈ av.out C ↔ ∃ c ∈ av.chunks, c.use = .client ∧ y = (c.addr + C.hdr, c.size - C.sizeSz) := by
  simp only [ArenaSt.out, Chunk.view, List.mem_map, List.mem_filter, decide_eq_true_eq, usable,
    Bool.false_eq_true, ite_false]
  constructor
  · rintro ⟨c, ⟨hc, hu⟩, rfl⟩; exact ⟨c, hc, hu, rfl⟩
  · rintro ⟨c, hc, hu, rfl⟩; exact ⟨c, ⟨hc, hu⟩, rfl⟩

theorem mem_shlive {sh : SharedSt} {y : Nat × Nat} :
    y ∈ sh.live C ↔ ∃ c ∈ sh.mm.chunks, c.use = .client ∧ y = (c.addr + C.hdr, c.size - 2 * C.sizeSz) := by
  simp only [SharedSt.live, List.mem_map, List.mem_filter, decide_eq_true_eq, usable, ite_true]
  constructor
  · rintro ⟨c, ⟨hc, hu⟩, rfl⟩; exact ⟨c, hc, hu, rfl⟩
  · rintro ⟨c, hc, hu, rfl⟩; exact ⟨c, ⟨hc, hu⟩, rfl⟩

theorem contains_false {l : List (Nat × Nat)} {y : Nat × Nat} : l.contains y = false ↔ y ∉ l := by
  rw [← List.contains_iff_mem]; cases l.contains y <;> simp

theorem mem_live {w : World} {y : Nat × Nat} :
    y ∈ w.live C ↔ ((∃ b ∈ w.arenaAddrs, ∃ av, w.arenas b = some av ∧ y ∈ av.out C) ∧
      y ∉ allParked C w) ∨ y ∈ w.shared.live C := by
  unfold World.live
  simp only [List.mem_append, List.mem_filter, List.mem_flatMap, Bool.not_eq_true', contains_false]
  constructor
  · rintro (⟨⟨b, hb, hy⟩, hp⟩ | h)
    · left
      refine ⟨?_, fun h => hp (by simpa [allParked] using h)⟩
      cases hab : w.arenas b with
      | none => rw [hab] at hy; cases hy
      | some av => rw [hab] at hy; exact ⟨b, hb, av, hab, hy⟩
    · exact .inr h
  · rintro (⟨⟨b, hb, av, hab, hy⟩, hp⟩ | h)
    · left; exact ⟨⟨b, hb, by rw [hab]; exact hy⟩, fun h => hp (by simpa [allParked] using h)⟩
    · exact .inr h

theorem mem_llive {l : Local} {y : Nat × Nat} :
    y ∈ l.live C ↔ (y ∈ l.av.out C ∧ y ∉ l.thread.parked C) ∨ y ∈ l.shared.live C := by
  unfold Local.live
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true', contains_false]

theorem addr_clash {X Y : List (Nat × Nat)} (h : Apart (X ++ Y)) {r s : Nat × Nat} (hr : r ∈ X)
    (hs : s ∈ Y) (he : r.1 = s.1) : False := by
  have h1 := Apart.cross h hr hs
  have h2 := h.2 r (List.mem_append_left _ hr)
  have h3 := h.2 s (List.mem_append_right _ hs)
  omega

/-- In a well-formed world, two chunks of different arenas are at different addresses. -/
theorem clash_arenas {w : World} (hw : WorldWF C w) {b b' : Nat} (hne : b ≠ b') {av av' : ArenaSt}
    (hb : w.arenas b = some av) (hb' : w.arenas b' = some av') {d d' : Chunk} (hd : d ∈ av.chunks)
    (hd' : d' ∈ av'.chunks) (he : d.addr = d'.addr) : False := by
  have hm := hw.mem_addrs hb
  have hm' := hw.mem_addrs hb'
  refine addr_clash (X := w.aspans b ++ w.mmSpans) (hw.apart_at hm) (r := (d.addr, d.size))
    (s := (d'.addr, d'.size)) ?_ (mem_others hm' (Ne.symm hne) hb' (span_mem_spans hd')) he
  rw [aspans_of hb]; exact List.mem_append_left _ (span_mem_spans hd)

/-- In a well-formed world, an arena chunk and an `mmap`ed chunk are at different addresses. -/
theorem clash_mm {w : World} (hw : WorldWF C w) {b : Nat} {av : ArenaSt}
    (hb : w.arenas b = some av) {d m : Chunk} (hd : d ∈ av.chunks) (hm : m ∈ w.shared.mm.chunks)
    (he : d.addr = m.addr) : False := by
  have hap := Apart.left (hw.apart_at (hw.mem_addrs hb))
  refine addr_clash hap (r := (d.addr, d.size)) (s := (m.addr, m.size)) ?_ ?_ he
  · rw [aspans_of hb]; exact span_mem_spans hd
  · exact List.mem_map.mpr ⟨m, hm, rfl⟩

theorem epay_inj {e e' : Nat × Nat} (h : epay C e = epay C e') (h1 : C.sizeSz ≤ e.2)
    (h2 : C.sizeSz ≤ e'.2) : e = e' := by
  unfold epay at h; simp only [Prod.mk.injEq] at h
  ext <;> omega

/-- A parked payload is that of a lent-out chunk of some arena. -/
theorem parked_chunk {w : World} (hw : WorldWF C w) {y : Nat × Nat} (hy : y ∈ allParked C w) :
    ∃ b av, w.arenas b = some av ∧ ∃ d ∈ av.chunks, d.use = .client ∧
      y = (d.addr + C.hdr, d.size - C.sizeSz) := by
  obtain ⟨t, ht, hy⟩ := mem_allParked.mp hy
  obtain ⟨tc, htc, i, -, e, he, rfl⟩ := mem_parked.mp hy
  obtain ⟨d, hd, hda, hds, hdu⟩ := hw.parked t tc ht htc i e he
  obtain ⟨b, -, av, hab, hdb⟩ := mem_world_chunks hd
  exact ⟨b, av, hab, d, hdb, hdu, by rw [epay, hda, hds]⟩

/-- A parked payload is not live. -/
theorem parked_not_live {w : World} (hw : WorldWF C w) {y : Nat × Nat} (hy : y ∈ allParked C w)
    (hl : y ∈ w.live C) : False := by
  rcases mem_live.mp hl with ⟨-, hp⟩ | hm
  · exact hp hy
  · obtain ⟨b, av, hab, d, hd, -, rfl⟩ := parked_chunk hw hy
    obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hm
    simp only [Prod.mk.injEq] at hme
    exact clash_mm hw hab hd hm (by omega)

theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, h, hn => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) hn.2⟩
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hm
    exact hn.1 (h y (by simp [hy]) x (by simp) hyx ▸ hy)

theorem nodup_flatMap_of {α β : Type} {f : α → List β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, (f x).Nodup) →
      (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ z ∈ f x, z ∉ f y) → (l.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | x :: l, hl, h1, h2 => by
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons]
    show List.Pairwise _ _
    rw [List.pairwise_append]
    refine ⟨h1 x (by simp), nodup_flatMap_of hl.2 (fun y hy => h1 y (by simp [hy]))
      (fun a ha b hb => h2 a (by simp [ha]) b (by simp [hb])), fun z hz z' hz' hzz => ?_⟩
    subst hzz
    obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hz'
    exact h2 x (by simp) y (by simp [hy]) (fun h => hl.1 (h ▸ hy)) z hz hzy

theorem disjoint_of_nodup_flatMap {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → ∀ {z : β},
      z ∈ f x → z ∈ f y → False
  | [], _, _, _, hx, _, _, _, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, hne, z, hz, hz' => by
    rw [List.flatMap_cons] at h
    have h' : List.Pairwise (· ≠ ·) (f a ++ l.flatMap f) := h
    rw [List.pairwise_append] at h'
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hne rfl
    · exact h'.2.2 z hz z (List.mem_flatMap.mpr ⟨y, hy, hz'⟩) rfl
    · exact h'.2.2 z hz' z (List.mem_flatMap.mpr ⟨x, hx, hz⟩) rfl
    · exact disjoint_of_nodup_flatMap h'.2.1 hx hy hne hz hz'

/-- The parked payloads of one thread have no duplicates. -/
theorem parked_nodup (hC : C.Ok) {t : ThreadSt} (hT : ∀ tc, t.tcache = some tc → TcacheWF C tc) :
    (t.parked C).Nodup := by
  unfold ThreadSt.parked
  cases htc : t.tcache with
  | none => simp
  | some tc =>
    have hW := hT tc htc
    simp only [Option.map_some, Option.getD_some, TcacheSt.payloads]
    refine nodup_map_on (fun x hx y hy hxy => ?_) ?_
    · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hx
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hy
      have := (hW.size i x hi).2.2; have := (hW.size j y hj).2.2
      have := hC.minSize; have := hC.sizeSz
      simp only [Prod.mk.injEq] at hxy
      ext <;> omega
    · refine nodup_flatMap_of List.nodup_range (fun i _ => (hW.nodup i).1) ?_
      intro i _ j _ hij x hx hx'
      exact hij ((hW.size i x hx).1.symm.trans (hW.size j x hx').1)

theorem pairwise_of_mem {α : Type} {R : α → α → Prop} (hs : ∀ {x y}, R x y → R y x) :
    ∀ {l : List α}, l.Pairwise R → ∀ {x y}, x ∈ l → y ∈ l → x ≠ y → R x y
  | [], _, _, _, hx, _, _ => by cases hx
  | z :: l, h, x, y, hx, hy, hne => by
    rw [List.pairwise_cons] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hne
    · exact h.1 y hy
    · exact hs (h.1 x hx)
    · exact pairwise_of_mem hs h.2 hx hy hne

/-! ## `WorldWF` after a body -/

theorem local?_fields {w : World} {tid a : Nat} {l : Local} (h : w.local? tid a = some l) :
    ∃ av, w.arenas a = some av ∧ l.av = av ∧ l.avAddr = a ∧ l.isMain = decide (a = w.mainArena) ∧
      l.thread = w.threads tid ∧ l.shared = w.shared ∧ l.kernel = w.kernel := by
  obtain ⟨av, hav, rfl⟩ := local?_some h
  exact ⟨av, hav, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem covers_one {k : KernelSt} {x : Nat} : k.Covers (x, 1) ↔ k.Has x := by
  constructor
  · intro h; exact h x (Nat.le_refl _) (by simp)
  · intro h y h1 h2; simp only at h1 h2; rw [show y = x by omega]; exact h

theorem put_threads {w : World} {tid : Nat} {l' : Local} (x : Nat) :
    (w.put tid l').threads x = if x = tid then l'.thread else w.threads x := rfl

section put2

variable {w : World} {tid a : Nat} {l l' : Local} {freed : List (Nat × Nat)}

/-- A lent-out chunk that is not freed survives into the world after. -/
theorem put_survive (hl : w.local? tid a = some l) (hF : Frame C l l' freed)
    {d : Chunk} (hd : d ∈ w.chunks) (hu : d.use = .client)
    (hnf : (d.addr + C.hdr, d.size - C.sizeSz) ∉ freed) : d ∈ (w.put tid l').chunks := by
  obtain ⟨b, hb, avb, hab, hdb⟩ := mem_world_chunks hd
  obtain ⟨av, hav, hlav, -⟩ := local?_fields hl
  have hb' : b ∈ (w.put tid l').arenaAddrs := by rw [put_addrs hl hF]; exact hb
  by_cases hba : b = a
  · rw [hba, hav] at hab; cases hab
    have : d ∈ l'.av.chunks := hF.clients d (by rw [hlav]; exact hdb) hu (by simpa [usable] using hnf)
    exact mem_world_chunks_of hb' (by rw [put_arenas hl hF, hba]; simp) this
  · exact mem_world_chunks_of hb' (by rw [put_arenas hl hF]; simp [hba, hab]) hdb

theorem put_parked (hw : WorldWF C w) (hl : w.local? tid a = some l) (hF : Frame C l l' freed)
    (hfr : ∀ x ∈ freed, x ∈ w.live C) :
    ∀ t tc, t ∈ (w.put tid l').tids → ((w.put tid l').threads t).tcache = some tc → ∀ i c,
      c ∈ tc.bins i → ∃ d ∈ (w.put tid l').chunks, d.addr = c.1 ∧ d.size = c.2 ∧ d.use = .client := by
  obtain ⟨av, hav, hlav, hla, -, hlt, -⟩ := local?_fields hl
  have old : ∀ t, t ∈ w.tids → ∀ tc, (w.threads t).tcache = some tc → ∀ i c, c ∈ tc.bins i →
      ∃ d ∈ (w.put tid l').chunks, d.addr = c.1 ∧ d.size = c.2 ∧ d.use = .client := by
    intro t ht tc htc i c hc
    obtain ⟨d, hd, hda, hds, hdu⟩ := hw.parked t tc ht htc i c hc
    have hy : epay C c ∈ allParked C w :=
      mem_allParked.mpr ⟨t, ht, mem_parked_of (hw.tcacheWF ht tc htc) htc hc⟩
    refine ⟨d, put_survive hl hF hd hdu fun hf => ?_, hda, hds, hdu⟩
    have : epay C c = (d.addr + C.hdr, d.size - C.sizeSz) := by rw [epay, hda, hds]
    exact parked_not_live hw hy (this ▸ hfr _ hf)
  intro t tc ht htc i c hc
  have ht0 : t ∈ w.tids := ht
  rw [put_threads] at htc
  by_cases htt : t = tid
  · simp only [htt, ite_true] at htc
    rcases hF.fresh tc i c htc hc with ⟨tc0, j, h0, hc0⟩ | ⟨⟨c', hc', h1, h2, h3⟩, -⟩
    · rw [hlt] at h0; exact old tid (htt ▸ ht0) tc0 h0 j c hc0
    · refine ⟨c', mem_world_chunks_of (b := a) ?_ ?_ hc', h1, h2, h3⟩
      · rw [put_addrs hl hF]; exact hw.mem_addrs hav
      · rw [put_arenas hl hF]; simp
  · simp only [htt, ite_false] at htc; exact old t ht0 tc htc i c hc

theorem put_parkedOnce (hC : C.Ok) (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf' : LocalWF C l') (hF : Frame C l l' freed) (hfr : ∀ x ∈ freed, x ∈ w.live C) :
    ((w.put tid l').tids.flatMap fun t => ((w.put tid l').threads t).parked C).Nodup := by
  obtain ⟨av, hav, hlav, hla, -, hlt, -⟩ := local?_fields hl
  have hP : ∀ t, ((w.put tid l').threads t).parked C =
      if t = tid then l'.thread.parked C else (w.threads t).parked C := by
    intro t; rw [put_threads]; split <;> rfl
  have cross : ∀ t', t' ∈ w.tids → t' ≠ tid → ∀ z, z ∈ l'.thread.parked C →
      z ∈ (w.threads t').parked C → False := by
    intro t' ht' hne z hz hz'
    obtain ⟨tc', htc', i, -, e, he, rfl⟩ := mem_parked.mp hz
    rcases hF.fresh tc' i e htc' he with ⟨tc0, j, h0, hc0⟩ | ⟨⟨c', hc', h1, -, -⟩, hor⟩
    · rw [hlt] at h0
      have hz0 := mem_parked_of (hw.tcacheWF ht tc0 h0) h0 hc0
      exact disjoint_of_nodup_flatMap hw.parkedOnce ht ht' (Ne.symm hne) hz0 hz'
    · obtain ⟨tc1, htc1, k, -, e', he', hee⟩ := mem_parked.mp hz'
      obtain ⟨d, hd, hda, -, hdu⟩ := hw.parked t' tc1 ht' htc1 k e' he'
      have he1 : e.1 = e'.1 := by
        unfold epay at hee; simp only [Prod.mk.injEq] at hee; omega
      obtain ⟨b, hb, avb, hab, hdb⟩ := mem_world_chunks hd
      by_cases hba : b = a
      · rw [hba, hav] at hab; cases hab
        rcases hor with hf | hnc
        · exact parked_not_live hw (mem_allParked.mpr ⟨t', ht', hz'⟩) (hfr _ hf)
        · exact hnc d (by rw [hlav]; exact hdb) (by rw [hda, he1]) hdu
      · refine addr_clash (put_apart hw hl hwf' hF) (r := (c'.addr, c'.size))
          (s := (d.addr, d.size)) ?_ (mem_others (hw.mem_addrs hab) hba hab (span_mem_spans hdb)) ?_
        · exact List.mem_append_left _ (span_mem_spans hc')
        · simp only; omega
  refine nodup_flatMap_of hw.tidsNodup (fun t ht => ?_) (fun x hx y hy hne z hz hz' => ?_)
  · rw [hP]; split
    · exact parked_nodup hC hwf'.tcache
    · exact parked_nodup hC (hw.tcacheWF ht)
  · rw [hP] at hz hz'
    by_cases hxt : x = tid <;> by_cases hyt : y = tid
    · exact hne (hxt.trans hyt.symm)
    · simp only [hxt, ite_true, hyt, ite_false] at hz hz'; exact cross y hy hyt z hz hz'
    · simp only [hxt, ite_false, hyt, ite_true] at hz hz'; exact cross x hx hxt z hz' hz
    · simp only [hxt, hyt, ite_false] at hz hz'
      exact disjoint_of_nodup_flatMap hw.parkedOnce hx hy hne hz hz'

/-- **`WorldWF` after a body.** -/
theorem worldWF_put (hC : C.Ok) (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf' : LocalWF C l') (hF : Frame C l l' freed) (hfr : ∀ x ∈ freed, x ∈ w.live C) :
    WorldWF C (w.put tid l') := by
  obtain ⟨av, hav, hlav, hla, hlm, hlt, hls, hlk⟩ := local?_fields hl
  have ha := hw.mem_addrs hav
  have hA := put_arenas hl hF
  have hperm := put_spans_perm hw hl hF
  have hap' : Apart (w.put tid l').spans := (put_apart hw hl hwf' hF).perm hperm.symm
  have harenaWF : ∀ x avx, (w.put tid l').arenas x = some avx → ArenaWF C avx := by
    intro x avx h; rw [hA] at h; split at h
    · cases h; exact hwf'.arena
    · exact hw.arenaWF x avx h
  have har : ∀ x, x ∈ (w.put tid l').arenaAddrs ↔ ((w.put tid l').arenas x).isSome := by
    intro x; rw [put_addrs hl hF, hA]; split
    · rename_i hx; subst hx; simp [ha]
    · exact hw.arenas x
  have hMain : MainOK C (w.put tid l') := by
    intro avm hm
    change (w.put tid l').arenas w.mainArena = some avm at hm
    rw [hA] at hm
    split at hm
    · rename_i hma
      cases hm
      have : l'.isMain = true := by rw [hF.isMain, hlm]; simp [hma]
      exact ⟨(hwf'.main this).1, (hwf'.main this).2, hwf'.sysMain this⟩
    · rename_i hma
      have ⟨h1, h2, h3⟩ := hw.mainOK ht avm hm
      have hnm : l.isMain = false := by rw [hlm]; simpa using Ne.symm hma
      obtain ⟨hbrk, hsb⟩ := hF.nonMain hnm
      have hac := hF.acct hnm
      have hbs := hF.brkStart
      rw [hls] at hsb hac; rw [hlk] at hbrk hbs hac
      change MainSbrk l'.shared avm ∧ MainBrk C l'.kernel avm ∧
        avm.tiles.systemMem + l'.shared.mm.mp.mmappedMem ≤ l'.kernel.total
      unfold MainSbrk MainBrk at *
      rw [hsb, hbrk, hbs]
      exact ⟨h1, h2, by omega⟩
  have hInit : InitOK (w.put tid l') := by
    intro hi
    have hi' : w.shared.init = false := by rw [← hls, ← hF.init]; exact hi
    obtain ⟨h1, -, h3⟩ := hw.initOK ht hi'
    have ⟨g1, g2, g3⟩ := hwf'.init hi
    refine ⟨fun b avb hb => ?_, g2, fun t htt => ?_⟩
    · rw [hA] at hb; split at hb
      · cases hb; exact g1
      · exact h1 b avb hb
    · rw [put_threads]; split
      · exact g3
      · exact h3 t htt
  have hHeap : HeapOK C (w.put tid l') := by
    intro x avx hx hne
    rw [hA] at hx; split at hx
    · rename_i hxa
      cases hx
      have : l'.isMain = false := by
        rw [hF.isMain, hlm]; simp only [decide_eq_false_iff_not]; intro h; exact hne (hxa.trans h)
      exact hwf'.heap this
    · exact hw.heapOK ht x avx hx hne
  have hT : ∀ t, t ∈ (w.put tid l').tids → ∀ tc, ((w.put tid l').threads t).tcache = some tc →
      TcacheWF C tc := by
    intro t htt tc htc; rw [put_threads] at htc; split at htc
    · exact hwf'.tcache tc htc
    · exact hw.tcacheWF htt tc htc
  have hsp : ∀ r ∈ (w.put tid l').spans, r ∈ l'.spans ∨ r ∈ w.others a := fun r hr =>
    List.mem_append.mp (hperm.subset hr)
  refine
    { main := by rw [show (w.put tid l').mainArena = w.mainArena from rfl, hA]; split
                 · rfl
                 · exact hw.main
      arenas := har
      arenaWF := harenaWF
      shared := hwf'.shared
      locals := fun t x lx htt hlx =>
        localWF_of harenaWF hwf'.shared hMain hInit hHeap hap' hwf'.mmSize har htt (hT t htt) hlx
      arenaNodup := by rw [put_addrs hl hF]; exact hw.arenaNodup
      apart := hap'
      mmSize := hwf'.mmSize
      parked := put_parked hw hl hF hfr
      parkedOnce := put_parkedOnce hC hw ht hl hwf' hF hfr
      tidsNodup := hw.tidsNodup
      threadArena := fun t x htt h => by
        rw [put_threads] at h; rw [put_addrs hl hF]; split at h
        · rename_i htid; rw [hF.arena, hlt, ← htid] at h; exact hw.threadArena t x htt h
        · exact hw.threadArena t x htt h
      covered := fun r hr => by
        rcases hsp r hr with h | h
        · exact hF.covered r h
        · obtain ⟨h0, hc, haw⟩ := others_facts hw hl h
          exact (hF.spatial r h0 hc haw).1
      structs := fun x hx => by
        rw [put_addrs hl hF] at hx
        obtain ⟨hhas, haw⟩ := hw.structs x hx
        have hawl : Away l.spans (x, 1) := fun s hs => haw s (mem_spans_of_local hl ha hs)
        have hcov : l.kernel.Covers (x, 1) := by rw [hlk]; exact covers_one.mpr hhas
        obtain ⟨hc', haw'⟩ := hF.spatial (x, 1) Nat.one_pos hcov hawl
        refine ⟨covers_one.mp hc', fun s hs => ?_⟩
        rcases hsp s hs with h | h
        · exact haw' s h
        · exact haw s (mem_spans_of_others ha h)
      heaps := fun x avx h hne => by
        rw [hA] at h; split at h
        · rename_i hx; cases h; subst hx
          exact hF.heaps (by rw [hlav]; exact hw.heaps _ av hav hne)
        · exact hw.heaps x avx h hne }

/-! ## The live set after a body -/

theorem put_allParked (ht : tid ∈ w.tids) {y : Nat × Nat} :
    y ∈ allParked C (w.put tid l') ↔ y ∈ l'.thread.parked C ∨
      ∃ t ∈ w.tids, t ≠ tid ∧ y ∈ (w.threads t).parked C := by
  rw [mem_allParked]
  constructor
  · rintro ⟨t, htt, hy⟩
    rw [put_threads] at hy
    by_cases h : t = tid
    · simp only [h, ite_true] at hy; exact .inl hy
    · simp only [h, ite_false] at hy; exact .inr ⟨t, htt, h, hy⟩
  · rintro (hy | ⟨t, htt, hne, hy⟩)
    · exact ⟨tid, ht, by rw [put_threads]; simpa using hy⟩
    · exact ⟨t, htt, by rw [put_threads]; simpa [hne] using hy⟩

theorem old_allParked (ht : tid ∈ w.tids) {y : Nat × Nat} :
    y ∈ allParked C w ↔ y ∈ (w.threads tid).parked C ∨
      ∃ t ∈ w.tids, t ≠ tid ∧ y ∈ (w.threads t).parked C := by
  rw [mem_allParked]
  constructor
  · rintro ⟨t, htt, hy⟩
    by_cases h : t = tid
    · rw [h] at hy; exact .inl hy
    · exact .inr ⟨t, htt, h, hy⟩
  · rintro (hy | ⟨t, htt, -, hy⟩)
    · exact ⟨tid, ht, hy⟩
    · exact ⟨t, htt, hy⟩

/-- **The world's live set after a body** changes as the view's does. -/
theorem put_live (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf' : LocalWF C l') (hF : Frame C l l' freed) (hK : KeptAway l l')
    (hfr : ∀ x ∈ freed, x ∈ w.live C ∧ x ∈ l.live C)
    (N : List (Nat × Nat)) (hN : ∀ y ∈ N, y ∉ l.live C)
    (hloc : ∀ y, y ∈ l'.live C ↔ y ∈ N ∨ (y ∈ l.live C ∧ y ∉ freed)) :
    ∀ y, y ∈ (w.put tid l').live C ↔ y ∈ N ∨ (y ∈ w.live C ∧ y ∉ freed) := by
  obtain ⟨av, hav, hlav, hla, -, hlt, hls, -⟩ := local?_fields hl
  have ha := hw.mem_addrs hav
  have hA := put_arenas hl hF
  have hap' := put_apart hw hl hwf' hF
  have hA' : (w.put tid l').arenaAddrs = w.arenaAddrs := put_addrs hl hF
  have hsh' : (w.put tid l').shared = l'.shared := rfl
  -- S1: an arena-`a` payload is not a payload of another arena
  have S1 : ∀ b avb, w.arenas b = some avb → b ≠ a → ∀ y, y ∈ avb.out C → y ∈ av.out C → False := by
    intro b avb hab hba y hy hy'
    obtain ⟨d, hd, -, rfl⟩ := mem_out.mp hy
    obtain ⟨d', hd', -, hdd⟩ := mem_out.mp hy'
    simp only [Prod.mk.injEq] at hdd
    exact clash_arenas hw hba hab hav hd hd' (by omega)
  -- S2: an arena payload is not an `mmap`ed one
  have S2 : ∀ b avb, w.arenas b = some avb → ∀ y, y ∈ avb.out C → y ∈ w.shared.live C → False := by
    intro b avb hab y hy hy'
    obtain ⟨d, hd, -, rfl⟩ := mem_out.mp hy
    obtain ⟨m, hm, -, hdm⟩ := mem_shlive.mp hy'
    simp only [Prod.mk.injEq] at hdm
    exact clash_mm hw hab hd hm (by omega)
  -- the other threads' parked payloads are not this thread's
  have Qno : ∀ y, (∃ t ∈ w.tids, t ≠ tid ∧ y ∈ (w.threads t).parked C) →
      y ∈ (w.threads tid).parked C → False := by
    rintro y ⟨t, htt, hne, hy⟩ hy'
    exact disjoint_of_nodup_flatMap hw.parkedOnce htt ht hne hy hy'
  -- S3: another arena's payload parked here stays parked
  have S3 : ∀ b avb, w.arenas b = some avb → b ≠ a → ∀ y, y ∈ avb.out C →
      y ∈ (w.threads tid).parked C → y ∈ l'.thread.parked C := by
    intro b avb hab hba y hy hp
    obtain ⟨tc, htc, i, -, e, he, rfl⟩ := mem_parked.mp hp
    obtain ⟨d, hd, hda, hds, hdu⟩ := hw.parked tid tc ht htc i e he
    obtain ⟨b'', hb'', avd, had, hdd⟩ := mem_world_chunks hd
    have hed : e = (d.addr, d.size) := by rw [hda, hds]
    by_cases hb''a : b'' = a
    · rw [hb''a, hav] at had; cases had
      exfalso
      refine S1 b avb hab hba _ hy (mem_out.mpr ⟨d, hdd, hdu, ?_⟩)
      rw [epay, hed]
    · have haw : Away l.spans e := by
        rw [hed]; exact away_of_other hw hl hb'' hb''a had (span_mem_spans hdd)
      obtain ⟨tc', htc', he'⟩ := hK tc i e (by rw [hlt]; exact htc) he haw
      exact mem_parked_of (hwf'.tcache tc' htc') htc' he'
  -- S4: another arena's payload newly parked here was parked before
  have S4 : ∀ b avb, w.arenas b = some avb → b ≠ a → ∀ y, y ∈ avb.out C →
      y ∈ l'.thread.parked C → y ∈ (w.threads tid).parked C := by
    intro b avb hab hba y hy hp
    obtain ⟨tc', htc', i, -, e, he, rfl⟩ := mem_parked.mp hp
    rcases hF.fresh tc' i e htc' he with ⟨tc0, j, h0, hc0⟩ | ⟨⟨c', hc', h1, -, -⟩, -⟩
    · rw [hlt] at h0; exact mem_parked_of (hw.tcacheWF ht tc0 h0) h0 hc0
    · exfalso
      obtain ⟨d, hd, -, hde⟩ := mem_out.mp hy
      unfold epay at hde; simp only [Prod.mk.injEq] at hde
      refine addr_clash hap' (r := (c'.addr, c'.size)) (s := (d.addr, d.size))
        (List.mem_append_left _ (span_mem_spans hc')) (mem_others (hw.mem_addrs hab) hba hab
        (span_mem_spans hd)) (by simp only; omega)
  -- S6: a payload `mmap`ed after is not parked before
  have S6 : ∀ y, y ∈ l'.shared.live C → y ∈ allParked C w → False := by
    intro y hy hp
    obtain ⟨b, avb, hab, d, hd, hdu, rfl⟩ := parked_chunk hw hp
    obtain ⟨m, hm, -, hdm⟩ := mem_shlive.mp hy
    simp only [Prod.mk.injEq] at hdm
    have hm' : (m.addr, m.size) ∈ l'.spans := List.mem_append_right _ (List.mem_map.mpr ⟨m, hm, rfl⟩)
    by_cases hba : b = a
    · rw [hba, hav] at hab; cases hab
      have hnf : (d.addr + C.hdr, d.size - C.sizeSz) ∉ freed := fun hf =>
        parked_not_live hw hp (hfr _ hf).1
      have hd' := hF.clients d (by rw [hlav]; exact hd) hdu (by simpa [usable] using hnf)
      exact addr_clash hwf'.apart (r := (d.addr, d.size)) (s := (m.addr, m.size))
        (span_mem_spans hd') (List.mem_map.mpr ⟨m, hm, rfl⟩) (by simp only; omega)
    · exact addr_clash hap' hm' (mem_others (hw.mem_addrs hab) hba hab (span_mem_spans hd))
        (by simp only; omega)
  -- S7: a new arena payload is not parked by another thread
  have S7 : ∀ y, y ∈ l'.av.out C → y ∉ l.live C →
      (∃ t ∈ w.tids, t ≠ tid ∧ y ∈ (w.threads t).parked C) → False := by
    intro y hy hnl hq
    obtain ⟨t, htt, hne, hp⟩ := hq
    obtain ⟨b, avb, hab, d, hd, hdu, rfl⟩ := parked_chunk hw (mem_allParked.mpr ⟨t, htt, hp⟩)
    by_cases hba : b = a
    · rw [hba, hav] at hab; cases hab
      refine hnl (mem_llive.mpr (.inl ⟨by rw [hlav]; exact mem_out.mpr ⟨d, hd, hdu, rfl⟩, ?_⟩))
      rw [hlt]; exact Qno _ ⟨t, htt, hne, hp⟩
    · obtain ⟨c', hc', -, hce⟩ := mem_out.mp hy
      simp only [Prod.mk.injEq] at hce
      exact addr_clash hap' (r := (c'.addr, c'.size)) (s := (d.addr, d.size))
        (List.mem_append_left _ (span_mem_spans hc')) (mem_others (hw.mem_addrs hab) hba hab
        (span_mem_spans hd)) (by simp only; omega)
  intro y
  constructor
  · intro hy
    rcases mem_live.mp hy with ⟨⟨b, hb, avb, hab, hyb⟩, hnp⟩ | hmm
    · rw [put_allParked ht] at hnp
      rw [hA] at hab
      split at hab
      · rename_i hba
        cases hab
        rcases (hloc y).mp (mem_llive.mpr (.inl ⟨hyb, fun h => hnp (.inl h)⟩)) with hN' | ⟨hyl, hnf⟩
        · exact .inl hN'
        · refine .inr ⟨?_, hnf⟩
          rcases mem_llive.mp hyl with ⟨hyo, hyp⟩ | hys
          · refine mem_live.mpr (.inl ⟨⟨a, ha, av, hav, by rw [← hlav]; exact hyo⟩, ?_⟩)
            rw [old_allParked ht]; rintro (h | h)
            · rw [← hlt] at h; exact hyp h
            · exact hnp (.inr h)
          · rw [hls] at hys; exact mem_live.mpr (.inr hys)
      · rename_i hba
        have hb0 : b ∈ w.arenaAddrs := by rw [← hA']; exact hb
        refine .inr ⟨mem_live.mpr (.inl ⟨⟨b, hb0, avb, hab, hyb⟩, ?_⟩), fun hf => ?_⟩
        · rw [old_allParked ht]; rintro (h | h)
          · exact hnp (.inl (S3 b avb hab hba y hyb h))
          · exact hnp (.inr h)
        · rcases mem_llive.mp (hfr y hf).2 with ⟨hyo, -⟩ | hys
          · exact S1 b avb hab hba y hyb (by rw [← hlav]; exact hyo)
          · rw [hls] at hys; exact S2 b avb hab y hyb hys
    · rw [hsh'] at hmm
      rcases (hloc y).mp (mem_llive.mpr (.inr hmm)) with hN' | ⟨hyl, hnf⟩
      · exact .inl hN'
      · refine .inr ⟨?_, hnf⟩
        rcases mem_llive.mp hyl with ⟨hyo, hyp⟩ | hys
        · refine mem_live.mpr (.inl ⟨⟨a, ha, av, hav, by rw [← hlav]; exact hyo⟩, ?_⟩)
          exact fun h => S6 y hmm h
        · rw [hls] at hys; exact mem_live.mpr (.inr hys)
  · rintro (hN' | ⟨hyw, hnf⟩)
    · rcases mem_llive.mp ((hloc y).mpr (.inl hN')) with ⟨hyo, hyp⟩ | hys
      · refine mem_live.mpr (.inl ⟨⟨a, by rw [hA']; exact ha, l'.av, by rw [hA]; simp, hyo⟩, ?_⟩)
        rw [put_allParked ht]; rintro (h | h)
        · exact hyp h
        · exact S7 y hyo (hN y hN') h
      · exact mem_live.mpr (.inr hys)
    · rcases mem_live.mp hyw with ⟨⟨b, hb, avb, hab, hyb⟩, hnp⟩ | hmm
      · rw [old_allParked ht] at hnp
        by_cases hba : b = a
        · rw [hba, hav] at hab; cases hab
          have hyl : y ∈ l.live C :=
            mem_llive.mpr (.inl ⟨by rw [hlav]; exact hyb, fun h => hnp (.inl (by rw [← hlt]; exact h))⟩)
          rcases mem_llive.mp ((hloc y).mpr (.inr ⟨hyl, hnf⟩)) with ⟨hyo, hyp⟩ | hys
          · refine mem_live.mpr (.inl ⟨⟨a, by rw [hA']; exact ha, l'.av, by rw [hA]; simp, hyo⟩, ?_⟩)
            rw [put_allParked ht]; rintro (h | h)
            · exact hyp h
            · exact hnp (.inr h)
          · exact mem_live.mpr (.inr hys)
        · refine mem_live.mpr (.inl ⟨⟨b, by rw [hA']; exact hb, avb, by rw [hA]; simp [hba, hab], hyb⟩, ?_⟩)
          rw [put_allParked ht]; rintro (h | h)
          · exact hnp (.inl (S4 b avb hab hba y hyb h))
          · exact hnp (.inr h)
      · have hyl : y ∈ l.live C := mem_llive.mpr (.inr (by rw [hls]; exact hmm))
        rcases mem_llive.mp ((hloc y).mpr (.inr ⟨hyl, hnf⟩)) with ⟨hyo, hyp⟩ | hys
        · refine mem_live.mpr (.inl ⟨⟨a, by rw [hA']; exact ha, l'.av, by rw [hA]; simp, hyo⟩, ?_⟩)
          rw [put_allParked ht]; rintro (h | h)
          · exact hyp h
          · exact parked_not_live hw ((old_allParked ht).mpr (.inr h)) hyw
        · exact mem_live.mpr (.inr hys)

end put2

/-! ## Corollaries: `malloc` and `free` at world level -/

theorem nodup_of_liveApart {live : List (Nat × Nat)} (h : LiveApart live) : live.Nodup :=
  h.1.imp_of_mem fun hx _ hr he => by
    subst he; have := (h.2 _ hx).2.1; omega

theorem live_nodup (hC : C.Ok) {w : World} (hw : WorldWF C w) : (w.live C).Nodup :=
  nodup_of_liveApart (liveApart C hC w hw)

/-- The kinded chunks of a view. -/
def lkchunks (l : Local) : List KChunk :=
  l.av.chunks.map (fun c => (c, false)) ++ l.shared.mm.chunks.map (fun c => (c, true))

/-- **A view's live payloads are apart and bounded** (as `liveApart`, for one view). -/
theorem llive_apart (hC : C.Ok) {l : Local} (hw : LocalWF C l) : LiveApart (l.live C) := by
  have hok : ∀ x ∈ lkchunks l, KOk C x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      have ht := hw.arena.tiles
      have hc' : c ∈ l.av.tiles.heapChunks := hc
      unfold KOk; simp only [Bool.false_eq_true, ite_false]
      exact ⟨(ht.sizes c hc').2, ht.aligned c hc', (ht.sizes c hc').1, ht.bound c hc'⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      unfold KOk; simp only [ite_true]; exact hw.mmSize c hc
  have hsub : ((lkchunks l).map kspan).Sublist l.spans := by
    unfold lkchunks Local.spans
    simp only [List.map_append, List.map_map]
    refine List.Sublist.append ?_ (List.Sublist.refl _)
    simp only [ArenaSt.spans, TopSt.spans, ArenaSt.chunks]
    exact (List.sublist_append_left ..).trans (List.sublist_append_left ..)
  have hlsub : (l.live C).Sublist ((lkchunks l).map (kpay C)) := by
    unfold Local.live lkchunks
    simp only [List.map_append, List.map_map]
    exact List.Sublist.append ((List.filter_sublist ..).trans (out_sublist l.av))
      ((List.filter_sublist ..).map _)
  have hsp := hw.apart.1.sublist hsub
  rw [List.pairwise_map] at hsp
  have hpay : ((lkchunks l).map (kpay C)).Pairwise (fun q r => q.1 + q.2 ≤ r.1 ∨ r.1 + r.2 ≤ q.1) := by
    rw [List.pairwise_map]
    exact hsp.imp_of_mem fun hx hy h => pay_apart hC (hok _ hx) (hok _ hy) h
  refine ⟨hpay.sublist hlsub, fun q hq => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (hlsub.subset hq)
  have := kpay_bounds hC (hok x hx)
  exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2⟩

section put3

variable {w : World} {tid a : Nat} {l l' : Local}

/-- A payload live in the view after and not before was not live in the world before. -/
theorem new_not_live (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf' : LocalWF C l') {freed : List (Nat × Nat)} (hF : Frame C l l' freed) {y : Nat × Nat}
    (hy : y ∈ l'.live C) (hn : y ∉ l.live C) : y ∉ w.live C := by
  obtain ⟨av, hav, hlav, hla, -, hlt, hls, -⟩ := local?_fields hl
  have hap' := put_apart hw hl hwf' hF
  intro hyw
  rcases mem_live.mp hyw with ⟨⟨b, hb, avb, hab, hyb⟩, hnp⟩ | hmm
  · by_cases hba : b = a
    · rw [hba, hav] at hab; cases hab
      refine hn (mem_llive.mpr (.inl ⟨by rw [hlav]; exact hyb, fun h => hnp ?_⟩))
      rw [hlt] at h; exact (old_allParked ht).mpr (.inl h)
    · obtain ⟨d, hd, -, rfl⟩ := mem_out.mp hyb
      have hs := mem_others hb hba hab (span_mem_spans hd)
      rcases mem_llive.mp hy with ⟨hyo, -⟩ | hys
      · obtain ⟨c', hc', -, hce⟩ := mem_out.mp hyo
        simp only [Prod.mk.injEq] at hce
        exact addr_clash hap' (r := (c'.addr, c'.size)) (List.mem_append_left _ (span_mem_spans hc'))
          hs (by simp only; omega)
      · obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hys
        simp only [Prod.mk.injEq] at hme
        exact addr_clash hap' (r := (m.addr, m.size))
          (List.mem_append_right _ (List.mem_map.mpr ⟨m, hm, rfl⟩)) hs (by simp only; omega)
  · exact hn (mem_llive.mpr (.inr (by rw [hls]; exact hmm)))

/-- **A body that `malloc`s**, put back: `WorldWF` and the world's `MallocLive`. -/
theorem put_malloc (hC : C.Ok) (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf' : LocalWF C l') (hF : Frame C l l' []) (hK : KeptAway l l') {n p : Nat}
    (hML : MallocLive C n p (l.live C) (l'.live C)) :
    WorldWF C (w.put tid l') ∧ MallocLive C n p (w.live C) ((w.put tid l').live C) := by
  have hw' := worldWF_put hC hw ht hl hwf' hF (by simp)
  refine ⟨hw', ?_⟩
  have hnd := live_nodup hC hw
  have hnd' := live_nodup hC hw'
  rcases hML with ⟨hp, hperm⟩ | ⟨hp, hal, u, hnu, hperm, hdis⟩
  · refine .inl ⟨hp, (List.perm_ext_iff_of_nodup hnd' hnd).mpr fun y => ?_⟩
    have := put_live hw ht hl hwf' hF hK (by simp) [] (by simp)
      (fun y => by rw [hperm.mem_iff]; simp) y
    simpa using this
  · have hpos : 0 < u := ((llive_apart hC hwf').2 (p, u) (hperm.symm.subset (List.mem_cons_self ..))).2.1
    have hnl : (p, u) ∉ l.live C := fun h => by have := hdis _ h; simp only at this; omega
    have hloc := put_live hw ht hl hwf' hF hK (by simp) [(p, u)] (by simpa using hnl)
      (fun y => by rw [hperm.mem_iff]; simp)
    have hnw : (p, u) ∉ w.live C :=
      new_not_live hw ht hl hwf' hF (hperm.symm.subset (List.mem_cons_self ..)) hnl
    have hmem : ∀ y, y ∈ (w.put tid l').live C ↔ y = (p, u) ∨ y ∈ w.live C := fun y => by
      rw [hloc y]; simp
    refine .inr ⟨hp, hal, u, hnu, (List.perm_ext_iff_of_nodup hnd' (List.nodup_cons.mpr ⟨hnw, hnd⟩)).mpr
      fun y => by rw [hmem y]; simp, fun q hq => ?_⟩
    have hap := (liveApart C hC _ hw').1
    have hq' := (hmem q).mpr (.inr hq)
    have hp' := (hmem (p, u)).mpr (.inl rfl)
    exact pairwise_of_mem (fun h => h.symm) hap hq' hp' (fun h => hnw (h ▸ hq))

/-- The fresh payload of a `malloc` body is live in the world after. -/
theorem put_malloc_new (hC : C.Ok) (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf' : LocalWF C l') (hF : Frame C l l' []) (hK : KeptAway l l') {p u : Nat}
    (hperm : (l'.live C).Perm ((p, u) :: l.live C))
    (hdis : ∀ q ∈ l.live C, q.1 + q.2 ≤ p ∨ p + u ≤ q.1) : (p, u) ∈ (w.put tid l').live C := by
  have hpos : 0 < u := ((llive_apart hC hwf').2 (p, u) (hperm.symm.subset (List.mem_cons_self ..))).2.1
  have hnl : (p, u) ∉ l.live C := fun h => by have := hdis _ h; simp only at this; omega
  have hloc := put_live hw ht hl hwf' hF hK (by simp) [(p, u)] (by simpa using hnl)
    (fun y => by rw [hperm.mem_iff]; simp)
  exact (hloc (p, u)).mpr (.inl (List.mem_singleton_self _))

/-- **A body that `free`s `(p, u)`**, put back: `WorldWF` and the world's live set without it. -/
theorem put_free (hC : C.Ok) (hw : WorldWF C w) (ht : tid ∈ w.tids) (hl : w.local? tid a = some l)
    (hwf : LocalWF C l) (hwf' : LocalWF C l') {p u : Nat} (hF : Frame C l l' [(p, u)])
    (hK : KeptAway l l')
    (hpw : (p, u) ∈ w.live C) (hpl : (p, u) ∈ l.live C)
    (hperm : (l'.live C).Perm ((l.live C).erase (p, u))) :
    WorldWF C (w.put tid l') ∧ ((w.put tid l').live C).Perm ((w.live C).erase (p, u)) := by
  have hw' := worldWF_put hC hw ht hl hwf' hF (by simpa using hpw)
  refine ⟨hw', ?_⟩
  have hndl := nodup_of_liveApart (llive_apart hC hwf)
  have hnd := live_nodup hC hw
  have hloc := put_live hw ht hl hwf' hF hK (by simpa using ⟨hpw, hpl⟩) [] (by simp)
    (fun y => by rw [hperm.mem_iff, hndl.mem_erase_iff]; simp [and_comm])
  refine (List.perm_ext_iff_of_nodup (live_nodup hC hw') (hnd.erase _)).mpr fun y => ?_
  rw [hloc y, hnd.mem_erase_iff]; simp [and_comm]

end put3

end Silmaril.Libc.Ptmalloc.Algo
