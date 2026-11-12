module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocLend

/-!
# ptmalloc: tiling lemmas for `_int_malloc`'s splits and free-to-free relabels

* `TopSt.runs_split'`: the runs after a split, in the runs normal form;
* `TopWF.replaceN`: `TopWF.replace` for a piece whose addresses are new (a split), given their
  alignment and the new tiling's distinct addresses;
* `TopWF.splitFree`: carving `s₁` bytes off a free chunk (neighbours not free) as a used chunk
  and a remainder keeps `TopWF`, given that the other chunks are apart from it;
* `TopSt.coal_relabel_same`: a relabelling that keeps the chunk's free tag keeps `Coal`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

namespace TopSt

variable {ts : TopSt}

/-- **The runs after a split** of the entry at `a`. -/
theorem runs_split' {R₁ R₂ : List (Nat × List (Nat × Use))} {s a : Nat}
    {pre post : List (Nat × Use)} {x : Nat × Use} (s₁ : Nat) (u₁ u₂ : Use)
    (hr : ts.runs = R₁ ++ (s, pre ++ x :: post) :: R₂) (ha : s + runLen pre = a)
    (hn : (ts.heapChunks.map (·.addr)).Nodup) :
    (ts.split a s₁ u₁ u₂).runs = R₁ ++ (s, pre ++ (s₁, u₁) :: (x.1 - s₁, u₂) :: post) :: R₂ := by
  obtain ⟨hoth, hpre, -⟩ := runs_local hr ha hn
  rw [split_eq, runs_mapRun_local (fun s cs h => splitRun_of_not_mem s₁ u₁ u₂ h) hr hoth,
    splitRun_hit s₁ u₁ u₂ x ha hpre]

/-! ### Free tags -/

/-- The free tags of a run. -/
def tags (cs : List (Nat × Use)) : List Bool := cs.map (·.2.tagFree)

theorem coalescedB_congr : ∀ {xs ys : List (Nat × Use)}, tags xs = tags ys →
    coalescedB xs = coalescedB ys
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | x :: x' :: xs, y :: y' :: ys, h => by
    simp only [tags, List.map_cons, List.cons.injEq] at h
    have ih := coalescedB_congr (xs := x' :: xs) (ys := y' :: ys)
      (by simp only [tags, List.map_cons, List.cons.injEq]; exact ⟨h.2.1, h.2.2⟩)
    simp only [coalescedB, h.1, h.2.1, ih]
  | [], _ :: _, h => by simp [tags] at h
  | _ :: _, [], h => by simp [tags] at h
  | [_], _ :: _ :: _, h => by simp [tags] at h
  | _ :: _ :: _, [_], h => by simp [tags] at h

theorem tags_relabelRun {a : Nat} {u : Use} : ∀ {s : Nat} {cs : List (Nat × Use)},
    (∀ c ∈ layout s cs, c.addr = a → c.use.tagFree = u.tagFree) →
    tags (relabelRun a u s cs) = tags cs
  | _, [], _ => rfl
  | s, (sz, v) :: cs, h => by
    simp only [relabelRun, tags, List.map_cons, List.cons.injEq]
    refine ⟨?_, tags_relabelRun (s := s + sz) fun c hc => h c (by simp [layout, hc])⟩
    by_cases hs : s = a
    · simp only [hs, ite_true]; exact (h ⟨s, sz, v⟩ (by simp [layout]) hs).symm
    · simp [hs]

theorem lastFree_congr {xs ys : List (Nat × Use)} (h : tags xs = tags ys)
    (hx : ∀ e ∈ xs.getLast?, e.2.tagFree = false) : ∀ e ∈ ys.getLast?, e.2.tagFree = false := by
  intro e he
  have h1 : (ys.getLast?).map (·.2.tagFree) = (xs.getLast?).map (·.2.tagFree) := by
    rw [← List.getLast?_map, ← List.getLast?_map]; unfold tags at h; rw [h]
  rw [Option.mem_def] at he
  rw [he] at h1
  cases hxl : xs.getLast? with
  | none => rw [hxl] at h1; cases h1
  | some x => rw [hxl] at h1; simp only [Option.map_some, Option.some.injEq] at h1; rw [h1]; exact hx x hxl

/-- **A relabelling that keeps the chunk's free tag keeps the tiling coalesced.** -/
theorem coal_relabel_same {a : Nat} {u : Use} (hc : ts.Coal) (hn : (ts.heapChunks.map (·.addr)).Nodup)
    {d : Chunk} (hd : d ∈ ts.heapChunks) (hda : d.addr = a) (hu : u.tagFree = d.use.tagFree) :
    (ts.relabel a u).Coal := by
  have hall : ∀ c ∈ ts.heapChunks, c.addr = a → c.use.tagFree = u.tagFree := by
    intro c hc' hca
    have := chunk_unique hn hc' hd (hca.trans hda.symm); subst this; exact hu.symm
  have hcur : tags (relabelRun a u ts.start ts.chunks) = tags ts.chunks :=
    tags_relabelRun fun c hc' => hall c (by unfold heapChunks; exact List.mem_append_right _ hc')
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · show coalescedB (relabelRun a u ts.start ts.chunks) = true
    rw [coalescedB_congr hcur]; exact h1
  · exact lastFree_congr hcur.symm h2
  · intro g hg
    simp only [relabel, List.mem_map] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    show coalescedB (relabelRun a u g₀.start g₀.chunks) = true
    rw [coalescedB_congr (tags_relabelRun fun c hc' => hall c (by
      unfold heapChunks; exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g₀, hg₀, hc'⟩)))]
    exact h3 g₀ hg₀

end TopSt

theorem nodup_insert {X1 X2 Y : List Nat} {a b : Nat} (h : (X1 ++ (X2 ++ a :: Y)).Nodup)
    (hb : b ∉ X1 ++ (X2 ++ a :: Y)) : (X1 ++ (X2 ++ a :: b :: Y)).Nodup := by
  have hp : (X1 ++ (X2 ++ a :: b :: Y)).Perm (b :: (X1 ++ (X2 ++ a :: Y))) := by
    have := @List.perm_middle _ b (X1 ++ X2 ++ [a]) Y
    simpa [List.append_assoc] using this
  exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hb, h⟩)

namespace TopWF

variable {C : Config} {ts ts' : TopSt}

/-- **`TopWF.replace` for new addresses**: as `replace`, with the new piece's addresses aligned
and non-null and the new tiling's addresses distinct instead of the new addresses among the
old ones. -/
theorem replaceN (h : TopWF C ts) {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre mid mid' post : List (Nat × Use)}
    (hr : ts.runs = R₁ ++ (s, pre ++ mid ++ post) :: R₂)
    (hr' : ts'.runs = R₁ ++ (s, pre ++ mid' ++ post) :: R₂)
    (hmid : mid ≠ []) (hlen : runLen mid' = runLen mid)
    (hsz : ∀ e ∈ mid', e.1 % C.align = 0 ∧ C.minSize ≤ e.1)
    (hal : ∀ c ∈ layout (s + runLen pre) mid', c.addr % C.align = 0 ∧ c.addr ≠ 0)
    (hnd : (ts'.heapChunks.map (·.addr)).Nodup)
    (hcoal : Coalesced (pre ++ mid' ++ post))
    (hlast : R₂ = [] → ∀ e ∈ (pre ++ mid' ++ post).getLast?, e.2.tagFree = false)
    (htop : ts'.top = ts.top) (htz : ts'.topSize = ts.topSize) (hsm : ts'.systemMem = ts.systemMem) :
    TopWF C ts' := by
  have hH := TopSt.heapChunks_of_runs hr
  have hH' := TopSt.heapChunks_of_runs hr'
  rw [hlen] at hH'
  obtain ⟨hst, hcur, hold, hnoh⟩ := TopSt.fields_of_runs hr hr'
  obtain ⟨a, ha⟩ : ∃ a, a = s + runLen pre := ⟨_, rfl⟩
  rw [← ha] at hH hH' hal
  have hall : ∀ P : Chunk → Prop, (∀ c ∈ ts.heapChunks, P c) → (∀ c ∈ layout a mid', P c) →
      ∀ c ∈ ts'.heapChunks, P c := by
    intro P h1 h2 c hc
    rw [hH'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact h1 c (by rw [hH]; exact List.mem_append_left _ (List.mem_append_left _ hc))
      · exact h2 c hc
    · exact h1 c (by rw [hH]; exact List.mem_append_right _ hc)
  have hold' : ∀ c ∈ layout a mid, c ∈ ts.heapChunks := fun c hc => by
    rw [hH]; exact List.mem_append_left _ (List.mem_append_right _ hc)
  obtain ⟨cl, hcl, hcle⟩ := layout_last_end mid hmid a
  have hend : a + runLen mid < 2 ^ 64 := by rw [← hcle]; exact h.bound cl (hold' cl hcl)
  have hsum : (ts'.heapChunks.map (·.size)).sum = (ts.heapChunks.map (·.size)).sum := by
    rw [hH, hH']
    simp only [List.map_append, List.sum_append, sum_sizes_layout, hlen]
  have hcurlen : (ts'.chunks.map (·.1)).sum = (ts.chunks.map (·.1)).sum := by
    rcases hcur with ⟨-, h1, h2, -⟩ | ⟨-, h2⟩
    · rw [h1, h2]
      show runLen _ = runLen _
      simp only [runLen_append, hlen]
    · rw [h2]
  exact
  { sizes := hall _ h.sizes fun c hc => by
      obtain ⟨pre', post', he, -⟩ := mem_layout_split hc
      exact hsz _ (by rw [he]; exact List.mem_append_right _ (List.mem_cons_self ..))
    aligned := hall _ h.aligned fun c hc => (hal c hc).1
    nonNull := hall _ h.nonNull fun c hc => (hal c hc).2
    topAt := fun hs => by
      rw [htop, hcurlen, hst]; exact h.topAt (by rw [← hst]; exact hs)
    topAligned := by rw [htop, htz]; exact h.topAligned
    topMin := fun hs => by rw [htz]; exact h.topMin (by rw [← hst]; exact hs)
    coalesced := by
      rcases hcur with ⟨-, -, h2, -⟩ | ⟨-, h2⟩
      · rw [h2]; exact hcoal
      · rw [h2]; exact h.coalesced
    lastUsed := by
      rcases hcur with ⟨h0, -, h2, -⟩ | ⟨-, h2⟩
      · rw [h2]; exact hlast h0
      · rw [h2]; exact h.lastUsed
    coalescedOld := fun g hg => by
      rcases hold g hg with ⟨g₀, hg₀, he⟩ | he
      · unfold Coalesced; rw [← he]; exact h.coalescedOld g₀ hg₀
      · unfold Coalesced; rw [he]; exact hcoal
    sysMem := by rw [hsum, htz, hsm]; exact h.sysMem
    sysMemBound := by rw [hsm]; exact h.sysMemBound
    noHeap := fun hs => by
      rw [hst] at hs
      have := h.noHeap hs
      exact absurd (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp (hnoh hs this)).1).2 hmid
    nodup := hnd
    bound := hall _ h.bound fun c hc => by
      have := mem_layout_bounds hc; rw [hlen] at this; omega
    topBound := fun hs => by rw [htop, htz]; exact h.topBound (by rw [← hst]; exact hs) }

/-- **Carving `s₁` bytes off a free chunk** (its neighbours not free, the other chunks apart from
it) as a used chunk and a remainder of any use keeps `TopWF`. -/
theorem splitFree (h : TopWF C ts) {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {sz : Nat} {v : Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ (sz, v) :: post) :: R₂)
    (hnext : ∀ e ∈ post.head?, e.2.tagFree = false)
    (hlast : R₂ = [] → post ≠ [])
    {s₁ : Nat} {u₁ u₂ : Use} (hu₁ : u₁.tagFree = false)
    (hs₁ : s₁ % C.align = 0) (hmin₁ : C.minSize ≤ s₁) (hmin₂ : C.minSize ≤ sz - s₁) (hlt : s₁ < sz) (hpos : 0 < s₁)
    (hap : ∀ c ∈ ts.heapChunks, c.addr ≠ s + runLen pre →
      c.addr + c.size ≤ s + runLen pre ∨ s + runLen pre + sz ≤ c.addr) :
    TopWF C (ts.split (s + runLen pre) s₁ u₁ u₂) := by
  have hn := h.nodup
  have hr' := TopSt.runs_split' (x := (sz, v)) s₁ u₁ u₂ hr rfl hn
  have hd := TopSt.mem_of_runs hr
  simp only at hd hr'
  have hr1 : ts.runs = R₁ ++ (s, pre ++ [(sz, v)] ++ post) :: R₂ := by rw [hr]; simp
  have hr1' : (ts.split (s + runLen pre) s₁ u₁ u₂).runs =
      R₁ ++ (s, pre ++ [(s₁, u₁), (sz - s₁, u₂)] ++ post) :: R₂ := by rw [hr']; simp
  have hcoal0 := h.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
  simp only at hcoal0
  rw [coalescedB_mid] at hcoal0
  obtain ⟨hc1, hc2, -⟩ := hcoal0
  have hszd := h.sizes _ hd
  simp only at hszd
  have hal0 := h.aligned _ hd
  have hnn0 := h.nonNull _ hd
  simp only at hal0 hnn0
  refine h.replaceN hr1 hr1' (by simp) (by simp [runLen]; omega) ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨hs₁, hmin₁⟩
    · refine ⟨?_, hmin₂⟩
      simp only
      exact Nat.sub_mod_eq_zero_of_mod_eq (by rw [hszd.1, hs₁])
  · intro c hc
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨hal0, hnn0⟩
    · simp only
      exact ⟨by rw [Nat.add_mod, hal0, hs₁]; rfl, by omega⟩
  · -- distinct addresses: the new one, `a + s₁`, lies inside the old chunk
    have hH := TopSt.heapChunks_of_runs hr1
    have hH' := TopSt.heapChunks_of_runs hr1'
    have hrl : runLen [(s₁, u₁), (sz - s₁, u₂)] = runLen [(sz, v)] := by simp [runLen]; omega
    rw [hrl] at hH'
    rw [hH']
    have hn' := hn
    rw [hH] at hn'
    simp only [layout, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append, List.nil_append, runLen_cons, runLen_nil, Nat.add_zero] at hn' ⊢
    refine nodup_insert hn' fun hm => ?_
    have hm' : s + runLen pre + s₁ ∈ ts.heapChunks.map (·.addr) := by
      rw [hH]
      simp only [layout, List.map_append, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append, runLen_cons, runLen_nil, Nat.add_zero]
      exact hm
    obtain ⟨c, hc, hca⟩ := List.mem_map.mp hm'
    rcases hap c hc (by omega) with h1 | h1 <;> omega
  · show coalescedB (pre ++ [(s₁, u₁), (sz - s₁, u₂)] ++ post) = true
    rw [List.append_assoc, List.cons_append, coalescedB_mid_used _ _ _ hu₁,
      List.singleton_append, coalescedB_cons]
    exact ⟨hc1, hc2, fun _ => hnext⟩
  · intro h0 e he
    have hne := hlast h0
    subst h0
    rw [List.append_assoc, List.cons_append, getLast?_append_cons, List.singleton_append,
      List.getLast?_cons_cons] at he
    rcases mem_getLast?_cons he with ⟨h, -⟩ | ⟨-, he⟩
    · exact absurd h hne
    · apply h.runs_last (R₁ := R₁) (s := s) hr e
      rw [getLast?_append_cons]
      cases post with
      | nil => exact absurd rfl hne
      | cons q qs => rw [List.getLast?_cons_cons]; exact he

end TopWF

end Silmaril.Libc.Ptmalloc
