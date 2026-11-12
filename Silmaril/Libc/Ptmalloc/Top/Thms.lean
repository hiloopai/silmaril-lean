module

public import Silmaril.Libc.Ptmalloc.Top.Defs
public import Silmaril.Libc.Ptmalloc.Chunk.Thms

/-!
# ptmalloc component: the tiling's lemmas (relabelling)

* `TopSt.heapChunks_relabel`: a relabelling is `Chunk.relabelAt` over the tiling's chunks, so it
  keeps every address and size (`sizeAt_relabel`) and the geometry (start, top, sizes, segments).
* `TopSt.view_relabel` (= `Task.algo.viewRelabel`): a view that sees neither the old nor the new
  use is unchanged.
* `TopWF.relabel`: relabelling to a use that is not free for the boundary tags (`client`,
  `internal`, a fastbin) keeps `TopWF`; `TopWF.relabel_free`: relabelling to a regular bin keeps
  it when the neighbours in the run are not free (the coalescing premise of glibc's binning).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- The coalescing facts of a tiling (`TopWF`'s `coalesced`, `lastUsed`, `coalescedOld`). -/
def TopSt.Coal (ts : TopSt) : Prop :=
  Coalesced ts.chunks ∧ (∀ c ∈ ts.chunks.getLast?, c.2.tagFree = false) ∧
    ∀ g ∈ ts.old, Coalesced g.chunks

namespace TopSt

variable (ts : TopSt) (a : Nat) (u : Use)

/-- **The relabelled tiling** is the tiling with the chunk at `a` relabelled. -/
theorem heapChunks_relabel :
    (ts.relabel a u).heapChunks = ts.heapChunks.map (Chunk.relabelAt a u) := by
  simp only [heapChunks, relabel, List.map_append, List.flatMap_map, List.map_flatMap,
    layout_relabelRun]

@[simp] theorem relabel_start : (ts.relabel a u).start = ts.start := rfl
@[simp] theorem relabel_top : (ts.relabel a u).top = ts.top := rfl
@[simp] theorem relabel_topSize : (ts.relabel a u).topSize = ts.topSize := rfl
@[simp] theorem relabel_noncontig : (ts.relabel a u).noncontig = ts.noncontig := rfl
@[simp] theorem relabel_systemMem : (ts.relabel a u).systemMem = ts.systemMem := rfl
@[simp] theorem relabel_old_nil : (ts.relabel a u).old = [] ↔ ts.old = [] := by
  simp [relabel]

/-- A relabelling keeps the owned ranges. -/
theorem spans_relabel : (ts.relabel a u).spans = ts.spans := by
  unfold spans
  rw [heapChunks_relabel, List.map_map]
  congr 1
  simp [Function.comp_def]

/-- A relabelling keeps every chunk's size. -/
theorem sizeAt_relabel : (ts.relabel a u).sizeAt = ts.sizeAt := by
  funext x
  simp only [sizeAt, heapChunks_relabel, List.find?_map]
  have : ((fun c : Chunk => decide (c.addr = x)) ∘ Chunk.relabelAt a u) = fun c => decide (c.addr = x) := by
    funext c; simp
  rw [this]
  cases ts.heapChunks.find? (fun c => decide (c.addr = x)) <;> simp

/-- **`Task.algo.viewRelabel`**: a view that sees neither the old use of the chunk at `a` nor `u`
is unchanged by the relabelling. -/
theorem view_relabel (p : Use → Bool) (hc : ∀ c ∈ ts.heapChunks, c.addr = a → p c.use = false)
    (hu : p u = false) :
    Chunk.view p (ts.relabel a u).heapChunks = Chunk.view p ts.heapChunks := by
  rw [heapChunks_relabel]
  unfold Chunk.view
  generalize ts.heapChunks = cs at hc
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih := ih fun d hd => hc d (List.mem_cons_of_mem _ hd)
    simp only [List.map_cons, List.filter_cons]
    by_cases h : c.addr = a
    · rw [Chunk.relabelAt_of_eq h]
      simp [hu, hc c (List.mem_cons_self ..) h, ih]
    · rw [Chunk.relabelAt_of_ne h, ih]

/-- Every entry of a relabelled run is an entry of the run or has the new use. -/
theorem mem_relabelRun {e : Nat × Use} :
    ∀ {s : Nat} {cs : List (Nat × Use)}, e ∈ relabelRun a u s cs → e ∈ cs ∨ e.2 = u
  | _, [], h => by cases h
  | s, (sz, v) :: cs, h => by
    simp only [relabelRun, List.mem_cons] at h
    rcases h with rfl | h
    · by_cases hs : s = a
      · simp [hs]
      · simp [hs]
    · rcases mem_relabelRun h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h

/-- The last entry of a relabelled run is the run's last entry or has the new use. -/
theorem getLast?_relabelRun {e : Nat × Use} :
    ∀ {s : Nat} {cs : List (Nat × Use)}, e ∈ (relabelRun a u s cs).getLast? →
      e ∈ cs.getLast? ∨ e.2 = u
  | _, [], h => by cases h
  | s, (sz, v) :: cs, h => by
    rw [relabelRun, List.getLast?_cons] at h
    simp only [Option.mem_def, Option.some.injEq] at h
    cases hc : (relabelRun a u (s + sz) cs).getLast? with
    | none =>
      rw [hc, Option.getD_none] at h; subst h
      have : cs = [] := by
        cases cs with
        | nil => rfl
        | cons _ _ => simp [relabelRun] at hc
      subst this; by_cases hs : s = a <;> simp [hs]
    | some e' =>
      rw [hc, Option.getD_some] at h; subst h
      rcases getLast?_relabelRun (s := s + sz) (cs := cs) (by rw [hc]; rfl) with h | h
      · left; rw [List.getLast?_cons]; simp only [Option.mem_def] at h ⊢; rw [h]; rfl
      · exact .inr h

end TopSt

/-- Relabelling to a use that is not free keeps a run coalesced. -/
theorem coalescedB_relabelRun (a : Nat) (u : Use) (hu : u.tagFree = false) :
    ∀ (s : Nat) (cs : List (Nat × Use)), coalescedB cs = true → coalescedB (relabelRun a u s cs) = true
  | _, [], _ => rfl
  | s, [x], _ => by simp [relabelRun, coalescedB]
  | s, x :: y :: cs, h => by
    simp only [coalescedB, Bool.and_eq_true, Bool.not_eq_true'] at h
    have ih := coalescedB_relabelRun a u hu (s + x.1) (y :: cs) h.2
    simp only [relabelRun] at ih ⊢
    simp only [coalescedB, Bool.and_eq_true, Bool.not_eq_true', ih, and_true]
    by_cases h1 : s = a <;> by_cases h2 : s + x.1 = a <;> simp_all

/-- Relabelling the entry at `a` to a free use keeps a run of positive sizes coalesced when the
entries next to it are not free. -/
theorem coalescedB_relabelRun_free (a : Nat) (u : Use) :
    ∀ (s : Nat) (cs : List (Nat × Use)), coalescedB cs = true → (∀ e ∈ cs, 0 < e.1) →
      (∀ (pre : List (Nat × Use)) (x : Nat × Use) (post : List (Nat × Use)),
        cs = pre ++ x :: post → s + (pre.map (·.1)).sum = a →
          (∀ y ∈ pre.getLast?, y.2.tagFree = false) ∧ (∀ y ∈ post.head?, y.2.tagFree = false)) →
      coalescedB (relabelRun a u s cs) = true
  | _, [], _, _, _ => rfl
  | s, [x], _, _, _ => by simp [relabelRun, coalescedB]
  | s, x :: y :: cs, h, hpos, hn => by
    simp only [coalescedB, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hx : 0 < x.1 := hpos x (List.mem_cons_self ..)
    have ih := coalescedB_relabelRun_free a u (s + x.1) (y :: cs) h.2
      (fun e he => hpos e (List.mem_cons_of_mem _ he)) (by
      intro pre z post hpre hs
      have := hn (x :: pre) z post (by rw [hpre]; rfl) (by simp at hs ⊢; omega)
      refine ⟨fun w hw => ?_, this.2⟩
      cases pre with
      | nil => cases hw
      | cons p ps =>
        apply this.1
        rw [List.getLast?_cons] at hw ⊢
        rw [List.getLast?_cons]; simpa using hw)
    simp only [relabelRun] at ih ⊢
    simp only [coalescedB, Bool.and_eq_true, Bool.not_eq_true', ih, and_true]
    by_cases h1 : s = a
    · have hy := (hn [] x (y :: cs) rfl (by simp [h1])).2 y rfl
      subst h1
      have hx0 : ¬ x.1 = 0 := by omega
      simp [hx0, hy]
    · by_cases h2 : s + x.1 = a
      · have hx' := (hn [x] y cs rfl (by simp; omega)).1 x rfl
        subst h2
        have hx0 : ¬ x.1 = 0 := by omega
        simp [hx0, hx']
      · simp only [h1, h2, ite_false]; simpa using h.1

namespace TopWF

variable {C : Config} {ts : TopSt} {a : Nat} {u : Use}

/-- The geometric fields of `TopWF` hold after a relabelling. -/
theorem relabel_geom (h : TopWF C ts) :
    (∀ c ∈ (ts.relabel a u).heapChunks, c.size % C.align = 0 ∧ C.minSize ≤ c.size) ∧
    (∀ c ∈ (ts.relabel a u).heapChunks, c.addr % C.align = 0) ∧
    (∀ c ∈ (ts.relabel a u).heapChunks, c.addr ≠ 0) ∧
    (((ts.relabel a u).heapChunks.map (·.size)).sum + ts.topSize ≤ ts.systemMem) ∧
    ((ts.relabel a u).heapChunks.map (·.addr)).Nodup ∧
    (∀ c ∈ (ts.relabel a u).heapChunks, c.addr + c.size < 2 ^ 64) := by
  rw [TopSt.heapChunks_relabel]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc; simpa using h.sizes d hd
  · intro c hc; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc; simpa using h.aligned d hd
  · intro c hc; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc; simpa using h.nonNull d hd
  · have : (ts.heapChunks.map (Chunk.relabelAt a u)).map (·.size) = ts.heapChunks.map (·.size) := by
      simp [List.map_map, Function.comp_def]
    rw [this]; exact h.sysMem
  · rw [map_relabelAt_addr]; exact h.nodup
  · intro c hc; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc; simpa using h.bound d hd

/-- **Relabelling to a use that is not free keeps `TopWF`.** -/
theorem relabel (h : TopWF C ts) (hu : u.tagFree = false) : TopWF C (ts.relabel a u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.relabel_geom (a := a) (u := u)
  exact
  { sizes := h1, aligned := h2, nonNull := h3
    topAt := fun hs => by simp only [TopSt.relabel]; rw [relabelRun_fst]; exact h.topAt hs
    topAligned := h.topAligned
    topMin := h.topMin
    coalesced := coalescedB_relabelRun a u hu _ _ h.coalesced
    lastUsed := fun c hc => by
      rcases TopSt.getLast?_relabelRun a u hc with hc | hc
      · exact h.lastUsed c hc
      · rw [hc, hu]
    coalescedOld := fun g hg => by
      simp only [TopSt.relabel, List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      exact coalescedB_relabelRun a u hu _ _ (h.coalescedOld g' hg')
    sysMem := h4
    sysMemBound := h.sysMemBound
    noHeap := fun hs => by
      obtain ⟨h1, h2⟩ := h.noHeap hs
      simp [TopSt.relabel, h1, h2, relabelRun]
    nodup := h5
    bound := h6
    topBound := h.topBound }

/-- **Relabelling to any use keeps `TopWF`** when the relabelled tiling is still coalesced
(`TopSt.Coal`: the premise a body discharges from the neighbours it merged or checked). -/
theorem relabel_coal (h : TopWF C ts) (hc : (ts.relabel a u).Coal) : TopWF C (ts.relabel a u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.relabel_geom (a := a) (u := u)
  exact
  { sizes := h1, aligned := h2, nonNull := h3
    topAt := fun hs => by simp only [TopSt.relabel]; rw [relabelRun_fst]; exact h.topAt hs
    topAligned := h.topAligned
    topMin := h.topMin
    coalesced := hc.1
    lastUsed := hc.2.1
    coalescedOld := hc.2.2
    sysMem := h4
    sysMemBound := h.sysMemBound
    noHeap := fun hs => by
      obtain ⟨h1, h2⟩ := h.noHeap hs
      simp [TopSt.relabel, h1, h2, relabelRun]
    nodup := h5
    bound := h6
    topBound := h.topBound }

/-- Every chunk of a well-formed tiling has at least `MINSIZE` bytes. -/
theorem minSize_all (h : TopWF C ts) : ∀ c ∈ ts.heapChunks, C.minSize ≤ c.size :=
  fun c hc => (h.sizes c hc).2

end TopWF

end Silmaril.Libc.Ptmalloc
