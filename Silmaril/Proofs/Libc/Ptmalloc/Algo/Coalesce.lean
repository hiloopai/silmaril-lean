module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Steps

/-!
# ptmalloc algorithm: coalescing (`Task.algo.wfCoalesce`)

`Algo.coalesce_spec`: coalescing a held (`internal`) chunk of a well-formed view is an arena step
(`ArenaStep`: well formed, only the arena changed, fastbins and lent-out payloads kept). The proof
follows the body: `coalesce = coalesceHead >>= coalesceTail` (backward merge, then into top, the
fence, or forward merge + unsorted head), each a chain of the step lemmas of
`Silmaril.Proofs.Libc.Ptmalloc.Algo.Steps` on the run decomposition of `Silmaril.Proofs.Libc.Ptmalloc.Algo.Tiling`.

`Algo.wfCoalesce : ∀ C, Task.algo.wfCoalesce C`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- The forward half of `coalesce` (into top, at a fence, or forward merge), then the unsorted
head. -/
def coalesceTail (l : Local) (a : Nat) : Res (Nat × Local) := do
  let some loc := l.av.tiles.locate a | .error .internal
  match loc.next with
  | .top =>
    let l := mergeTop l
    pure (l.av.tiles.topSize, l)
  | .fence => pure (loc.self.size, l.unsortedPush a)
  | .chunk n =>
    if n.use.tagFree then do
      let l ← unlink l n.addr .internal
      let l := fuse l a .internal
      pure (loc.self.size + n.size, l.unsortedPush a)
    else pure (loc.self.size, l.unsortedPush a)

/-- **`coalesce` once the chunk is located**: the backward merge, then the forward half. -/
theorem coalesce_of_locate {l : Local} {a : Nat} {loc : Loc} (h : l.av.tiles.locate a = some loc) :
    coalesce l a = match loc.prev with
      | some pc =>
        if pc.use.tagFree then
          unlink l pc.addr .internal >>= fun l₁ => coalesceTail (fuse l₁ pc.addr .internal) pc.addr
        else coalesceTail l a
      | none => coalesceTail l a := by
  unfold coalesce
  rw [h]
  obtain ⟨prev, self, next, cur⟩ := loc
  cases prev with
  | none => rfl
  | some pc =>
    by_cases hf : pc.use.tagFree = true
    · simp only [hf, ite_true]; rfl
    · simp only [hf, Bool.false_eq_true, ite_false]; rfl

theorem ok_bind {α β : Type} (x : α) (f : α → Res β) : (Except.ok x >>= f) = f x := rfl

/-- **The forward half** on a held chunk whose previous chunk is used. -/
theorem coalesceTail_spec {l l' : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))}
    {s : Nat} {pre post : List (Nat × Use)} {sz r : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: post) :: R₂)
    (hprev : ∀ e ∈ pre.getLast?, e.2.tagFree = false)
    (h : coalesceTail l (s + runLen pre) = .ok (r, l')) : ArenaStep C l l' := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hloc := TopSt.locate_of_runs hr rfl ht.nodup
  unfold coalesceTail at h
  rw [hloc] at h
  simp only at h
  cases post with
  | nil =>
    by_cases hR : R₂ = []
    · subst hR
      simp only [List.head?_nil, Option.map_none, Option.getD_none, ite_true] at h
      cases h
      exact mergeTop_step hw hr hprev
    · simp only [List.head?_nil, Option.map_none, Option.getD_none, hR, ite_false] at h
      cases h
      exact unsortedPush_step hw hr hprev (by simp) (fun h0 => absurd h0 hR)
  | cons n post' =>
    obtain ⟨nsz, nu⟩ := n
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at h
    have hcoal := ht.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
    simp only at hcoal
    rw [coalescedB_mid_used _ _ _ rfl, coalescedB_cons] at hcoal
    by_cases hf : nu.tagFree = true
    · simp only [hf, ite_true] at h
      obtain ⟨l₃, hu, hst₃, ht₃⟩ := unlink_step hw (TopSt.mem_of_runs_next hr) hf
      simp only at hu
      rw [hu, ok_bind] at h
      cases h
      have hr₀ : l.av.tiles.runs = R₁ ++ (s, (pre ++ [(sz, .internal)]) ++ (nsz, nu) :: post') :: R₂ := by
        rw [hr]; simp
      have hr₃ : l₃.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: (nsz, .internal) :: post') :: R₂ := by
        rw [ht₃, TopSt.runs_relabel (x := (nsz, nu)) .internal hr₀ (by simp [runLen_append, Nat.add_assoc]) ht.nodup]
        simp
      obtain ⟨hst₄, hr₄⟩ := fuse_step hst₃.wf hr₃
      have hst₅ := unsortedPush_step hst₄.wf hr₄ hprev (hcoal.2.2 hf) (by
        intro h0; subst h0
        intro hnil; subst hnil
        have := ht.runs_last (R₁ := R₁) (s := s) hr (nsz, nu)
          (by rw [getLast?_append_cons]; rfl)
        rw [hf] at this; cases this)
      exact hst₃.trans (hst₄.trans hst₅)
    · simp only [hf, Bool.false_eq_true, ite_false] at h
      cases h
      exact unsortedPush_step hw hr hprev (by simpa using hf) (fun _ => by simp)

/-- **`coalesce` of a held chunk is an arena step.** -/
theorem coalesce_spec {l l' : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))}
    {s : Nat} {pre post : List (Nat × Use)} {sz r : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: post) :: R₂)
    (h : coalesce l (s + runLen pre) = .ok (r, l')) : ArenaStep C l l' := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hloc := TopSt.locate_of_runs hr rfl ht.nodup
  rw [coalesce_of_locate hloc] at h
  simp only at h
  rcases List.eq_nil_or_concat pre with hpre | ⟨pre₀, pe, hpre⟩
  · subst hpre
    simp only [layout_nil, List.getLast?_nil] at h
    exact coalesceTail_spec hw hr (by simp) h
  · rw [List.concat_eq_append] at hpre
    subst hpre
    obtain ⟨psz, pu⟩ := pe
    have hr' : l.av.tiles.runs = R₁ ++ (s, pre₀ ++ (psz, pu) :: (sz, .internal) :: post) :: R₂ := by
      rw [hr]; simp
    have hlast : (layout s (pre₀ ++ [(psz, pu)])).getLast? = some ⟨s + runLen pre₀, psz, pu⟩ := by
      rw [layout_append]; simp [layout]
    rw [hlast] at h
    have hcoal := ht.runs_coal _ (by rw [hr']; exact List.mem_append_right _ (List.mem_cons_self ..))
    simp only at hcoal
    by_cases hpf : pu.tagFree = true
    · obtain ⟨l₁, hu, hst₁, ht₁⟩ := unlink_step hw (TopSt.mem_of_runs_prev hr') hpf
      simp only at hu
      simp only [hpf, ite_true, hu, ok_bind] at h
      have hr₁ : l₁.av.tiles.runs = R₁ ++ (s, pre₀ ++ (psz, .internal) :: (sz, .internal) :: post) :: R₂ := by
        rw [ht₁, TopSt.runs_relabel (x := (psz, pu)) .internal hr' rfl ht.nodup]
      obtain ⟨hst₂, hr₂⟩ := fuse_step hst₁.wf hr₁
      rw [coalescedB_mid _ _ _] at hcoal
      exact hst₁.trans (hst₂.trans (coalesceTail_spec hst₂.wf hr₂ (hcoal.2.2 hpf).1 h))
    · simp only [hpf, Bool.false_eq_true, ite_false] at h
      exact coalesceTail_spec hw hr (by simpa using hpf) h

theorem coalesce_spec' {l l' : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))}
    {s a : Nat} {pre post : List (Nat × Use)} {sz r : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: post) :: R₂) (ha : s + runLen pre = a)
    (h : coalesce l a = .ok (r, l')) : ArenaStep C l l' := by
  subst ha; exact coalesce_spec hw hr h

/-- A held chunk of a well-formed view sits in a run decomposition. -/
theorem runs_of_chunk {ts : TopSt} (ht : TopWF C ts) {c : Chunk} (hc : c ∈ ts.heapChunks) :
    ∃ R₁ s pre post R₂, ts.runs = R₁ ++ (s, pre ++ (c.size, c.use) :: post) :: R₂ ∧
      s + runLen pre = c.addr := by
  have hn := ht.nodup
  rw [TopSt.heapChunks_eq] at hn hc
  obtain ⟨R₁, s, cs, R₂, hr, hcs, -⟩ := runs_split hn hc
  obtain ⟨pre, post, hcs', ha⟩ := mem_layout_split hcs
  exact ⟨R₁, s, pre, post, R₂, by rw [hr, hcs'], ha⟩

/-- **`Algo.wfCoalesce`**. -/
theorem wfCoalesce (C : Config) : Task.algo.wfCoalesce C := by
  intro _ l l' a r hw ⟨c, hc, hca, hcu⟩ h
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk hw.arena.tiles hc
  rw [hcu] at hr
  rw [← hca, ← ha] at h
  have hst := coalesce_spec hw.hf hr h
  refine ⟨hst.wf.of_hf fun hne => ?_, hst.within, by rw [hst.out]⟩
  rw [hst.fast] at hne ⊢; exact hw.arena.fast.flag hne

end Silmaril.Libc.Ptmalloc.Algo
