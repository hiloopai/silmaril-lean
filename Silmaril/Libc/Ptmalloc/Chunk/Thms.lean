module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc: lemmas on chunks, views, runs and exact lists

The generic facts every component's lemmas reuse:

* `Chunk.relabelAt a u`: a relabelling as a map over the chunks (`layout_relabelRun`);
* `ListExact.view`: a list is exact for a use against a view that keeps that use iff against the
  whole tiling (so lemmas are stated once, on the tiling);
* the three list moves under a relabelling of the chunk at `a` from `v` to `u` (addresses
  distinct): `ListExact.relabel_keep` (a list of another use is unaffected),
  `ListExact.relabel_cons` (push `a` on the `u` list), `ListExact.relabel_erase` (remove `a`
  from the `v` list).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- Relabel a chunk if it is at `a`. -/
def Chunk.relabelAt (a : Nat) (u : Use) (c : Chunk) : Chunk :=
  if c.addr = a then { c with use := u } else c

@[simp] theorem Chunk.relabelAt_addr (a : Nat) (u : Use) (c : Chunk) : (c.relabelAt a u).addr = c.addr := by
  unfold Chunk.relabelAt; split <;> rfl

@[simp] theorem Chunk.relabelAt_size (a : Nat) (u : Use) (c : Chunk) : (c.relabelAt a u).size = c.size := by
  unfold Chunk.relabelAt; split <;> rfl

theorem Chunk.relabelAt_of_ne {a : Nat} {u : Use} {c : Chunk} (h : c.addr ≠ a) : c.relabelAt a u = c := by
  simp [Chunk.relabelAt, h]

theorem Chunk.relabelAt_of_eq {a : Nat} {u : Use} {c : Chunk} (h : c.addr = a) :
    c.relabelAt a u = { c with use := u } := by
  simp [Chunk.relabelAt, h]

/-- **A relabelled run lays out as the relabelled chunks.** -/
theorem layout_relabelRun (a : Nat) (u : Use) :
    ∀ (s : Nat) (cs : List (Nat × Use)),
      layout s (relabelRun a u s cs) = (layout s cs).map (Chunk.relabelAt a u)
  | _, [] => rfl
  | s, (sz, v) :: cs => by
    simp only [relabelRun, layout, List.map_cons, layout_relabelRun a u (s + sz) cs]
    congr 1
    by_cases h : s = a <;> simp [Chunk.relabelAt, h]

/-- A relabelling keeps the sizes of a run. -/
theorem relabelRun_fst (a : Nat) (u : Use) :
    ∀ (s : Nat) (cs : List (Nat × Use)), (relabelRun a u s cs).map (·.1) = cs.map (·.1)
  | _, [] => rfl
  | s, (sz, v) :: cs => by simp [relabelRun, relabelRun_fst a u (s + sz) cs]

theorem relabelRun_length (a : Nat) (u : Use) (s : Nat) (cs : List (Nat × Use)) :
    (relabelRun a u s cs).length = cs.length := by
  have := congrArg List.length (relabelRun_fst a u s cs); simpa using this

/-- **A view keeps exactly the chunks of the uses it shows**, so exactness for such a use can be
read on the whole list. -/
theorem ListExact.view_iff {p : Use → Bool} {l : List Nat} {cs : List Chunk} {u : Use}
    (hp : p u = true) : ListExact l (Chunk.view p cs) u ↔ ListExact l cs u := by
  unfold ListExact Chunk.view
  constructor
  · intro h x; rw [h x]; constructor
    · rintro ⟨c, hc, h1, h2⟩; exact ⟨c, (List.mem_filter.mp hc).1, h1, h2⟩
    · rintro ⟨c, hc, h1, h2⟩; exact ⟨c, List.mem_filter.mpr ⟨hc, by rw [h2]; exact hp⟩, h1, h2⟩
  · intro h x; rw [h x]; constructor
    · rintro ⟨c, hc, h1, h2⟩; exact ⟨c, List.mem_filter.mpr ⟨hc, by rw [h2]; exact hp⟩, h1, h2⟩
    · rintro ⟨c, hc, h1, h2⟩; exact ⟨c, (List.mem_filter.mp hc).1, h1, h2⟩

/-- Membership in a relabelled list. -/
theorem mem_map_relabelAt {a : Nat} {u : Use} {cs : List Chunk} {c : Chunk} :
    c ∈ cs.map (Chunk.relabelAt a u) ↔
      (∃ d ∈ cs, d.addr = a ∧ c = { d with use := u }) ∨ (c.addr ≠ a ∧ c ∈ cs) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    by_cases h : d.addr = a
    · exact .inl ⟨d, hd, h, Chunk.relabelAt_of_eq h⟩
    · exact .inr ⟨by simpa using h, by rw [Chunk.relabelAt_of_ne h]; exact hd⟩
  · rintro (⟨d, hd, h, rfl⟩ | ⟨h, hc⟩)
    · exact ⟨d, hd, Chunk.relabelAt_of_eq h⟩
    · exact ⟨c, hc, Chunk.relabelAt_of_ne h⟩

/-- With distinct addresses, the chunk at an address is unique. -/
theorem chunk_unique {cs : List Chunk} (hn : (cs.map (·.addr)).Nodup) {c d : Chunk}
    (hc : c ∈ cs) (hd : d ∈ cs) (h : c.addr = d.addr) : c = d := by
  induction cs with
  | nil => cases hc
  | cons e cs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · rw [hc, hd]
    · subst hc; exact absurd (by rw [h]; exact List.mem_map_of_mem (f := (·.addr)) hd) hn.1
    · subst hd; exact absurd (by rw [← h]; exact List.mem_map_of_mem (f := (·.addr)) hc) hn.1
    · exact ih hn.2 hc hd

section relabel

variable {a : Nat} {u v w : Use} {cs : List Chunk} {l : List Nat}

/-- **A list of another use is unaffected** by relabelling the chunk at `a` from `v` to `u`. -/
theorem ListExact.relabel_keep (h : ListExact l cs w) (hn : (cs.map (·.addr)).Nodup)
    (ha : ∃ d ∈ cs, d.addr = a ∧ d.use = v) (hu : u ≠ w) (hv : v ≠ w) :
    ListExact l (cs.map (Chunk.relabelAt a u)) w := by
  intro x; rw [h x]
  obtain ⟨d, hd, hda, hdv⟩ := ha
  constructor
  · rintro ⟨c, hc, rfl, hcw⟩
    refine ⟨c, mem_map_relabelAt.mpr (.inr ⟨fun hca => ?_, hc⟩), rfl, hcw⟩
    have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hv (hdv.symm.trans hcw)
  · rintro ⟨c, hc, rfl, hcw⟩
    rcases mem_map_relabelAt.mp hc with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
    · exact absurd hcw hu
    · exact ⟨c, hc, rfl, hcw⟩

/-- **Push**: relabelling the chunk at `a` from `v ≠ u` to `u` adds `a` to the `u` list. -/
theorem ListExact.relabel_cons (h : ListExact l cs u) (hn : (cs.map (·.addr)).Nodup)
    (ha : ∃ d ∈ cs, d.addr = a ∧ d.use = v) (hv : v ≠ u) :
    ListExact (a :: l) (cs.map (Chunk.relabelAt a u)) u := by
  intro x
  obtain ⟨d, hd, hda, hdv⟩ := ha
  rw [List.mem_cons, h x]
  constructor
  · rintro (rfl | ⟨c, hc, rfl, hcu⟩)
    · exact ⟨{ d with use := u }, mem_map_relabelAt.mpr (.inl ⟨d, hd, hda, rfl⟩), hda, rfl⟩
    · refine ⟨c, mem_map_relabelAt.mpr (.inr ⟨fun hca => ?_, hc⟩), rfl, hcu⟩
      have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hv (hdv.symm.trans hcu)
  · rintro ⟨c, hc, rfl, hcu⟩
    rcases mem_map_relabelAt.mp hc with ⟨e, he, hea, rfl⟩ | ⟨hca, hc⟩
    · exact .inl hea
    · exact .inr ⟨c, hc, rfl, hcu⟩

/-- **Remove**: relabelling the chunk at `a` from `v` to `u ≠ v` removes `a` from the `v` list. -/
theorem ListExact.relabel_erase (h : ListExact l cs v) (hl : l.Nodup) (hu : u ≠ v) :
    ListExact (l.erase a) (cs.map (Chunk.relabelAt a u)) v := by
  intro x
  rw [hl.mem_erase_iff, h x]
  constructor
  · rintro ⟨hxa, c, hc, rfl, hcv⟩
    exact ⟨c, mem_map_relabelAt.mpr (.inr ⟨hxa, hc⟩), rfl, hcv⟩
  · rintro ⟨c, hc, rfl, hcv⟩
    rcases mem_map_relabelAt.mp hc with ⟨e, he, hea, rfl⟩ | ⟨hca, hc⟩
    · exact absurd hcv hu
    · exact ⟨hca, c, hc, rfl, hcv⟩

/-- A list exact for a use the relabelled chunk neither had nor gets is still nodup-compatible:
the relabelled chunks keep their addresses. -/
theorem map_relabelAt_addr : (cs.map (Chunk.relabelAt a u)).map (·.addr) = cs.map (·.addr) := by
  simp [List.map_map, Function.comp_def]

end relabel

/-- Lists that are exact for the same use against the same chunks have the same members. -/
theorem ListExact.mem_iff {l l' : List Nat} {cs : List Chunk} {u : Use}
    (h : ListExact l cs u) (h' : ListExact l' cs u) (x : Nat) : x ∈ l ↔ x ∈ l' := by
  rw [h x, h' x]

/-- A list exact for `u` under a list with the same members. -/
theorem ListExact.of_mem_iff {l l' : List Nat} {cs : List Chunk} {u : Use}
    (h : ListExact l cs u) (hm : ∀ x, x ∈ l' ↔ x ∈ l) : ListExact l' cs u := by
  intro x; rw [hm x, h x]

end Silmaril.Libc.Ptmalloc
