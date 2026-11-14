module

public import Silmaril.Machine.Link.Defs

/-! # Patch application and the structure of a successful link

Architecture-independent facts about the imported static linker:

* `applyPatch_get`: one patch overwrites exactly the offsets it covers;
* `foldl_patches_get`, `foldl_patches_get_mem`, `foldl_patches_size`: a list of
  pairwise-disjoint patches, applied in order, leaves uncovered bytes alone and
  leaves each patch's own bytes in place, whatever the order;
* `linkSection_some`, `link_some`, `resolveRelocations_mem`, `addressAt_of_mem`:
  what a successful `linkSection`/`link`/`resolveRelocations` exposes.
-/

@[expose] public section

namespace Silmaril.Machine.Link

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link

theorem applyPatch_get {d d' : Bytes} {p : Patch} (h : applyPatch d p = some d') (i : Nat) :
    d'[i]? = if Covers p i then p.bytes[i - p.offset]? else d[i]? := by
  unfold applyPatch at h
  by_cases hb : p.offset + p.bytes.size ≤ d.size
  · simp only [hb, guard_true] at h
    cases h
    have hlen : (d.toList.take p.offset).length = p.offset := by simp; omega
    simp only [Covers, ← Array.getElem?_toList, List.append_assoc]
    by_cases h1 : i < p.offset
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1]
      have : ¬ (p.offset ≤ i ∧ i < p.offset + p.bytes.size) := by omega
      simp [this]
    · rw [List.getElem?_append_right (by omega), hlen]
      by_cases h2 : i < p.offset + p.bytes.size
      · have : p.offset ≤ i ∧ i < p.offset + p.bytes.size := ⟨by omega, h2⟩
        rw [List.getElem?_append_left (by simp; omega)]
        simp [this]
      · have : ¬ (p.offset ≤ i ∧ i < p.offset + p.bytes.size) := by omega
        rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
        simp only [this, ite_false, Array.length_toList]
        congr 1; omega
  · simp [hb] at h

/-- Bytes covered by no patch keep their section value. -/
theorem foldl_patches_get : ∀ {patches : List Patch} {d d' : Bytes},
    patches.Pairwise Patch.Disjoint → patches.foldlM applyPatch d = some d' → ∀ i,
    (∀ q ∈ patches, ¬ Covers q i) → d'[i]? = d[i]?
  | [], d, d', _, h, i, _ => by simp at h; cases h; rfl
  | q :: qs, d, d', hpw, h, i, hn => by
    simp only [List.foldlM_cons] at h
    cases hq : applyPatch d q with
    | none => simp [hq] at h
    | some e =>
      simp only [hq, Option.bind_eq_bind, Option.bind_some] at h
      rw [foldl_patches_get (List.pairwise_cons.mp hpw).2 h i
        (fun q' hq' => hn q' (List.mem_cons_of_mem _ hq')), applyPatch_get hq]
      simp only [hn q List.mem_cons_self, ite_false]

/-- Each patch's bytes survive the other (disjoint) patches. -/
theorem foldl_patches_get_mem : ∀ {patches : List Patch} {d d' : Bytes},
    patches.Pairwise Patch.Disjoint → patches.foldlM applyPatch d = some d' → ∀ q ∈ patches,
    ∀ i, Covers q i → d'[i]? = q.bytes[i - q.offset]?
  | [], _, _, _, _, q, hq, _, _ => by simp at hq
  | q :: qs, d, d', hpw, h, q', hq', i, hc => by
    simp only [List.foldlM_cons] at h
    cases he : applyPatch d q with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨hdisj, hpw'⟩ := List.pairwise_cons.mp hpw
      rcases List.mem_cons.mp hq' with rfl | hmem
      · rw [foldl_patches_get hpw' h i, applyPatch_get he]
        · simp only [hc, ite_true]
        · intro r hr hrc
          have := hdisj r hr
          simp only [Covers, Patch.Disjoint] at hc hrc this
          omega
      · exact foldl_patches_get_mem hpw' h q' hmem i hc

theorem foldl_patches_size : ∀ {patches : List Patch} {d d' : Bytes},
    patches.foldlM applyPatch d = some d' → d'.size = d.size
  | [], d, d', h => by simp at h; cases h; rfl
  | q :: qs, d, d', h => by
    simp only [List.foldlM_cons] at h
    cases he : applyPatch d q with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      rw [foldl_patches_size h, applyPatch_size he]

/-- Reassemble a suffix from pointwise facts about its first bytes. -/
theorem drop_eq_of_getElem? {α} {l pre : List α} {o : Nat}
    (h : ∀ j < pre.length, l[o + j]? = pre[j]?) :
    l.drop o = pre ++ l.drop (o + pre.length) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_drop]
  by_cases hj : j < pre.length
  · rw [List.getElem?_append_left hj, h j hj]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1; omega

theorem mapM_some_mem {α β} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], _, _, a, ha => by simp at ha
  | x :: xs, l', h, a, ha => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp ha with rfl | hmem
        · exact ⟨b, List.mem_cons_self, hx⟩
        · obtain ⟨c, hc, hfc⟩ := mapM_some_mem hxs a hmem
          exact ⟨c, List.mem_cons_of_mem _ hc, hfc⟩

theorem mapM_some_mem' {α β} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by simp at h; subst h; simp at hb
  | x :: xs, l', h, b, hb => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some c =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some bs =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hb with rfl | hmem
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨a, ha, hfa⟩ := mapM_some_mem' hxs b hmem
          exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

/-- A successful section link applied the patches of exactly the relocations
aimed at that section, disjointly, to the input section bytes. -/
theorem linkSection_some {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {relocate : Relocator} {placement : Placement} {out : LinkedSection}
    (h : linkSection objects rels relocate placement = some out) :
    ∃ part patches, sectionAt objects placement.key = some part ∧
      (rels.filter (fun r => r.key == placement.key)).mapM (fun r => do
        let patch ← relocate rels r part.data
        guard (patch.offset = r.offset ∧ 0 < patch.bytes.size)
        pure patch) = some patches ∧
      patches.Pairwise Patch.Disjoint ∧ patches.foldlM applyPatch part.data = some out.data ∧
      out.address = placement.address ∧ out.key = placement.key := by
  unfold linkSection at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨part, hpart, _, _, _, _, _, _, _, _, _, _, patches, hmap, _, hpw, data, hfold, h⟩ := h
  obtain ⟨_, _, rfl⟩ := h
  refine ⟨part, patches, hpart, hmap, ?_, hfold, rfl, rfl⟩
  by_contra hn
  simp [hn] at hpw

/-- The structure exposed by a successful `link`. -/
theorem link_some {accepts : Header → Bool} {relocate : Relocator} {objects : List ObjectFile}
    {layout : Layout} {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : link accepts relocate objects layout absolute = some out) :
    (layout.map Placement.key).Nodup ∧
    ∃ rels, resolveRelocations objects layout absolute = some rels ∧
      layout.mapM (linkSection objects rels relocate) = some out ∧
      out.Pairwise LinkedSection.Disjoint := by
  unfold link at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, -, _, -, _, hnd, _, -, _, -, _, -, rels, hrels, sections, hsec, _, hpw, rfl⟩ := h
  refine ⟨?_, rels, hrels, hsec, ?_⟩
  · by_contra hn; simp [hn] at hnd
  · by_contra hn; simp [hn] at hpw

theorem addressAt_of_mem : ∀ {layout : Layout} {placement : Placement},
    placement ∈ layout → (layout.map Placement.key).Nodup →
    addressAt layout placement.key = some placement.address
  | [], _, h, _ => by simp at h
  | q :: qs, placement, h, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp h with rfl | hmem
    · simp [addressAt]
    · have hne : (q.key == placement.key) = false := by
        simp only [beq_eq_false_iff_ne]; intro he
        exact hnd.1 ⟨placement, hmem, he.symm⟩
      have ih := addressAt_of_mem hmem hnd.2
      simp only [addressAt, List.find?_cons, hne] at ih ⊢
      exact ih

/-- A resolved relocation's place is its target section's base plus its offset. -/
theorem resolveRelocations_mem {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {rels : List ResolvedRelocation}
    (h : resolveRelocations objects layout absolute = some rels) {r : ResolvedRelocation}
    (hr : r ∈ rels) :
    ∃ base, addressAt layout r.key = some base ∧ r.place = base + r.offset := by
  unfold resolveRelocations at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨groups, hgroups, rfl⟩ := h
  obtain ⟨g, hg, hrg⟩ := List.mem_flatten.mp hr
  obtain ⟨⟨object, idx⟩, -, hgo⟩ := mapM_some_mem' hgroups g hg
  obtain ⟨rel, -, hrel⟩ := mapM_some_mem' hgo r hrg
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hrel
  obtain ⟨part, -, _, -, base, hbase, _, -, sv, -, rfl⟩ := hrel
  exact ⟨base, hbase, rfl⟩

end Silmaril.Machine.Link
