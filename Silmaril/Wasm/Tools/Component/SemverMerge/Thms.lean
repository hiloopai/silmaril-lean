module

public import Silmaril.Wasm.Tools.Component.SemverMerge.Defs

/-!
# `--merge-world-imports-based-on-semver`: what the source transformation guarantees

* `mergeWorld_no_removed`: the merged world imports no replaced interface by its path;
* `mergeWorld_sublist_keys`: every item of the merged world comes from an item of the source
  world (the same kind of item, with its `use`s redirected);
* `tracks_inv`, `replacements_track`: every replacement stays on its semver track: the
  replaced interface and its replacement have the same `track` (same namespace, package,
  interface name and compatibility track).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.SemverMerge

open Silmaril.Wasm.Wit

/-- The transformation of one item (the map in `mergeWorld`). -/
def fixItem (rp : List (Id × Id)) (cur : PackageName) : WorldItem → WorldItem
  | .use u => .use (fixUse rp cur u)
  | .import e => match e.ext with
    | .iface n items => .import { e with ext := .iface n (fixIfaceItems rp cur items) }
    | _ => .import e
  | .export e => match e.ext with
    | .iface n items => .export { e with ext := .iface n (fixIfaceItems rp cur items) }
    | _ => .export e
  | it => it

theorem mergeWorld_items (rp : List (Id × Id)) (cur : PackageName) (w : World) :
    (mergeWorld rp cur w).items =
      (w.items.filter fun it => !removedImport rp cur it).map (fixItem rp cur) := by
  unfold mergeWorld
  congr 1

/-- `fixItem` keeps whether an item is a removed import. -/
theorem removedImport_fixItem (rp : List (Id × Id)) (cur : PackageName) (it : WorldItem) :
    removedImport rp cur (fixItem rp cur it) = removedImport rp cur it := by
  cases it with
  | «import» e =>
    obtain ⟨ext, docs, gates⟩ := e
    cases ext <;> rfl
  | «export» e =>
    obtain ⟨ext, docs, gates⟩ := e
    cases ext <;> rfl
  | use u => rfl
  | type d => rfl
  | «include» i => rfl

/-- **No replaced import is left** in the merged world. -/
theorem mergeWorld_no_removed (rp : List (Id × Id)) (cur : PackageName) (w : World)
    {it : WorldItem} (h : it ∈ (mergeWorld rp cur w).items) : removedImport rp cur it = false := by
  rw [mergeWorld_items] at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have hk : (!removedImport rp cur x) = true := (List.mem_filter.mp hx).2
  rw [removedImport_fixItem]
  cases hr : removedImport rp cur x with
  | false => rfl
  | true => rw [hr] at hk; cases hk

/-- Every item of the merged world is the transformation of an item of the source world. -/
theorem mergeWorld_sublist_keys (rp : List (Id × Id)) (cur : PackageName) (w : World)
    {it : WorldItem} (h : it ∈ (mergeWorld rp cur w).items) :
    ∃ x ∈ w.items, it = fixItem rp cur x := by
  rw [mergeWorld_items] at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact ⟨x, (List.mem_filter.mp hx).1, rfl⟩

/-- The invariant of `tracks`: every greatest version and every removed interface is on a
track, the greatest on its own. -/
def TracksInv (tops : List ((Name × Name × Version × Name) × Id)) (removed : List Id) : Prop :=
  (∀ p ∈ tops, track p.2 = some p.1) ∧ (∀ i ∈ removed, ∃ t, track i = some t ∧ ∃ j, (t, j) ∈ tops)

theorem lookup_mem {t : Name × Name × Version × Name} {j : Id} :
    ∀ {l : List ((Name × Name × Version × Name) × Id)}, l.lookup t = some j → (t, j) ∈ l
  | [], h => by cases h
  | (t', k) :: l, h => by
    unfold List.lookup at h
    split at h
    · rename_i heq
      have ht : t = t' := eq_of_beq heq
      have hk : k = j := Option.some.inj h
      rw [ht, hk]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- Replacing a track's greatest keeps every track present. -/
theorem mem_map_top {tops : List ((Name × Name × Version × Name) × Id)}
    {t : Name × Name × Version × Name} {i : Id} {u : Name × Name × Version × Name} {k : Id}
    (h : (u, k) ∈ tops) :
    ∃ k', (u, k') ∈ tops.map fun (t', k) => if t' == t then (t', i) else (t', k) := by
  by_cases hu : u = t
  · exact ⟨i, List.mem_map.mpr ⟨(u, k), h, by simp only [hu, beq_self_eq_true, ite_true]⟩⟩
  · refine ⟨k, List.mem_map.mpr ⟨(u, k), h, ?_⟩⟩
    have hb : (u == t) = false := by simpa only [beq_eq_false_iff_ne] using hu
    simp only [hb, Bool.false_eq_true, ite_false]

theorem tracks_inv : ∀ (is : List Id) (tops : List ((Name × Name × Version × Name) × Id))
    (removed : List Id), TracksInv tops removed →
    TracksInv (tracks is tops removed).1 (tracks is tops removed).2
  | [], _, _, h => h
  | i :: is, tops, removed, h => by
    unfold tracks
    split
    · exact tracks_inv is tops removed h
    · rename_i t ht
      split
      · show TracksInv (tracks is (tops ++ [(t, i)]) removed).1 (tracks is (tops ++ [(t, i)]) removed).2
        apply tracks_inv
        refine ⟨fun p hp => ?_, fun r hr => ?_⟩
        · rcases List.mem_append.mp hp with hp | hp
          · exact h.1 p hp
          · rw [List.mem_singleton.mp hp]
            exact ht
        · obtain ⟨u, hu, k, hk⟩ := h.2 r hr
          exact ⟨u, hu, k, List.mem_append_left _ hk⟩
      · rename_i j hj
        have hjm : (t, j) ∈ tops := lookup_mem hj
        split
        · rename_i vi vj _ _
          split
          · show TracksInv (tracks is _ (removed ++ [j])).1 (tracks is _ (removed ++ [j])).2
            apply tracks_inv
            refine ⟨fun p hp => ?_, fun r hr => ?_⟩
            · obtain ⟨⟨u, k⟩, hk, rfl⟩ := List.mem_map.mp hp
              by_cases hu : u = t
              · simp only [hu, beq_self_eq_true, ite_true]
                exact ht
              · have hb : (u == t) = false := by simpa only [beq_eq_false_iff_ne] using hu
                simp only [hb, Bool.false_eq_true, ite_false]
                exact h.1 (u, k) hk
            · rcases List.mem_append.mp hr with hr | hr
              · obtain ⟨u, hu, k, hk⟩ := h.2 r hr
                exact ⟨u, hu, mem_map_top hk⟩
              · rw [List.mem_singleton.mp hr]
                exact ⟨t, h.1 (t, j) hjm, mem_map_top hjm⟩
          · split
            · show TracksInv (tracks is tops (removed ++ [i])).1 (tracks is tops (removed ++ [i])).2
              apply tracks_inv
              refine ⟨h.1, fun r hr => ?_⟩
              rcases List.mem_append.mp hr with hr | hr
              · exact h.2 r hr
              · rw [List.mem_singleton.mp hr]
                exact ⟨t, ht, j, hjm⟩
            · exact tracks_inv is tops removed h
        · exact tracks_inv is tops removed h

/-- **Replacements stay on their track**: a replaced interface and its replacement have the same
semver track. -/
theorem replacements_track {is : List Id} {i j : Id} (h : (i, j) ∈ replacements is) :
    ∃ t, track i = some t ∧ track j = some t := by
  unfold replacements at h
  obtain ⟨r, _, hr⟩ := List.mem_filterMap.mp h
  have h0 : TracksInv [] [] := by
    unfold TracksInv
    exact ⟨fun _ hp => (nomatch hp), fun _ hr => (nomatch hr)⟩
  have hinv := tracks_inv is [] [] h0
  cases hti : track r with
  | none => rw [hti] at hr; cases hr
  | some t =>
    rw [hti] at hr
    cases hl : (tracks is [] []).1.lookup t with
    | none => simp only [hl, Option.bind_some, Option.map_none] at hr; cases hr
    | some k =>
      simp only [hl, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨t, hti, hinv.1 (t, k) (lookup_mem hl)⟩

end Silmaril.Wasm.Tools.Component.SemverMerge
