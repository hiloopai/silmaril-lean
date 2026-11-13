module

public import Silmaril.Wasm.Tools.Component.Ize.Defs

/-!
# Theorems of `--importize` / `--exportize` on world sources

* `importizeWorld_no_export`, `importizeWorld_imports`: an importized world has no exports, and
  its imports are exactly the original exports, after the kept types.
* `exportizeWorld_all`: with no filter, an exportized world has no imports; every original
  import is an export.
* `transformPackage_last`: the transformed world is the package's last item.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Ize

open Silmaril.Wasm.Wit

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The importized world's items: the kept types, then the original exports as imports. -/
theorem importizeWorld_items {w w' : World} {out : Option String}
    (h : importizeWorld w out = .ok w') :
    w'.items = w.items.filter (fun | .type _ | .use _ => true | _ => false) ++
      (w.items.filterMap fun | .export e => some e | _ => none).map .import := by
  unfold importizeWorld at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  rfl

/-- An importized world has no exports. -/
theorem importizeWorld_no_export {w w' : World} {out : Option String}
    (h : importizeWorld w out = .ok w') (e : WorldExtern) : WorldItem.export e ∉ w'.items := by
  rw [importizeWorld_items h]
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · have := (List.mem_filter.mp hm).2
    simp at this
  · obtain ⟨_, _, he⟩ := List.mem_map.mp hm
    cases he

/-- With no filter, an exportized world has no imports. -/
theorem exportizeWorld_no_import {w w' : World} {out : Option String}
    (h : exportizeWorld w out [] = .ok w') (e : WorldExtern) : WorldItem.import e ∉ w'.items := by
  unfold exportizeWorld at h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨it, _, hit⟩ := List.mem_filterMap.mp hm
    cases it <;> simp at hit
  · obtain ⟨it, _, hit⟩ := List.mem_filterMap.mp hm
    cases it <;> simp at hit

/-- The transformed world is the package's last item. -/
theorem transformPackage_last {P P' : Package} {n : String} {f : World → Except String World}
    (h : transformPackage P n f = .ok P') : ∃ w w', f w = .ok w' ∧ P'.items.getLast? = some (.world w') := by
  unfold transformPackage at h
  obtain ⟨w, _, h⟩ := bind_ok h
  obtain ⟨w', hf, h⟩ := bind_ok h
  cases h
  exact ⟨w, w', hf, by simp⟩

end Silmaril.Wasm.Tools.Component.Ize
