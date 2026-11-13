module

public import Silmaril.Wasm.Tools.Component.WitText.Defs

/-!
# Theorems of `component wit`'s options

* `docFree_no_doc`, `docFree_sublist`: `--no-docs` keeps exactly the lines of the printed text
  that are not doc comment lines, in order (the printer writes docs only as such lines).
* `encodeTextXF_nil`: without features, the encoder is `WitDir.encodeTextX`.
* `withWorld_mem`: the embedded world is printed in its package, which is among the nested
  packages.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.WitText

theorem docFree_no_doc {t l : String} (h : l ∈ docFree t) : isDocLine l = false := by
  unfold docFree at h
  have := (List.mem_filter.mp h).2
  simpa using this

theorem docFree_sublist (t : String) : (docFree t).Sublist (t.splitOn "\n") :=
  List.filter_sublist

theorem docFree_keep {t l : String} (hl : l ∈ t.splitOn "\n") (hd : isDocLine l = false) :
    l ∈ docFree t :=
  List.mem_filter.mpr ⟨hl, by simp [hd]⟩

theorem encodeTextXF_nil (m : List (String × String)) (ds : List (List (String × String))) :
    encodeTextXF m ds [] = Wac.WitDir.encodeTextX m ds := rfl

theorem withWorld_mem (ns : List (Wit.Binary.PackageName × List (String × Wit.Binary.Interface)))
    (wp : Wit.Binary.PackageName) (w : String × Wit.Binary.World) :
    ∃ ifs, (wp, ifs, [w]) ∈ withWorld ns wp w := by
  unfold withWorld
  split
  · rename_i h
    obtain ⟨⟨q, ifs⟩, hm, hq⟩ := List.any_eq_true.mp h
    have hq' : q = wp := by simpa using hq
    refine ⟨ifs, List.mem_map.mpr ⟨(q, ifs), hm, ?_⟩⟩
    simp [hq']
  · exact ⟨[], List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

end Silmaril.Wasm.Tools.Component.WitText
