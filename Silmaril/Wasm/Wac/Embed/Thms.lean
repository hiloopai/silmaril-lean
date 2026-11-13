module

public import Silmaril.Wasm.Wac.Embed.Defs

/-!
# WAC: embedding packages keeps index spaces, the profile and the composition graph

* `secAllocs_embedSec`, `allocs_embed`: every section allocates in the same index spaces as
  before, so every index of the composition still names the same item;
* `isProfile_embed`: the result is in the composition profile exactly when `c` is;
* `graph_embed`: it lowers to the same composition graph (`Lower.graph` counts an embedded
  `(component …)` and an imported component alike).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Embed

open Silmaril.Wasm.Component.Binary

theorem embedSec_eq (ps : PkgTable) (s : Section) :
    embedSec ps s = s ∨ ∃ n t d, s = .imports [⟨n, .component t⟩] ∧ embedSec ps s = .component d := by
  unfold embedSec
  split
  · rename_i n t
    split
    · rename_i d _; exact .inr ⟨n, t, d, rfl, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem secAllocs_embedSec (ps : PkgTable) (s : Section) :
    secAllocs (embedSec ps s) = secAllocs s := by
  rcases embedSec_eq ps s with h | ⟨n, t, d, rfl, h⟩
  · rw [h]
  · rw [h]; rfl

/-- **Embedding keeps every index space.** -/
theorem allocs_embed (ps : PkgTable) (c : Ast) : allocs (embed ps c) = allocs c := by
  cases c with
  | mk ss =>
    simp only [allocs, embed, Ast.sections, List.flatMap_map, secAllocs_embedSec]

theorem secOk_embedSec (ps : PkgTable) (s : Section) : secOk (embedSec ps s) = secOk s := by
  rcases embedSec_eq ps s with h | ⟨n, t, d, rfl, h⟩
  · rw [h]
  · rw [h]; rfl

/-- **Embedding keeps the composition profile.** -/
theorem isProfile_embed (ps : PkgTable) (c : Ast) : isProfile (embed ps c) = isProfile c := by
  cases c with
  | mk ss => simp only [isProfile, embed, Ast.sections, List.all_map, Function.comp_def, secOk_embedSec]

theorem forM_map_embedSec {m : Type → Type} [Monad m] [LawfulMonad m] (ps : PkgTable)
    (g : Section → m Unit) (h : ∀ s, g (embedSec ps s) = g s) (ss : List Section) :
    (ss.map (embedSec ps)).forM g = ss.forM g := by
  induction ss with
  | nil => rfl
  | cons a l ih => simp [List.forM, h] at *

theorem section_embedSec (S : Nat → PkgSig) (ps : PkgTable) (s : Section) :
    Wac.Lower.section_ S (embedSec ps s) = Wac.Lower.section_ S s := by
  rcases embedSec_eq ps s with h | ⟨n, t, d, rfl, h⟩
  · rw [h]
  · rw [h]
    simp [Wac.Lower.section_, List.forM, Wac.Lower.import_]

/-- **Embedding keeps the composition graph.** -/
theorem graph_embed (S : Nat → PkgSig) (ps : PkgTable) (c : Ast) :
    Wac.Lower.graph S (embed ps c) = Wac.Lower.graph S c := by
  have hs : (embed ps c).sections.forM (Wac.Lower.section_ S) = c.sections.forM (Wac.Lower.section_ S) := by
    cases c with
    | mk ss => exact forM_map_embedSec ps _ (section_embedSec S ps) ss
  unfold Wac.Lower.graph
  rw [isProfile_embed, hs]

end Silmaril.Wasm.Wac.Embed
