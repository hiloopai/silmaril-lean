module

public import Silmaril.Wasm.Wac.Bridge.Encode.Defs

/-!
# WAC bridge: the encoding lands in the composition profile

`encode_profile`: whatever `encode` returns is a component in the composition profile
(`Silmaril.Wasm.Wac.Profile`). No hypothesis is needed: every item is one section of a
kind the profile allows, instantiations keep the first argument of each name
(`firstArgs_nodup`), and aliases are instance exports.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary

/-- `firstArgs` keeps one argument per name. -/
theorem firstArgs_nodup (as : List (String × SortIdx)) : ((firstArgs as).map Prod.fst).Nodup := by
  induction as with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    have hf : (((firstArgs as).filter fun b => b.1 != a.1).map Prod.fst).Nodup :=
      ih.sublist ((List.filter_sublist).map Prod.fst)
    have hn : a.1 ∉ ((firstArgs as).filter fun b => b.1 != a.1).map Prod.fst := by
      intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have hne : (b.1 != a.1) = true := (List.mem_filter.mp hb).2
      exact absurd he (by simpa using hne)
    exact List.nodup_cons.mpr ⟨hn, hf⟩

/-- Every item is a section of the profile. -/
theorem secOk_toSection (it : Item) : secOk it.toSection = true := by
  cases it with
  | inst c as =>
    have h := firstArgs_nodup as
    simp only [Item.toSection, secOk, List.all_cons, List.all_nil, Bool.and_true, instOk,
      decide_eq_true_eq]
    exact h
  | _ => rfl

/-- **The encoding is in the composition profile.** -/
theorem encode_profile {nom : NomTable} {g : CGraph} {c : Ast} (h : encode nom g = .ok c) :
    Profile c := by
  unfold encode at h
  cases he : encodeItems nom g with
  | error e => rw [he] at h; cases h
  | ok its =>
    rw [he] at h
    have hc : c = .mk (its.map Item.toSection) := by cases h; rfl
    rw [hc]
    show (its.map Item.toSection).all secOk = true
    exact List.all_eq_true.mpr fun s hs => by
      obtain ⟨it, _, rfl⟩ := List.mem_map.mp hs
      exact secOk_toSection it

end Silmaril.Wasm.Wac.Bridge
