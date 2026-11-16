module

public import Silmaril.Logic.Consequence.Metamath.Defs

/-! Proofs for `Silmaril.Logic.Consequence.Metamath.Thms`: rewrites preserve derivability. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Metamath

open Silmaril.Consequence Silmaril.Consequence.Metamath
open Silmaril.Logic.Institution.Metatheory (MMSig)
open Silmaril.Logic.Institution.Metatheory.Metamath (er senMap senMap_derives)

universe u

theorem derives_rewrite {X Y : MMSig.{u}} (f : X ⟶ Y) {Γ : List (Sen X)} {A : Sen X}
    (h : derives X Γ A) : derives Y (Γ.map (senMap f)) (senMap f A) := by
  refine (er Y).mono ?_ (senMap_derives f h)
  rintro _ ⟨x, hx, rfl⟩
  exact List.mem_map_of_mem hx

theorem theory_rewrite {X Y : MMSig.{u}} (f : X ⟶ Y) {T : Set (Sen X)} {T' : Set (Sen Y)}
    (hT : ∀ t ∈ T, theory Y T' [] (senMap f t))
    {Γ : List (Sen X)} {A : Sen X} (h : theory X T Γ A) :
    theory Y T' (Γ.map (senMap f)) (senMap f A) := by
  have d := senMap_derives f h
  show (er Y).Derives (T' ∪ {x | x ∈ Γ.map (senMap f)}) (senMap f A)
  refine (er Y).trans (Δ := senMap f '' (T ∪ {x | x ∈ Γ})) ?_
    ((er Y).mono Set.subset_union_right d)
  rintro _ ⟨t, ht | ht, rfl⟩
  · exact (er Y).mono (Set.union_subset_union_right _ fun _ hx => by cases hx) (hT t ht)
  · exact (er Y).mono (Set.singleton_subset_iff.2 (Or.inr (List.mem_map_of_mem ht)))
      ((er Y).refl _)

end Silmaril.Proofs.Logic.Consequence.Metamath
