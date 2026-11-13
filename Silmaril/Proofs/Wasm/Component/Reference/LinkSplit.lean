module

public import Silmaril.Proofs.Wasm.Component.Reference.SplitBack

/-!
# Both parts of a `Linked2` in the shared core store

The exporter's part (its store `π`) and the importer's relocated part (`κ = reloc s₀ u`) embed
disjointly into the shared core store `σ`: `Linking.Split.Rel4` (provider = exporter, consumer
= importer). A shared run of one part, mapped back (`reach_link_back`), grows that part's
renaming and ownership (`Grow`) and touches the shared store only at what that part owns
(`Touch`); the relation then holds again with the other part unchanged:

* `Rel4.after_c`: after a run of the importer;
* `Rel4.after_p`: after a run of the exporter;
* `rel4_init`: right after instantiation, `σ = reloc s₀ u` with the identity renamings
  (`partRel_prefix`, `partRel_reloc`, `shOwn_ownOf_disjoint`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch Rel4)

variable {H : Type} {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own} {σ π κ : Store H}

/-- **The importer moved the shared world**: the exporter's relation survives, the images stay
disjoint. -/
theorem Rel4.after_c {ρc' : Ren} {Oc' : Own} {σ' κ' : Store H}
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc σ π κ) (hrc : PartRel ρc' Oc' κ' σ')
    (hg : Grow ρc Oc ρc' Oc' σ) (ht : Touch ρc Oc σ σ') :
    Rel4 Op₀ Oc₀ ρp Op ρc' Oc' σ' π κ' := by
  refine ⟨?_, hrc, hR.fnp, hR.glp, hg.fn.trans hR.fnc, hg.gl.trans hR.glc, ?_, ?_, ?_⟩
  · exact hR.rp.touch ht (fun a ha => hR.gl a ha) (fun a b ha hb e => hR.st a b ha hb e.symm)
      (fun a b ha hb e => hR.ar a b ha hb e.symm)
  · intro a ha
    rw [hg.gl]
    exact hR.gl a ha
  · intro a b ha hb e
    rcases hg.stNew b hb with hb' | hb'
    · exact hR.st a b ha hb' (e.trans (hg.st b hb').2)
    · have := (hR.rp.st_lt ha).2
      omega
  · intro a b ha hb e
    rcases hg.arNew b hb with hb' | hb'
    · exact hR.ar a b ha hb' (e.trans (hg.ar b hb').2)
    · have := (hR.rp.ar_lt ha).2
      omega

/-- **The exporter moved the shared world**: the importer's relation survives, the images stay
disjoint. -/
theorem Rel4.after_p {ρp' : Ren} {Op' : Own} {σ' π' : Store H}
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc σ π κ) (hrp : PartRel ρp' Op' π' σ')
    (hg : Grow ρp Op ρp' Op' σ) (ht : Touch ρp Op σ σ') :
    Rel4 Op₀ Oc₀ ρp' Op' ρc Oc σ' π' κ := by
  refine ⟨hrp, ?_, hg.fn.trans hR.fnp, hg.gl.trans hR.glp, hR.fnc, hR.glc, ?_, ?_, ?_⟩
  · exact hR.rc.touch ht (fun a ha hp => hR.gl a hp ha) (fun a b ha hb e => hR.st b a hb ha e)
      (fun a b ha hb e => hR.ar b a hb ha e)
  · intro a ha
    rw [hg.gl] at ha
    exact hR.gl a ha
  · intro a b ha hb e
    rcases hg.stNew a ha with ha' | ha'
    · exact hR.st a b ha' hb ((hg.st a ha').2.symm.trans e)
    · have := (hR.rc.st_lt hb).2
      omega
  · intro a b ha hb e
    rcases hg.arNew a ha with ha' | ha'
    · exact hR.ar a b ha' hb ((hg.ar a ha').2.symm.trans e)
    · have := (hR.rc.ar_lt hb).2
      omega

/-- **The initial relation of the two parts**: right after instantiation, the shared store is
the exporter's store `s₀` followed by the importer's `u`, relocated, both related by the identity
renamings for the ownership of everything in them. -/
theorem rel4_init {s₀ u : Store H} (hg₀ : StoreGood s₀) (hgu : StoreGood u) :
    Rel4 (ownOf s₀) (shOwn (sh s₀) (ownOf u)) Ren.id (ownOf s₀) Ren.id
      (shOwn (sh s₀) (ownOf u)) (reloc s₀ u) s₀ (reloc s₀ u) := by
  obtain ⟨hst, har, -, hgl⟩ := shOwn_ownOf_disjoint s₀ u
  exact ⟨partRel_prefix s₀ hg₀ u, partRel_reloc s₀ hgu, rfl, rfl, rfl, rfl, hgl,
    fun a b ha hb e => hst a ha (by have e' : a = b := e; exact e' ▸ hb), fun a b ha hb e =>
      har a ha (by have e' : a = b := e; exact e' ▸ hb)⟩

end Silmaril.Proofs.Wasm.Component.Reference
