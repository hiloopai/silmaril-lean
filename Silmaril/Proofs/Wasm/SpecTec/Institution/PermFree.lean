module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermSat

/-!
# Renaming identifiers: free identifiers

The free identifiers of renamed syntax are the renamed free identifiers (`freeExp_rn`, …,
`freeRule_rn`), for a permutation fixing `"_"`. So the functions a renamed rule calls are the
renamed functions it calls (`ruleFuns_rnRule`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod

variable {π : Equiv.Perm IL.Id}

/-- Rename every component of an identifier-set record. -/
def smap (π : Equiv.Perm IL.Id) (s : Sets) : Sets :=
  ⟨s.typid.map π.toEmbedding, s.relid.map π.toEmbedding, s.varid.map π.toEmbedding,
    s.defid.map π.toEmbedding, s.gramid.map π.toEmbedding⟩

theorem smap_union (s t : Sets) : smap π (s.union t) = (smap π s).union (smap π t) := by
  simp only [smap, Sets.union, Finset.map_union]

theorem smap_diff (s t : Sets) : smap π (s.diff t) = (smap π s).diff (smap π t) := by
  simp only [smap, Sets.diff, Finset.map_sdiff]

theorem smap_empty : smap π Sets.empty = Sets.empty := rfl

theorem freeVarid_rn (x : IL.Id) : freeVarid (π x) = smap π (freeVarid x) := by
  simp only [freeVarid, smap, Sets.empty, Finset.map_singleton, Finset.map_empty]
  rfl

theorem freeTypid_rn (x : IL.Id) : freeTypid (π x) = smap π (freeTypid x) := by
  simp only [freeTypid, smap, Sets.empty, Finset.map_singleton, Finset.map_empty]
  rfl

theorem freeDefid_rn (x : IL.Id) : freeDefid (π x) = smap π (freeDefid x) := by
  simp only [freeDefid, smap, Sets.empty, Finset.map_singleton, Finset.map_empty]
  rfl

theorem freeRelid_rn (x : IL.Id) : freeRelid (π x) = smap π (freeRelid x) := by
  simp only [freeRelid, smap, Sets.empty, Finset.map_singleton, Finset.map_empty]
  rfl

theorem freeGramid_rn (x : IL.Id) : freeGramid (π x) = smap π (freeGramid x) := by
  simp only [freeGramid, smap, Sets.empty, Finset.map_singleton, Finset.map_empty]
  rfl

theorem fix_iff (hπ : π "_" = "_") (x : IL.Id) : π x = "_" ↔ x = "_" :=
  ⟨fun h => π.injective (h.trans hπ.symm), fun h => h ▸ hπ⟩

theorem boundVarid_rn (hπ : π "_" = "_") (x : IL.Id) :
    boundVarid (π x) = smap π (boundVarid x) := by
  by_cases h : x = "_"
  · simp only [boundVarid, h, hπ, ite_true, smap_empty]
  · simp only [boundVarid, (fix_iff hπ x).not.mpr h, h, ite_false, freeVarid_rn]

theorem boundTypid_rn (hπ : π "_" = "_") (x : IL.Id) :
    boundTypid (π x) = smap π (boundTypid x) := by
  by_cases h : x = "_"
  · simp only [boundTypid, h, hπ, ite_true, smap_empty]
  · simp only [boundTypid, (fix_iff hπ x).not.mpr h, h, ite_false, freeTypid_rn]

theorem boundDefid_rn (hπ : π "_" = "_") (x : IL.Id) :
    boundDefid (π x) = smap π (boundDefid x) := by
  by_cases h : x = "_"
  · simp only [boundDefid, h, hπ, ite_true, smap_empty]
  · simp only [boundDefid, (fix_iff hπ x).not.mpr h, h, ite_false, freeDefid_rn]

theorem boundGramid_rn (hπ : π "_" = "_") (x : IL.Id) :
    boundGramid (π x) = smap π (boundGramid x) := by
  by_cases h : x = "_"
  · simp only [boundGramid, h, hπ, ite_true, smap_empty]
  · simp only [boundGramid, (fix_iff hπ x).not.mpr h, h, ite_false, freeGramid_rn]

theorem boundIter_rn (hπ : π "_" = "_") (it : Iter) : boundIter (rnIter π it) = smap π (boundIter it) := by
  rcases it with _ | _ | _ | ⟨e, _ | x⟩ <;>
    simp only [rnIter, rnIdOpt, boundIter, freeOpt, smap_empty, boundVarid_rn hπ]

theorem boundDoms_rn (hπ : π "_" = "_") (ds : List Dom) :
    boundDoms (rnDoms π ds) = smap π (boundDoms ds) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨x, e⟩ := d
    simp only [rnDoms, rnDom, boundDoms, boundDom, ih, boundVarid_rn hπ, smap_union]

theorem boundIterExp_rn (hπ : π "_" = "_") (it : IterExp) :
    boundIterExp (rnIterExp π it) = smap π (boundIterExp it) := by
  obtain ⟨i, ds⟩ := it
  simp only [rnIterExp, boundIterExp, boundIter_rn hπ, boundDoms_rn hπ, smap_union]

theorem boundTypBind_rn (hπ : π "_" = "_") (b : TypBind) :
    boundTypBind (rnTypBind π b) = smap π (boundTypBind b) := by
  obtain ⟨x, t⟩ := b
  exact boundVarid_rn hπ x

theorem boundTypBinds_rn (hπ : π "_" = "_") (bs : List TypBind) :
    boundTypBinds (rnTypBinds π bs) = smap π (boundTypBinds bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [rnTypBinds, boundTypBinds, ih, boundTypBind_rn hπ, smap_union]

theorem boundTyp_rn (hπ : π "_" = "_") (t : Typ) : boundTyp (rnTyp π t) = smap π (boundTyp t) := by
  cases t <;> simp only [rnTyp, boundTyp, boundTypBinds_rn hπ, smap_empty]

theorem boundParam_rn (hπ : π "_" = "_") (p : Param) :
    boundParam (rnParam π p) = smap π (boundParam p) := by
  cases p <;> simp only [rnParam, boundParam, boundVarid_rn hπ, boundTypid_rn hπ,
    boundDefid_rn hπ, boundGramid_rn hπ]

theorem boundParams_rn (hπ : π "_" = "_") (ps : List Param) :
    boundParams (rnParams π ps) = smap π (boundParams ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [rnParams, boundParams, ih, boundParam_rn hπ, smap_union]

theorem boundPrem_rn (pr : Prem) : boundPrem (rnPrem π pr) = smap π (boundPrem pr) := by
  cases pr <;> rfl

section Free

variable (hπ : π "_" = "_")
include hπ

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

mutual
theorem freeIter_rn : ∀ x : Iter, freeIter (rnIter π x) = smap π (freeIter x)
  | .opt => by simp only [rnIter, freeIter, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .list => by simp only [rnIter, freeIter, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .list1 => by simp only [rnIter, freeIter, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .listN a0 a1 => by simp only [rnIter, freeIter, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTyp_rn : ∀ x : Typ, freeTyp (rnTyp π x) = smap π (freeTyp x)
  | .varT a0 a1 => by simp only [rnTyp, freeTyp, freeArgs_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .boolT => by simp only [rnTyp, freeTyp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .numT a0 => by simp only [rnTyp, freeTyp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .textT => by simp only [rnTyp, freeTyp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .tupT a0 => by simp only [rnTyp, freeTyp, freeTypBinds_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .iterT a0 a1 => by simp only [rnTyp, freeTyp, freeTyp_rn a0, freeIter_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTypBind_rn : ∀ x : TypBind, freeTypBind (rnTypBind π x) = smap π (freeTypBind x)
  | .mk a0 a1 => by simp only [rnTypBind, freeTypBind, freeTyp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTypBinds_rn : ∀ x : List TypBind, freeTypBinds (rnTypBinds π x) = smap π (freeTypBinds x)
  | [] => by simp only [rnTypBinds, freeTypBinds, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnTypBinds, freeTypBinds, freeTypBind_rn a0, freeTypBinds_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeDefTyp_rn : ∀ x : DefTyp, freeDefTyp (rnDefTyp π x) = smap π (freeDefTyp x)
  | .aliasT a0 => by simp only [rnDefTyp, freeDefTyp, freeTyp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .structT a0 => by simp only [rnDefTyp, freeDefTyp, freeTypFields_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .variantT a0 => by simp only [rnDefTyp, freeDefTyp, freeTypCases_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTypField_rn : ∀ x : TypField, freeTypField (rnTypField π x) = smap π (freeTypField x)
  | .mk a0 a1 a2 a3 => by simp only [rnTypField, freeTypField, freeTyp_rn a1, freeParams_rn a2, freePrems_rn a3, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTypFields_rn : ∀ x : List TypField, freeTypFields (rnTypFields π x) = smap π (freeTypFields x)
  | [] => by simp only [rnTypFields, freeTypFields, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnTypFields, freeTypFields, freeTypField_rn a0, freeTypFields_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTypCase_rn : ∀ x : TypCase, freeTypCase (rnTypCase π x) = smap π (freeTypCase x)
  | .mk a0 a1 a2 a3 => by simp only [rnTypCase, freeTypCase, freeTyp_rn a1, freeParams_rn a2, freePrems_rn a3, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeTypCases_rn : ∀ x : List TypCase, freeTypCases (rnTypCases π x) = smap π (freeTypCases x)
  | [] => by simp only [rnTypCases, freeTypCases, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnTypCases, freeTypCases, freeTypCase_rn a0, freeTypCases_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeExp_rn : ∀ x : Exp, freeExp (rnExp π x) = smap π (freeExp x)
  | .varE a0 => by simp only [rnExp, freeExp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .boolE a0 => by simp only [rnExp, freeExp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .numE a0 => by simp only [rnExp, freeExp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .textE a0 => by simp only [rnExp, freeExp, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .unE a0 a1 a2 => by simp only [rnExp, freeExp, freeExp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .binE a0 a1 a2 a3 => by simp only [rnExp, freeExp, freeExp_rn a2, freeExp_rn a3, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .cmpE a0 a1 a2 a3 => by simp only [rnExp, freeExp, freeExp_rn a2, freeExp_rn a3, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .tupE a0 => by simp only [rnExp, freeExp, freeExps_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .projE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .caseE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .uncaseE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .optE a0 => by simp only [rnExp, freeExp, freeExpOpt_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .theE a0 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .strE a0 => by simp only [rnExp, freeExp, freeExpFields_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .dotE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .compE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .listE a0 => by simp only [rnExp, freeExp, freeExps_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .liftE a0 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .memE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .lenE a0 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .catE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .idxE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .sliceE a0 a1 a2 => by simp only [rnExp, freeExp, freeExp_rn a0, freeExp_rn a1, freeExp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .updE a0 a1 a2 => by simp only [rnExp, freeExp, freeExp_rn a0, freePath_rn a1, freeExp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .extE a0 a1 a2 => by simp only [rnExp, freeExp, freeExp_rn a0, freePath_rn a1, freeExp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .callE a0 a1 => by simp only [rnExp, freeExp, freeArgs_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .iterE a0 a1 => by simp only [rnExp, freeExp, freeExp_rn a0, freeIterExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .cvtE a0 a1 a2 => by simp only [rnExp, freeExp, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .subE a0 a1 a2 => by simp only [rnExp, freeExp, freeExp_rn a0, freeTyp_rn a1, freeTyp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeExpOpt_rn : ∀ x : Option Exp, freeExpOpt (rnExpOpt π x) = smap π (freeExpOpt x)
  | none => by simp only [rnExpOpt, freeExpOpt, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | some a0 => by simp only [rnExpOpt, freeExpOpt, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeExps_rn : ∀ x : List Exp, freeExps (rnExps π x) = smap π (freeExps x)
  | [] => by simp only [rnExps, freeExps, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnExps, freeExps, freeExp_rn a0, freeExps_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeExpField_rn : ∀ x : ExpField, freeExpField (rnExpField π x) = smap π (freeExpField x)
  | .mk a0 a1 => by simp only [rnExpField, freeExpField, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeExpFields_rn : ∀ x : List ExpField, freeExpFields (rnExpFields π x) = smap π (freeExpFields x)
  | [] => by simp only [rnExpFields, freeExpFields, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnExpFields, freeExpFields, freeExpField_rn a0, freeExpFields_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freePath_rn : ∀ x : Path, freePath (rnPath π x) = smap π (freePath x)
  | .rootP => by simp only [rnPath, freePath, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .idxP a0 a1 => by simp only [rnPath, freePath, freePath_rn a0, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .sliceP a0 a1 a2 => by simp only [rnPath, freePath, freePath_rn a0, freeExp_rn a1, freeExp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .dotP a0 a1 => by simp only [rnPath, freePath, freePath_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeIterExp_rn : ∀ x : IterExp, freeIterExp (rnIterExp π x) = smap π (freeIterExp x)
  | .mk a0 a1 => by simp only [rnIterExp, freeIterExp, freeIter_rn a0, freeDoms_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeDom_rn : ∀ x : Dom, freeDom (rnDom π x) = smap π (freeDom x)
  | .mk a0 a1 => by simp only [rnDom, freeDom, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeDoms_rn : ∀ x : List Dom, freeDoms (rnDoms π x) = smap π (freeDoms x)
  | [] => by simp only [rnDoms, freeDoms, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnDoms, freeDoms, freeDom_rn a0, freeDoms_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeSym_rn : ∀ x : Sym, freeSym (rnSym π x) = smap π (freeSym x)
  | .varG a0 a1 => by simp only [rnSym, freeSym, freeArgs_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .numG a0 => by simp only [rnSym, freeSym, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .textG a0 => by simp only [rnSym, freeSym, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .epsG => by simp only [rnSym, freeSym, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .seqG a0 => by simp only [rnSym, freeSym, freeSyms_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .altG a0 => by simp only [rnSym, freeSym, freeSyms_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .rangeG a0 a1 => by simp only [rnSym, freeSym, freeSym_rn a0, freeSym_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .iterG a0 a1 => by simp only [rnSym, freeSym, freeSym_rn a0, freeIterExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .attrG a0 a1 => by simp only [rnSym, freeSym, freeExp_rn a0, freeSym_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeSyms_rn : ∀ x : List Sym, freeSyms (rnSyms π x) = smap π (freeSyms x)
  | [] => by simp only [rnSyms, freeSyms, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnSyms, freeSyms, freeSym_rn a0, freeSyms_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeArg_rn : ∀ x : Arg, freeArg (rnArg π x) = smap π (freeArg x)
  | .expA a0 => by simp only [rnArg, freeArg, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .typA a0 => by simp only [rnArg, freeArg, freeTyp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .defA a0 => by simp only [rnArg, freeArg, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .gramA a0 => by simp only [rnArg, freeArg, freeSym_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeArgs_rn : ∀ x : List Arg, freeArgs (rnArgs π x) = smap π (freeArgs x)
  | [] => by simp only [rnArgs, freeArgs, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnArgs, freeArgs, freeArg_rn a0, freeArgs_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeParam_rn : ∀ x : Param, freeParam (rnParam π x) = smap π (freeParam x)
  | .expP a0 a1 => by simp only [rnParam, freeParam, freeTyp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .typP a0 => by simp only [rnParam, freeParam, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .defP a0 a1 a2 => by simp only [rnParam, freeParam, freeParams_rn a1, freeTyp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .gramP a0 a1 a2 => by simp only [rnParam, freeParam, freeParams_rn a1, freeTyp_rn a2, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freeParams_rn : ∀ x : List Param, freeParams (rnParams π x) = smap π (freeParams x)
  | [] => by simp only [rnParams, freeParams, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnParams, freeParams, freeParam_rn a0, freeParams_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freePrem_rn : ∀ x : Prem, freePrem (rnPrem π x) = smap π (freePrem x)
  | .rulePr a0 a1 a2 a3 => by simp only [rnPrem, freePrem, freeArgs_rn a1, freeExp_rn a3, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .ifPr a0 => by simp only [rnPrem, freePrem, freeExp_rn a0, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .letPr a0 a1 => by simp only [rnPrem, freePrem, freeExp_rn a0, freeExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .elsePr => by simp only [rnPrem, freePrem, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | .iterPr a0 a1 => by simp only [rnPrem, freePrem, freePrem_rn a0, freeIterExp_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

theorem freePrems_rn : ∀ x : List Prem, freePrems (rnPrems π x) = smap π (freePrems x)
  | [] => by simp only [rnPrems, freePrems, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]
  | a0 :: a1 => by simp only [rnPrems, freePrems, freePrem_rn a0, freePrems_rn a1, smap_union, smap_diff, smap_empty, boundIter_rn hπ, boundIterExp_rn hπ, boundTypBind_rn hπ, boundTyp_rn hπ, boundParam_rn hπ, boundParams_rn hπ, boundPrem_rn, freeVarid_rn, freeTypid_rn, freeDefid_rn, freeRelid_rn, freeGramid_rn]

end


end Free

theorem freeRule_rn (hπ : π "_" = "_") (r : Rule) : freeRule (rnRule π r) = smap π (freeRule r) := by
  obtain ⟨nm, qs, op, e, prems⟩ := r
  simp only [rnRule, freeRule, freeParams_rn hπ, freeExp_rn hπ, freePrems_rn hπ,
    boundParams_rn hπ, smap_union, smap_diff]

/-- **The functions a renamed rule calls are the renamed functions it calls.** -/
theorem ruleFuns_rnRule (hπ : π "_" = "_") (r : Rule) :
    ruleFuns (rnRule π r) = (ruleFuns r).map π.toEmbedding := by
  simp only [ruleFuns, freeRule_rn hπ, smap]

end Silmaril.Wasm.SpecTec.Institution.Perm
