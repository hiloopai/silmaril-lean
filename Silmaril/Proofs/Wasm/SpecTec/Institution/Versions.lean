module

public import Silmaril.Wasm.SpecTec.Institution.Versions.Defs
public import Silmaril.Wasm.SpecTec.Scripts.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Versions of a SpecTec specification as theories: errata that change no rule

* `relsOfDefs_replaceDefs`: splicing in a definition that declares no relation leaves the
  relation table of a script unchanged; `relsOfDefs_applyErrata` lifts this to a list of errata.
* `theoryOf_eq_of_rels`, `sigOf_rels_eq_of_rels`: the theory and the relation part of the
  signature of an environment depend only on its relation table.
* `theoryOf_applyErrata`: errata that correct no relation are identities on theories.
* The `theory-diff` rows checked in Lean: wasm-3.0 original → `binary51`, `text6x`, `fixed`, and
  wasm-2.0 original → fixed, all with nothing dropped; wasm-1.0 original → fixed, where every
  dropped or added rule is a rule of `Module_ok` (`dropped_wasm10_fixed`, from
  `dropped_applyErrata_sub`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- A definition of the same kind as a relation-free one is relation-free, and adds no `rels`. -/
theorem relsOfDef_of_relFree {d : Def} (hd : relFree d = true) (hr : isRecD d = false) :
    relsOfDef d = Map.empty := by
  cases d <;> simp_all [relFree, declKind?, relsOfDef, isRecD]

/-- The non-`recD` case of `relsOfDef_replaceDef`. -/
theorem relsOfDef_replaceDef_aux {new : Def} (hn : relFree new = true) {d : Def}
    (hd : isRecD d = false) : relsOfDef (replaceDef new d) = relsOfDef d := by
  rw [replaceDef_of_not_isRecD hd]
  by_cases hm : matchesDecl new d
  · obtain ⟨kx, hk, hk'⟩ := declKind?_of_matchesDecl hm
    have hnr : isRecD new = false := by cases new <;> simp_all [declKind?, isRecD]
    have hdf : relFree d = true := by simpa [relFree, hk, hk'] using hn
    simp only [hm, ite_true]
    rw [relsOfDef_of_relFree hn hnr, relsOfDef_of_relFree hdf hd]
  · simp [hm]

mutual

/-- **Splicing in a relation-free definition leaves the relations of a definition unchanged.** -/
theorem relsOfDef_replaceDef {new : Def} (hn : relFree new = true) :
    ∀ d : Def, relsOfDef (replaceDef new d) = relsOfDef d
  | .recD ds => by
      simp only [replaceDef, relsOfDef]
      exact relsOfDefs_replaceDefs hn ds
  | .typD .. => relsOfDef_replaceDef_aux hn rfl
  | .relD .. => relsOfDef_replaceDef_aux hn rfl
  | .decD .. => relsOfDef_replaceDef_aux hn rfl
  | .gramD .. => relsOfDef_replaceDef_aux hn rfl

/-- **Splicing in a relation-free definition leaves the relations of a script unchanged.** -/
theorem relsOfDefs_replaceDefs {new : Def} (hn : relFree new = true) :
    ∀ ds : List Def, relsOfDefs (replaceDefs new ds) = relsOfDefs ds
  | [] => rfl
  | d :: ds => by
      simp only [replaceDefs, relsOfDefs]
      rw [relsOfDef_replaceDef hn d, relsOfDefs_replaceDefs hn ds]

end

/-- **Relation-free errata leave the relation table unchanged.** -/
theorem relsOfDefs_applyErrata : ∀ {es : List Erratum} {s s' : Script}, ErrataRelFree es →
    applyErrata es s = some s' → relsOfDefs s' = relsOfDefs s
  | [], _, _, _, h => by
      simp only [applyErrata_nil, Option.some.injEq] at h
      rw [h]
  | e :: es, s, s', hes, h => by
      simp only [applyErrata_cons] at h
      cases hs : applyErratum e s with
      | none => simp [hs] at h
      | some s₁ =>
        rw [hs, Option.bind_some] at h
        have h₁ := relsOfDefs_applyErrata (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) h
        rw [h₁, (applyErratum_eq_some hs).2,
          relsOfDefs_replaceDefs (hes e (List.mem_cons_self ..)) s]

/-- The theory of an environment depends only on its relation table. -/
theorem theoryOf_eq_of_rels {env₁ env₂ : Env} (h : env₁.rels = env₂.rels) :
    theoryOf env₁ = theoryOf env₂ := by
  have hf : ∀ x, env₁.findRel? x = env₂.findRel? x := fun x => by
    simp only [Env.findRel?, h]
  ext φ
  simp only [theoryOf, Set.mem_ofPred_eq, hf]

/-- The declared relations of an environment depend only on its relation table. -/
theorem sigOf_rels_eq_of_rels {env₁ env₂ : Env} (h : env₁.rels = env₂.rels) :
    (sigOf env₁).rels = (sigOf env₂).rels := by
  have hf : ∀ x, env₁.findRel? x = env₂.findRel? x := fun x => by
    simp only [Env.findRel?, h]
  ext d
  simp only [sigOf, Set.mem_ofPred_eq, hf]

/-- **Errata that correct no relation are identities on theories**: the corrected script has the
same theory, so the identity is a theory morphism both ways and nothing is dropped. -/
theorem theoryOf_applyErrata {es : List Erratum} {s s' : Script} (hes : ErrataRelFree es)
    (h : applyErrata es s = some s') : theoryOf (envOfScript s) = theoryOf (envOfScript s') := by
  apply theoryOf_eq_of_rels
  rw [rels_envOfScript, rels_envOfScript, relsOfDefs_applyErrata hes h]

/-- `theoryOf_applyErrata`, as `dropped = ∅` in both directions. -/
theorem dropped_applyErrata {es : List Erratum} {s s' : Script} (hes : ErrataRelFree es)
    (h : applyErrata es s = some s') :
    dropped (envOfScript s) (envOfScript s') = ∅ ∧ dropped (envOfScript s') (envOfScript s) = ∅ := by
  rw [dropped, dropped, theoryOf_applyErrata hes h]
  exact ⟨Set.sdiff_self, Set.sdiff_self⟩

/-- An `ErrataRelFree` check that the kernel can run: every corrected definition is relation-free. -/
theorem errataRelFree_of_all {es : List Erratum} (h : es.all (fun e => relFree e.corrected) = true) :
    ErrataRelFree es := fun e he => List.all_eq_true.1 h e he


/-! ## Errata that correct the relations `X` only -/

/-- A definition of a relation-free kind outside `X` binds no relation outside `X`. -/
theorem find?_relsOfDef_of_relFreeExcept {X : List IL.Id} {d : Def}
    (hd : relFreeExcept X d = true) (hr : isRecD d = false) {x : IL.Id} (hx : x ∉ X) :
    (relsOfDef d).find? x = none := by
  cases d with
  | relD y ps op t rules =>
    have hy : y ∈ X := by simpa [relFreeExcept, declKind?] using hd
    have hne : y ≠ x := fun h => hx (h ▸ hy)
    simp [relsOfDef, Map.empty, hne]
  | recD _ => simp [isRecD] at hr
  | typD => rfl
  | decD => rfl
  | gramD => rfl

/-- The non-`recD` case of `find?_relsOfDef_replaceDef`. -/
theorem find?_relsOfDef_replaceDef_aux {X : List IL.Id} {new : Def}
    (hn : relFreeExcept X new = true) {d : Def} (hd : isRecD d = false) {x : IL.Id}
    (hx : x ∉ X) : (relsOfDef (replaceDef new d)).find? x = (relsOfDef d).find? x := by
  rw [replaceDef_of_not_isRecD hd]
  by_cases hm : matchesDecl new d
  · obtain ⟨kx, hk, hk'⟩ := declKind?_of_matchesDecl hm
    have hnr : isRecD new = false := by cases new <;> simp_all [declKind?, isRecD]
    have hdf : relFreeExcept X d = true := by simpa [relFreeExcept, hk, hk'] using hn
    simp only [hm, ite_true]
    rw [find?_relsOfDef_of_relFreeExcept hn hnr hx, find?_relsOfDef_of_relFreeExcept hdf hd hx]
  · simp [hm]

mutual

/-- **Splicing in a definition relation-free outside `X` keeps every relation outside `X`.** -/
theorem find?_relsOfDef_replaceDef {X : List IL.Id} {new : Def} (hn : relFreeExcept X new = true)
    {x : IL.Id} (hx : x ∉ X) :
    ∀ d : Def, (relsOfDef (replaceDef new d)).find? x = (relsOfDef d).find? x
  | .recD ds => by
      simp only [replaceDef, relsOfDef]
      exact find?_relsOfDefs_replaceDefs hn hx ds
  | .typD .. => find?_relsOfDef_replaceDef_aux hn rfl hx
  | .relD .. => find?_relsOfDef_replaceDef_aux hn rfl hx
  | .decD .. => find?_relsOfDef_replaceDef_aux hn rfl hx
  | .gramD .. => find?_relsOfDef_replaceDef_aux hn rfl hx

/-- `find?_relsOfDef_replaceDef` on a list of definitions. -/
theorem find?_relsOfDefs_replaceDefs {X : List IL.Id} {new : Def}
    (hn : relFreeExcept X new = true) {x : IL.Id} (hx : x ∉ X) :
    ∀ ds : List Def, (relsOfDefs (replaceDefs new ds)).find? x = (relsOfDefs ds).find? x
  | [] => rfl
  | d :: ds => by
      simp only [replaceDefs, relsOfDefs, Map.find?_append]
      rw [find?_relsOfDef_replaceDef hn hx d, find?_relsOfDefs_replaceDefs hn hx ds]

end

/-- **Errata relation-free outside `X` keep every relation outside `X`.** -/
theorem find?_relsOfDefs_applyErrata {X : List IL.Id} {x : IL.Id} (hx : x ∉ X) :
    ∀ {es : List Erratum} {s s' : Script}, ErrataRelFreeExcept X es →
      applyErrata es s = some s' → (relsOfDefs s').find? x = (relsOfDefs s).find? x
  | [], _, _, _, h => by
      simp only [applyErrata_nil, Option.some.injEq] at h
      rw [h]
  | e :: es, s, s', hes, h => by
      simp only [applyErrata_cons] at h
      cases hs : applyErratum e s with
      | none => simp [hs] at h
      | some s₁ =>
        rw [hs, Option.bind_some] at h
        have h₁ := find?_relsOfDefs_applyErrata hx
          (fun e' he' => hes e' (List.mem_cons_of_mem _ he')) h
        rw [h₁, (applyErratum_eq_some hs).2,
          find?_relsOfDefs_replaceDefs (hes e (List.mem_cons_self ..)) hx s]

/-- **Errata relation-free outside `X` drop only rules of `X`**: every rule of the original
theory that the corrected theory does not keep belongs to a relation named in `X`, and so does
every new rule. -/
theorem dropped_applyErrata_sub {X : List IL.Id} {es : List Erratum} {s s' : Script}
    (hes : ErrataRelFreeExcept X es) (h : applyErrata es s = some s') :
    (∀ φ ∈ dropped (envOfScript s) (envOfScript s'), ∃ d r, φ = .rule d r ∧ d.1 ∈ X) ∧
      ∀ φ ∈ dropped (envOfScript s') (envOfScript s), ∃ d r, φ = .rule d r ∧ d.1 ∈ X := by
  have hf : ∀ x, x ∉ X → (envOfScript s').findRel? x = (envOfScript s).findRel? x :=
    fun x hx => by
      simp only [Env.findRel?, rels_envOfScript]
      exact find?_relsOfDefs_applyErrata hx hes h
  constructor
  · rintro φ ⟨⟨d, rules, r, hd, hr, rfl⟩, hn⟩
    refine ⟨d, r, rfl, Classical.byContradiction fun hx => hn ?_⟩
    exact ⟨d, rules, r, (hf d.1 hx).trans hd, hr, rfl⟩
  · rintro φ ⟨⟨d, rules, r, hd, hr, rfl⟩, hn⟩
    refine ⟨d, r, rfl, Classical.byContradiction fun hx => hn ?_⟩
    exact ⟨d, rules, r, (hf d.1 hx).symm.trans hd, hr, rfl⟩

/-- An `ErrataRelFreeExcept` check that the kernel can run. -/
theorem errataRelFreeExcept_of_all {X : List IL.Id} {es : List Erratum}
    (h : es.all (fun e => relFreeExcept X e.corrected) = true) : ErrataRelFreeExcept X es :=
  fun e he => List.all_eq_true.1 h e he

/-! ## The scripts -/

namespace Versions

open Silmaril.Wasm.SpecTec.Scripts

/-- The thirteen wasm-3.0 errata correct grammars and functions only. -/
theorem relFree_wasm30 : ErrataRelFree Wasm30.fixedErrata := errataRelFree_of_all (by rfl)

/-- The binary §5.1 errata correct no relation. -/
theorem relFree_binary51 : ErrataRelFree IL.Binary51.binary51 := errataRelFree_of_all (by rfl)

/-- The text §6.x errata correct no relation. -/
theorem relFree_text6x : ErrataRelFree IL.Text6x.text6x := errataRelFree_of_all (by rfl)

/-- The four wasm-2.0 errata correct no relation. -/
theorem relFree_wasm20 : ErrataRelFree Wasm20.fixedErrata := errataRelFree_of_all (by rfl)

/-- **`theory-diff`, wasm-3.0 original → fixed: 566 / 566 retained.** The pinned and the fixed
wasm-3.0 scripts have the same theory. -/
theorem theoryOf_wasm30_fixed : theoryOf Wasm30.envOriginal = theoryOf Wasm30.envFixed :=
  theoryOf_applyErrata relFree_wasm30 applyErrata_wasm30_fixed

/-- **wasm-3.0 original → Binary51**: the same theory. -/
theorem theoryOf_wasm30_binary51 : theoryOf Wasm30.envOriginal = theoryOf Wasm30.envBinary51 := by
  have h : applyErrata IL.Binary51.binary51 Wasm30.original = some Wasm30.binary51 := by
    rw [wasm30_original_eq, wasm30_binary51_eq]
    exact IL.Binary51.applyErrata_binary51
  exact theoryOf_applyErrata relFree_binary51 h

/-- **wasm-3.0 original → Text6x**: the same theory. -/
theorem theoryOf_wasm30_text6x : theoryOf Wasm30.envOriginal = theoryOf Wasm30.envText6x := by
  have h : applyErrata IL.Text6x.text6x Wasm30.original = some Wasm30.text6x := by
    rw [wasm30_original_eq, wasm30_text6x_eq]
    exact IL.Text6x.applyErrata_text6x
  exact theoryOf_applyErrata relFree_text6x h

/-- **`theory-diff`, wasm-2.0 original → fixed: 259 / 259 retained.** -/
theorem theoryOf_wasm20_fixed : theoryOf Wasm20.envOriginal = theoryOf Wasm20.envFixed :=
  theoryOf_applyErrata relFree_wasm20 applyErrata_wasm20_fixed

/-- The eight wasm-1.0 errata correct no relation except `Module_ok` (erratum 680). -/
theorem relFreeExcept_wasm10 : ErrataRelFreeExcept ["Module_ok"] Wasm10.fixedErrata :=
  errataRelFreeExcept_of_all (by rfl)

/-- **`theory-diff`, wasm-1.0 original → fixed: partial.** Every rule dropped (or added) by the
wasm-1.0 errata is a rule of `Module_ok`. -/
theorem dropped_wasm10_fixed :
    (∀ φ ∈ dropped Wasm10.envOriginal Wasm10.envFixed, ∃ d r, φ = .rule d r ∧ d.1 = "Module_ok") ∧
      ∀ φ ∈ dropped Wasm10.envFixed Wasm10.envOriginal, ∃ d r, φ = .rule d r ∧ d.1 = "Module_ok" := by
  have h := dropped_applyErrata_sub relFreeExcept_wasm10 applyErrata_wasm10_fixed
  exact ⟨fun φ hφ => by simpa using h.1 φ hφ, fun φ hφ => by simpa using h.2 φ hφ⟩

/-- The wasm-3.0 original and fixed scripts declare the same relations. -/
theorem sigOf_rels_wasm30_fixed :
    (sigOf Wasm30.envOriginal).rels = (sigOf Wasm30.envFixed).rels := by
  apply sigOf_rels_eq_of_rels
  rw [rels_envOfScript, rels_envOfScript,
    relsOfDefs_applyErrata relFree_wasm30 applyErrata_wasm30_fixed]

end Versions

end Silmaril.Wasm.SpecTec.Institution
