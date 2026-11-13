module

public import Silmaril.Wasi.Versions.WitImport.KErase.Pkg.Thms
public import Silmaril.Wasi.Versions.WitImport.KSplit.Thms

@[expose] public section

/-!
# Doc comments cannot change an imported table

`Elab.elaborate_erase`: elaborating the universe with every doc comment erased gives the
elaboration of the universe, erased. The importer only merges and filters packages by name
(`kUniv_erase`), so on files whose parses agree up to doc comments it gives the same package
up to doc comments (`importKD_erase`), and the signature tables, the resource drops and the
resolved packages read no doc comments (`table_erase`, `drops_erase`, `rtable_erase`,
`envOf_erase`).

Hence `kTable_of_erase`, `kDrops_of_erase`, `kRPkg_of_erase`: when each vendored text with its
doc comments parses, up to doc comments, as the text without them (`(parseCharsK full).map
Document.erase = parseCharsK cs`, checked per file in the kernel), the kernel importer on the
vendored texts gives the tables and resolved packages of the importer on the texts without doc
comments. This removes the assumption of `Silmaril.Wasi.Versions.WitImport.KTokens` that dropping
doc-comment tokens does not change a table: the statements are about the importer on the full
texts, doc-comment tokens parsed.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Wit.Elab

theorem lookupPkg_erase (U : Universe) (p : PackageName) :
    lookupPkg U.erase p = (lookupPkg U p).map Package.erase := by
  unfold lookupPkg
  rw [Universe.pkg?_erase]
  cases U.pkg? p <;> rfl

theorem filter_env_erase (env : Binary.Env) (p : PackageName) :
    env.erase.filter (fun x => x.1.pkg != pkgName p) =
      Binary.Env.erase (env.filter (fun x => x.1.pkg != pkgName p)) := by
  simp [Binary.Env.erase, List.filter_map, Function.comp_def]

/-- **Doc comments do not reach elaboration**: the erased universe elaborates to the erased
package and dependencies. -/
theorem elaborate_erase (U : Universe) (p : PackageName) (fs : List Name) :
    elaborate U.erase p fs = (elaborate U p fs).map fun r => (r.1.erase, r.2.erase) := by
  unfold elaborate
  simp only [Universe.gate_erase, check_erase]
  cases check (Universe.gate fs U) with
  | false => rfl
  | true =>
    simp only [require, ↓reduceIte, pure_bind, lookupPkg_erase]
    refine except_bind_map _ _ _ _ _ (fun P => ?_)
    rw [elabEnv_erase]
    refine except_bind_map _ _ _ _ _ (fun env => ?_)
    rw [elabPackage_erase]
    refine except_bind_map _ _ _ _ _ (fun out => ?_)
    rw [filter_env_erase, Package.validB_erase, Package.namesUniqueB_erase]
    cases Package.validB out (env.filter (fun x => x.1.pkg != pkgName p)) <;>
      cases Package.namesUniqueB out <;> rfl

end Silmaril.Wasm.Wit.Elab

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-! ## Merging and selecting packages -/

theorem pkgNames_erase (ps : List Package) : pkgNames (ps.map Package.erase) = pkgNames ps := by
  unfold pkgNames
  rw [List.foldl_map]
  rfl

theorem mergeDocs_erase (ds : List Document) :
    mergeDocs (ds.map Document.erase) = Universe.erase (mergeDocs ds) := by
  have hps : (ds.map Document.erase).flatMap Document.packages =
      (ds.flatMap Document.packages).map Package.erase := by
    simp [List.flatMap_map, List.map_flatMap, Document.packages, Document.erase]
  unfold mergeDocs
  simp only [hps, pkgNames_erase, Universe.erase, List.map_map]
  congr 1
  funext n
  simp only [Function.comp_apply, List.filter_map, Function.comp_def, Package.erase_name]
  cases (ds.flatMap Document.packages).filter (·.name == n) <;>
    simp [Package.erase, List.flatMap_map, List.map_flatMap]

theorem dropWorlds_erase (P : Package) : dropWorlds P.erase = (dropWorlds P).erase := by
  have hw : ∀ it : PackageItem, notWorld it.erase = notWorld it := fun it => by cases it <;> rfl
  simp [dropWorlds, Package.erase, List.filter_map, Function.comp_def, hw]

theorem kUniv_erase (sel : Bool) (ds : List Document) :
    kUniv sel (ds.map Document.erase) = (kUniv sel ds).erase := by
  cases sel with
  | false => exact mergeDocs_erase ds
  | true =>
    show List.map dropWorlds (mergeDocs (ds.map Document.erase)) =
      Universe.erase (List.map dropWorlds (mergeDocs ds))
    rw [mergeDocs_erase]
    simp [Universe.erase, List.map_map, Function.comp_def, dropWorlds_erase]

/-! ## The importer -/

theorem parseStep_erase {cs full : List Char}
    (h : (parseCharsK full).map Document.erase = parseCharsK cs) :
    parseStep cs = (parseStep full).map Document.erase := by
  unfold parseStep
  rw [← h]
  cases parseCharsK full <;> rfl

theorem mapM_parseStep_erase {srcs fulls : List (List Char)}
    (h : List.Forall₂ (fun cs full => (parseCharsK full).map Document.erase = parseCharsK cs) srcs fulls) :
    srcs.mapM parseStep = (fulls.mapM parseStep).map (List.map Document.erase) := by
  induction h with
  | nil => rfl
  | @cons cs full l₁ l₂ hx _ ih =>
    rw [List.mapM_cons, List.mapM_cons, parseStep_erase hx, ih]
    cases parseStep full <;> cases l₂.mapM parseStep <;> rfl

/-- The importer on texts whose parses agree up to doc comments gives the same package and
dependencies up to doc comments. -/
theorem importKD_erase {sel : Bool} {srcs fulls : List (List Char)}
    (h : List.Forall₂ (fun cs full => (parseCharsK full).map Document.erase = parseCharsK cs) srcs fulls) :
    importKD sel srcs = (importKD sel fulls).map fun r => (r.1.erase, Binary.Env.erase r.2) := by
  unfold importKD
  rw [mapM_parseStep_erase h]
  refine Elab.except_bind_map _ _ _ _ _ (fun ds => ?_)
  simp only [kUniv_erase]
  cases kUniv sel ds with
  | nil => rfl
  | cons P U =>
    show Elab.elaborate (Universe.erase (P :: U)) P.erase.name [] = _
    rw [Package.erase_name, Elab.elaborate_erase]
    rfl

/-! ## The outputs read no doc comments -/

theorem table_erase (ver : Bool) (P : Binary.Package) : table ver P.erase = table ver P := by
  have hf : ∀ f : Binary.Func, plainName f.erase = plainName f := fun _ => rfl
  have hs : ∀ f : Binary.Func, f.erase.sig = f.sig := fun _ => rfl
  simp only [table, Binary.Package.erase, List.flatMap_map, Function.comp_def, Binary.Interface.erase,
    List.map_map, hf, hs]

theorem drops_erase (ver : Bool) (P : Binary.Package) : drops ver P.erase = drops ver P := by
  unfold drops
  simp only [Binary.Package.erase, List.flatMap_map, Binary.Interface.erase, List.filterMap_map]
  congr 1
  funext x
  congr 1
  funext td
  rcases td with ⟨n, k, ds, st⟩
  cases k <;> rfl

theorem rtable_erase (ver : Bool) (P : Binary.Package) : rtable ver P.erase = rtable ver P := by
  have hf : ∀ f : Binary.Func, plainName f.erase = plainName f := fun _ => rfl
  have hs : ∀ f : Binary.Func, f.erase.sig = f.sig := fun _ => rfl
  simp only [rtable, Binary.Package.erase, List.flatMap_map, Function.comp_def, Binary.Interface.erase,
    List.map_map, hf, hs]

theorem plainKind_erase (k : Binary.TyDefKind) : plainKind k.erase = plainKind k := by
  cases k <;> simp [plainKind, Binary.TyDefKind.erase, plainLabel, Binary.Labeled.erase]

theorem typesOf_erase (b : Binary.Interface) : typesOf b.erase = typesOf b := by
  simp [typesOf, Binary.Interface.erase, Binary.TypeDef.erase, Function.comp_def, plainKind_erase]

theorem envOf_erase (P : Binary.Package) (deps : Binary.Env) :
    envOf P.erase (Binary.Env.erase deps) = envOf P deps := by
  simp [envOf, Binary.Package.erase, Binary.Env.erase, Function.comp_def, typesOf_erase]

/-! ## Transfer to the vendored texts with their doc comments -/

/-- The importer on the full texts, from the importer on the texts without doc comments. -/
theorem importKD_full_of {sel : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env}
    (h : List.Forall₂ (fun cs full => (parseCharsK full).map Document.erase = parseCharsK cs) srcs fulls)
    (hk : importKD sel srcs = .ok (B, deps)) :
    ∃ B' deps', importKD sel fulls = .ok (B', deps') ∧ B'.erase = B ∧ Binary.Env.erase deps' = deps := by
  have he : (importKD sel fulls).map (fun r => (r.1.erase, Binary.Env.erase r.2)) = .ok (B, deps) :=
    (importKD_erase h).symm.trans hk
  cases hf : importKD sel fulls with
  | error e => rw [hf] at he; cases he
  | ok r =>
    rw [hf] at he
    cases he
    exact ⟨r.1, r.2, rfl, rfl, rfl⟩

/-- **Tables on the vendored texts, doc comments parsed.** -/
theorem kTable_of_erase {ver sel : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env}
    (h : List.Forall₂ (fun cs full => (parseCharsK full).map Document.erase = parseCharsK cs) srcs fulls)
    (hk : importKD sel srcs = .ok (B, deps)) : kTable ver sel fulls = some (table ver B) := by
  obtain ⟨B', deps', hf, hB, -⟩ := importKD_full_of h hk
  rw [kTable_of hf, ← hB, table_erase]

/-- **Drops on the vendored texts, doc comments parsed.** -/
theorem kDrops_of_erase {ver : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env}
    (h : List.Forall₂ (fun cs full => (parseCharsK full).map Document.erase = parseCharsK cs) srcs fulls)
    (hk : importKD false srcs = .ok (B, deps)) : kDrops ver fulls = some (drops ver B) := by
  obtain ⟨B', deps', hf, hB, -⟩ := importKD_full_of h hk
  rw [kDrops_of hf, ← hB, drops_erase]

/-- **Resolved packages on the vendored texts, doc comments parsed.** -/
theorem kRPkg_of_erase {ver sel : Bool} {srcs fulls : List (List Char)} {B : Binary.Package}
    {deps : Binary.Env}
    (h : List.Forall₂ (fun cs full => (parseCharsK full).map Document.erase = parseCharsK cs) srcs fulls)
    (hk : importKD sel srcs = .ok (B, deps)) :
    kRPkg ver sel fulls = some (rtable ver B, envOf B deps) := by
  obtain ⟨B', deps', hf, hB, hd⟩ := importKD_full_of h hk
  rw [kRPkg_of hf, ← hB, ← hd, rtable_erase, envOf_erase]

end Silmaril.Wasi.Versions.WitImport
