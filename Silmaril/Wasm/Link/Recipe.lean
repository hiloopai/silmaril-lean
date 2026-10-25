module

public import Silmaril.Wasm.Link.GC

/-! # Witnesses from the actual partial GC linker

Successful assembly exposes the validators, resolved imports and each source
rewrite used to build its output. These are algorithm witnesses, rather than
assumptions about execution preservation. They retain source-definition order
and permit lookup of the exact rewritten function or global at its linked index.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC

open Silmaril.Wasm.Validation

namespace Recipe

/-- The actual consumer relocation, including resolved provider exports. -/
def relocation (provider : Module) (imports : List FuncIdx) : Relocation :=
  ⟨provider.typeDefinitions.length, provider.funcs.length, provider.globals.length, imports⟩

def identity : Relocation := ⟨0, 0, 0, []⟩

/-- Data and successful checks retained from one execution of `assemble?`. -/
structure Assembly (namespaceName : String) (provider consumer result : Module) where
  providerType : CModuleType
  consumerType : CModuleType
  imports : List FuncIdx
  types : List RecType
  funcs : List Func
  globals : List Global
  exports : List Export
  providerFuncs : List Func
  providerGlobals : List Global
  providerProfile : inProfile provider = true
  consumerProfile : inProfile consumer = true
  providerImports : provider.imports = []
  providerValidation : validate? provider = some providerType
  consumerValidation : validate? consumer = some consumerType
  typeBound : provider.typeDefinitions.length + consumer.typeDefinitions.length < 2^32
  functionBound : provider.funcs.length + consumer.funcs.length < 2^32
  globalBound : provider.globals.length + consumer.globals.length < 2^32
  resolved : resolveImports? namespaceName provider consumer providerType consumerType = some imports
  typesRewrite : consumer.types.mapM (recType? (relocation provider imports).types) = some types
  funcsRewrite : consumer.funcs.mapM (func? (relocation provider imports)) = some funcs
  globalsRewrite : consumer.globals.mapM (global? (relocation provider imports)) = some globals
  exportsRewrite : consumer.exports.mapM (export? (relocation provider imports)) = some exports
  providerFuncsRewrite : provider.funcs.mapM (func? identity) = some providerFuncs
  providerGlobalsRewrite : provider.globals.mapM (global? identity) = some providerGlobals
  output : result = {
    types := provider.types ++ types
    funcs := providerFuncs ++ funcs
    globals := providerGlobals ++ globals
    exports := provider.exports ++ exports }

private theorem mapM_length {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length :=
  (List.mapM_some_forall₂ (R := fun a b => f a = some b) (fun h => h) h).length_eq.symm

/-- A valid module type has one import type for every source import. -/
theorem validation_imports_length {m : Module} {mt : CModuleType}
    (h : validate? m = some mt) : mt.imports.length = m.imports.length := by
  cases validate?_sound h with
  | mk _ hi => exact hi.length_eq.symm

theorem Assembly.imports_length {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) :
    w.imports.length = consumer.imports.length := by
  have h := mapM_length w.resolved
  rw [List.length_zip, validation_imports_length w.consumerValidation, Nat.min_self] at h
  exact h

theorem Assembly.funcs_length {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) :
    w.funcs.length = consumer.funcs.length := mapM_length w.funcsRewrite

theorem Assembly.globals_length {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) :
    w.globals.length = consumer.globals.length := mapM_length w.globalsRewrite

theorem Assembly.providerFuncs_length {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) :
    w.providerFuncs.length = provider.funcs.length := mapM_length w.providerFuncsRewrite

theorem Assembly.providerGlobals_length {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) :
    w.providerGlobals.length = provider.globals.length := mapM_length w.providerGlobalsRewrite

private theorem mapM_lookup {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β} {i : Nat} {a : α},
      xs.mapM f = some ys → xs[i]? = some a →
      ∃ b, ys[i]? = some b ∧ f a = some b
  | [], _, _, _, h, ha => by simp at ha
  | _ :: _, _, 0, _, h, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, _, rfl⟩ := h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    exact ⟨b, rfl, hb⟩
  | _ :: _, _, i+1, _, h, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, _, bs, hbs, rfl⟩ := h
    simpa only [List.getElem?_cons_succ] using mapM_lookup hbs ha

/-- Every resolved source import names an actual provider export with a checked subtype of
the requested closed function type. The actual type remains explicit. The index comes from that export. -/
theorem Assembly.import_lookup {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result)
    {i : Nat} {entry : Import} {expected : DefType}
    (hi : consumer.imports[i]? = some entry)
    (ht : w.consumerType.imports[i]? = some (.func expected)) :
    ∃ f sourceType exported actual,
      w.imports[i]? = some f ∧ entry.moduleName = namespaceName ∧
      entry.type = .func sourceType ∧
      (provider.exports.zip w.providerType.exports).find?
        (fun (e, _) => e.name == entry.name) = some (exported, .func actual) ∧
      exported.index = .func f ∧ Sub {} actual expected := by
  have hz : (consumer.imports.zip w.consumerType.imports)[i]? = some (entry, .func expected) :=
    List.getElem?_zip_eq_some.mpr ⟨hi, ht⟩
  obtain ⟨f, hf, hr⟩ := mapM_lookup w.resolved hz
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i hn
    have hn' : entry.moduleName = namespaceName := by simpa using hn
    cases he : entry.type <;> simp only [he] at hr
    all_goals try contradiction
    rename_i sourceType
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨exported, actualType⟩, hfind, hr⟩ := hr
    cases hx : exported.index <;> simp only [hx] at hr
    all_goals try contradiction
    rename_i fi
    cases hd : actualType <;> simp only [hd] at hr
    all_goals try contradiction
    rename_i actual
    split at hr
    · rename_i heq
      cases hr
      exact ⟨f, sourceType, exported, expected, hf, hn', rfl,
        by simpa [hd, heq] using hfind, hx, Sub.refl _ (k := .def) trivial _⟩
    · split at hr
      · rename_i subtype
        cases hr
        exact ⟨f, sourceType, exported, actual, hf, hn', rfl,
          by simpa only [hd] using hfind, hx, Sub.check_sound subtype⟩
      · cases hr

/-- Every resolved source import names an actual provider export with exactly
the requested closed function type. The index comes from that export. -/
theorem Assembly.import_lookup_exact {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result)
    (exactMatch : resolveImportsExact? namespaceName provider consumer
      w.providerType w.consumerType = some w.imports)
    {i : Nat} {entry : Import} {expected : DefType}
    (hi : consumer.imports[i]? = some entry)
    (ht : w.consumerType.imports[i]? = some (.func expected)) :
    ∃ f sourceType exported,
      w.imports[i]? = some f ∧ entry.moduleName = namespaceName ∧
      entry.type = .func sourceType ∧
      (provider.exports.zip w.providerType.exports).find?
        (fun (e, _) => e.name == entry.name) = some (exported, .func expected) ∧
      exported.index = .func f := by
  have hz : (consumer.imports.zip w.consumerType.imports)[i]? = some (entry, .func expected) :=
    List.getElem?_zip_eq_some.mpr ⟨hi, ht⟩
  obtain ⟨f, hf, hr⟩ := mapM_lookup exactMatch hz
  dsimp only at hr
  split at hr
  · cases hr
  · rename_i hn
    have hn' : entry.moduleName = namespaceName := by simpa using hn
    cases he : entry.type <;> simp only [he] at hr
    all_goals try contradiction
    rename_i sourceType
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨exported, actualType⟩, hfind, hr⟩ := hr
    cases hx : exported.index <;> simp only [hx] at hr
    all_goals try contradiction
    rename_i fi
    cases hd : actualType <;> simp only [hd] at hr
    all_goals try contradiction
    rename_i actual
    split at hr
    · rename_i heq
      cases hr
      exact ⟨f, sourceType, exported, hf, hn', rfl, by simpa [hd, heq] using hfind, hx⟩
    · cases hr

/-- Source consumer definitions occupy the suffix after provider definitions. -/
theorem Assembly.consumer_func_lookup {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) {i : Nat} {f : Func}
    (hf : consumer.funcs[i]? = some f) :
    ∃ f', result.funcs[provider.funcs.length + i]? = some f' ∧
      func? (relocation provider w.imports) f = some f' := by
  obtain ⟨f', hf', hr⟩ := mapM_lookup w.funcsRewrite hf
  refine ⟨f', ?_, hr⟩
  rw [w.output, List.getElem?_append_right (by rw [w.providerFuncs_length]; omega)]
  simpa [w.providerFuncs_length] using hf'

theorem Assembly.provider_func_lookup {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) {i : Nat} {f : Func}
    (hf : provider.funcs[i]? = some f) :
    ∃ f', result.funcs[i]? = some f' ∧ func? identity f = some f' := by
  obtain ⟨f', hf', hr⟩ := mapM_lookup w.providerFuncsRewrite hf
  refine ⟨f', ?_, hr⟩
  rw [w.output, List.getElem?_append_left (by
    rw [w.providerFuncs_length]
    exact (List.getElem?_eq_some_iff.mp hf).1)]
  exact hf'

theorem Assembly.consumer_global_lookup {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) {i : Nat} {g : Global}
    (hg : consumer.globals[i]? = some g) :
    ∃ g', result.globals[provider.globals.length + i]? = some g' ∧
      global? (relocation provider w.imports) g = some g' := by
  obtain ⟨g', hg', hr⟩ := mapM_lookup w.globalsRewrite hg
  refine ⟨g', ?_, hr⟩
  rw [w.output, List.getElem?_append_right (by rw [w.providerGlobals_length]; omega)]
  simpa [w.providerGlobals_length] using hg'

theorem Assembly.provider_global_lookup {namespaceName provider consumer result}
    (w : Assembly namespaceName provider consumer result) {i : Nat} {g : Global}
    (hg : provider.globals[i]? = some g) :
    ∃ g', result.globals[i]? = some g' ∧ global? identity g = some g' := by
  obtain ⟨g', hg', hr⟩ := mapM_lookup w.providerGlobalsRewrite hg
  refine ⟨g', ?_, hr⟩
  rw [w.output, List.getElem?_append_left (by
    rw [w.providerGlobals_length]
    exact (List.getElem?_eq_some_iff.mp hg).1)]
  exact hg'

end Recipe

theorem assemble?_recipe {namespaceName : String} {provider consumer result : Module}
    (h : assemble? namespaceName provider consumer = some result) :
    Nonempty (Recipe.Assembly namespaceName provider consumer result) := by
  unfold assemble? at h
  split at h
  · cases h
  · rename_i hp
    have hp' : inProfile provider = true ∧ inProfile consumer = true ∧
        provider.imports = [] := by simpa [and_assoc] using hp
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨pt, hpt, ct, hct, h⟩ := h
    split at h
    · cases h
    · rename_i hb
      have hb' : provider.typeDefinitions.length + consumer.typeDefinitions.length < 2^32 ∧
          provider.funcs.length + consumer.funcs.length < 2^32 ∧
          provider.globals.length + consumer.globals.length < 2^32 := by
        simpa [not_or, and_assoc] using hb
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨imports, hi, types, ht, funcs, hf, globals, hg, exports, he,
        pfuncs, hpf, pglobals, hpg, rfl⟩ := h
      exact ⟨⟨pt, ct, imports, types, funcs, globals, exports, pfuncs, pglobals,
        hp'.1, hp'.2.1, hp'.2.2, hpt, hct, hb'.1, hb'.2.1, hb'.2.2,
        hi, ht, hf, hg, he, hpf, hpg, rfl⟩⟩

/-- Extract the assembly recipe from the validated two-input linker itself. -/
theorem link?_recipe {namespaceName : String} {provider consumer result : Module}
    (h : link? namespaceName provider consumer = some result) :
    Nonempty (Recipe.Assembly namespaceName provider consumer result) := by
  obtain ⟨assembled, ha, hv⟩ := Option.bind_eq_some_iff.mp h
  have he : assembled = result := by
    unfold validated? at hv
    split at hv
    · exact Option.some.inj hv
    · cases hv
  subst result
  exact assemble?_recipe ha

end Silmaril.Wasm.Link.GC
