module

public import Silmaril.Wasm.Verify.Check.Defs

/-!
# The computed instance of a module is its instance

`isInstance_of_instance?`: when `instance? m = some (mt, I)`, `IsInstance m mt I`. This makes
the soundness theorem of the verifier non-vacuous on concrete modules: the instance is computed
by kernel evaluation.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

theorem forall₂_of_mapM {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → List.Forall₂ (fun a b => g a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM hbs)

theorem isFuncImport_all {l : List CExternType} (h : l.all isFuncImport = true) :
    ∀ xt ∈ l, ∃ d, xt = .func d := by
  intro xt hxt
  have hx := List.all_eq_true.1 h xt hxt
  cases xt with
  | func d => exact ⟨d, rfl⟩
  | _ => cases hx

theorem instFrom_inv {mt mt' : CModuleType} {imps : List FnType} {s : Store Nat} {f : Frame}
    {I : ScalarInstance} (h : instFrom mt imps s f = some (mt', I)) :
    mt' = mt ∧ ∃ exps, (exportFuncAddrs f.module).mapM
      (fun a => s.funcs[a]?.bind fun fi => FnType.ofDefType? fi.type) = some exps ∧
      I = ⟨imps, exps, exportFuncAddrs f.module, s⟩ := by
  obtain ⟨exps, hexps, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact ⟨rfl, exps, hexps, rfl⟩

theorem instImps_inv {m : Module} {mt : CModuleType} {imps : List FnType}
    {r : CModuleType × ScalarInstance} (h : instImps m mt imps = some r) :
    ∃ s f, instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
      ((List.range mt.imports.length).map ExternAddr.func) = some (s, f, none) ∧
      instFrom mt imps s f = some r := by
  unfold instImps at h
  split at h
  · exact ⟨_, _, ‹_›, h⟩
  · cases h

theorem instance?_inv {m : Module} {r : CModuleType × ScalarInstance} (h : instance? m = some r) :
    ∃ mt, validate? m = some mt ∧ mt.imports.all isFuncImport = true ∧ ∃ imps,
      (CExternType.funcs mt.imports).mapM FnType.ofDefType? = some imps ∧
      instImps m mt imps = some r := by
  obtain ⟨mt, hv, h'⟩ := Option.bind_eq_some_iff.1 h
  by_cases hall : mt.imports.all isFuncImport = true
  · simp only [hall, ↓reduceIte] at h'
    obtain ⟨imps, himps, hi⟩ := Option.bind_eq_some_iff.1 h'
    exact ⟨mt, hv, hall, imps, himps, hi⟩
  · simp [hall] at h'

/-- **The computed instance of a module is its instance** (`IsInstance`). -/
theorem isInstance_of_instance? {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (h : instance? m = some (mt, I)) : IsInstance m mt I := by
  obtain ⟨mt', hv, hall, imps, himps, hi⟩ := instance?_inv h
  obtain ⟨s, f, hinst, hfrom⟩ := instImps_inv hi
  obtain ⟨rfl, exps, hexps, rfl⟩ := instFrom_inv hfrom
  have hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, s.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) (exportFuncAddrs f.module) exps :=
    (forall₂_of_mapM hexps).imp fun a ft hft => Option.bind_eq_some_iff.1 hft
  exact ⟨hv, isFuncImport_all hall, forall₂_of_mapM himps, ⟨f, hinst, rfl⟩, hexp⟩

end Silmaril.Wasm.Verify
