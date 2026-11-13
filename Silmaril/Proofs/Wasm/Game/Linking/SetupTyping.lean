module

public import Silmaril.Proofs.Wasm.Game.Linking.SharedExists
public import Silmaril.Proofs.Wasm.Game.Linking.Retype
public import Silmaril.Proofs.Wasm.Game.Instantiate.Basic
public import Silmaril.Wasm.Component.Engine.Core3.Defs

/-!
# Static linking: typing of the stores

Original module documentation:

# Typing of the stores of a static link (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. The provider and
linked stores (closed instantiations over a typed store) and #1936's shared store (the
consumer instantiated against the provider functions it imports) are typed, and their new
functions are Wasm functions (`once_storeOk`, from the typing of `instantiateOnce?` through the
checked engine instantiation `prepareE?`). The consumer's import addresses have its declared
import types (`consumer_imports_ok`): the linker resolves each import to a provider export of
a closed subtype of the declared type, and the provider's export type is the type of the
stored function.

Change from the source: the old linker matched import types exactly, and so did the first
port (an `exactMatch : resolveImportsExact? … = some w.imports` hypothesis). The pinned public
linker resolves up to closed subtyping (`resolveImports?`, `Recipe.Assembly.import_lookup`);
`consumer_imports_ok` now uses that subtype through `ExternAddrOk.sub`, with the validity of
the declared import type in the empty context from
`Silmaril.Wasm.Component.Engine.Core3.ModuleOk.imports_externTypeOk`, so no exactness
hypothesis is needed.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC

variable {H : Type}

/-- Single instantiation keeps a store typed and appends only Wasm functions. (The old proof
went through the checked engine instantiation `prepareE?`, absent from the pinned
silmaril-lean; this one uses `prepare?_globalResidue_ok` as `IsInstance.ok` does.) -/
theorem once_storeOk {s s' : Store Nat} {m : Module} {mt : CModuleType} {xas : List ExternAddr}
    {f : Frame} (hs : StoreOk s) (hv : validate? m = some mt)
    (hx : List.Forall₂ (ExternAddrOk s) xas mt.imports)
    (h : instantiateOnce? s m xas = some (s', f, none)) :
    StoreOk s' ∧ ∃ new : List (FuncInst Nat), s'.funcs = s.funcs ++ new ∧
      ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  obtain ⟨s₁, f₁, vs, c, hg, hp, hS⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail)
    (host := SingleThreaded.divHost) h
  obtain ⟨s₁', f₁', vs', c', hg', hp', hS'⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail) (host := fun _ _ _ _ => False) h
  rw [hg] at hg'
  cases hg'
  rw [hp] at hp'
  cases hp'
  obtain ⟨hc, -, new, hnew, hwasm⟩ :=
    InstantiateAux.prepare?_globalResidue_ok (P := SingleThreaded.profile SingleThreaded.neverFail)
      SingleThreaded.divHost_ok hs ⟨mt.exports, mt.imports, validate?_sound hv, hx⟩ hg hp
  have hS₂ : Steps (SingleThreaded.profile SingleThreaded.neverFail) SingleThreaded.divHost
      (c.withStart none) ⟨s', f, startCode none⟩ := by
    rw [← Config.withStart_nil]
    exact Steps.withStart hS
  have hc' := steps_configOk SingleThreaded.divHost_ok hc hS₂
  exact ⟨SingleThreaded.ConfigOk.storeOk hc', new, (steps_funcs_eq hS').trans hnew, hwasm⟩

/-- Closed single instantiation keeps a store typed and appends only Wasm functions. -/
theorem once_storeOk_closed {s s' : Store Nat} {m : Module} {mt : CModuleType} {f : Frame}
    (hs : StoreOk s) (hv : validate? m = some mt) (himp : m.imports = [])
    (h : instantiateOnce? s m (Preparation.imports []) = some (s', f, none)) :
    StoreOk s' ∧ ∃ new : List (FuncInst Nat), s'.funcs = s.funcs ++ new ∧
      ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  have hl := Recipe.validation_imports_length hv
  rw [himp] at hl
  have hmt : mt.imports = [] := List.length_eq_zero_iff.mp hl
  exact once_storeOk hs hv (by rw [hmt]; exact .nil) h

theorem link?_validate {ns : String} {provider consumer result : Module}
    (hl : link? ns provider consumer = some result) : ∃ mt, validate? result = some mt := by
  obtain ⟨m, _, hv⟩ := Option.bind_eq_some_iff.mp hl
  unfold validated? at hv
  split at hv
  · rename_i h
    cases hv
    exact Option.isSome_iff_exists.mp h
  · cases hv

private theorem forall₂_lookup'' {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

private theorem forall₂_of_lookup' {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (length : xs.length = ys.length)
    (lookup : ∀ (i : Nat) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → R x y) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp length.symm
    subst ys; exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at length; omega
    | cons y ys =>
      refine .cons (lookup 0 x y rfl rfl) (ih (by simpa using length) ?_)
      intro i x' y' hx hy
      exact lookup (i+1) x' y' hx hy

/-- Every resolved import type is a function type. -/
theorem resolved_import_func {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) {i : Nat} {xt : CExternType}
    (ht : w.consumerType.imports[i]? = some xt) : ∃ d, xt = .func d := by
  have hlen := Recipe.validation_imports_length w.consumerValidation
  have hb := (List.getElem?_eq_some_iff.mp ht).1
  obtain ⟨entry, he⟩ : ∃ entry, consumer.imports[i]? = some entry :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hz : (consumer.imports.zip w.consumerType.imports)[i]? = some (entry, xt) :=
    List.getElem?_zip_eq_some.mpr ⟨he, ht⟩
  obtain ⟨f, hr⟩ := mapM_some_mem w.resolved _ (List.mem_of_getElem? hz)
  dsimp only at hr
  split at hr
  · cases hr
  · cases hty : entry.type <;> simp only [hty] at hr
    all_goals try contradiction
    cases xt with
    | func d => exact ⟨d, rfl⟩
    | _ => simp at hr

/-- A function export of a closed valid module `m`, at type `expected`, is typed in the store
after instantiating `m` once. -/
private theorem export_func_ok {m : Module} {mt : CModuleType} (hmo : ModuleOk m mt)
    (himp : m.imports = []) {s s' : Store H} {f' : Frame} {start : Option FuncIdx}
    (hm : inProfile m = true)
    (hp : instantiateOnce? s m (Preparation.imports []) = some (s', f', start))
    {k : Nat} {ex : Export} {f : FuncIdx} {expected : DefType}
    (hke : m.exports[k]? = some ex) (hkt : mt.exports[k]? = some (.func expected))
    (hidx : ex.index = .func f) :
    ExternAddrOk s' (.func (s.funcs.length + f.toNat)) (.func expected) := by
  cases hmo with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports
      hdisjoint =>
    rename_i dts xtI jts gts tts fdts rts xtE C' C
    have hxtI : xtI = [] := List.forall₂_nil_left_iff.mp (himp ▸ himports)
    obtain ⟨xt', hxt', hok⟩ := forall₂_lookup'' hexports hke
    have hxt'' : xt' = .func expected := Option.some.inj (hxt'.symm.trans hkt)
    have hok' : ExternIdxOk C (.func f) (.func expected) := by
      rw [← hidx, ← hxt'']
      exact hok
    have hcf : C.funcs[f.toNat]? = some expected := by cases hok' with | func h => exact h
    have hcf' : fdts[f.toNat]? = some expected := by
      simpa only [hC, hC', hxtI, CExternType.funcs, List.nil_append] using hcf
    obtain ⟨fn, hfn, hfok⟩ := forall₂_lookup'' hfuncs.flip hcf'
    have hd : C.type? fn.type = some expected := by cases hfok with | mk hd _ _ _ => exact hd
    have hd' : (allocTypes m.types)[fn.type.toNat]? = some expected := by
      rw [allocTypes_eq htypes]
      simpa only [hC, hC', Context.type?] using hd
    exact ExternAddrOk.func (PreparationOnce.once_function hm hp hfn hd').2

/-- **The consumer's imports are typed in the provider's store**: import `i` resolves to the
provider function `f`, whose stored type is a closed subtype of the declared import type (the
pinned public linker resolves imports up to subtyping). -/
theorem consumer_imports_ok {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result)
    {s sp : Store H} {fp : Frame} {startP : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP)) :
    List.Forall₂ (ExternAddrOk sp) (Preparation.imports (importAddrs w s.funcs.length))
      w.consumerType.imports := by
  have hlen : w.consumerType.imports.length = consumer.imports.length :=
    Recipe.validation_imports_length w.consumerValidation
  have hwl : w.imports.length = consumer.imports.length := w.imports_length
  have hvalid : ∀ τ ∈ w.consumerType.imports, ExternTypeOk {} τ := by
    have hok : ModuleOk consumer ⟨w.consumerType.imports, w.consumerType.exports⟩ :=
      validate?_sound w.consumerValidation
    exact Silmaril.Wasm.Component.Engine.Core3.ModuleOk.imports_externTypeOk hok
  apply forall₂_of_lookup'
  · simp [Preparation.imports, importAddrs, hlen, hwl]
  intro i xa xt hxa hxt
  obtain ⟨expected, hexp⟩ := resolved_import_func w hxt
  have hxt' : w.consumerType.imports[i]? = some (.func expected) := hexp ▸ hxt
  have hi : i < consumer.imports.length := hlen ▸ (List.getElem?_eq_some_iff.mp hxt).1
  obtain ⟨entry, he⟩ : ∃ entry, consumer.imports[i]? = some entry :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨f, _, exported, actual, hf, -, -, hfind, hidx, hsub⟩ := w.import_lookup he hxt'
  have hxa' : xa = .func (s.funcs.length + f.toNat) := by
    simpa only [Preparation.imports, importAddrs, List.map_map, List.getElem?_map, hf,
      Option.map_some, Option.some.injEq, Function.comp_apply, eq_comm] using hxa
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
  obtain ⟨hke, hkt⟩ := List.getElem?_zip_eq_some.mp hk
  have hactual : ExternAddrOk sp (.func (s.funcs.length + f.toNat)) (.func actual) :=
    export_func_ok (validate?_sound w.providerValidation) w.providerImports
      w.providerProfile hp hke hkt hidx
  have hok : ExternTypeOk {} (.func expected) := hvalid _ (List.mem_of_getElem? hxt')
  rw [hxa', hexp]
  exact ExternAddrOk.sub hactual hok (ExternSub.func hsub)

end Silmaril.Proofs.Wasm.Game.Linking
