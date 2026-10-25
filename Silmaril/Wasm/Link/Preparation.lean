module

public import Silmaril.Wasm.Link.Allocation
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

@[expose] public section

/-! # Concrete preparation bindings for memory-free GC modules

These lemmas extract the actual initializer and module-allocation witnesses
from `prepare?`. Imported function addresses retain their order, and source
definitions are installed with their exact closed tags, code and module view.
The ordinary Core preparation allocates every global twice; both copies are
recorded here so a linker proof can account for their different addresses.
-/

namespace Silmaril.Wasm.Link.GC.Preparation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Extern addresses for an arbitrary ordered list of imported functions. -/
def imports (as : List Nat) : List ExternAddr := as.map .func

/-- Consecutive addresses used by the concrete allocator. -/
def addresses (base count : Nat) : List Nat := (List.range count).map (base + ·)

@[simp] theorem addresses_length (base count : Nat) : (addresses base count).length = count := by
  simp [addresses]

theorem addresses_lookup {base count i : Nat} (hi : i < count) :
    (addresses base count)[i]? = some (base + i) := by
  simp [addresses, List.getElem?_map, List.getElem?_range hi]

@[simp] theorem imports_funcs (as : List Nat) : ExternAddr.funcs (imports as) = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [imports] at ih ⊢
    simp [ExternAddr.funcs, ih]

@[simp] theorem imports_globals (as : List Nat) : ExternAddr.globals (imports as) = [] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [imports] at ih ⊢
    simp [ExternAddr.globals, ih]

private theorem forall₂_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

/-- Allocation installs source function `n` after the imported function indices,
at its actual store address, with the exact source code and closed type tag. -/
theorem allocModule_function {s s' : Store H} {m : Module} {mi : ModuleInst}
    {as : List Nat} {values : List Val} {refsT : List Ref} {refsE : List (List Ref)}
    {n : Nat} {fn : Func} {d : DefType}
    (ha : allocModule? s m (imports as) values refsT refsE = some (s', mi))
    (hfn : m.funcs[n]? = some fn) (hd : (allocTypes m.types)[fn.type.toNat]? = some d) :
    mi.funcs[as.length + n]? = some (s.funcs.length + n) ∧
      s'.funcs[s.funcs.length + n]? = some ⟨d, mi, .wasm fn⟩ := by
  obtain ⟨_, funcTypes, _, _, hft, _, hmi, hs'⟩ := allocModule?_inv ha
  obtain ⟨d', hdn, hd'⟩ := forall₂_lookup (forall₂_of_mapM hft) hfn
  have he : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  have hn := (List.getElem?_eq_some_iff.mp hfn).1
  have hz : (funcTypes.zip m.funcs)[n]? = some (d, fn) :=
    List.getElem?_zip_eq_some.mpr ⟨hdn, hfn⟩
  constructor
  · rw [hmi]
    simp [List.getElem?_append_right (Nat.le_add_right as.length n),
      List.getElem?_map, List.getElem?_range hn]
  · rw [hs']
    simp [List.getElem?_append_right (Nat.le_add_right s.funcs.length n),
      List.getElem?_map, hz]

/-- Allocation closes the module's actual source type section. -/
theorem allocModule_types {s s' : Store H} {m : Module} {mi : ModuleInst}
    {as : List Nat} {values : List Val} {refsT : List Ref} {refsE : List (List Ref)}
    (ha : allocModule? s m (imports as) values refsT refsE = some (s', mi)) :
    mi.types = allocTypes m.types := by
  obtain ⟨_, _, _, _, _, _, hmi, _⟩ := allocModule?_inv ha
  rw [hmi]

/-- Global definitions and their actual initializer values are installed at
the addresses recorded by the allocated instance. Function imports add no
global indices. -/
theorem allocModule_global {s s' : Store H} {m : Module} {mi : ModuleInst}
    {as : List Nat} {values : List Val} {refsT : List Ref} {refsE : List (List Ref)}
    {n : Nat} {g : Global} {v : Val}
    (ha : allocModule? s m (imports as) values refsT refsE = some (s', mi))
    (hg : m.globals[n]? = some g) (hv : values[n]? = some v) :
    mi.globals[n]? = some (s.globals.length + n) ∧
      s'.globals[s.globals.length + n]? = some
        ⟨⟨g.type.mutability, (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩, v⟩ := by
  obtain ⟨_, _, _, _, _, _, hmi, hs'⟩ := allocModule?_inv ha
  have hn : n < min m.globals.length values.length :=
    Nat.lt_min.mpr ⟨(List.getElem?_eq_some_iff.mp hg).1, (List.getElem?_eq_some_iff.mp hv).1⟩
  have hz : ((Module.closedGlobalTypes m).zip values)[n]? = some
      (⟨g.type.mutability, (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩, v) := by
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨by simp [Module.closedGlobalTypes, List.getElem?_map, hg], hv⟩
  constructor
  · rw [hmi]
    simpa using List.getElem?_range' (s := s.globals.length) (step := 1) hn
  · rw [hs']
    unfold Module.closedGlobalTypes at hz
    simp [List.getElem?_append_right (Nat.le_add_right s.globals.length n),
      List.getElem?_map, hz]

private theorem profile_sections {m : Module} (hp : inProfile m = true) :
    m.memories = [] ∧ m.tables = [] ∧ m.tags = [] ∧ m.data = [] ∧ m.elems = [] ∧ m.start = none := by
  simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
  exact ⟨hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2,
    hp.1.1.1.2, hp.1.1.2, hp.1.2⟩

/-- A successful preparation in the linker's profile supplies the actual
initializer result and the subsequent module-allocation call. -/
theorem prepare_allocation {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) :
    ∃ s₁ f₁ values,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (imports as)⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, values) ∧
      allocModule? s₁ m (imports as) values [] [] = some (c.store, c.frame.module) ∧
      c.frame.locals = [] ∧ c.code = [] ∧ st = none := by
  obtain ⟨_, ht, _, hd, he, hs⟩ := profile_sections hm
  unfold prepare? at hp
  simp [ht, hd, he, hs, evalExprs?, evalExprss?] at hp
  cases hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (imports as)⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) with
  | none =>
    simp only [Module.closedGlobalTypes] at hg
    simp [hg] at hp
  | some p =>
    obtain ⟨s₁, f₁, values⟩ := p
    simp only [Module.closedGlobalTypes] at hg
    simp only [hg] at hp
    cases ha : allocModule? s₁ m (imports as) values [] [] with
    | none => simp [ha] at hp
    | some p =>
      obtain ⟨s₂, mi⟩ := p
      simp [ha, expression] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨s₁, f₁, values, rfl, ha, rfl, rfl, rfl⟩

theorem evalGlobals_values_length {s s₁ : Store H} {f f₁ : Frame}
    {gts : List CGlobalType} {es : List Expr} {values : List Val}
    (h : evalGlobals? evalConst? s f gts es = some (s₁, f₁, values)) :
    values.length = gts.length := by
  induction gts generalizing s f es values s₁ f₁ with
  | nil =>
    cases es with
    | nil =>
      simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
    | cons e es => simp [evalGlobals?] at h
  | cons g gts ih =>
    cases es with
    | nil => simp [evalGlobals?] at h
    | cons e es =>
      simp only [evalGlobals?] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp [ih hrec]

/-- The actual closed global instances built from an initializer's values. -/
def globalInstances (m : Module) (values : List Val) : List GlobalInst :=
  List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) values

/-- The actual function instances appended by module allocation. -/
def functionInstances (mi : ModuleInst) (types : List DefType) (funcs : List Func) :
    List (FuncInst H) := (types.zip funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩

/-- Concrete bindings derived from preparation; the values and function tags
are the witnesses produced by its initializer and allocator. -/
structure Bindings (s : Store H) (m : Module) (as : List Nat) (c : Config H)
    (values : List Val) (functionTypes : List DefType) : Prop where
  values_length : values.length = m.globals.length
  functionTypes_ok : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some functionTypes
  types : c.frame.module.types = allocTypes m.types
  functions : c.frame.module.funcs = as ++ addresses s.funcs.length m.funcs.length
  globals : c.frame.module.globals = addresses (s.globals.length + m.globals.length) m.globals.length
  store_globals : c.store.globals = s.globals ++ globalInstances m values ++ globalInstances m values
  store_functions : c.store.funcs = s.funcs ++ functionInstances c.frame.module functionTypes m.funcs
  locals : c.frame.locals = []
  code : c.code = []

/-- Actual preparation determines all function/global bindings, while retaining
the executions and allocator call that produced them. In particular the store
contains two identical blocks of the module's closed global instances. -/
theorem prepare?_gc_bindings {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) :
    ∃ s₁ f₁ values functionTypes,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (imports as)⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, values) ∧
      allocModule? s₁ m (imports as) values [] [] = some (c.store, c.frame.module) ∧
      Bindings s m as c values functionTypes := by
  obtain ⟨s₁, f₁, values, hg, ha, hl, hcode, _⟩ := prepare_allocation hm hp
  obtain ⟨_, functionTypes, _, _, hft, _, hmi, hs'⟩ := allocModule?_inv ha
  obtain ⟨hsg, hsf, _⟩ := evalGlobals?_shape hg
  have hvalues : values.length = m.globals.length := by
    simpa only [Module.closedGlobalTypes, List.length_map] using evalGlobals_values_length hg
  have hglobalLength : s₁.globals.length = s.globals.length + m.globals.length := by
    rw [hsg]
    simp [Module.closedGlobalTypes, hvalues]
  refine ⟨s₁, f₁, values, functionTypes, hg, ha,
    ⟨hvalues, hft, allocModule_types ha, ?_, ?_, ?_, ?_, hl, hcode⟩⟩
  · rw [hmi]
    simp only [imports_funcs, hsf, addresses]
  · rw [hmi]
    simp only [imports_globals, List.nil_append, hvalues, min_self, hglobalLength,
      List.range'_eq_map_range, addresses]
  · rw [hs', hsg]
    simp only [globalInstances, Module.closedGlobalTypes, List.map_zip_eq_zipWith]
    rfl
  · rw [hs', hsf]
    rfl

theorem Bindings.function_count {s : Store H} {m : Module} {as : List Nat} {c : Config H}
    {values : List Val} {functionTypes : List DefType} (h : Bindings s m as c values functionTypes) :
    c.store.funcs.length = s.funcs.length + m.funcs.length := by
  have hlen : functionTypes.length = m.funcs.length :=
    (forall₂_of_mapM h.functionTypes_ok).length_eq.symm
  rw [h.store_functions]
  simp [functionInstances, hlen]

theorem Bindings.global_count {s : Store H} {m : Module} {as : List Nat} {c : Config H}
    {values : List Val} {functionTypes : List DefType} (h : Bindings s m as c values functionTypes) :
    c.store.globals.length = s.globals.length + 2 * m.globals.length := by
  rw [h.store_globals]
  simp only [List.length_append, globalInstances, List.length_zipWith,
    Module.closedGlobalTypes, List.length_map, h.values_length, min_self]
  omega

/-- Source function definitions become concrete prepared store bindings, at
addresses independent of the imported-function index count. -/
theorem prepared_function {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} {n : Nat} {fn : Func} {d : DefType}
    (hm : inProfile m = true) (hp : prepare? evalConst? s m (imports as) = some (c, st))
    (hfn : m.funcs[n]? = some fn) (hd : (allocTypes m.types)[fn.type.toNat]? = some d) :
    c.frame.module.funcs[as.length + n]? = some (s.funcs.length + n) ∧
      c.store.funcs[s.funcs.length + n]? = some ⟨d, c.frame.module, .wasm fn⟩ := by
  obtain ⟨s₁, _, _, hg, ha, _, _, _⟩ := prepare_allocation hm hp
  obtain ⟨_, hsf, _⟩ := evalGlobals?_shape hg
  simpa only [hsf] using allocModule_function ha hfn hd

/-- Preparation's closed type view is supplied by the actual allocator. -/
theorem prepared_types {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) :
    c.frame.module.types = allocTypes m.types := by
  obtain ⟨_, _, _, _, ha, _, _, _⟩ := prepare_allocation hm hp
  exact allocModule_types ha

/-- A prepared global has its actual initializer value at the installed
address, after the first block allocated during initializer evaluation. -/
theorem prepared_global {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} {n : Nat} {g : Global}
    (hm : inProfile m = true) (hp : prepare? evalConst? s m (imports as) = some (c, st))
    (hgl : m.globals[n]? = some g) :
    ∃ s₁ f₁ values v,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (imports as)⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, values) ∧
      values[n]? = some v ∧
      c.frame.module.globals[n]? = some (s.globals.length + m.globals.length + n) ∧
      c.store.globals[s.globals.length + m.globals.length + n]? = some
        ⟨⟨g.type.mutability, (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩, v⟩ := by
  obtain ⟨s₁, f₁, values, hg, ha, _, _, _⟩ := prepare_allocation hm hp
  have hvalues : values.length = m.globals.length := by
    simpa only [Module.closedGlobalTypes, List.length_map] using evalGlobals_values_length hg
  have hn : n < values.length := by
    rw [hvalues]
    exact (List.getElem?_eq_some_iff.mp hgl).1
  have hv : values[n]? = some values[n] := List.getElem?_eq_getElem hn
  obtain ⟨hsg, _, _⟩ := evalGlobals?_shape hg
  have hlen : s₁.globals.length = s.globals.length + m.globals.length := by
    rw [hsg]
    simp [Module.closedGlobalTypes, hvalues]
  refine ⟨s₁, f₁, values, values[n], hg, hv, ?_⟩
  simpa only [hlen] using allocModule_global ha hgl hv

/-- Function and global counts follow from the actual initializer/allocator
results, including the two global allocations of ordinary preparation. -/
theorem prepared_counts {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) :
    c.store.funcs.length = s.funcs.length + m.funcs.length ∧
      c.store.globals.length = s.globals.length + 2 * m.globals.length := by
  obtain ⟨_, _, _, _, _, _, hb⟩ := prepare?_gc_bindings hm hp
  exact ⟨hb.function_count, hb.global_count⟩

/-- The concrete prepared module views, independent of the initializer values. -/
theorem prepared_views {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) :
    c.frame.module.types = allocTypes m.types ∧
      c.frame.module.funcs = as ++ addresses s.funcs.length m.funcs.length ∧
      c.frame.module.globals = addresses (s.globals.length + m.globals.length) m.globals.length := by
  obtain ⟨_, _, _, _, _, _, hb⟩ := prepare?_gc_bindings hm hp
  exact ⟨hb.types, hb.functions, hb.globals⟩

end Silmaril.Wasm.Link.GC.Preparation
