module

public import Silmaril.Wasm.Link.Preparation
public import Silmaril.Wasm.Component.Engine.Core3.Defs

@[expose] public section

/-! # Concrete bindings from single-allocation preparation

The component engine evaluates the original globals, then allocates the
global-free residue with those globals as imports. Its installed functions
retain the source definitions and closed tags, and its module instance names
the original initializer globals. No second copy of the globals is allocated.
-/

namespace Silmaril.Wasm.Link.GC.PreparationOnce

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Imported functions followed by the actual globals of the initializer run. -/
def residueImports (s : Store H) (m : Module) (as : List Nat) : List ExternAddr :=
  Preparation.imports as ++ globalAddrs s.globals.length m.globals.length

private theorem profile_sections {m : Module} (hp : inProfile m = true) :
    m.memories = [] ∧ m.tables = [] ∧ m.tags = [] ∧ m.data = [] ∧ m.elems = [] ∧ m.start = none := by
  simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
  exact ⟨hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2,
    hp.1.1.1.2, hp.1.1.2, hp.1.2⟩

/-- In the linker's segment-free profile, single instantiation ends at the
actual residue allocator, after its actual initializer execution. -/
theorem once_allocation {s s' : Store H} {m : Module} {as : List Nat}
    {f' : Frame} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (Preparation.imports as) = some (s', f', st)) :
    ∃ s₁ f₁ values,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, values) ∧
      allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] = some (s', f'.module) ∧
      f'.locals = [] ∧ st = none := by
  obtain ⟨_, ht, _, hd, he, hs⟩ := profile_sections hm
  unfold instantiateOnce? at hp
  cases hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) with
  | none => simp [hg] at hp
  | some p =>
    obtain ⟨s₁, f₁, values⟩ := p
    simp only [hg] at hp
    unfold instantiateDirect? prepareDirect? prepare? at hp
    simp [Module.globalResidue, ht, hd, he, hs, evalGlobals?, evalExprs?, evalExprss?] at hp
    cases ha : allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] with
    | none =>
      simp only [Module.globalResidue, residueImports, ht, hd, he, hs] at ha
      simp [ha] at hp
    | some p =>
      obtain ⟨s₂, mi⟩ := p
      have ha' := ha
      simp only [Module.globalResidue, residueImports, ht, hd, he, hs] at ha'
      simp [ha'] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      exact ⟨s₁, f₁, values, rfl, ha, rfl, rfl⟩

private theorem forall₂_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

/-- The residue installs the original source functions with their original
closed tags; trailing global imports do not change function indices. -/
theorem residue_function {s s₁ s' : Store H} {m : Module} {as : List Nat} {mi : ModuleInst}
    {n : Nat} {fn : Func} {d : DefType}
    (ha : allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] = some (s', mi))
    (hfn : m.funcs[n]? = some fn) (hd : (allocTypes m.types)[fn.type.toNat]? = some d) :
    mi.funcs[as.length + n]? = some (s₁.funcs.length + n) ∧
      s'.funcs[s₁.funcs.length + n]? = some ⟨d, mi, .wasm fn⟩ := by
  obtain ⟨_, functionTypes, _, _, hft, _, hmi, hs'⟩ := allocModule?_inv ha
  simp only [Module.globalResidue] at hft
  obtain ⟨d', hdn, hd'⟩ := forall₂_lookup (forall₂_of_mapM hft) hfn
  have he : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  have hn := (List.getElem?_eq_some_iff.mp hfn).1
  have hz : (functionTypes.zip m.funcs)[n]? = some (d, fn) :=
    List.getElem?_zip_eq_some.mpr ⟨hdn, hfn⟩
  constructor
  · rw [hmi]
    simp [Module.globalResidue, residueImports, ExternAddr.funcs_append,
      ExternAddr.funcs_globalAddrs, List.getElem?_append_right (Nat.le_add_right as.length n),
      List.getElem?_map, List.getElem?_range hn]
  · rw [hs']
    simp [Module.globalResidue, List.getElem?_append_right (Nat.le_add_right s₁.funcs.length n),
      List.getElem?_map, hz]

theorem residue_types {s s₁ s' : Store H} {m : Module} {as : List Nat} {mi : ModuleInst}
    (ha : allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] = some (s', mi)) :
    mi.types = allocTypes m.types := by
  obtain ⟨_, _, _, _, _, _, hmi, _⟩ := allocModule?_inv ha
  rw [hmi]
  rfl

/-- The installed instance names the globals at their actual initializer
addresses, without shifting past another allocated copy. -/
theorem residue_globals {s s₁ s' : Store H} {m : Module} {as : List Nat} {mi : ModuleInst}
    (ha : allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] = some (s', mi)) :
    mi.globals = Preparation.addresses s.globals.length m.globals.length := by
  have hg := (allocModule?_globalResidue ha).2
  simpa [residueImports, Preparation.addresses] using hg

/-- In this profile the residue allocation changes only the function list.
The globals and all GC objects are exactly those of the initializer result. -/
theorem residue_store {s s₁ s' : Store H} {m : Module} {as : List Nat} {mi : ModuleInst}
    (hm : inProfile m = true)
    (ha : allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] = some (s', mi)) :
    ∃ functionTypes,
      m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some functionTypes ∧
      s' = { s₁ with funcs := s₁.funcs ++ Preparation.functionInstances mi functionTypes m.funcs } := by
  obtain ⟨hmemory, htable, htag, hdata, helem, _⟩ := profile_sections hm
  obtain ⟨tagTypes, functionTypes, _, htt, hft, _, _, hs'⟩ := allocModule?_inv ha
  simp only [Module.globalResidue, htag, List.mapM_nil, Option.pure_def, Option.some.injEq] at htt
  subst tagTypes
  refine ⟨functionTypes, ?_, ?_⟩
  · simpa only [Module.globalResidue] using hft
  · rw [hs']
    simp [Module.globalResidue, hmemory, htable, hdata, helem, Preparation.functionInstances]

/-- Single allocation installs a source function at the address following
the original store's functions, even when its initializers allocate GC objects. -/
theorem once_function {s s' : Store H} {m : Module} {as : List Nat}
    {f' : Frame} {st : Option FuncIdx} {n : Nat} {fn : Func} {d : DefType}
    (hm : inProfile m = true)
    (hp : instantiateOnce? s m (Preparation.imports as) = some (s', f', st))
    (hfn : m.funcs[n]? = some fn) (hd : (allocTypes m.types)[fn.type.toNat]? = some d) :
    f'.module.funcs[as.length + n]? = some (s.funcs.length + n) ∧
      s'.funcs[s.funcs.length + n]? = some ⟨d, f'.module, .wasm fn⟩ := by
  obtain ⟨_, _, _, hg, ha, _, _⟩ := once_allocation hm hp
  obtain ⟨_, hsf, _⟩ := evalGlobals?_shape hg
  simpa only [hsf] using residue_function ha hfn hd

theorem once_types {s s' : Store H} {m : Module} {as : List Nat}
    {f' : Frame} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (Preparation.imports as) = some (s', f', st)) :
    f'.module.types = allocTypes m.types := by
  obtain ⟨_, _, _, _, ha, _, _⟩ := once_allocation hm hp
  exact residue_types ha

theorem once_globals {s s' : Store H} {m : Module} {as : List Nat}
    {f' : Frame} {st : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (Preparation.imports as) = some (s', f', st)) :
    f'.module.globals = Preparation.addresses s.globals.length m.globals.length := by
  obtain ⟨_, _, _, _, ha, _, _⟩ := once_allocation hm hp
  exact residue_globals ha

/-- The component engine's successful preparation retains an actual
single-allocation instantiation. The profile has no start function. -/
theorem prepareE_once {s s' : Store H} {m : Module} {as : List Nat}
    {mi : ModuleInst} {st : Option Nat} (hm : inProfile m = true)
    (hp : Component.Engine.Core3.prepareE? s m (Preparation.imports as) = some (s', mi, st)) :
    ∃ f', instantiateOnce? s m (Preparation.imports as) = some (s', f', none) ∧
      f'.module = mi ∧ st = none := by
  obtain ⟨_, _, _, _, _, hs⟩ := profile_sections hm
  unfold Component.Engine.Core3.prepareE? at hp
  split at hp
  · cases hp
  · split at hp
    · cases hi : instantiateOnce? s m (Preparation.imports as) with
      | none => simp [hi] at hp
      | some p =>
        obtain ⟨s₂, f₂, start⟩ := p
        have hstart : start = none := (instantiateOnce?_start hi).trans hs
        subst start
        simp only [hi, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, hmi, rfl⟩ := hp
        exact ⟨f₂, rfl, hmi, rfl⟩
    · cases hp

/-- Source function bindings at the actual component-engine boundary. -/
theorem prepareE_function {s s' : Store H} {m : Module} {as : List Nat}
    {mi : ModuleInst} {st : Option Nat} {n : Nat} {fn : Func} {d : DefType}
    (hm : inProfile m = true)
    (hp : Component.Engine.Core3.prepareE? s m (Preparation.imports as) = some (s', mi, st))
    (hfn : m.funcs[n]? = some fn) (hd : (allocTypes m.types)[fn.type.toNat]? = some d) :
    mi.funcs[as.length + n]? = some (s.funcs.length + n) ∧
      s'.funcs[s.funcs.length + n]? = some ⟨d, mi, .wasm fn⟩ := by
  obtain ⟨f', hi, hmi, _⟩ := prepareE_once hm hp
  simpa only [hmi] using once_function hm hi hfn hd

theorem prepareE_types {s s' : Store H} {m : Module} {as : List Nat}
    {mi : ModuleInst} {st : Option Nat} (hm : inProfile m = true)
    (hp : Component.Engine.Core3.prepareE? s m (Preparation.imports as) = some (s', mi, st)) :
    mi.types = allocTypes m.types := by
  obtain ⟨_, hi, hmi, _⟩ := prepareE_once hm hp
  simpa only [hmi] using once_types hm hi

theorem prepareE_globals {s s' : Store H} {m : Module} {as : List Nat}
    {mi : ModuleInst} {st : Option Nat} (hm : inProfile m = true)
    (hp : Component.Engine.Core3.prepareE? s m (Preparation.imports as) = some (s', mi, st)) :
    mi.globals = Preparation.addresses s.globals.length m.globals.length := by
  obtain ⟨_, hi, hmi, _⟩ := prepareE_once hm hp
  simpa only [hmi] using once_globals hm hi

/-- Actual initializer and residue-allocation witnesses at the engine boundary. -/
theorem prepareE_allocation {s s' : Store H} {m : Module} {as : List Nat}
    {mi : ModuleInst} {st : Option Nat} (hm : inProfile m = true)
    (hp : Component.Engine.Core3.prepareE? s m (Preparation.imports as) = some (s', mi, st)) :
    ∃ s₁ f₁ values,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, values) ∧
      allocModule? s₁ m.globalResidue (residueImports s m as) [] [] [] = some (s', mi) ∧
      st = none := by
  obtain ⟨f', hi, hmi, hst⟩ := prepareE_once hm hp
  obtain ⟨s₁, f₁, values, hg, ha, _, _⟩ := once_allocation hm hi
  exact ⟨s₁, f₁, values, hg, by simpa only [hmi] using ha, hst⟩

end Silmaril.Wasm.Link.GC.PreparationOnce
