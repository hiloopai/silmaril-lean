module

public import Silmaril.Wasm.Jco.Real.ValidAll.Thms

/-!
# Validation of the adaptors up to `|world| < 2^31`: proofs

`Silmaril.Proofs.Wasm.Jco.Real.ValidAll` proves that `adaptorLime md` and `adaptorLimeW md` are valid
Lime1 modules when `2 * |world| + 2 < 2^32`. The index arithmetic needs less: the largest type
and function index is the one of the last shim, `|world| + 2 + (|world| - 1) = 2 * |world| + 1`,
so `mkIdx` wraps no index exactly when `|world| < 2^31`. This module redoes the module-level part
of that proof (the function types of the module context, imports, exports) under
`|world| < 2^31` and reuses the function-level typings (`realloc_valid`, `shim_valid`,
`reallocW_valid`, `shimW_valid`), which have no bound on `|world|`. The one new case is
`|world| = 2^31 - 1`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real.ValidRange

open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Jco
open Silmaril.Wasm.Jco.Real
open Silmaril.Proofs.Wasm.Jco.Real.ValidAll

section Module

variable {cT sT : Sig → Lime1.FuncType} {m : Lime1.Module} {md : Meta} {f0 : Lime1.Func}
  {F : Sig × Nat → Lime1.Func} (h : Shape m cT sT md f0 F) (hw : md.world.length < 2 ^ 31)

include h hw

/-- **The function types of the module context are the module's types**, for `|world| < 2^31`. -/
theorem funcs_eq : (moduleContext m).funcs = Tg cT sT md := by
  have hA : (Tg cT sT md)[(mkIdx 0 : TypeIdx).toNat]? = some allocType := rfl
  have hR : (Tg cT sT md)[(mkIdx (md.world.length + 1) : TypeIdx).toNat]? = some reallocType := by
    rw [mkIdx_toNat, Nat.mod_eq_of_lt (show md.world.length + 1 < 2 ^ 32 by omega)]
    exact T_realloc md
  simp only [moduleContext, h.types, h.imports, h.funcs, stdImports, List.filterMap_cons,
    List.filterMap_map, h.ty0, hA, hR]
  rw [filterMap_zipIdx _ _ cT, filterMap_zipIdx _ _ sT]
  · rfl
  · intro i hi
    show (Tg cT sT md)[(F (md.world[i], i)).type.toNat]? = _
    rw [h.tyF, mkIdx_toNat, Nat.mod_eq_of_lt (show md.world.length + 2 + i < 2 ^ 32 by omega)]
    exact T_shim md hi
  · intro i hi
    show (Tg cT sT md)[(mkIdx (i + 1) : TypeIdx).toNat]? = _
    rw [mkIdx_toNat, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 32 by omega)]
    exact T_callee md hi

theorem ctx_alloc :
    (moduleContext m).funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? =
      some allocType := by
  rw [funcs_eq h hw, funcIdxOf_alloc]
  rfl

theorem ctx_callee (hn : (importNames md).Nodup) {i : Nat} (hi : i < md.world.length) :
    (moduleContext m).funcs[(mkIdx (funcIdxOf md md.world[i].name) : FuncIdx).toNat]? =
      some (cT md.world[i]) := by
  rw [funcs_eq h hw, funcIdxOf_world md hn hi, mkIdx_toNat,
    Nat.mod_eq_of_lt (show i + 1 < 2 ^ 32 by omega)]
  exact T_callee md hi

theorem imports_valid : ∀ i ∈ m.imports, ImportValid m.types i := by
  intro im him
  simp only [h.imports, stdImports, List.mem_cons, List.mem_map] at him
  rcases him with rfl | rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · exact ⟨_, rfl, by simp [ExternTypeValid, MemoryTypeValid, LimitsValid]⟩
  · exact ⟨.func allocType, by rw [h.types]; rfl, trivial⟩
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hc : (Tg cT sT md)[(mkIdx (i + 1) : TypeIdx).toNat]? = some (cT md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_callee md hi
    exact ⟨.func (cT md.world[i]), by simp [importType?, h.types, hc], trivial⟩

theorem exports_valid : ∀ e ∈ m.exports, ExportValid (moduleContext m) e := by
  intro e he
  simp only [h.exports, stdExports, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · have hT : (Tg cT sT md)[(mkIdx (md.world.length + 1) : FuncIdx).toNat]? =
        some reallocType := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_realloc md
    exact ⟨.func reallocType, by simp [exportType?, funcs_eq h hw, hT]⟩
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hT : (Tg cT sT md)[(mkIdx (md.world.length + 2 + i) : FuncIdx).toNat]? =
        some (sT md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_shim md hi
    exact ⟨.func (sT md.world[i]), by simp [exportType?, funcs_eq h hw, hT]⟩

/-- **A module of the adaptor shape is valid when its functions are**, for `|world| < 2^31`. -/
theorem shape_valid (hn : (importNames md).Nodup) (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hf : ∀ f ∈ m.funcs, FuncValid (moduleContext m) f) : ModuleValid m where
  types _ _ := trivial
  imports := imports_valid h hw
  functions := hf
  tables := by simp [h.tables]
  memories := by simp [h.memories]
  globals := by simp [h.globals]
  elements := by simp [h.elems]
  data := by simp [h.data]
  start := by simp [StartValid, h.start]
  exports := exports_valid h hw
  uniqueExports := by
    rw [export_names h]
    exact List.nodup_cons.2 ⟨hr, (List.nodup_cons.1 hn).2⟩
  singleTable := by simp [moduleContext, h.imports, h.tables, stdImports]
  singleMemory := by simp [moduleContext, h.imports, h.memories, stdImports]

end Module

theorem funcs_valid (md : Meta) (hn : (importNames md).Nodup)
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    ∀ f ∈ (adaptorLime md).funcs, FuncValid (moduleContext (adaptorLime md)) f := by
  have h := shape_adaptorLime md
  intro f hf
  rw [h.funcs, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · have hT : (T md)[(mkIdx (md.world.length + 1) : TypeIdx).toNat]? = some reallocType := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_realloc md
    exact realloc_valid _ md _ hT (ctx_alloc h hw) (ctx_memories h)
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hT : (T md)[(mkIdx (md.world.length + 2 + i) : TypeIdx).toNat]? =
        some (shimType md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_shim md hi
    exact shim_valid _ md _ _ hT (ctx_alloc h hw) (ctx_callee h hw hn hi)
      (hp _ (List.getElem_mem hi))

/-- **`adaptorLime md` is a valid Lime1 module for every world of fewer than `2^31` functions**
with distinct names. -/
theorem adaptorLime_limeValid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    ModuleValid (adaptorLime md) :=
  shape_valid (shape_adaptorLime md) hw hn hr (funcs_valid md hn hp hw)

theorem funcsW_valid (md : Meta) (hn : (importNames md).Nodup)
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    ∀ f ∈ (adaptorLimeW md).funcs, FuncValid (moduleContext (adaptorLimeW md)) f := by
  have h := shape_adaptorLimeW md
  intro f hf
  rw [h.funcs, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · have hT : (Tg calleeTypeW shimTypeW md)[(mkIdx (md.world.length + 1) : TypeIdx).toNat]? =
        some reallocType := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_realloc md
    exact reallocW_valid _ md _ hT (ctx_alloc h hw)
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hT : (Tg calleeTypeW shimTypeW md)[(mkIdx (md.world.length + 2 + i) :
        TypeIdx).toNat]? = some (shimTypeW md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_shim md hi
    have hs := List.getElem_mem hi
    exact shimW_valid _ md _ _ hT (ctx_alloc h hw) (ctx_callee h hw hn hi) (ctx_memories h)
      (hp _ hs) (hq _ hs)

/-- **`adaptorLimeW md` is a valid Lime1 module for every world of fewer than `2^31`
functions** with distinct names and wide results that fit. -/
theorem adaptorLimeW_limeValid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hq : ∀ s ∈ md.world, ∀ ts ns, wideOf s.result = some (ts, ns) →
      (flatParams s.params).length + ts.length + 2 < 2 ^ 32)
    (hw : md.world.length < 2 ^ 31) :
    ModuleValid (adaptorLimeW md) :=
  shape_valid (shape_adaptorLimeW md) hw hn hr (funcsW_valid md hn hp hq hw)

end Silmaril.Proofs.Wasm.Jco.Real.ValidRange
