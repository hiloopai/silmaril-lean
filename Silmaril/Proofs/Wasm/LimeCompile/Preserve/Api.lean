module

public import Silmaril.Wasm.LimeCompile.Preserve.Defs

/-!
# Export APIs a Lime1 module can have: proofs

* necessity, `apiLime_toCore`: every resolved export type of a Lime1 module's Core image is a
  Lime type (`ApiTy.lime`);
* sufficiency, `exportApi_stub`: every API whose resolved types are Lime types, with fewer than
  `2 ^ 32 - 1` entries, is the export API of a Lime1 module (`stub`, one declaration of each kind
  per export, empty bodies; validity is not claimed);
* `apiLime_iff`: decidability of `ApiLime`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Preserve

open Silmaril.Wasm Silmaril.Wasm.LimeCompile.Preserve

/-! ## Lime types of the Core image -/

theorem apiLime_iff (A : List (String × Option ApiTy)) :
    ApiLime A ↔ A.all (fun p => p.2.all ApiTy.lime) = true := by
  simp only [ApiLime, List.all_eq_true, Option.all_eq_true]

instance (A : List (String × Option ApiTy)) : Decidable (ApiLime A) :=
  decidable_of_iff _ (apiLime_iff A).symm

theorem fits32_toCore (v : V1.Limits) : fits32 v.toCore = true := by
  rcases v with ⟨min, max⟩
  cases max <;> simp [fits32, V1.Limits.toCore, V1.widen32]

theorem lime_func_toCore (ft : V1.FuncType) :
    (ApiTy.func ⟨true, [], .func ft.toCore⟩).lime = true := by
  simp [ApiTy.lime, V1.FuncType.toCore, V1.ValType.toCore, limeVal]

theorem lime_table_toCore (v : V1.TableType) : (ApiTy.table v.toCore).lime = true := by
  simp [ApiTy.lime, V1.TableType.toCore, fits32_toCore]

theorem lime_memory_toCore (v : V1.MemoryType) : (ApiTy.memory v.toCore).lime = true := by
  simp [ApiTy.lime, V1.MemoryType.toCore, fits32_toCore]

theorem lime_global_toCore (v : V1.GlobalType) : (ApiTy.global v.toCore).lime = true := by
  simp [ApiTy.lime, V1.GlobalType.toCore, V1.ValType.toCore, limeVal]

theorem typeAt_toCore {l : Lime1.Module} {x : TypeIdx} {st : SubType}
    (h : Module.typeAt l.toCore x = some st) :
    ∃ ft : V1.FuncType, st = ⟨true, [], .func ft.toCore⟩ := by
  have hm : st ∈ (l.toCore).typeDefinitions := List.mem_of_getElem? h
  simp only [Silmaril.Wasm.Module.typeDefinitions, Lime1.Module.toCore, List.mem_flatMap,
    List.mem_map, V1.FuncType.toCoreRec] at hm
  obtain ⟨_, ⟨ft, _, rfl⟩, hst⟩ := hm
  simp only [List.mem_singleton] at hst
  exact ⟨ft, hst⟩

theorem impTables_toCore {l : Lime1.Module} {t : TableType}
    (h : t ∈ Module.impTables l.toCore) : ∃ v : V1.TableType, t = v.toCore := by
  simp only [Module.impTables, Lime1.Module.toCore, List.mem_filterMap, List.mem_map] at h
  obtain ⟨_, ⟨⟨_, _, d⟩, _, rfl⟩, hd⟩ := h
  cases d <;> simp_all [V1.Import.toCore, V1.ImportDesc.toCore]
  exact ⟨_, hd.symm⟩

theorem impMems_toCore {l : Lime1.Module} {t : MemoryType}
    (h : t ∈ Module.impMems l.toCore) : ∃ v : V1.MemoryType, t = v.toCore := by
  simp only [Module.impMems, Lime1.Module.toCore, List.mem_filterMap, List.mem_map] at h
  obtain ⟨_, ⟨⟨_, _, d⟩, _, rfl⟩, hd⟩ := h
  cases d <;> simp_all [V1.Import.toCore, V1.ImportDesc.toCore]
  exact ⟨_, hd.symm⟩

theorem impGlobals_toCore {l : Lime1.Module} {t : GlobalType}
    (h : t ∈ Module.impGlobals l.toCore) : ∃ v : V1.GlobalType, t = v.toCore := by
  simp only [Module.impGlobals, Lime1.Module.toCore, List.mem_filterMap, List.mem_map] at h
  obtain ⟨_, ⟨⟨_, _, d⟩, _, rfl⟩, hd⟩ := h
  cases d <;> simp_all [V1.Import.toCore, V1.ImportDesc.toCore]
  exact ⟨_, hd.symm⟩

theorem resolve_toCore_func (l : Lime1.Module) (i : FuncIdx) {t : ApiTy}
    (h : Module.resolve l.toCore (V1.ExternIdx.func i).toCore = some t) : t.lime = true := by
  simp only [V1.ExternIdx.toCore, Module.resolve, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at h
  obtain ⟨x, _, st, hst, rfl⟩ := h
  obtain ⟨ft, rfl⟩ := typeAt_toCore hst
  exact lime_func_toCore ft

theorem resolve_toCore_table (l : Lime1.Module) (i : TableIdx) {t : ApiTy}
    (h : Module.resolve l.toCore (V1.ExternIdx.table i).toCore = some t) : t.lime = true := by
  simp only [V1.ExternIdx.toCore, Module.resolve, Option.map_eq_some_iff] at h
  obtain ⟨tt, ht, rfl⟩ := h
  have hm : tt ∈ Module.impTables l.toCore ++ (l.toCore).tables.map Table.type :=
    List.mem_of_getElem? ht
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨v, rfl⟩ := impTables_toCore hm
    exact lime_table_toCore v
  · simp only [Lime1.Module.toCore, List.map_map, List.mem_map] at hm
    obtain ⟨v, _, rfl⟩ := hm
    exact lime_table_toCore v

theorem resolve_toCore_memory (l : Lime1.Module) (i : MemIdx) {t : ApiTy}
    (h : Module.resolve l.toCore (V1.ExternIdx.memory i).toCore = some t) : t.lime = true := by
  simp only [V1.ExternIdx.toCore, Module.resolve, Option.map_eq_some_iff] at h
  obtain ⟨tt, ht, rfl⟩ := h
  have hm : tt ∈ Module.impMems l.toCore ++ (l.toCore).memories := List.mem_of_getElem? ht
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨v, rfl⟩ := impMems_toCore hm
    exact lime_memory_toCore v
  · simp only [Lime1.Module.toCore, List.mem_map] at hm
    obtain ⟨v, _, rfl⟩ := hm
    exact lime_memory_toCore v

theorem resolve_toCore_global (l : Lime1.Module) (i : GlobalIdx) {t : ApiTy}
    (h : Module.resolve l.toCore (V1.ExternIdx.global i).toCore = some t) : t.lime = true := by
  simp only [V1.ExternIdx.toCore, Module.resolve, Option.map_eq_some_iff] at h
  obtain ⟨tt, ht, rfl⟩ := h
  have hm : tt ∈ Module.impGlobals l.toCore ++ (l.toCore).globals.map Global.type :=
    List.mem_of_getElem? ht
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨v, rfl⟩ := impGlobals_toCore hm
    exact lime_global_toCore v
  · simp only [Lime1.Module.toCore, List.map_map, List.mem_map] at hm
    obtain ⟨g, _, rfl⟩ := hm
    exact lime_global_toCore g.type

/-- **Necessity**: the resolved export types of a Lime1 module's Core image are Lime types. -/
theorem resolve_toCore_lime (l : Lime1.Module) (i : V1.ExternIdx) {t : ApiTy}
    (h : Module.resolve l.toCore i.toCore = some t) : t.lime = true := by
  cases i with
  | func i => exact resolve_toCore_func l i h
  | table i => exact resolve_toCore_table l i h
  | memory i => exact resolve_toCore_memory l i h
  | global i => exact resolve_toCore_global l i h

theorem apiLime_toCore (l : Lime1.Module) : ApiLime (Module.exportApi l.toCore) := by
  intro p hp t ht
  simp only [Module.exportApi, Lime1.Module.toCore, List.map_map, List.mem_map] at hp
  obtain ⟨e, _, rfl⟩ := hp
  exact resolve_toCore_lime l e.index ht

/-! ## Sufficiency: a stub module for every Lime API -/

theorem valTypes_of_lime :
    ∀ ts : List ValType, ts.all limeVal = true →
      ∃ vs : List V1.ValType, ts.mapM V1.ValType.ofCore? = some vs ∧ vs.map V1.ValType.toCore = ts
  | [], _ => ⟨[], rfl, rfl⟩
  | t :: ts, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨vs, hvs, hmap⟩ := valTypes_of_lime ts h.2
    cases t with
    | num n =>
      exact ⟨n :: vs, by simp [List.mapM_cons, hvs, V1.ValType.ofCore?],
        by rw [List.map_cons, hmap]; rfl⟩
    | vec _ => simp [limeVal] at h
    | ref _ => simp [limeVal] at h

theorem funcType_of_lime {ft : FuncType} (hp : ft.params.all limeVal = true)
    (hr : ft.results.all limeVal = true) :
    ∃ v : V1.FuncType, V1.FuncType.ofCore? ft = some v ∧ v.toCore = ft := by
  obtain ⟨ps, hps, hpm⟩ := valTypes_of_lime _ hp
  obtain ⟨rs, hrs, hrm⟩ := valTypes_of_lime _ hr
  refine ⟨⟨ps, rs⟩, ?_, ?_⟩
  · simp [V1.FuncType.ofCore?, hps, hrs]
  · cases ft
    simp_all [V1.FuncType.toCore]

theorem limits_of_fits {l : Limits} (h : fits32 l = true) :
    ∃ v : V1.Limits, V1.Limits.ofCore? l = some v ∧ v.toCore = l := by
  rcases l with ⟨min, max⟩
  simp only [fits32, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hmin, hmax⟩ := h
  have hmin' : (min : Nat) < 4294967296 := hmin
  cases max with
  | none =>
    exact ⟨⟨⟨min.val, hmin⟩, none⟩, by simp [V1.Limits.ofCore?, V1.narrow32?, hmin'],
      by simp [V1.Limits.toCore, V1.widen32]⟩
  | some n =>
    simp only [Option.all_some, decide_eq_true_eq] at hmax
    have hmax' : (n : Nat) < 4294967296 := hmax
    exact ⟨⟨⟨min.val, hmin⟩, some ⟨n.val, hmax⟩⟩,
      by simp [V1.Limits.ofCore?, V1.narrow32?, hmin', hmax'],
      by simp [V1.Limits.toCore, V1.widen32]⟩

/-- The Lime1 function type standing for an API entry (empty when not a function). -/
def funcOf : Option ApiTy → V1.FuncType
  | some (.func ⟨_, _, .func ft⟩) => (V1.FuncType.ofCore? ft).getD ⟨[], []⟩
  | _ => ⟨[], []⟩

/-- The Lime1 table type standing for an API entry. -/
def tableOf : Option ApiTy → V1.TableType
  | some (.table t) => (V1.TableType.ofCore? t).getD ⟨⟨0, none⟩⟩
  | _ => ⟨⟨0, none⟩⟩

/-- The Lime1 memory type standing for an API entry. -/
def memOf : Option ApiTy → V1.MemoryType
  | some (.memory t) => (V1.MemoryType.ofCore? t).getD ⟨⟨0, none⟩⟩
  | _ => ⟨⟨0, none⟩⟩

/-- The Lime1 global type standing for an API entry. -/
def globalOf : Option ApiTy → V1.GlobalType
  | some (.global t) => (V1.GlobalType.ofCore? t).getD ⟨.const, .int .i32⟩
  | _ => ⟨.const, .int .i32⟩

/-- The export index of the `k`-th API entry (an out-of-range function index when the entry
does not resolve). -/
def idxOf (k : Nat) : Option ApiTy → V1.ExternIdx
  | some (.func _) => .func ⟨Fin.ofNat _ k⟩
  | some (.table _) => .table ⟨Fin.ofNat _ k⟩
  | some (.memory _) => .memory ⟨Fin.ofNat _ k⟩
  | some (.global _) => .global ⟨Fin.ofNat _ k⟩
  | _ => .func ⟨Fin.last _⟩

/-- **A stub Lime1 module with a given API**: one declaration of each kind per entry. -/
def stub (A : List (String × Option ApiTy)) : Lime1.Module :=
  { types := A.map fun p => funcOf p.2
    funcs := A.mapIdx fun k _ => ⟨⟨Fin.ofNat _ k⟩, [], []⟩
    tables := A.map fun p => tableOf p.2
    memories := A.map fun p => memOf p.2
    globals := A.map fun p => ⟨globalOf p.2, []⟩
    exports := A.mapIdx fun k p => ⟨p.1, idxOf k p.2⟩ }

theorem typeDefinitions_toCore (l : Lime1.Module) :
    (l.toCore).typeDefinitions = l.types.map fun ft => ⟨true, [], .func ft.toCore⟩ := by
  simp only [Silmaril.Wasm.Module.typeDefinitions, Lime1.Module.toCore]
  induction l.types with
  | nil => rfl
  | cons ft fts ih => simp [List.flatMap_cons, V1.FuncType.toCoreRec, ih]

theorem ofNat_val {k : Nat} (hk : k < 2 ^ 32) : (Fin.ofNat (2 ^ 32) k).val = k :=
  Nat.mod_eq_of_lt hk

theorem resolve_stub_func {A : List (String × Option ApiTy)} {k : Nat} {p : String × Option ApiTy}
    (hk : A[k]? = some p) (hlen : A.length ≤ 2 ^ 32 - 1) {st : SubType}
    (hp : p.2 = some (.func st)) (hl : (ApiTy.func st).lime = true) :
    Module.resolve (stub A).toCore (V1.ExternIdx.func ⟨Fin.ofNat _ k⟩).toCore =
      some (.func st) := by
  have hkl : k < A.length := (List.getElem?_eq_some_iff.1 hk).1
  have hk32 : (Fin.ofNat (2 ^ 32) k).val = k := ofNat_val (by omega)
  obtain ⟨fin, sup, body⟩ := st
  have hst : fin = true ∧ sup = [] ∧ ∃ ft, body = .func ft ∧ ft.params.all limeVal = true ∧
      ft.results.all limeVal = true := by
    cases fin <;> cases sup <;> cases body <;> simp_all [ApiTy.lime]
  obtain ⟨rfl, rfl, ft, rfl, hpar, hres⟩ := hst
  obtain ⟨v, hv, hvc⟩ := funcType_of_lime hpar hres
  have hfun : funcOf p.2 = v := by simp [hp, funcOf, hv]
  have hft : (Silmaril.Wasm.Module.functionTypes (stub A).toCore)[k]? =
      some ⟨Fin.ofNat _ k⟩ := by
    simp [Silmaril.Wasm.Module.functionTypes, Silmaril.Wasm.Module.importedFunctions,
      Lime1.Module.toCore, stub, hk, Lime1.Func.toCore]
  have hty : Module.typeAt (stub A).toCore ⟨Fin.ofNat _ k⟩ = some ⟨true, [], .func ft⟩ := by
    simp only [Module.typeAt, typeDefinitions_toCore, hk32]
    simp [stub, hk, hfun, hvc]
  simp only [V1.ExternIdx.toCore, Module.resolve, hk32, hft, Option.bind_some, hty,
    Option.map_some]

theorem tableType_of_lime {t : TableType} (h : (ApiTy.table t).lime = true) :
    ∃ v : V1.TableType, V1.TableType.ofCore? t = some v ∧ v.toCore = t := by
  obtain ⟨addr, lim, el⟩ := t
  simp only [ApiTy.lime, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, rfl⟩, hf⟩ := h
  obtain ⟨v, hv, hvc⟩ := limits_of_fits hf
  exact ⟨⟨v⟩, by simp [V1.TableType.ofCore?, hv], by simp [V1.TableType.toCore, hvc]⟩

theorem memType_of_lime {t : MemoryType} (h : (ApiTy.memory t).lime = true) :
    ∃ v : V1.MemoryType, V1.MemoryType.ofCore? t = some v ∧ v.toCore = t := by
  obtain ⟨addr, lim⟩ := t
  simp only [ApiTy.lime, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl, hf⟩ := h
  obtain ⟨v, hv, hvc⟩ := limits_of_fits hf
  exact ⟨⟨v⟩, by simp [V1.MemoryType.ofCore?, hv], by simp [V1.MemoryType.toCore, hvc]⟩

theorem globalType_of_lime {t : GlobalType} (h : (ApiTy.global t).lime = true) :
    ∃ v : V1.GlobalType, V1.GlobalType.ofCore? t = some v ∧ v.toCore = t := by
  obtain ⟨m, val⟩ := t
  cases val with
  | num n =>
    exact ⟨⟨m, n⟩, by simp [V1.GlobalType.ofCore?, V1.ValType.ofCore?],
      by simp [V1.GlobalType.toCore, V1.ValType.toCore]⟩
  | vec _ => simp [ApiTy.lime, limeVal] at h
  | ref _ => simp [ApiTy.lime, limeVal] at h

theorem stub_toCore_imports (A : List (String × Option ApiTy)) :
    (stub A).toCore.imports = [] := rfl

theorem resolve_stub_none {A : List (String × Option ApiTy)} (hlen : A.length ≤ 2 ^ 32 - 1)
    (k : Nat) : Module.resolve (stub A).toCore (idxOf k none).toCore = none := by
  have hlenF : (Silmaril.Wasm.Module.functionTypes (stub A).toCore).length = A.length := by
    simp [Silmaril.Wasm.Module.functionTypes, Silmaril.Wasm.Module.importedFunctions,
      Lime1.Module.toCore, stub]
  have hnone : (Silmaril.Wasm.Module.functionTypes (stub A).toCore)[4294967295]? = none := by
    rw [List.getElem?_eq_none_iff, hlenF]
    omega
  simp only [idxOf, V1.ExternIdx.toCore, Module.resolve, Fin.val_last, hnone, Option.bind_none]

theorem resolve_stub_table {A : List (String × Option ApiTy)} {k : Nat} {name : String}
    {tt : TableType} (hk : A[k]? = some (name, some (.table tt)))
    (hk32 : (Fin.ofNat (2 ^ 32) k).val = k) (hl : (ApiTy.table tt).lime = true) :
    Module.resolve (stub A).toCore (idxOf k (some (.table tt))).toCore = some (.table tt) := by
  obtain ⟨v, hv, hvc⟩ := tableType_of_lime hl
  have hget : (Module.impTables (stub A).toCore ++ (stub A).toCore.tables.map Table.type)[k]?
      = some tt := by
    simp [Module.impTables, Lime1.Module.toCore, stub, hk, tableOf, hv,
      Lime1.tableToCore, hvc]
  simp only [idxOf, V1.ExternIdx.toCore, Module.resolve, hk32, hget, Option.map_some]

theorem resolve_stub_memory {A : List (String × Option ApiTy)} {k : Nat} {name : String}
    {tt : MemoryType} (hk : A[k]? = some (name, some (.memory tt)))
    (hk32 : (Fin.ofNat (2 ^ 32) k).val = k) (hl : (ApiTy.memory tt).lime = true) :
    Module.resolve (stub A).toCore (idxOf k (some (.memory tt))).toCore = some (.memory tt) := by
  obtain ⟨v, hv, hvc⟩ := memType_of_lime hl
  have hget : (Module.impMems (stub A).toCore ++ (stub A).toCore.memories)[k]? = some tt := by
    simp [Module.impMems, Lime1.Module.toCore, stub, hk, memOf, hv, hvc]
  simp only [idxOf, V1.ExternIdx.toCore, Module.resolve, hk32, hget, Option.map_some]

theorem resolve_stub_global {A : List (String × Option ApiTy)} {k : Nat} {name : String}
    {tt : GlobalType} (hk : A[k]? = some (name, some (.global tt)))
    (hk32 : (Fin.ofNat (2 ^ 32) k).val = k) (hl : (ApiTy.global tt).lime = true) :
    Module.resolve (stub A).toCore (idxOf k (some (.global tt))).toCore = some (.global tt) := by
  obtain ⟨v, hv, hvc⟩ := globalType_of_lime hl
  have hget : (Module.impGlobals (stub A).toCore ++ (stub A).toCore.globals.map Global.type)[k]?
      = some tt := by
    simp [Module.impGlobals, Lime1.Module.toCore, stub, hk, globalOf, hv,
      Lime1.Global.toCore, hvc]
  simp only [idxOf, V1.ExternIdx.toCore, Module.resolve, hk32, hget, Option.map_some]

/-- **The stub resolves each entry to its API type.** -/
theorem resolve_stub {A : List (String × Option ApiTy)} (hA : ApiLime A)
    (hlen : A.length ≤ 2 ^ 32 - 1) {k : Nat} {p : String × Option ApiTy} (hk : A[k]? = some p) :
    Module.resolve (stub A).toCore (idxOf k p.2).toCore = p.2 := by
  have hkl : k < A.length := (List.getElem?_eq_some_iff.1 hk).1
  have hk32 : (Fin.ofNat (2 ^ 32) k).val = k := ofNat_val (by omega)
  have hmem : p ∈ A := List.mem_of_getElem? hk
  obtain ⟨name, o⟩ := p
  cases o with
  | none => exact resolve_stub_none hlen k
  | some t =>
    have hl : t.lime = true := hA _ hmem t rfl
    cases t with
    | func st => exact resolve_stub_func hk hlen rfl hl
    | tag st => simp [ApiTy.lime] at hl
    | table tt => exact resolve_stub_table hk hk32 hl
    | memory tt => exact resolve_stub_memory hk hk32 hl
    | global tt => exact resolve_stub_global hk hk32 hl

/-- **Sufficiency**: a Lime API (with fewer than `2 ^ 32 - 1` entries) is the export API of the
stub. -/
theorem exportApi_stub {A : List (String × Option ApiTy)} (hA : ApiLime A)
    (hlen : A.length ≤ 2 ^ 32 - 1) : Module.exportApi (stub A).toCore = A := by
  apply List.ext_getElem?
  intro k
  cases hk : A[k]? with
  | none =>
    have hge : A.length ≤ k := List.getElem?_eq_none_iff.1 hk
    simp [Module.exportApi, Lime1.Module.toCore, stub, hge]
  | some p =>
    have hr := resolve_stub hA hlen hk
    have hex : (stub A).toCore.exports =
        (A.mapIdx fun k p => (⟨p.1, idxOf k p.2⟩ : V1.Export)).map V1.Export.toCore := rfl
    rw [Module.exportApi, hex]
    generalize (stub A).toCore = S at hr ⊢
    simp [hk, V1.Export.toCore, hr]

end Silmaril.Proofs.Wasm.LimeCompile.Preserve
