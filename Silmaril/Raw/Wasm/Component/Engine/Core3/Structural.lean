module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Structural.Defs

public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.Lime1.ToCore.Modules
public import Silmaril.Wasm.Validation.Types

/-!
# Structural view of Core 3.0 modules

Syntax-level helpers about Core 3.0 modules (`Silmaril.Wasm.Module`), in the namespace
`Engine.Core3`. They depend only on the module syntax and on `Validation/Types.lean`, not on
Core 3.0 instruction typing or execution, so they can be imported without the Core 3.0 machine
(`Engine/Core3.lean`). The component validator's Core 3.0 profile does not use them: it types
core modules with `validate?` over closed extern types (`Validation/Defs.lean`).

* Index spaces (imports first, then definitions) and the extern type of an index
  (`externTypeOf?`); import types `importTypes` and export types `exportTypes?` read off the
  syntax. Type indices inside these `Wasm.ExternType`s stay relative to the module.
* `funcTypeAt?`: the function type named by a type index (Core 3.0 requires `C.types[x]` to
  expand to a function type for function and tag types).
* `StructurallyValid` (decidable, `checkStructure`): structure of the recursive groups
  (`RecType.checkStructure`); every entry of every index space is structurally valid, with
  function and tag type indices naming a `func` composite type; resolvable exports with
  distinct names; a start function of type `[] -> []`. Instruction bodies, initializers,
  segments and declared sub-type matching are NOT checked. Hence all import and export types
  are structurally valid (`StructurallyValid.import_valid`, `StructurallyValid.export_valid`).
* Flat canon signatures as numeric Core 3.0 function types (`ofFlatType`, partial inverse
  `flatType?`, `flatType?_eq_some_iff`) and the flat signature of a function export
  (`exportFuncType?`, `exportFlatType?`), as compared by a component-level `canon lift`.
* `ImportsMatch E s vs m`: positional import matching in an engine store, the check the
  component instantiator performs with `ExternSub` against `externType?`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

namespace Core3

/-! ## Structural typing of Core 3.0 modules -/

theorem StructurallyValid.exportTypes_isSome {m : Wasm.Module} (h : StructurallyValid m) :
    (exportTypes? m).isSome := by
  simp only [StructurallyValid, checkStructure, Bool.and_eq_true] at h
  exact h.1.1.2

theorem StructurallyValid.allExternTypes_valid {m : Wasm.Module} (h : StructurallyValid m)
    {τ : Wasm.ExternType} (hτ : τ ∈ allExternTypes m) :
    externTypeValid m.typeDefinitions τ = true := by
  simp only [StructurallyValid, checkStructure, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.2 τ hτ

/-- Every resolved index lies in `allExternTypes`. -/
theorem mem_allExternTypes_of_externTypeOf? {m : Wasm.Module} {x : ExternIdx}
    {τ : Wasm.ExternType} (h : externTypeOf? m x = some τ) : τ ∈ allExternTypes m := by
  cases x <;> simp only [externTypeOf?, Option.map_eq_some_iff] at h <;>
    obtain ⟨t, ht, rfl⟩ := h <;>
    simp [allExternTypes, List.mem_of_getElem? ht]

/-- Every import type lies in `allExternTypes`. -/
theorem mem_allExternTypes_of_import {m : Wasm.Module} {i : Import} (h : i ∈ m.imports) :
    i.type ∈ allExternTypes m := by
  obtain ⟨mn, n, τ⟩ := i
  cases τ with
  | tag t =>
    have : t ∈ tagTypes m := List.mem_append_left _ (List.mem_filterMap.2 ⟨_, h, rfl⟩)
    simp [allExternTypes, this]
  | global t =>
    have : t ∈ globalTypes m := List.mem_append_left _ (List.mem_filterMap.2 ⟨_, h, rfl⟩)
    simp [allExternTypes, this]
  | memory t =>
    have : t ∈ memoryTypes m := List.mem_append_left _ (List.mem_filterMap.2 ⟨_, h, rfl⟩)
    simp [allExternTypes, this]
  | table t =>
    have : t ∈ tableTypes m := List.mem_append_left _ (List.mem_filterMap.2 ⟨_, h, rfl⟩)
    simp [allExternTypes, this]
  | func t =>
    have : t ∈ m.functionTypes :=
      List.mem_append_left _ (List.mem_filterMap.2 ⟨_, h, rfl⟩)
    simp [allExternTypes, this]

/-- Structurally valid modules have structurally valid import types. -/
theorem StructurallyValid.import_valid {m : Wasm.Module} (h : StructurallyValid m)
    {i : Import} (hi : i ∈ m.imports) : externTypeValid m.typeDefinitions i.type = true :=
  h.allExternTypes_valid (mem_allExternTypes_of_import hi)

private theorem mem_of_mapM_eq_some {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} (h : xs.mapM f = some ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp at hy
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := ih hbs hy
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- Structurally valid modules have structurally valid export types. -/
theorem StructurallyValid.export_valid {m : Wasm.Module} (h : StructurallyValid m)
    {es : List (String × Wasm.ExternType)} (he : exportTypes? m = some es)
    {p : String × Wasm.ExternType} (hp : p ∈ es) :
    externTypeValid m.typeDefinitions p.2 = true := by
  obtain ⟨e, _, hx⟩ := mem_of_mapM_eq_some he hp
  obtain ⟨τ, hτ, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact h.allExternTypes_valid (mem_allExternTypes_of_externTypeOf? hτ)

/-- Structurally valid modules export resolvable function types: a function export always
resolves (its type index names a `func` composite type). -/
theorem StructurallyValid.externFuncType?_isSome {m : Wasm.Module} (h : StructurallyValid m)
    {es : List (String × Wasm.ExternType)} (he : exportTypes? m = some es) {n : String}
    {i : TypeIdx} (hp : (n, Wasm.ExternType.func i) ∈ es) :
    (externFuncType? m (.func i)).isSome := h.export_valid he hp

private def idx0 {k : IndexKind} : Idx k := ⟨⟨0, by decide⟩⟩

private def idx1 {k : IndexKind} : Idx k := ⟨⟨1, by decide⟩⟩

/-- A module importing a memory64 memory and re-exporting it. -/
private def memory64Module : Wasm.Module where
  imports := [⟨"env", "mem", .memory ⟨.i64, ⟨⟨1, by decide⟩, none⟩⟩⟩]
  exports := [⟨"mem", .memory idx0⟩]

example : checkStructure memory64Module = true := by decide +kernel

example : exportTypes? memory64Module =
    some [("mem", .memory ⟨.i64, ⟨⟨1, by decide⟩, none⟩⟩)] := by decide +kernel

private def danglingExport : Wasm.Module where
  exports := [⟨"f", .func idx0⟩]

/-- An export of an undefined function does not resolve. -/
example : checkStructure danglingExport = false := by decide +kernel

private def duplicateExport : Wasm.Module where
  memories := [⟨.i32, ⟨⟨0, by decide⟩, none⟩⟩]
  exports := [⟨"m", .memory idx0⟩, ⟨"m", .memory idx0⟩]

/-- Duplicate export names are rejected. -/
example : checkStructure duplicateExport = false := by decide +kernel

private def i32 : Wasm.ValType := .num (.int .i32)

/-- Type 0: `[i32] -> [i32]`; type 1: `[] -> []`; type 2: an empty struct. -/
private def testTypes : List RecType :=
  [⟨[⟨true, [], .func ⟨[i32], [i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩,
    ⟨[⟨true, [], .struct []⟩]⟩]

/-- A function of type 0 exported as `f`, and a start function of type 1. -/
private def funcModule : Wasm.Module where
  types := testTypes
  funcs := [⟨idx0, [], []⟩, ⟨idx1, [], []⟩]
  start := some idx1
  exports := [⟨"f", .func idx0⟩]

example : checkStructure funcModule = true := by decide +kernel

/-- The flat signature of a Core 3.0 export is resolved through the type definitions. -/
example : exportFlatType? funcModule "f" = some ⟨[.int .i32], [.int .i32]⟩ := by decide +kernel

/-- A start function whose type is not `[] -> []` is rejected. -/
example : checkStructure { funcModule with start := some idx0 } = false := by decide +kernel

/-- A function import whose type index names a struct type is rejected. -/
example : checkStructure
    { types := testTypes, imports := [⟨"env", "f", .func ⟨⟨2, by decide⟩⟩⟩] } = false := by
  decide +kernel

/-- A local function with an out-of-range type index is rejected (also when exported). -/
example : checkStructure
    { funcs := [⟨⟨⟨5, by decide⟩⟩, [], []⟩], exports := [⟨"f", .func idx0⟩] } = false := by
  decide +kernel

/-- A local memory with `min > max` is rejected (also when exported). -/
example : checkStructure
    { memories := [⟨.i32, ⟨⟨5, by decide⟩, some ⟨1, by decide⟩⟩⟩],
      exports := [⟨"m", .memory idx0⟩] } = false := by
  decide +kernel

/-- A successful `mapM V1.ValType.ofCore?` reads a numeric result type. -/
theorem mapM_valType_ofCore?_eq_some {xs : List Wasm.ValType} {ys : List V1.ValType}
    (h : xs.mapM V1.ValType.ofCore? = some ys) : xs = ys.map V1.ValType.toCore := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    cases a <;> simp only [V1.ValType.ofCore?, Option.some.injEq, reduceCtorEq] at hb
    subst hb
    simp [ih hbs, V1.ValType.toCore]

/-- `flatType?` succeeds exactly on the numeric image `ofFlatType`. -/
theorem flatType?_eq_some_iff (t : Wasm.FuncType) (ft : V1.FuncType) :
    flatType? t = some ft ↔ t = ofFlatType ft := by
  constructor
  · intro h
    obtain ⟨ps, rs⟩ := t
    simp only [flatType?, V1.FuncType.ofCore?, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨ps', hps, rs', hrs, rfl⟩ := h
    simp [mapM_valType_ofCore?_eq_some hps, mapM_valType_ofCore?_eq_some hrs,
      V1.FuncType.toCore]
  · rintro rfl
    exact flatType?_ofFlatType ft

/-- `exportFlatType?` succeeds exactly on exports whose resolved type is a numeric image. -/
theorem exportFlatType?_eq_some_iff (m : Wasm.Module) (name : String) (ft : V1.FuncType) :
    exportFlatType? m name = some ft ↔ exportFuncType? m name = some (ofFlatType ft) := by
  simp only [exportFlatType?, Option.bind_eq_some_iff, flatType?_eq_some_iff, exists_eq_right]

end Core3

end Silmaril.Wasm.Component.Engine
