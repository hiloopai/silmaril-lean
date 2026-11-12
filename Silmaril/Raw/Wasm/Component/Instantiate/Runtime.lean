module

public import Silmaril.Wasm.Component.Reference.Instantiate.Runtime.Defs

public import Silmaril.Raw.Wasm.Component.Instantiate.Items
public import Silmaril.Raw.Wasm.Component.Runtime.Builtin
public import Silmaril.Raw.Wasm.Component.Runtime.Store
public import Silmaril.Raw.Wasm.Component.Types.Basic
public import Silmaril.Raw.Wasm.Component.Value.Basic
public import Silmaril.Raw.Wasm.Component.Validation.Context
public import Silmaril.Raw.Wasm.Component.Engine.Mock
public import Silmaril.Wasm.V1.ToCore.Types

/-!
# Instantiation-time runtime values and resolution of canonical immediates

The run-time index spaces of component instantiation (Explainer.md, "Index
Spaces" and "Instance Definitions") and the resolution of the index immediates of `canon`
definitions against them. There is no upstream function for this: the Python reference
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
receives already-resolved `CanonicalOptions` (L608-613), `ResourceType`s and core functions
in `canon_*`, `Store.lift` and `Store.lower`; the resolution step corresponds to wasmtime's
inliner (`crates/environ/src/component/translate/inline.rs` at wasmtime `a7b4f29`: the
`*Def` item values, `ExtractMemory`/`ExtractRealloc`/`ExtractPostReturn`/`ExtractCallback`,
and the import vector of `GlobalInitializer::InstantiateModule`).

Provided:

* (from `Instantiate/Items.lean`) `ItemVal E`, `Closure E`, `Frame E`: the value of each
  component index space at run time. Core entities are engine addresses/extern values; component
  functions are `FuncId`s; types are semantic types over resource-type identities
  `Types.TypeDef RtId E.ExternType`; a component is a closure over its enclosing frames
  (innermost first). `Frame.empty`, per-sort lookups (`coreFunc?`, ..., `component?`), the
  sort-indexed `Frame.size`/`Frame.get?`/`Frame.push` over `Entry E`, with `get?_push`,
  `size_push`, `get?_push_lt` and `get?_push_ne`.
* `resolveValType?`, `resolveDefValType?`, `resolveFuncType?`: syntactic value/function types
  to closed WIT types over `RtId` (a type index must denote a value type; the index of
  `own`/`borrow` must denote a resource type; a `map` key must resolve to a key primitive).
* `resolveOpts?`: `canonopt` lists to `CanonOpts E` (memory index → `E.MemAddr` via
  `coreMems` and `E.asMemory?`; realloc/post-return/callback → `E.FuncAddr`); a list with two
  options of the same kind (two string encodings count as the same kind) is rejected
  (`resolveOpts?_eq_none_of_not_nodup`, `nodup_of_resolveOpts?_eq_some`).
* `resolveBuiltin?`: `Syntax.Builtin` to `Runtime.ResolvedBuiltin E`, carrying exactly the
  `Runtime.ResolvedBuiltin` immediates; `resolveLift?`, `resolveLower?` for `canon lift`/`canon
  lower`.
* `coreImportsFor?`: the positional import vector of a core module (for each
  `(module, name, type)` of `E.importTypes m` in declaration order: the core-instance
  argument named `module`, its export `name`, whose type `E.externType?` must be an
  `E.ExternSub`-subtype of the declared type), with `coreImportsFor_length` and the
  relational characterisation `coreImportsFor?_eq_some_iff`.
* Resolution of instance and component types (Explainer.md, "Type Definitions" and
  "Declarators"): `resolveDefType?`, `resolveInstanceDecl(s)?`, `resolveComponentDecl(s)?` over
  the per-scope state `TyScope E` (local index spaces, ∀-binders and imports, ∃-binders and
  exports), `descEntity?` (the entity type of an `externdesc` and the binders it introduces)
  and `pushEntityType`. Binders are the reserved identities `binderVar k = ⟨binderBase + k⟩`
  with `binderBase = 2 ^ 32`; this assumes the store allocates fewer than `2 ^ 32` resource
  types (not proved). A standalone instance type used in import or export position is
  freshened and its binders hoisted to the enclosing scope (`freshenInstance`). Unsupported
  declarators (`alias export`/`alias core export` inside a type, 🪙 value descriptors) make
  resolution fail (`none`); callers fall back to an empty placeholder type
  (`Instantiate.staticType?`). `coreTypeSlots`: core type definitions as frame slots, one per
  recursion group member (core module types are inert placeholders).
* Run-time item typing: `itemEntity?`/`itemEntities`, the entity type of an item value
  (functions from their `CFuncInst`, types, instances of those); core modules and components
  are typed by sort only (empty placeholder types); 🪙 values and unallocated function ids are
  untyped (`none`) and dropped from instance types.
* Kernel tests (`Tests`): canonical-option, value-type, builtin and core-import resolution,
  and the type-resolution tests `instType_resolve`, `instType_func`, `instType_bad_outer` and
  `desc_freshen`.

Design notes:
* Fallible functions carry the `?` suffix (`resolveOpts?` and so on).
* `Frame.coreTypes` stores `Validation.CoreTypeSlot E.ExternType` (a Core 3.0 recursion group,
  or a core module type over the engine's extern types), mirroring the validation context:
  the engine interface has no translation of Core 3.0 syntax into `E.FuncType`.
  A recursion group occupies one slot per member (`coreTypeSlots`).
  `thread.new-indirect`'s expected type is read from the member's function type through
  `V1.FuncType.ofCore?` (flat signatures are `V1.FuncType`, as in `ResolvedBuiltin`).
* `coreImportsFor?` also takes the engine store (for `E.externType?`) and a decidability
  instance for `E.ExternSub`.
* `resolveBuiltin?` takes `rep : RtId → Option AddrType` (the representation type of a
  resource type lives in the `CStore`, see `CStore.resourceRep?`), since
  `ResolvedBuiltin.resourceNew`/`resourceRep` carry it.
* `Frame.push` takes an `Entry E` (the value of any sort) and fails on a sort mismatch:
  core functions, tables, memories and globals are checked with `E.asFunc?`-style accessors
  (the constructor for functions, `E.asTable?`/`E.asMemory?`/`E.asGlobal?` for the others);
  tags are not checked (the engine interface has no `asTag?`).
* A `map` key that is a type index naming a primitive key type is accepted (types are
  index-free, so `(type $k u8) (type (map $k u32))` is `map<u8, u32>`), as in
  `Validation/ValTypes.lean`; `Binary.md` says "if k is in `<keytype>`".

NOT modelled here: the instantiation program itself (`Instantiate/Defs.lean`), resource-type
allocation, validation of options against their use
site (which options a builtin admits, `realloc`/`callback` signatures) and of builtin
immediates beyond "the index denotes an entity of the right kind". Resolution success is not
claimed to coincide with validity.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine _root_.Silmaril.Wasm.Component.Runtime
open _root_.Silmaril.Wasm.Component.Validation (CoreTypeSlot)

variable {E : CoreEngine}

namespace Frame

/-! ### Lookups by index -/

variable (f : Frame E) (i : Nat)

end Frame

/-! ### Sort-indexed access -/

namespace Frame

/-- A successful push appends the entry at the old size of its sort. -/
theorem get?_push {f f' : Frame E} {s : Syntax.Sort_} {v : Entry E} (h : f.push s v = some f') :
    f'.get? s (f.size s) = some v := by
  rcases s with (_ | _ | _ | _ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
    rcases v with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) <;>
    simp only [push, reduceCtorEq, Option.some.injEq, Option.map_eq_some_iff] at h <;>
    (first | subst h | obtain ⟨_, _, rfl⟩ := h) <;>
    simp [get?, size, coreFunc?, coreTable?, coreMem?, coreGlobal?, coreTag?, coreType?,
      coreModule?, coreInstance?, func?, value?, type?, component?, instance?]

/-- A successful push grows its sort by one. -/
theorem size_push {f f' : Frame E} {s : Syntax.Sort_} {v : Entry E} (h : f.push s v = some f') :
    f'.size s = f.size s + 1 := by
  rcases s with (_ | _ | _ | _ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
    rcases v with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) <;>
    simp only [push, reduceCtorEq, Option.some.injEq, Option.map_eq_some_iff] at h <;>
    (first | subst h | obtain ⟨_, _, rfl⟩ := h) <;>
    simp [size]

/-- A push leaves the earlier entries of its sort unchanged. -/
theorem get?_push_lt {f f' : Frame E} {s : Syntax.Sort_} {v : Entry E} {i : Nat}
    (h : f.push s v = some f') (hi : i < f.size s) : f'.get? s i = f.get? s i := by
  rcases s with (_ | _ | _ | _ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
    rcases v with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) <;>
    simp only [push, reduceCtorEq, Option.some.injEq, Option.map_eq_some_iff] at h <;>
    (first | subst h | obtain ⟨_, _, rfl⟩ := h) <;>
    simp only [size] at hi <;>
    simp [get?, coreFunc?, coreTable?, coreMem?, coreGlobal?, coreTag?, coreType?,
      coreModule?, coreInstance?, func?, value?, type?, component?, instance?,
      List.getElem?_append_left hi]

/-- A push leaves every other sort unchanged. -/
theorem get?_push_ne {f f' : Frame E} {s t : Syntax.Sort_} {v : Entry E} (i : Nat)
    (h : f.push s v = some f') (hst : s ≠ t) : f'.get? t i = f.get? t i := by
  rcases s with (_ | _ | _ | _ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
    rcases v with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) <;>
    simp only [push, reduceCtorEq, Option.some.injEq, Option.map_eq_some_iff] at h <;>
    (first | subst h | obtain ⟨_, _, rfl⟩ := h) <;>
    rcases t with (_ | _ | _ | _ | _ | _ | _ | _) | _ | _ | _ | _ | _ <;>
    first
      | exact absurd rfl hst
      | rfl

end Frame

/-! ## Resolution of value and function types -/

/-! ## Canonical options -/

theorem resolveOpts?_eq_none_of_not_nodup (f : Frame E) {opts : List Syntax.CanonOpt}
    (h : ¬ (opts.map canonOptKind).Nodup) : resolveOpts? f opts = none := by
  simp [resolveOpts?, h]

/-- Duplicates are rejected: two options of the same kind make resolution fail. -/
theorem resolveOpts?_eq_none_of_dup (f : Frame E) {opts : List Syntax.CanonOpt}
    {a b : Syntax.CanonOpt} (hab : [a, b].Sublist opts) (hk : canonOptKind a = canonOptKind b) :
    resolveOpts? f opts = none := by
  apply resolveOpts?_eq_none_of_not_nodup
  intro hn
  have := (hn.sublist (hab.map canonOptKind))
  simp [hk] at this

theorem nodup_of_resolveOpts?_eq_some {f : Frame E} {opts : List Syntax.CanonOpt}
    {o : CanonOpts E} (h : resolveOpts? f opts = some o) : (opts.map canonOptKind).Nodup := by
  by_contra hn
  rw [resolveOpts?_eq_none_of_not_nodup f hn] at h
  cases h

/-! ## Canonical definitions -/

/-! ## Core instantiation arguments -/

section CoreImports

variable {H : Type} [∀ a b, Decidable (E.ExternSub a b)]

private theorem mapM_option_eq_some_iff {α β : Type} (g : α → Option β) :
    ∀ (l : List α) (r : List β),
      l.mapM g = some r ↔ List.Forall₂ (fun a b => g a = some b) l r
  | [], r => by cases r <;> simp
  | a :: l, r => by
    rw [List.mapM_cons]
    cases r with
    | nil => cases g a <;> cases l.mapM g <;> simp
    | cons c r =>
      rw [List.forall₂_cons, ← mapM_option_eq_some_iff g l r]
      cases g a <;> cases l.mapM g <;> simp

theorem coreImportFor?_eq_some_iff (s : E.Store H) (args : List (String × Nat)) (f : Frame E)
    (imp : String × String × E.ExternType) (v : E.ExternVal) :
    coreImportFor? s args f imp = some v ↔ CoreImportOk s args f imp v := by
  simp only [coreImportFor?, CoreImportOk, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨i, hi, exports, he, w, hw, τ, hτ, h⟩
    by_cases hs : E.ExternSub τ imp.2.2
    · simp only [hs, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨i, exports, τ, hi, he, hw, hτ, hs⟩
    · simp [hs] at h
  · rintro ⟨i, exports, τ, hi, he, hw, hτ, hs⟩
    exact ⟨i, hi, exports, he, v, hw, τ, hτ, by simp [hs]⟩

/-- `coreImportsFor?` succeeds exactly when every import, in order, is provided correctly. -/
theorem coreImportsFor?_eq_some_iff (s : E.Store H) (m : E.Module) (args : List (String × Nat))
    (f : Frame E) (vs : List E.ExternVal) :
    coreImportsFor? s m args f = some vs ↔
      List.Forall₂ (CoreImportOk s args f) (E.importTypes m) vs := by
  have hfun : (fun imp v => coreImportFor? s args f imp = some v) = CoreImportOk s args f :=
    funext fun imp => funext fun v => propext (coreImportFor?_eq_some_iff s args f imp v)
  rw [coreImportsFor?, mapM_option_eq_some_iff, hfun]

/-- The import vector has one value per declared import. -/
theorem coreImportsFor_length {s : E.Store H} {m : E.Module} {args : List (String × Nat)}
    {f : Frame E} {vs : List E.ExternVal} (h : coreImportsFor? s m args f = some vs) :
    vs.length = (E.importTypes m).length :=
  ((coreImportsFor?_eq_some_iff s m args f vs).1 h).length_eq.symm

end CoreImports

/-! ## Resolution of instance and component types -/

section TypeResolution

end TypeResolution

/-! ## Run-time types of item values -/

/-! ## Tests (Mock engine) -/

namespace Tests

open Engine.Mock

/-- The adder's `canon lift 0 [] 0`: no options, hence the default options (no memory). -/
theorem adder_resolveOpts : resolveOpts? adderFrame [] = some ({} : CanonOpts mock) := by
  decide +kernel

theorem adder_resolveFuncType : resolveFuncType? adderFrame adderSyntaxType = some adderType := by
  decide +kernel

theorem adder_resolveLift :
    (resolveLift? adderFrame 0 [] 0).map (fun p => (p.1, p.2.2)) =
      some (7, ({} : CanonOpts mock)) := by
  decide +kernel

theorem opts_full :
    resolveOpts? optFrame [.memory 0, .realloc 1, .encoding .utf16, .async_, .callback 0] =
      some ({ memory := some 3, realloc := some 11, encoding := .utf16
              async_ := true, callback := some 10 } : CanonOpts mock) := by
  decide +kernel

theorem opts_duplicate_encoding :
    resolveOpts? optFrame [.encoding .utf8, .encoding .utf16] = none := by decide +kernel

theorem opts_duplicate_memory : resolveOpts? optFrame [.memory 0, .memory 0] = none := by
  decide +kernel

/-- A memory index must denote a memory. -/
theorem opts_not_memory : resolveOpts? optFrame [.memory 1] = none := by decide +kernel

theorem valType_own : resolveDefValType? optFrame (.own 0) = some (.own ⟨5⟩) := by
  decide +kernel

/-- `own` of a non-resource type index fails. -/
theorem valType_own_bad : resolveDefValType? optFrame (.own 1) = none := by decide +kernel

/-- A type index in value position must denote a value type. -/
theorem valType_idx_resource : resolveValType? optFrame (.idx 0) = none := by decide +kernel

theorem valType_map :
    resolveDefValType? optFrame (.map (.prim .string) (.idx 2)) =
      some (.map .string (.prim .u32)) := by decide +kernel

theorem valType_map_float_key :
    resolveDefValType? optFrame (.map (.prim .f32) (.idx 2)) = none := by decide +kernel

theorem builtin_resourceNew :
    resolveBuiltin? (fun _ => some .i32) optFrame (.resourceNew 0) =
      some (.resourceNew ⟨5⟩ .i32) := by decide +kernel

theorem builtin_streamRead :
    resolveBuiltin? (fun _ => none) optFrame (.streamRead 1 [.async_, .memory 0]) =
      some (.streamRead (some (.prim .u8)) { memory := some 3, async_ := true }) := by
  decide +kernel

/-- A stream built-in on a non-stream type fails. -/
theorem builtin_streamNew_bad :
    resolveBuiltin? (fun _ => none) optFrame (.streamNew 2) = none := by decide +kernel

theorem builtin_wait :
    resolveBuiltin? (fun _ => none) optFrame (.waitableSetWait 0) =
      some (.waitableSetWait 3) := by decide +kernel

theorem builtin_threadNewIndirect :
    resolveBuiltin? (fun _ => none) optFrame (.threadNewIndirect 0 0) =
      some (.threadNewIndirect 2 ⟨[.i32], []⟩) := by decide +kernel

theorem imports_ok :
    coreImportsFor? importStore importer [("env", 0)] importFrame =
      some [.func 0, .memory 0] := by decide +kernel

/-- A missing instance argument fails. -/
theorem imports_missing_arg :
    coreImportsFor? importStore importer [("other", 0)] importFrame = none := by decide +kernel

/-- An export of the wrong type fails the `ExternSub` check. -/
theorem imports_type_mismatch :
    coreImportsFor? importStore importer [("env", 1)] importFrame = none := by decide +kernel

theorem push_coreFunc :
    ((Frame.empty : Frame mock).push (.core .func) (.coreFunc 4)).map (·.coreFuncs) =
      some [4] := by decide +kernel

theorem push_mismatch :
    ((Frame.empty : Frame mock).push .func (.coreFunc 4)).isNone = true := by decide +kernel

/-- A table extern pushed as a memory is rejected. -/
theorem push_table_as_memory :
    ((Frame.empty : Frame mock).push (.core .memory) (.coreExtern (.table 2))).isNone = true := by
  decide +kernel

theorem push_memory :
    ((Frame.empty : Frame mock).push (.core .memory) (.coreExtern (.memory 0))).map
      (·.coreMems.length) = some 1 := by decide +kernel

theorem instType_resolve :
    instShape (resolveDefType? [] adderFrame 0 (.instance_ instDecls)) =
      some ([binderVar 0], [("t", .type), ("f", .func)], 1) := by decide +kernel

/-- The exported function has the aliased outer type. -/
theorem instType_func :
    ((resolveDefType? [] adderFrame 0 (.instance_ instDecls)).bind fun
      | (.instance it, _) =>
        match it.exports.lookup "f" with
        | some (.func t) => some (decide (t = adderType))
        | _ => none
      | _ => none) = some true := by decide +kernel

/-- An outer alias past the enclosing frames fails. -/
theorem instType_bad_outer :
    instShape (resolveDefType? [] adderFrame 0 (.instance_ [.alias (.outer 2 0 .type)])) =
      none := by decide +kernel

/-- Using a standalone instance type in import position freshens and hoists its binder. -/
theorem desc_freshen :
    ((adderFrame.types ++ (resolveDefType? [] adderFrame 0 (.instance_ instDecls)).toList.map
        Prod.fst) |> fun ts =>
      (descEntity? ({ adderFrame with types := ts } : Frame mock) 5 (.instance_ 1)).map
        fun (e, bs, n) => (e.sort, bs, n)) =
      some (.instance, [binderVar 5], 6) := by decide +kernel

end Tests

end Silmaril.Wasm.Component.Instantiate
