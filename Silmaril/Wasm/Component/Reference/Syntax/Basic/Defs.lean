module

public import Silmaril.Wasm.Types
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs

/-!
# Component syntax: the index-based, core-parametric AST

The abstract syntax of a component as it stands after `flatten(sections)` of the binary format:
an ordered list of definitions that refer to earlier definitions by index. The AST transcribes
the grammar of `design/mvp/Binary.md` at component-model revision `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Binary.md),
§Component Definitions, §Instance Definitions, §Alias Definitions, §Type Definitions,
§Canonical Definitions, §🪙 Start Definitions, §Import and Export Definitions and §🪙 Value
Definitions, with the prose of `Explainer.md` at the same revision.

It is parametric in the core module type `M`, so `Component Lime1.Module`,
`Component V1.Module` and `Component Silmaril.Wasm.Module` are all instances; `Component.map`
embeds one into another, and `Component.coreModules` lists every (nested) core module in order.
Core *types* that occur inside components (core module types, the `core:rectype` definitions,
the function type of `thread.new-indirect`) always use the Core 3.0 syntax
`Silmaril.Wasm.RecType` / `Silmaril.Wasm.ExternType`; profiles restrict them later.

| Lean | `Binary.md` production |
| --- | --- |
| `CoreSort`, `Sort_`, `SortIdx` | `core:sort`, `sort`, `sortidx`, `core:sortidx` |
| `CoreInstanceExpr`, `InstanceExpr` | `core:instanceexpr`, `instanceexpr` |
| `Alias` | `alias` |
| `CoreModuleDecl`, `CoreTypeDef` | `core:moduledecl`, `core:deftype` |
| `Prim`, `VT`, `DefValType` | `primvaltype`, `valtype`, `defvaltype` |
| `FuncType`, `TypeBound`, `ValueBound` | `functype`, `typebound`, `valuebound` |
| `ExternDesc` | `externtype` |
| `DefType` | `deftype`, including `resourcetype` |
| `InstanceDecl`, `ComponentDecl` | `instancedecl`, `componentdecl` |
| `Attribute`, `ExternName` | `attribute`, `nameattributes` |
| `CanonOpt`, `Builtin`, `Canon` | `canonopt`, `canon` |
| `Definition`, `Component` | `definition` (Explainer §Component Definitions), `component` |

Representation choices (not claims about the binary format):
* Keywords are suffixed with `_` (`Sort_`, `module_`, `instance_`, `import_`, `export_`,
  `async_`, `rec_`); `Sort` itself is a Lean keyword, hence `Sort_`.
* Binary-only warts are dropped: the duplicate `0x00`/`0x01` forms of `nameattributes`, the
  `0x00` prefix of a non-final `sub` core type (it is an ordinary one-element `RecType`), the
  `0x00` sort byte of `canon lift`/`lower`, and the reserved `0x00` byte of `thread.yield`,
  `thread.suspend` and `thread.*-then-*`. `waitable-set.wait`/`poll` keep only their memory
  index. Custom sections and the name section are not represented.
* `canonopt` string encodings reuse `ABI.StringEncoding` (the runtime's type).
* `resourcetype`'s `rep` core value type is an `AddrType` (`i32`, or `i64` under 🐘), as are the
  core value types of `context.get`/`context.set`; other core value types are not
  representable there.
* 🪙 `value` definitions carry their type and the opaque binary payload `val(t)` (bytes).
* `stream.read`/`write` and `future.read`/`write` carry the full `opts`; whether they are sync
  or async is the presence of the `async` option (sync forms are gated by 🚝).

Not modelled: text format sugar and identifiers, binary decoding, the 🧵② builtins
`thread.spawn-ref`, `thread.spawn-indirect`, `thread.available-parallelism`, and 🪺 is only
present as far as names are strings. No well-formedness or validation is claimed here: every
side condition of `Binary.md` (non-empty records, `flags` bound, `fixedList` length > 0,
option compatibility, index ranges, ...) belongs to validation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Syntax

/-! ## Sorts and indices -/

/-- `core:sort`: the core index spaces, plus `module` and `instance`. -/
inductive CoreSort where
  | func | table | memory | global | tag | type | module_ | instance_
  deriving Repr, DecidableEq

/-- `sort`: `core cs`, or one of the five component-level index spaces. -/
inductive Sort_ where
  | core (s : CoreSort)
  | func | value | type | component | instance_
  deriving Repr, DecidableEq

/-- `sortidx` / `core:sortidx`: an index into the index space of the given sort. -/
structure SortIdx (S : Type) where
  sort : S
  idx : Nat
  deriving Repr, DecidableEq

/-! ## Instances and aliases -/

/-- `core:instanceexpr`. `instantiate m args`: each argument names a core instance (the only
sort `core:instantiatearg` allows); `exports`: an inline-export ("synthetic") instance. -/
inductive CoreInstanceExpr where
  | instantiate (module : Nat) (args : List (String × Nat))
  | exports (items : List (String × SortIdx CoreSort))
  deriving Repr, DecidableEq

/-- `alias`: export aliases of component or core instances, and de Bruijn outer aliases
(`count` enclosing scopes outward; `s` must be an `outeraliassort`, checked by validation). -/
inductive Alias where
  | export_ (inst : Nat) (name : String) (s : Sort_)
  | coreExport (inst : Nat) (name : String) (s : CoreSort)
  | outer (count idx : Nat) (s : Sort_)
  deriving Repr, DecidableEq

/-! ## Names -/

/-- `attribute` of `nameattributes` (🏷️ / 🔗). Attributes are ignored by type checking. -/
inductive Attribute where
  | implements (interface : String)
  | versionSuffix (suffix : String)
  | externalId (id : String)
  deriving Repr, DecidableEq

/-- `nameattributes`: an `externname` with its attributes. The spelling of `name` is checked
by `Names.lean` (`ExternName.kind`). -/
structure ExternName where
  name : String
  attrs : List Attribute := []
  deriving Repr, DecidableEq

/-- `InstanceExpr` arguments and inline exports; arguments may be of any sort. -/
inductive InstanceExpr where
  | instantiate (component : Nat) (args : List (String × SortIdx Sort_))
  | exports (items : List (ExternName × SortIdx Sort_))
  deriving Repr, DecidableEq

/-! ## Core types -/

/-- `core:moduledecl`. Core `import`s use the core-spec `(module, name)` pair; the only core
alias form is `(alias outer ct idx (type))`. -/
inductive CoreModuleDecl where
  | import_ (module name : String) (ty : Silmaril.Wasm.ExternType)
  | type (t : Silmaril.Wasm.RecType)
  | aliasOuter (count idx : Nat)
  | export_ (name : String) (ty : Silmaril.Wasm.ExternType)
  deriving Repr, DecidableEq

/-- `core:deftype`: a Core 3.0 recursion group, or a core module type. -/
inductive CoreTypeDef where
  | rec_ (t : Silmaril.Wasm.RecType)
  | module_ (decls : List CoreModuleDecl)
  deriving Repr, DecidableEq

/-! ## Component types -/

/-- `primvaltype` (`errorContext` is 📝). -/
inductive Prim where
  | bool | s8 | u8 | s16 | u16 | s32 | u32 | s64 | u64 | f32 | f64 | char | string
  | errorContext
  deriving Repr, DecidableEq

/-- `valtype`: a primitive, or a type index that validation requires to name a `defvaltype`. -/
inductive VT where
  | prim (p : Prim)
  | idx (i : Nat)
  deriving Repr, DecidableEq

/-- `defvaltype`. `fixedList` is 🔧, `stream`/`future` 🔀, `map` 🗺️. `own`/`borrow` carry the
type index of a resource type. -/
inductive DefValType where
  | prim (p : Prim)
  | record (fields : List (String × VT))
  | variant (cases : List (String × Option VT))
  | list (t : VT)
  | fixedList (t : VT) (len : Nat)
  | tuple (ts : List VT)
  | flags (labels : List String)
  | enum (labels : List String)
  | option (t : VT)
  | result (ok err : Option VT)
  | map (k v : VT)
  | own (r : Nat)
  | borrow (r : Nat)
  | stream (t : Option VT)
  | future (t : Option VT)
  deriving Repr, DecidableEq

/-- `functype`: `0x40` (sync) or `0x43` (`async_ = true`), named params, at most one result. -/
structure FuncType where
  async_ : Bool := false
  params : List (String × VT)
  result : Option VT
  deriving Repr, DecidableEq

/-- `typebound`: `(eq i)` or `(sub resource)`. -/
inductive TypeBound where
  | eq (i : Nat)
  | subResource
  deriving Repr, DecidableEq

/-- 🪙 `valuebound`: `(eq i)` of a value index, or a value type. -/
inductive ValueBound where
  | eq (i : Nat)
  | type (t : VT)
  deriving Repr, DecidableEq

/-- `externtype` (the `importdecl` / `exportdecl` descriptor). -/
inductive ExternDesc where
  | coreModule (coreTypeIdx : Nat)
  | func (typeIdx : Nat)
  | value (b : ValueBound)
  | type (b : TypeBound)
  | component (typeIdx : Nat)
  | instance_ (typeIdx : Nat)
  deriving Repr, DecidableEq

mutual

/-- `deftype`. `resource rep dtor`: `rep` is `i32` (or 🐘 `i64`), `dtor` a core function
index. -/
inductive DefType where
  | val (t : DefValType)
  | func (t : FuncType)
  | component (decls : List ComponentDecl)
  | instance_ (decls : List InstanceDecl)
  | resource (rep : Silmaril.Wasm.AddrType) (dtor : Option Nat)

/-- `instancedecl`. -/
inductive InstanceDecl where
  | coreType (t : CoreTypeDef)
  | type (t : DefType)
  | alias (a : Alias)
  | export_ (n : ExternName) (d : ExternDesc)

/-- `componentdecl`: an `importdecl`, or an `instancedecl`. -/
inductive ComponentDecl where
  | import_ (n : ExternName) (d : ExternDesc)
  | decl (d : InstanceDecl)

end

deriving instance Repr for DefType, InstanceDecl, ComponentDecl

/-! The deriving handler does not support nested inductives, so decidable equality of the
declarator types (and of `Definition` below) goes through a structural Boolean equality, which
reduces in the kernel, and its correctness proof. -/

mutual

/-- Structural Boolean equality of `DefType`s. -/
def DefType.beq : DefType → DefType → Bool
  | .val a, .val b => decide (a = b)
  | .func a, .func b => decide (a = b)
  | .component a, .component b => ComponentDecl.beqList a b
  | .instance_ a, .instance_ b => InstanceDecl.beqList a b
  | .resource r d, .resource r' d' => decide (r = r') && decide (d = d')
  | _, _ => false
  termination_by structural a _ => a

/-- Structural Boolean equality of `InstanceDecl`s. -/
def InstanceDecl.beq : InstanceDecl → InstanceDecl → Bool
  | .coreType a, .coreType b => decide (a = b)
  | .type a, .type b => DefType.beq a b
  | .alias a, .alias b => decide (a = b)
  | .export_ n d, .export_ n' d' => decide (n = n') && decide (d = d')
  | _, _ => false
  termination_by structural a _ => a

/-- Structural Boolean equality of `ComponentDecl`s. -/
def ComponentDecl.beq : ComponentDecl → ComponentDecl → Bool
  | .import_ n d, .import_ n' d' => decide (n = n') && decide (d = d')
  | .decl a, .decl b => InstanceDecl.beq a b
  | _, _ => false
  termination_by structural a _ => a

/-- `InstanceDecl.beq` on lists. -/
def InstanceDecl.beqList : List InstanceDecl → List InstanceDecl → Bool
  | [], [] => true
  | x :: xs, y :: ys => InstanceDecl.beq x y && InstanceDecl.beqList xs ys
  | _, _ => false
  termination_by structural a _ => a

/-- `ComponentDecl.beq` on lists. -/
def ComponentDecl.beqList : List ComponentDecl → List ComponentDecl → Bool
  | [], [] => true
  | x :: xs, y :: ys => ComponentDecl.beq x y && ComponentDecl.beqList xs ys
  | _, _ => false
  termination_by structural a _ => a

end

mutual

theorem DefType.beq_refl : (a : DefType) → a.beq a = true
  | .val _ | .func _ | .resource _ _ => by simp only [DefType.beq, decide_true, Bool.and_self]
  | .component ds => by rw [DefType.beq]; exact ComponentDecl.beqList_refl ds
  | .instance_ ds => by rw [DefType.beq]; exact InstanceDecl.beqList_refl ds

theorem InstanceDecl.beq_refl : (a : InstanceDecl) → a.beq a = true
  | .coreType _ | .alias _ | .export_ _ _ => by
    simp only [InstanceDecl.beq, decide_true, Bool.and_self]
  | .type t => by rw [InstanceDecl.beq]; exact DefType.beq_refl t

theorem ComponentDecl.beq_refl : (a : ComponentDecl) → a.beq a = true
  | .import_ _ _ => by simp only [ComponentDecl.beq, decide_true, Bool.and_self]
  | .decl d => by rw [ComponentDecl.beq]; exact InstanceDecl.beq_refl d

theorem InstanceDecl.beqList_refl : (a : List InstanceDecl) → InstanceDecl.beqList a a = true
  | [] => rfl
  | d :: ds => by
    rw [InstanceDecl.beqList, InstanceDecl.beq_refl d, InstanceDecl.beqList_refl ds]; rfl

theorem ComponentDecl.beqList_refl : (a : List ComponentDecl) → ComponentDecl.beqList a a = true
  | [] => rfl
  | d :: ds => by
    rw [ComponentDecl.beqList, ComponentDecl.beq_refl d, ComponentDecl.beqList_refl ds]; rfl

end

mutual

theorem DefType.eq_of_beq : (a b : DefType) → a.beq b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp only [DefType.beq, decide_eq_true_eq, Bool.and_eq_true] at h
    all_goals first
      | rw [ComponentDecl.eq_of_beqList _ _ h]
      | rw [InstanceDecl.eq_of_beqList _ _ h]
      | simp_all
  termination_by a => sizeOf a

theorem InstanceDecl.eq_of_beq : (a b : InstanceDecl) → a.beq b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp only [InstanceDecl.beq, decide_eq_true_eq, Bool.and_eq_true] at h
    all_goals first
      | rw [DefType.eq_of_beq _ _ h]
      | simp_all
  termination_by a => sizeOf a

theorem ComponentDecl.eq_of_beq : (a b : ComponentDecl) → a.beq b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;>
      simp only [ComponentDecl.beq, decide_eq_true_eq, Bool.and_eq_true] at h
    all_goals first
      | rw [InstanceDecl.eq_of_beq _ _ h]
      | simp_all
  termination_by a => sizeOf a

theorem InstanceDecl.eq_of_beqList :
    (a b : List InstanceDecl) → InstanceDecl.beqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [InstanceDecl.beqList, Bool.and_eq_true] at h
    rw [InstanceDecl.eq_of_beq x y h.1, InstanceDecl.eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [InstanceDecl.beqList] at h
  termination_by a => sizeOf a

theorem ComponentDecl.eq_of_beqList :
    (a b : List ComponentDecl) → ComponentDecl.beqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [ComponentDecl.beqList, Bool.and_eq_true] at h
    rw [ComponentDecl.eq_of_beq x y h.1, ComponentDecl.eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ComponentDecl.beqList] at h
  termination_by a => sizeOf a

end

instance : DecidableEq DefType := fun a b =>
  decidable_of_iff (a.beq b = true) ⟨DefType.eq_of_beq a b, fun h => h ▸ DefType.beq_refl a⟩

instance : DecidableEq InstanceDecl := fun a b =>
  decidable_of_iff (a.beq b = true)
    ⟨InstanceDecl.eq_of_beq a b, fun h => h ▸ InstanceDecl.beq_refl a⟩

instance : DecidableEq ComponentDecl := fun a b =>
  decidable_of_iff (a.beq b = true)
    ⟨ComponentDecl.eq_of_beq a b, fun h => h ▸ ComponentDecl.beq_refl a⟩

/-! ## Canonical definitions -/

/-- `canonopt`. Validation (not this AST) rejects duplicates and conflicts. -/
inductive CanonOpt where
  | encoding (e : ABI.StringEncoding)
  | memory (i : Nat)
  | realloc (i : Nat)
  | postReturn (i : Nat)
  | async_
  | callback (i : Nat)
  deriving Repr, DecidableEq

/-- The builtins of `canon` (`Binary.md` §Canonical Definitions), every immediate explicit.
Type immediates `t` are component type indices; `mem` a core memory index; `coreType` and
`table` of `threadNewIndirect` are a core type and a core table index. The 🧵② builtins are
omitted. -/
inductive Builtin where
  | resourceNew (rt : Nat)
  | resourceDrop (rt : Nat)
  | resourceRep (rt : Nat)
  | backpressureInc
  | backpressureDec
  | taskReturn (result : Option VT) (opts : List CanonOpt)
  | taskCancel
  | contextGet (t : Silmaril.Wasm.AddrType) (i : Nat)
  | contextSet (t : Silmaril.Wasm.AddrType) (i : Nat)
  | subtaskCancel (async_ : Bool)
  | subtaskDrop
  | streamNew (t : Nat)
  | streamRead (t : Nat) (opts : List CanonOpt)
  | streamWrite (t : Nat) (opts : List CanonOpt)
  | streamCancelRead (t : Nat) (async_ : Bool)
  | streamCancelWrite (t : Nat) (async_ : Bool)
  | streamDropReadable (t : Nat)
  | streamDropWritable (t : Nat)
  | streamForward (t : Nat)
  | futureNew (t : Nat)
  | futureRead (t : Nat) (opts : List CanonOpt)
  | futureWrite (t : Nat) (opts : List CanonOpt)
  | futureCancelRead (t : Nat) (async_ : Bool)
  | futureCancelWrite (t : Nat) (async_ : Bool)
  | futureDropReadable (t : Nat)
  | futureDropWritable (t : Nat)
  | futureForward (t : Nat)
  | errorContextNew (opts : List CanonOpt)
  | errorContextDebugMessage (opts : List CanonOpt)
  | errorContextDrop
  | waitableSetNew
  | waitableSetWait (mem : Nat)
  | waitableSetPoll (mem : Nat)
  | waitableSetDrop
  | waitableJoin
  | threadIndex
  | threadNewIndirect (coreType table : Nat)
  | threadResumeLater
  | threadSuspend
  | threadYield
  | threadSuspendThenResume
  | threadYieldThenResume
  | threadSuspendThenPromote
  | threadYieldThenPromote
  deriving Repr, DecidableEq

/-- `canon`: `lift` of a core function at a component function type index, `lower` of a
component function, or a builtin. -/
inductive Canon where
  | lift (coreFunc : Nat) (opts : List CanonOpt) (funcType : Nat)
  | lower (func : Nat) (opts : List CanonOpt)
  | builtin (b : Builtin)
  deriving Repr, DecidableEq

/-! ## Definitions and components -/

/-- A component `definition` over core modules `M`. Components nest (`component`). `start` and
`value` are 🪙-gated: `start f args results` is `start f (value arg)* (result (value))^results`,
and `value t payload` carries the opaque binary payload `val(t)`. `export_` has an optional type
ascription. -/
inductive Definition (M : Type) where
  | coreModule (m : M)
  | coreInstance (e : CoreInstanceExpr)
  | coreType (t : CoreTypeDef)
  | component (defs : List (Definition M))
  | instance_ (e : InstanceExpr)
  | alias (a : Alias)
  | type (t : DefType)
  | canon (c : Canon)
  | start (f : Nat) (args : List Nat) (results : Nat)
  | import_ (n : ExternName) (d : ExternDesc)
  | export_ (n : ExternName) (item : SortIdx Sort_) (ascribed : Option ExternDesc)
  | value (t : VT) (payload : List UInt8)
  deriving Repr

set_option linter.dupNamespace false in
/-- A component is its flattened list of definitions. -/
abbrev Component (M : Type) := List (Definition M)

variable {M N P : Type}

section DecEq

variable [DecidableEq M]

mutual

/-- Structural Boolean equality of definitions. -/
def Definition.beq : Definition M → Definition M → Bool
  | .coreModule a, .coreModule b => decide (a = b)
  | .coreInstance a, .coreInstance b => decide (a = b)
  | .coreType a, .coreType b => decide (a = b)
  | .component a, .component b => Definition.beqList a b
  | .instance_ a, .instance_ b => decide (a = b)
  | .alias a, .alias b => decide (a = b)
  | .type a, .type b => decide (a = b)
  | .canon a, .canon b => decide (a = b)
  | .start f a r, .start f' a' r' => decide (f = f') && decide (a = a') && decide (r = r')
  | .import_ n d, .import_ n' d' => decide (n = n') && decide (d = d')
  | .export_ n i a, .export_ n' i' a' => decide (n = n') && decide (i = i') && decide (a = a')
  | .value t p, .value t' p' => decide (t = t') && decide (p = p')
  | _, _ => false
  termination_by structural a _ => a

/-- `Definition.beq` on lists. -/
def Definition.beqList : List (Definition M) → List (Definition M) → Bool
  | [], [] => true
  | x :: xs, y :: ys => Definition.beq x y && Definition.beqList xs ys
  | _, _ => false
  termination_by structural a _ => a

end

mutual

theorem Definition.beq_refl : (a : Definition M) → a.beq a = true
  | .component ds => by rw [Definition.beq]; exact Definition.beqList_refl ds
  | .coreModule _ | .coreInstance _ | .coreType _ | .instance_ _ | .alias _ | .type _
  | .canon _ | .start _ _ _ | .import_ _ _ | .export_ _ _ _ | .value _ _ => by
    simp only [Definition.beq, decide_true, Bool.and_self]

theorem Definition.beqList_refl : (a : List (Definition M)) → Definition.beqList a a = true
  | [] => rfl
  | d :: ds => by
    rw [Definition.beqList, Definition.beq_refl d, Definition.beqList_refl ds]; rfl

end

mutual

theorem Definition.eq_of_beq : (a b : Definition M) → a.beq b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp only [Definition.beq, decide_eq_true_eq, Bool.and_eq_true] at h
    all_goals first
      | rw [Definition.eq_of_beqList _ _ h]
      | simp_all
  termination_by a => sizeOf a

theorem Definition.eq_of_beqList :
    (a b : List (Definition M)) → Definition.beqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [Definition.beqList, Bool.and_eq_true] at h
    rw [Definition.eq_of_beq x y h.1, Definition.eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Definition.beqList] at h
  termination_by a => sizeOf a

end

instance : DecidableEq (Definition M) := fun a b =>
  decidable_of_iff (a.beq b = true)
    ⟨Definition.eq_of_beq a b, fun h => h ▸ Definition.beq_refl a⟩

end DecEq

/-! ## Changing the core module type -/

mutual

/-- Replace every core module, including those of nested components. -/
def Definition.map (f : M → N) : Definition M → Definition N
  | .coreModule m => .coreModule (f m)
  | .coreInstance e => .coreInstance e
  | .coreType t => .coreType t
  | .component defs => .component (Definition.mapList f defs)
  | .instance_ e => .instance_ e
  | .alias a => .alias a
  | .type t => .type t
  | .canon c => .canon c
  | .start g args results => .start g args results
  | .import_ n d => .import_ n d
  | .export_ n item ascribed => .export_ n item ascribed
  | .value t payload => .value t payload
  termination_by structural d => d

/-- `Definition.map` on a list (structural helper; equal to `List.map`). -/
def Definition.mapList (f : M → N) : List (Definition M) → List (Definition N)
  | [] => []
  | d :: ds => Definition.map f d :: Definition.mapList f ds
  termination_by structural ds => ds

end

set_option linter.dupNamespace false in
/-- Change the core module type of a component (e.g. the `V1 → Lime1 → Core 3.0`
embeddings). -/
def Component.map (f : M → N) (c : Component M) : Component N := Definition.mapList f c

mutual

/-- The core modules of a definition, including those of nested components, in order. -/
def Definition.coreModules : Definition M → List M
  | .coreModule m => [m]
  | .component defs => Definition.coreModulesList defs
  | _ => []
  termination_by structural d => d

/-- `Definition.coreModules` of a list, concatenated in order. -/
def Definition.coreModulesList : List (Definition M) → List M
  | [] => []
  | d :: ds => Definition.coreModules d ++ Definition.coreModulesList ds
  termination_by structural ds => ds

end

set_option linter.dupNamespace false in
/-- Every core module of a component, including those of nested components, in definition
order. -/
def Component.coreModules (c : Component M) : List M := Definition.coreModulesList c

mutual

theorem Definition.map_id : (d : Definition M) → Definition.map id d = d
  | .coreModule _ | .coreInstance _ | .coreType _ | .instance_ _ | .alias _ | .type _
  | .canon _ | .start _ _ _ | .import_ _ _ | .export_ _ _ _ | .value _ _ => rfl
  | .component defs => by rw [Definition.map, Definition.mapList_id defs]

theorem Definition.mapList_id : (ds : List (Definition M)) → Definition.mapList id ds = ds
  | [] => rfl
  | d :: ds => by rw [Definition.mapList, Definition.map_id d, Definition.mapList_id ds]

end

mutual

theorem Definition.coreModules_map (f : M → N) :
    (d : Definition M) → (Definition.map f d).coreModules = d.coreModules.map f
  | .coreModule _ => rfl
  | .coreInstance _ | .coreType _ | .instance_ _ | .alias _ | .type _
  | .canon _ | .start _ _ _ | .import_ _ _ | .export_ _ _ _ | .value _ _ => rfl
  | .component defs => by
    simp only [Definition.map, Definition.coreModules, Definition.coreModulesList_mapList f defs]

theorem Definition.coreModulesList_mapList (f : M → N) :
    (ds : List (Definition M)) →
      Definition.coreModulesList (Definition.mapList f ds) =
        (Definition.coreModulesList ds).map f
  | [] => rfl
  | d :: ds => by
    simp only [Definition.mapList, Definition.coreModulesList, List.map_append,
      Definition.coreModules_map f d, Definition.coreModulesList_mapList f ds]

end

set_option linter.dupNamespace false in
@[simp] theorem Component.map_id (c : Component M) : Component.map id c = c :=
  Definition.mapList_id c

set_option linter.dupNamespace false in
@[simp] theorem Component.coreModules_map (f : M → N) (c : Component M) :
    (Component.map f c).coreModules = c.coreModules.map f :=
  Definition.coreModulesList_mapList f c

set_option linter.dupNamespace false in
@[simp] theorem Component.coreModules_nil : Component.coreModules ([] : Component M) = [] := rfl

set_option linter.dupNamespace false in
@[simp] theorem Component.coreModules_cons (d : Definition M) (c : Component M) :
    Component.coreModules (d :: c) = d.coreModules ++ Component.coreModules c := rfl

end Silmaril.Wasm.Component.Syntax
