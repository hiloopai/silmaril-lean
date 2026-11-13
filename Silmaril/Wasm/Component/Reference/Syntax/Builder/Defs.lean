module

public import Silmaril.Wasm.Component.Reference.Syntax.Basic.Defs
public import Silmaril.Wasm.Lime1.Modules

/-!
# A builder DSL for component definitions

Small, total helpers for writing example components compactly as `Component Lime1.Module`
(or `Component M` for any core module type `M`), together with `Component.nextIndex`, which
computes the next free index of every index space so that authors do not miscount indices.

The index-space bookkeeping transcribes `Explainer.md` §Index Spaces and `Binary.md` at
component-model revision `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Binary.md):
every definition appends to exactly one index space, and in particular

* `canon lift` defines a component `func`; `canon lower` and every canon builtin define a
  core `func`;
* an alias appends to the sort it names (`alias core export` to a core sort);
* an `import` appends to the sort of its descriptor, and **every export introduces a new
  index** of the exported sort (`Binary.md` §Import and Export Definitions, note 1);
* a core `type` definition that is a recursion group appends one core type per sub type
  (Core 3.0 `rectype`); a core module type appends one;
* 🪙 `start f args results` appends `results` values (`Binary.md` §Start Definitions), and
  🪙 `value` appends one value.

Definitions inside nested `component` definitions live in their own index spaces and are not
counted by the enclosing component's `nextIndex`.

Tests: `nextIndex` is checked by `rfl` on three examples assembled from `Explainer.md`
(§Component Definitions, §Instance Definitions, §Canonical ABI): the adder, the simple
async-callback component, and the two-component linking example. The examples are syntax only: no
validation or typing of them is claimed here. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Syntax

variable {M : Type}

/-! ## Value type shorthands -/

namespace VT

/-- `bool` as a value type. -/
abbrev bool : VT := .prim .bool
/-- `s8` as a value type. -/
abbrev s8 : VT := .prim .s8
/-- `u8` as a value type. -/
abbrev u8 : VT := .prim .u8
/-- `s16` as a value type. -/
abbrev s16 : VT := .prim .s16
/-- `u16` as a value type. -/
abbrev u16 : VT := .prim .u16
/-- `s32` as a value type. -/
abbrev s32 : VT := .prim .s32
/-- `u32` as a value type. -/
abbrev u32 : VT := .prim .u32
/-- `s64` as a value type. -/
abbrev s64 : VT := .prim .s64
/-- `u64` as a value type. -/
abbrev u64 : VT := .prim .u64
/-- `f32` as a value type. -/
abbrev f32 : VT := .prim .f32
/-- `f64` as a value type. -/
abbrev f64 : VT := .prim .f64
/-- `char` as a value type. -/
abbrev char : VT := .prim .char
/-- `string` as a value type. -/
abbrev string : VT := .prim .string
/-- 📝 `error-context` as a value type. -/
abbrev errorContext : VT := .prim .errorContext

end VT

/-! ## Sort-index shorthands -/

namespace SortIdx

/-- `(core func i)`. -/
abbrev coreFunc (i : Nat) : SortIdx CoreSort := ⟨.func, i⟩
/-- `(core table i)`. -/
abbrev coreTable (i : Nat) : SortIdx CoreSort := ⟨.table, i⟩
/-- `(core memory i)`. -/
abbrev coreMemory (i : Nat) : SortIdx CoreSort := ⟨.memory, i⟩
/-- `(core global i)`. -/
abbrev coreGlobal (i : Nat) : SortIdx CoreSort := ⟨.global, i⟩
/-- `(core tag i)`. -/
abbrev coreTag (i : Nat) : SortIdx CoreSort := ⟨.tag, i⟩
/-- `(func i)`. -/
abbrev func (i : Nat) : SortIdx Sort_ := ⟨.func, i⟩
/-- `(instance i)`. -/
abbrev instance_ (i : Nat) : SortIdx Sort_ := ⟨.instance_, i⟩
/-- `(type i)`. -/
abbrev type (i : Nat) : SortIdx Sort_ := ⟨.type, i⟩
/-- `(component i)`. -/
abbrev component (i : Nat) : SortIdx Sort_ := ⟨.component, i⟩
/-- `(core module i)`. -/
abbrev coreModule (i : Nat) : SortIdx Sort_ := ⟨.core .module_, i⟩

end SortIdx

/-! ## Type shorthands -/

/-- A sync component function type `(func (param "a" t)* (result t)?)`. -/
abbrev fnTy (params : List (String × VT)) (result : Option VT) : DefType :=
  .func { async_ := false, params, result }

/-- An async component function type `(func async (param "a" t)* (result t)?)`. -/
abbrev asyncFnTy (params : List (String × VT)) (result : Option VT) : DefType :=
  .func { async_ := true, params, result }

/-- `(type (func ...))`: defines the next component type index as a sync function type, e.g.
`funcT [("a", .u32), ("b", .u32)] (some .u32)`. -/
abbrev funcT (params : List (String × VT)) (result : Option VT) : Definition M :=
  .type (fnTy params result)

/-- `(type (func async ...))`: the async counterpart of `funcT`. -/
abbrev asyncFuncT (params : List (String × VT)) (result : Option VT) : Definition M :=
  .type (asyncFnTy params result)

/-- `(type (resource (rep rep) (dtor dtor)?))`: a resource type definition (`rep` is `i32`
by default; `i64` is 🐘). -/
abbrev resourceT (rep : Silmaril.Wasm.AddrType := .i32) (dtor : Option Nat := none) :
    Definition M :=
  .type (.resource rep dtor)

/-- `(type (instance decls))`: an instance type definition. -/
abbrev instanceT (decls : List InstanceDecl) : Definition M := .type (.instance_ decls)

/-- `(type (component decls))`: a component type definition. -/
abbrev componentT (decls : List ComponentDecl) : Definition M := .type (.component decls)

/-- `(export "name" (func i))` inside an instance or component type. -/
abbrev exportFuncDecl (name : String) (typeIdx : Nat) : InstanceDecl :=
  .export_ { name } (.func typeIdx)

/-! ## Instances and aliases -/

/-- `(core instance (instantiate m (with "name" (instance i))*))`. -/
abbrev coreInst (m : Nat) (args : List (String × Nat) := []) : Definition M :=
  .coreInstance (.instantiate m args)

/-- A synthetic core instance `(core instance (export "name" sortidx)*)`, e.g.
`synthCoreInstance [("task.return", .coreFunc 0)]`. -/
abbrev synthCoreInstance (items : List (String × SortIdx CoreSort)) : Definition M :=
  .coreInstance (.exports items)

/-- `(instance (instantiate c (with "name" sortidx)*))`. -/
abbrev instantiate (c : Nat) (args : List (String × SortIdx Sort_) := []) : Definition M :=
  .instance_ (.instantiate c args)

/-- A synthetic component instance `(instance (export "name" sortidx)*)`. -/
abbrev synthInstance (items : List (String × SortIdx Sort_)) : Definition M :=
  .instance_ (.exports (items.map fun (n, i) => ({ name := n }, i)))

/-- `(alias core export inst "name" (core s))`; `s` defaults to `func`. -/
abbrev aliasCoreExport (inst : Nat) (name : String) (s : CoreSort := .func) : Definition M :=
  .alias (.coreExport inst name s)

/-- `(alias export inst "name" (s))`; `s` defaults to `func`. -/
abbrev aliasExport (inst : Nat) (name : String) (s : Sort_ := .func) : Definition M :=
  .alias (.export_ inst name s)

/-- `(alias outer count idx (s))`. -/
abbrev aliasOuter (count idx : Nat) (s : Sort_) : Definition M :=
  .alias (.outer count idx s)

/-! ## Canonical definitions -/

/-- `(func (type ft) (canon lift (core func coreFunc) opts*))`. -/
abbrev liftFunc (coreFunc : Nat) (opts : List CanonOpt) (ft : Nat) : Definition M :=
  .canon (.lift coreFunc opts ft)

/-- `(core func (canon lower (func f) opts*))`. -/
abbrev lowerFunc (f : Nat) (opts : List CanonOpt := []) : Definition M :=
  .canon (.lower f opts)

/-- `(core func (canon b))` for a canon builtin `b`. -/
abbrev builtin (b : Builtin) : Definition M := .canon (.builtin b)

/-! ## Imports and exports -/

/-- `(import "name" desc)`. -/
abbrev importItem (name : String) (d : ExternDesc) : Definition M := .import_ { name } d

/-- `(import "name" (func (type typeIdx)))`. -/
abbrev importFunc (name : String) (typeIdx : Nat) : Definition M :=
  .import_ { name } (.func typeIdx)

/-- `(import "name" (instance (type typeIdx)))`. -/
abbrev importInstance (name : String) (typeIdx : Nat) : Definition M :=
  .import_ { name } (.instance_ typeIdx)

/-- `(import "name" (type (sub resource)))`. -/
abbrev importResource (name : String) : Definition M :=
  .import_ { name } (.type .subResource)

/-- `(export "name" (s idx))` with no type ascription. -/
abbrev exportItem (name : String) (item : SortIdx Sort_) : Definition M :=
  .export_ { name } item none

/-- `(export "name" (func idx))`. -/
abbrev exportFunc (name : String) (idx : Nat) : Definition M :=
  .export_ { name } ⟨.func, idx⟩ none

/-- `(export "name" (type idx))`. -/
abbrev exportType (name : String) (idx : Nat) : Definition M :=
  .export_ { name } ⟨.type, idx⟩ none

/-- `(export "name" (instance idx))`. -/
abbrev exportInstance (name : String) (idx : Nat) : Definition M :=
  .export_ { name } ⟨.instance_, idx⟩ none

/-! ## Index spaces -/

/-- The sort of the index space an `externtype` descriptor appends to. -/
def ExternDesc.sort : ExternDesc → Sort_
  | .coreModule _ => .core .module_
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance_ _ => .instance_

/-- The number of core type indices a `core:deftype` defines: one per sub type of a Core 3.0
recursion group, one for a module type. -/
def CoreTypeDef.count : CoreTypeDef → Nat
  | .rec_ t => t.types.length
  | .module_ _ => 1

/-- The index space a definition appends to (`Explainer.md` §Index Spaces). -/
def Definition.sort : Definition M → Sort_
  | .coreModule _ => .core .module_
  | .coreInstance _ => .core .instance_
  | .coreType _ => .core .type
  | .component _ => .component
  | .instance_ _ => .instance_
  | .alias (.export_ _ _ s) => s
  | .alias (.coreExport _ _ s) => .core s
  | .alias (.outer _ _ s) => s
  | .type _ => .type
  | .canon (.lift _ _ _) => .func
  | .canon (.lower _ _) => .core .func
  | .canon (.builtin _) => .core .func
  | .start _ _ _ => .value
  | .import_ _ d => d.sort
  | .export_ _ item _ => item.sort
  | .value _ _ => .value

/-- How many indices a definition appends to its index space `Definition.sort`. -/
def Definition.count : Definition M → Nat
  | .coreType t => t.count
  | .start _ _ results => results
  | _ => 1

/-- How many indices of sort `s` a definition appends. -/
def Definition.added (s : Sort_) (d : Definition M) : Nat :=
  if d.sort = s then d.count else 0

set_option linter.dupNamespace false in
/-- The next index of sort `s` after the definitions of `c` (equivalently, the size of the
`s` index space of `c`), counting indices created by imports, aliases and exports. Nested
components have their own index spaces and are not looked into. -/
def Component.nextIndex (s : Sort_) : Component M → Nat
  | [] => 0
  | d :: ds => d.added s + Component.nextIndex s ds

section NextIndex

set_option linter.dupNamespace false

@[simp] theorem Component.nextIndex_nil (s : Sort_) :
    Component.nextIndex s ([] : Component M) = 0 := rfl

@[simp] theorem Component.nextIndex_cons (s : Sort_) (d : Definition M) (c : Component M) :
    Component.nextIndex s (d :: c) = d.added s + Component.nextIndex s c := rfl

end NextIndex

/-! ## Examples (assembled from `Explainer.md`) -/

namespace BuilderExamples

/-- The adder (`Explainer.md` §Canonical ABI) over any core module `m` exporting `"add"`:
```wat
(component
  (core module $M ...)                                    ;; core module 0
  (core instance $m (instantiate $M))                     ;; core instance 0
  (func $add (param "a" u32) (param "b" u32) (result u32) ;; core func 0, type 0, func 0
    (canon lift (core func $m "add")))
  (export "add" (func $add)))                             ;; func 1
```
-/
def adder (m : M) : Component M :=
  [ .coreModule m
  , coreInst 0
  , aliasCoreExport 0 "add"
  , funcT [("a", .u32), ("b", .u32)] (some .u32)
  , liftFunc 0 [] 0
  , exportFunc "add" 0 ]

/-- The core module `(func (export "add") (param i32 i32) (result i32) (i32.add ...))` of the
adder, as a Lime1 module (no validity is claimed here). -/
def adderCore : Lime1.Module where
  types := [⟨[.i32, .i32], [.i32]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add]⟩]
  exports := [⟨"add", .func ⟨0⟩⟩]

/-- The adder as a `Component Lime1.Module`. -/
def adderLime1 : Component Lime1.Module := adder adderCore

/-- The simple async-callback component (`Explainer.md` §Canonical ABI and §`task.return`):
a `task.return` builtin fed to the core module through a synthetic core instance, and an async
lift with a callback. -/
def asyncRun (m : M) : Component M :=
  [ .coreModule m                                             -- core module 0
  , builtin (.taskReturn (some .u32) [])                      -- core func 0
  , synthCoreInstance [("task.return", .coreFunc 0)]          -- core instance 0
  , coreInst 0 [("", 0)]                                      -- core instance 1
  , aliasCoreExport 1 "run"                                   -- core func 1
  , aliasCoreExport 1 "cb"                                    -- core func 2
  , asyncFuncT [("x", .u32)] (some .u32)                      -- type 0
  , liftFunc 1 [.async_, .callback 2] 0                       -- func 0
  , exportFunc "run" 0 ]                                      -- func 1

/-- Component `$A` of the linking example: exports `foo` lifted from core function `f`. -/
def linkA (m : M) : Component M :=
  [ .coreModule m, coreInst 0, aliasCoreExport 0 "f", funcT [] (some .u32), liftFunc 0 [] 0
  , exportFunc "foo" 0 ]

/-- Component `$B` of the linking example: imports an instance exporting `foo`, lowers it,
feeds it to its core module and exports `bar`. -/
def linkB (n : M) : Component M :=
  [ instanceT [.type (fnTy [] (some .u32)), exportFuncDecl "foo" 0]  -- type 0
  , importInstance "a" 0                                            -- instance 0
  , aliasExport 0 "foo"                                             -- func 0
  , lowerFunc 0                                                     -- core func 0
  , .coreModule n                                                   -- core module 0
  , synthCoreInstance [("foo", .coreFunc 0)]                        -- core instance 0
  , coreInst 0 [("a", 0)]                                           -- core instance 1
  , aliasCoreExport 1 "g"                                           -- core func 1
  , funcT [] (some .u32)                                            -- type 1
  , liftFunc 1 [] 1                                                 -- func 1
  , exportFunc "bar" 1 ]                                            -- func 2

/-- The parent `$P` of the linking example (`Linking.md` lines 107–133). -/
def linkP (m n : M) : Component M :=
  [ .component (linkA m)                            -- component 0
  , .component (linkB n)                            -- component 1
  , instantiate 0                                   -- instance 0
  , instantiate 1 [("a", .instance_ 0)]             -- instance 1
  , aliasExport 1 "bar"                             -- func 0
  , exportFunc "bar" 0 ]                            -- func 1

end BuilderExamples

end Silmaril.Wasm.Component.Syntax
