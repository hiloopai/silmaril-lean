module

public import Silmaril.Wasm.V2.ToCore.Instructions
public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Validation.Check.ModuleCompleteWf
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# Wasm 2.0 modules as Core 3.0 syntax

The module half of the `2.0 ⊆ 3.0` subset theorem. `Module.toCore` injects the
Wasm 2.0 module syntax of `Silmaril.Wasm.V2.Modules` (`1-syntax:538-568`) into
the Core 3.0 source syntax of `Silmaril.Wasm.Modules`, `Module.ofCore?` retracts
it, and injectivity follows. Types, imports, exports and instruction immediates
are already handled by `Silmaril/Wasm/V2/ToCore/Types.lean`
(`FuncType.toCoreRec`, `Import.toCore`, `Export.toCore`, `ExternIdx.toCore`,
`TableType.toCore`, `MemoryType.toCore`, `GlobalType.toCore`) and
`Silmaril/Wasm/V2/ToCore/Instructions.lean` (`Instr.toCore`, `Expr.toCore`);
this file only adds the declaration sorts: `func`, `global`, `table`,
`elemmode`, `elem`, `datamode`, `data`, `module`. **`Import` and `Export` are
*not* redefined here**; they live in `ToCore/Types.lean` because `Import.toCore`
is the `ImportDesc`/`ExternType` map and belongs with the type injections.

Line references `1-syntax:NN`, `9-module:NN` and `A-binary:NN` point into
`specification/wasm-2.0/*.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (hash-pinned in
`specs/wasm/core-2.0.json`) and were re-checked with `cat -n`; `5.4:NN` points
into the pinned Core 3.0 `5.4-binary.modules.spectec`.

## Everything is `Option`-valued

`V2.Instr.toCore` is partial — `CVTOP numtype_1 numtype_2 cvtop` (`1-syntax:437`)
is untyped in 2.0 and 111 of its 144 immediate triples denote no Core 3.0
`ConvertOp`; see the module docstring of `ToCore/Instructions.lean`. (The count:
`V2.CvtOp` has twelve values — eight constructors, four of which carry a
`Signedness` — and there are four number types, so with the grammar's side
condition `numtype_1 =/= numtype_2` there are `12 * 12 = 144` well-formed
immediate triples; `V2.CvtOp.toShared` has an equation for `33` of them, namely
`2` extends, `1` wrap, `8` converts, `8` truncs, `8` saturating truncs, `1`
promote, `1` demote and `4` reinterprets, leaving `111` undefined.) Expressions
occur in `func`, `global`, `elem` and `data`, so every declaration-level
injection inherits the `Option`, and so does `Module.toCore`. The retraction and
injectivity statements are therefore conditioned on definedness, exactly as
`Instr.toCore_injective` is:

```
theorem Module.toCore_injective {m n : Module} {c : Wasm.Module}
    (hm : m.toCore = some c) (hn : n.toCore = some c) : m = n
```

`Function.Injective Module.toCore` is *false* for the `Option`-valued map (two
different modules with different ill-formed `CVTOP`s both go to `none`), so this
conditional form is the strongest true statement.

## Tables get their implicit null initializer

Core 3.0 tables carry an initializer expression, `table ::= TABLE tabletype expr`
(`1.4-syntax.modules:22`). Wasm 2.0 tables do not: `table ::= TABLE tabletype`
(`1-syntax:549`), and `$alloctable(s, [i .. j?] rt)` fills the table with
`(REF.NULL rt)^i` (`9-module:58`). `TableType.toCoreTable` therefore emits
`[REF.NULL $heap(rt)]` — the null of the table's **own** element type, not
always `func`.

This differs from `Lime1.tableToCore` and `V1.TableType.toCoreTable`
(`Lime1/ToCore/Modules.lean:35`, `V1/ToCore.lean`), which hard-code
`[.refNull (.abstract .func)]`: in those profiles every table is a `funcref`
table, so the two agree there. Wasm 2.0 has `externref` tables, for which
`[.refNull (.abstract .func)]` would not even validate (`ref.null func` has type
`(ref null func)`, which is not a subtype of `externref`), so the element type
must be threaded. `TableType.ofCoreTable?` accepts exactly the matching null.

## The `funcref` / `(ref func)` split: binary-faithful embedding

the version-compatibility goal. The Core 3.0 *binary* decoder gives the
function-index element forms a **non-nullable** `(ref func)`, while a
*syntax-level* 2.0 → 3.0 injection has to give them `funcref = (ref null func)`,
because that is what the 2.0 abstract syntax says. Concretely, the pinned
grammars:

| kind | 2.0 `Belem` (`A-binary:860-876`) | 3.0 `Belem` (`5.4:100-116`) |
|------|----------------------------------|------------------------------|
| `0` `e y*`              | `ELEM FUNCREF (REF.FUNC y)* (ACTIVE 0 e)` | `ELEM (REF FUNC) …` |
| `1` `rt y*`             | `Belemkind: 0x00 => FUNCREF`              | `Belemkind: 0x00 => REF FUNC` |
| `2` `x e rt y*`         | `ELEM rt (REF.FUNC y)* (ACTIVE x e)`      | same shape, `rt = REF FUNC` |
| `3` `rt y*`             | `ELEM rt (REF.FUNC y)* DECLARE`           | same shape, `rt = REF FUNC` |
| `4` `e e*`              | `ELEM FUNCREF e* (ACTIVE 0 e)`            | `ELEM (REF NULL FUNC) e*` |
| `5`, `6`, `7`           | `reftype`-carrying                        | `reftype`-carrying |

**Clarification for 2.0.** The description "kind 0
and kind 4, where the element type is implicit" is the right description
for the V1/Lime1 profiles, where kind 0 is the only legacy form. For 2.0 the
affected kinds are **0, 1, 2 and 3** — the *function-index* forms, whose element
type comes from `Belemkind`. Kind `4` is **not** affected: `5.4:109-110` reads
`4:Bu32 e_O:Bexpr e*:Blist(Bexpr) => ELEM (REF NULL FUNC) e* (ACTIVE 0 e_O)`,
i.e. 3.0 decodes kind 4 to `funcref`, agreeing with 2.0. This was checked three
ways: the pinned `specification/wasm-3.0/5.4-binary.modules.spectec:100-116` and
`specification/wasm-3.0/5.4-binary.modules.spectec:100-116`; this
repository's own decoder `Silmaril/Wasm/Binary/Core/Modules.lean:92-116`
(`Elem.k0`–`k3` produce `⟨false, .abstract .func⟩`, `Elem.k4` produces
`⟨true, .abstract .func⟩`); and the reference encoder
`interpreter/binary/encode.ml:1042-1082`, whose `is_elem_kind` is
`(NoNull, FuncHT)` and which only falls back to kind 4 `when rt = (Null, FuncHT)`.

So, following a separate cross-version binary-agreement development (not included in this package), there are **two**
embeddings, differing only in element-segment types:

* `Elem.toCore` / `Module.toCore` — *syntax-faithful*: `2.0 FUNCREF ↦ funcref`.
  This is the embedding the validation and execution subset theorems use.
* `Elem.toCoreBinary` / `Module.toCoreBinary` — *decoder-faithful*: a segment
  that the 2.0 encoder puts in a function-index form (kinds 0–3) is retyped to
  `(ref func)`. The criterion `Elem.coreFuncIdxForm` is exactly the reference
  encoder's `is_elem_kind rt && List.for_all is_elem_index cs`
  (`encode.ml:1062-1063`): element type `funcref` and every initializer a single
  `ref.func`.

`Module.toCoreBinary` is literally `Module.toCore` post-composed with the
retyping `Module.binaryRetype`, so `Module.toCoreBinary_eq_map` is `rfl`, and
`Module.ofCore?` retracts both (it accepts `(ref func)` element types as well,
via `RefType.ofCoreElem?`, like `V1.Elem.ofCore?` and `Lime1.Elem.ofCore?`).

**A segment in function-index form has two legal encodings.** Unlike the Lime1
situation, where kind 0 is the only form available, a 2.0 segment satisfying
`coreFuncIdxForm` can also be written in the expression forms 4/5/7, which 3.0
decodes to `funcref`. `toCoreBinary` models the *compact* encoding, the one the
reference encoder emits and the one every producer uses;
`toCore` models the expression encoding. Both are genuine decoder outputs, which
is why the bridge below, not a choice between them, is what makes the semantic
results apply to what Core decodes.

The bridge (`Module.toCoreBinary_ok`, `Module.toCoreBinary_instantiate`,
`Module.toCore_instantiate_of_binary`) says that validity and instantiation
carry over: `(ref func) <: funcref`, element types occur in a module's typing
only through `C.ELEMS` (never in its `moduletype`), and at run time only in the
`TYPE` field of the allocated `eleminst`s, which `$runelem`/`TABLE.INIT`/
`ELEM.DROP` never read (`9-module`, `Execution/Core/Instantiation.lean:145`).
-/

@[expose] public section

namespace Silmaril.Wasm.V2

open Silmaril.Wasm.Validation

/-! ## Generic plumbing -/

/-- A pointwise retraction lifts to lists. -/
theorem mapM_ofCore? {α β : Type*} {f : α → Option β} {g : β → Option α}
    (h : ∀ a b, f a = some b → g b = some a) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.mapM g = some xs := by
  intro xs
  induction xs with
  | nil =>
      intro ys hy
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hy
      subst hy
      rfl
  | cons a xs ih =>
      intro ys hy
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at hy
      obtain ⟨b, hb, bs, hbs, rfl⟩ := hy
      simp [List.mapM_cons, h a b hb, ih hbs]

/-- Two lists with a common pointwise-injective image are equal. -/
theorem mapM_injective {α β : Type*} {f : α → Option β} {g : β → Option α}
    (h : ∀ a b, f a = some b → g b = some a) {xs ys : List α} {zs : List β}
    (hx : xs.mapM f = some zs) (hy : ys.mapM f = some zs) : xs = ys :=
  Option.some.inj ((mapM_ofCore? h hx).symm.trans (mapM_ofCore? h hy))

/-! ## Functions

`func ::= FUNC typeidx local* expr` (`1-syntax:545`), with
`local ::= LOCAL valtype` (`1-syntax:543`). Core 3.0 has the same shape
(`1.4-syntax.modules:31`), so only the local value types and the body move. -/

/-- `func ::= FUNC typeidx local* expr` (`1-syntax:545`). -/
def Func.toCore (f : Func) : Option Wasm.Func :=
  (Expr.toCore f.body).map fun body => ⟨f.type, f.locals.map ValType.toCore, body⟩

/-- The retraction of `Func.toCore` (`1-syntax:545`). -/
def Func.ofCore? (f : Wasm.Func) : Option Func := do
  return ⟨f.type, ← f.locals.mapM ValType.ofCore?, ← Expr.ofCore? f.body⟩

/-- `Func.ofCore?` inverts `Func.toCore` wherever the latter is defined. -/
theorem Func.ofCore?_toCore {f : Func} {c : Wasm.Func} (h : Func.toCore f = some c) :
    Func.ofCore? c = some f := by
  obtain ⟨t, ls, e⟩ := f
  simp only [Func.toCore, Option.map_eq_some_iff] at h
  obtain ⟨body, hbody, rfl⟩ := h
  simp [Func.ofCore?, List.mapM_map, Function.comp_def, Expr.ofCore?_toCore hbody]

/-- Wasm 2.0 functions are determined by their Core 3.0 image (`1-syntax:545`). -/
theorem Func.toCore_injective {f g : Func} {c : Wasm.Func}
    (hf : Func.toCore f = some c) (hg : Func.toCore g = some c) : f = g :=
  Option.some.inj ((Func.ofCore?_toCore hf).symm.trans (Func.ofCore?_toCore hg))

/-! ## Globals

`global ::= GLOBAL globaltype expr` (`1-syntax:547`). -/

/-- `global ::= GLOBAL globaltype expr` (`1-syntax:547`). -/
def Global.toCore (g : Global) : Option Wasm.Global :=
  (Expr.toCore g.init).map fun init => ⟨g.type.toCore, init⟩

/-- The retraction of `Global.toCore` (`1-syntax:547`). -/
def Global.ofCore? (g : Wasm.Global) : Option Global := do
  return ⟨← GlobalType.ofCore? g.type, ← Expr.ofCore? g.init⟩

/-- `Global.ofCore?` inverts `Global.toCore` wherever the latter is defined. -/
theorem Global.ofCore?_toCore {g : Global} {c : Wasm.Global} (h : Global.toCore g = some c) :
    Global.ofCore? c = some g := by
  obtain ⟨t, e⟩ := g
  simp only [Global.toCore, Option.map_eq_some_iff] at h
  obtain ⟨init, hinit, rfl⟩ := h
  simp [Global.ofCore?, Expr.ofCore?_toCore hinit]

/-- Wasm 2.0 globals are determined by their Core 3.0 image (`1-syntax:547`). -/
theorem Global.toCore_injective {g g' : Global} {c : Wasm.Global}
    (hg : Global.toCore g = some c) (hg' : Global.toCore g' = some c) : g = g' :=
  Option.some.inj ((Global.ofCore?_toCore hg).symm.trans (Global.ofCore?_toCore hg'))

/-! ## Tables

`table ::= TABLE tabletype` (`1-syntax:549`) against
`table ::= TABLE tabletype expr` (`1.4-syntax.modules:22`); see the module
documentation for the implicit null initializer. -/

/-- `table ::= TABLE tabletype` (`1-syntax:549`), with the initializer that
`$alloctable` supplies implicitly in 2.0: `(REF.NULL rt)^i` (`9-module:58`),
where `rt` is the table's own element type. -/
def TableType.toCoreTable (t : TableType) : Wasm.Table :=
  ⟨t.toCore, [.refNull t.element.toCoreHeap]⟩

/-- The retraction of `TableType.toCoreTable` (`1-syntax:549`): the initializer
must be the null of the table's own element type. -/
def TableType.ofCoreTable? (t : Wasm.Table) : Option TableType :=
  match t.init with
  | [.refNull h] => do
      let tt ← TableType.ofCore? t.type
      if tt.element.toCoreHeap = h then some tt else none
  | _ => none

@[simp] theorem TableType.ofCoreTable?_toCoreTable (t : TableType) :
    TableType.ofCoreTable? t.toCoreTable = some t := by
  simp [TableType.toCoreTable, TableType.ofCoreTable?]

theorem TableType.toCoreTable_injective : Function.Injective TableType.toCoreTable :=
  injective_of_ofCore? TableType.ofCoreTable?_toCoreTable

/-! ## Element segments

`elemmode ::= ACTIVE tableidx expr | PASSIVE | DECLARE` (`1-syntax:538`) and
`elem ::= ELEM reftype expr* elemmode` (`1-syntax:553`). Core 3.0 spells
`DECLARE` as `DECLARE`/`declarative` and lists the modes in a different order
(`1.4-syntax.modules:5`, `:34`). -/

/-- `elemmode ::= ACTIVE tableidx expr | PASSIVE | DECLARE` (`1-syntax:538`). -/
def ElemMode.toCore : ElemMode → Option Wasm.ElemMode
  | .active table offset => (Expr.toCore offset).map (Wasm.ElemMode.active table)
  | .passive => some .passive
  | .declare => some .declarative

/-- The retraction of `ElemMode.toCore` (`1-syntax:538`). -/
def ElemMode.ofCore? : Wasm.ElemMode → Option ElemMode
  | .active table offset => (Expr.ofCore? offset).map (ElemMode.active table)
  | .passive => some .passive
  | .declarative => some .declare

/-- `ElemMode.ofCore?` inverts `ElemMode.toCore` wherever the latter is defined. -/
theorem ElemMode.ofCore?_toCore {m : ElemMode} {c : Wasm.ElemMode}
    (h : ElemMode.toCore m = some c) : ElemMode.ofCore? c = some m := by
  cases m with
  | active table offset =>
      simp only [ElemMode.toCore, Option.map_eq_some_iff] at h
      obtain ⟨off, hoff, rfl⟩ := h
      simp [ElemMode.ofCore?, Expr.ofCore?_toCore hoff]
  | passive | declare =>
      simp only [ElemMode.toCore, Option.some.injEq] at h
      subst h
      rfl

/-- Wasm 2.0 element modes are determined by their Core 3.0 image. -/
theorem ElemMode.toCore_injective {m m' : ElemMode} {c : Wasm.ElemMode}
    (h : ElemMode.toCore m = some c) (h' : ElemMode.toCore m' = some c) : m = m' :=
  Option.some.inj ((ElemMode.ofCore?_toCore h).symm.trans (ElemMode.ofCore?_toCore h'))

/-- `funcref = (ref null func)`, the Core 3.0 image of 2.0's `FUNCREF`
(`1-syntax:135`). -/
abbrev coreFuncref : Wasm.RefType := ⟨true, .abstract .func⟩

/-- `(ref func)`, the non-nullable type that the Core 3.0 binary format assigns
to the function-index element forms (`5.4:100-108`). Outside the image of
`RefType.toCore`. -/
abbrev coreRefFunc : Wasm.RefType := ⟨false, .abstract .func⟩

/-- `RefType.ofCore?` extended to accept `(ref func)` as `FUNCREF`, so that the
same retraction inverts both `Elem.toCore` and `Elem.toCoreBinary`; cf.
`V1.Elem.ofCore?` and `Lime1.Elem.ofCore?`. -/
def RefType.ofCoreElem? (t : Wasm.RefType) : Option RefType :=
  if t = coreRefFunc then some .funcref else RefType.ofCore? t

@[simp] theorem RefType.ofCoreElem?_toCore (t : RefType) :
    RefType.ofCoreElem? t.toCore = some t := by
  cases t <;> simp [RefType.ofCoreElem?, RefType.toCore, RefType.ofCore?, coreRefFunc]

@[simp] theorem RefType.ofCoreElem?_coreRefFunc :
    RefType.ofCoreElem? coreRefFunc = some RefType.funcref := by
  simp [RefType.ofCoreElem?]

/-- `elem ::= ELEM reftype expr* elemmode` (`1-syntax:553`). -/
def Elem.toCore (e : Elem) : Option Wasm.Elem :=
  (e.init.mapM Expr.toCore).bind fun init =>
    (ElemMode.toCore e.mode).map fun mode => ⟨e.type.toCore, init, mode⟩

/-- The retraction of `Elem.toCore` (`1-syntax:553`). Accepts the non-nullable
`(ref func)` as well, so that it also retracts `Elem.toCoreBinary`; see the
module documentation. -/
def Elem.ofCore? (c : Wasm.Elem) : Option Elem :=
  (RefType.ofCoreElem? c.type).bind fun type =>
    (c.init.mapM Expr.ofCore?).bind fun init =>
      (ElemMode.ofCore? c.mode).map fun mode => ⟨type, init, mode⟩

/-- `Elem.ofCore?` inverts `Elem.toCore` wherever the latter is defined. -/
theorem Elem.ofCore?_toCore {e : Elem} {c : Wasm.Elem} (h : Elem.toCore e = some c) :
    Elem.ofCore? c = some e := by
  obtain ⟨type, init, mode⟩ := e
  simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨is, his, m, hm, rfl⟩ := h
  simp [Elem.ofCore?, mapM_ofCore? (fun _ _ => Expr.ofCore?_toCore) his,
    ElemMode.ofCore?_toCore hm]

/-- Wasm 2.0 element segments are determined by their Core 3.0 image
(`1-syntax:553`). -/
theorem Elem.toCore_injective {e e' : Elem} {c : Wasm.Elem}
    (h : Elem.toCore e = some c) (h' : Elem.toCore e' = some c) : e = e' :=
  Option.some.inj ((Elem.ofCore?_toCore h).symm.trans (Elem.ofCore?_toCore h'))

/-! ## Data segments

`datamode ::= ACTIVE memidx expr | PASSIVE` (`1-syntax:539`) and
`data ::= DATA byte* datamode` (`1-syntax:555`). -/

/-- `datamode ::= ACTIVE memidx expr | PASSIVE` (`1-syntax:539`). -/
def DataMode.toCore : DataMode → Option Wasm.DataMode
  | .active memory offset => (Expr.toCore offset).map (Wasm.DataMode.active memory)
  | .passive => some .passive

/-- The retraction of `DataMode.toCore` (`1-syntax:539`). -/
def DataMode.ofCore? : Wasm.DataMode → Option DataMode
  | .active memory offset => (Expr.ofCore? offset).map (DataMode.active memory)
  | .passive => some .passive

/-- `DataMode.ofCore?` inverts `DataMode.toCore` wherever the latter is defined. -/
theorem DataMode.ofCore?_toCore {m : DataMode} {c : Wasm.DataMode}
    (h : DataMode.toCore m = some c) : DataMode.ofCore? c = some m := by
  cases m with
  | active memory offset =>
      simp only [DataMode.toCore, Option.map_eq_some_iff] at h
      obtain ⟨off, hoff, rfl⟩ := h
      simp [DataMode.ofCore?, Expr.ofCore?_toCore hoff]
  | passive =>
      simp only [DataMode.toCore, Option.some.injEq] at h
      subst h
      rfl

/-- Wasm 2.0 data modes are determined by their Core 3.0 image. -/
theorem DataMode.toCore_injective {m m' : DataMode} {c : Wasm.DataMode}
    (h : DataMode.toCore m = some c) (h' : DataMode.toCore m' = some c) : m = m' :=
  Option.some.inj ((DataMode.ofCore?_toCore h).symm.trans (DataMode.ofCore?_toCore h'))

/-- `data ::= DATA byte* datamode` (`1-syntax:555`). -/
def Data.toCore (d : Data) : Option Wasm.Data :=
  (DataMode.toCore d.mode).map fun mode => ⟨d.bytes, mode⟩

/-- The retraction of `Data.toCore` (`1-syntax:555`). -/
def Data.ofCore? (c : Wasm.Data) : Option Data :=
  (DataMode.ofCore? c.mode).map fun mode => ⟨c.bytes, mode⟩

/-- `Data.ofCore?` inverts `Data.toCore` wherever the latter is defined. -/
theorem Data.ofCore?_toCore {d : Data} {c : Wasm.Data} (h : Data.toCore d = some c) :
    Data.ofCore? c = some d := by
  obtain ⟨bytes, mode⟩ := d
  simp only [Data.toCore, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  simp [Data.ofCore?, DataMode.ofCore?_toCore hm]

/-- Wasm 2.0 data segments are determined by their Core 3.0 image
(`1-syntax:555`). -/
theorem Data.toCore_injective {d d' : Data} {c : Wasm.Data}
    (h : Data.toCore d = some c) (h' : Data.toCore d' = some c) : d = d' :=
  Option.some.inj ((Data.ofCore?_toCore h).symm.trans (Data.ofCore?_toCore h'))

/-! ## Modules

`module ::= MODULE type* import* func* global* table* mem* elem* data* start?
export*` (`1-syntax:567`). Core 3.0 adds a tag section, which the image leaves
empty. -/

/-- `module ::= MODULE type* import* func* global* table* mem* elem* data*
start? export*` (`1-syntax:567`). Each 2.0 function type becomes one singleton
final recursive group (`FuncType.toCoreRec`), so type indices do not shift. -/
def Module.toCore (m : Module) : Option Wasm.Module :=
  (m.globals.mapM Global.toCore).bind fun globals =>
  (m.funcs.mapM Func.toCore).bind fun funcs =>
  (m.elems.mapM Elem.toCore).bind fun elems =>
  (m.data.mapM Data.toCore).map fun data =>
         { types := m.types.map FuncType.toCoreRec
           imports := m.imports.map Import.toCore
           tags := []
           globals := globals
           memories := m.memories.map MemoryType.toCore
           tables := m.tables.map TableType.toCoreTable
           funcs := funcs
           data := data
           elems := elems
           start := m.start
           exports := m.exports.map Export.toCore }

/-- The retraction of `Module.toCore` (`1-syntax:567`); a Core 3.0 module with a
tag section is outside the Wasm 2.0 image. -/
def Module.ofCore? (c : Wasm.Module) : Option Module := do
  if !c.tags.isEmpty then none else
  let types ← c.types.mapM FuncType.ofCoreRec?
  let imports ← c.imports.mapM Import.ofCore?
  let funcs ← c.funcs.mapM Func.ofCore?
  let globals ← c.globals.mapM Global.ofCore?
  let tables ← c.tables.mapM TableType.ofCoreTable?
  let memories ← c.memories.mapM MemoryType.ofCore?
  let elems ← c.elems.mapM Elem.ofCore?
  let data ← c.data.mapM Data.ofCore?
  let exports ← c.exports.mapM Export.ofCore?
  return { types := types
           imports := imports
           funcs := funcs
           globals := globals
           tables := tables
           memories := memories
           elems := elems
           data := data
           start := c.start
           exports := exports }

/-- `Module.ofCore?` inverts `Module.toCore` wherever the latter is defined
(`1-syntax:567`). -/
theorem Module.ofCore?_toCore {m : Module} {c : Wasm.Module} (h : Module.toCore m = some c) :
    Module.ofCore? c = some m := by
  obtain ⟨types, imports, funcs, globals, tables, memories, elems, data, start, exports⟩ := m
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨gs, hgs, fs, hfs, es, hes, ds, hds, rfl⟩ := h
  simp [Module.ofCore?, List.mapM_map, Function.comp_def,
    mapM_ofCore? (fun _ _ => Global.ofCore?_toCore) hgs,
    mapM_ofCore? (fun _ _ => Func.ofCore?_toCore) hfs,
    mapM_ofCore? (fun _ _ => Elem.ofCore?_toCore) hes,
    mapM_ofCore? (fun _ _ => Data.ofCore?_toCore) hds]

/-- Wasm 2.0 modules are determined by their Core 3.0 image (`1-syntax:567`).

`Function.Injective Module.toCore` is false for the `Option`-valued map, since
all modules containing an undefined `CVTOP` share the image `none`; this
conditional form is the strongest true statement. -/
theorem Module.toCore_injective {m n : Module} {c : Wasm.Module}
    (hm : Module.toCore m = some c) (hn : Module.toCore n = some c) : m = n :=
  Option.some.inj ((Module.ofCore?_toCore hm).symm.trans (Module.ofCore?_toCore hn))

/-- Type indices are unchanged: every 2.0 function type contributes exactly one
member to the Core 3.0 type index space (`FuncType.toCoreRec`). -/
theorem Module.toCore_typeDefinitions_length {m : Module} {c : Wasm.Module}
    (h : Module.toCore m = some c) : c.typeDefinitions.length = m.types.length := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
  simp [Wasm.Module.typeDefinitions, FuncType.toCoreRec, Function.comp_def]

/-- The unconditional, `simp`-usable form of `Module.toCore_typeDefinitions_length`:
the hypothesis-free statement needs the `Option`, since `Module.toCore` is partial. -/
@[simp] theorem Module.map_toCore_typeDefinitions_length (m : Module) :
    (Module.toCore m).map (fun c => c.typeDefinitions.length)
      = (Module.toCore m).map (fun _ => m.types.length) := by
  cases h : Module.toCore m with
  | none => rfl
  | some c => simp [Module.toCore_typeDefinitions_length h]

/-! ## The binary-faithful embedding

See the module documentation. `toCoreBinary` is `toCore` with the element types
that the Core 3.0 binary format decodes for the function-index element forms. -/

/-- A Core 3.0 element initializer of the function-index form `(REF.FUNC y)`
(`5.4:101`); the reference encoder's `is_elem_index` (`encode.ml:1052`). -/
def funcIdxInit? : Wasm.Expr → Option FuncIdx
  | [.refFunc y] => some y
  | _ => none

/-- The element segments that a 2.0 encoder writes in a function-index form
(`Belem` kinds `0`–`3`, `A-binary:861-868`): element type `FUNCREF` and every
initializer a single `REF.FUNC`. This is exactly the reference encoder's test
`is_elem_kind rt && List.for_all is_elem_index cs` (`encode.ml:1062-1063`). -/
def Elem.coreFuncIdxForm (c : Wasm.Elem) : Bool :=
  decide (c.type = coreFuncref) && c.init.all fun e => (funcIdxInit? e).isSome

/-- Retype a function-index element segment to the non-nullable `(ref func)`
that Core 3.0 decodes it to (`5.4:100-108`). -/
def Elem.binaryRetype (c : Wasm.Elem) : Wasm.Elem :=
  if Elem.coreFuncIdxForm c then { c with type := coreRefFunc } else c

/-- Retype every function-index element segment of a Core 3.0 module. -/
def Module.binaryRetype (c : Wasm.Module) : Wasm.Module :=
  { c with elems := c.elems.map Elem.binaryRetype }

/-- `Elem.toCore` with the element type that the Core 3.0 binary format decodes
for the function-index forms; see the module documentation. -/
def Elem.toCoreBinary (e : Elem) : Option Wasm.Elem :=
  (Elem.toCore e).map Elem.binaryRetype

/-- `Module.toCore` with the element types that the Core 3.0 binary format
decodes for the function-index forms; see the module documentation. -/
def Module.toCoreBinary (m : Module) : Option Wasm.Module :=
  (Module.toCore m).map Module.binaryRetype

/-- `toCoreBinary` is `toCore` followed by the retyping, by definition. -/
theorem Module.toCoreBinary_eq_map (m : Module) :
    Module.toCoreBinary m = (Module.toCore m).map Module.binaryRetype := rfl

/-- The two embeddings agree on modules without element segments. -/
theorem Module.toCoreBinary_eq_toCore {m : Module} (h : m.elems = []) :
    Module.toCoreBinary m = Module.toCore m := by
  rw [Module.toCoreBinary_eq_map, Module.toCore]
  cases hg : m.globals.mapM Global.toCore <;>
    cases hf : m.funcs.mapM Func.toCore <;>
      cases hd : m.data.mapM Data.toCore <;>
        simp [h, Module.binaryRetype]

/-- Retyping a function-index element segment does not disturb the retraction:
`RefType.ofCoreElem?` maps both `funcref` and `(ref func)` to 2.0's `FUNCREF`. -/
@[simp] theorem Elem.ofCore?_binaryRetype (c : Wasm.Elem) :
    Elem.ofCore? (Elem.binaryRetype c) = Elem.ofCore? c := by
  unfold Elem.binaryRetype
  split
  · rename_i h
    simp only [Elem.coreFuncIdxForm, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [Elem.ofCore?, h.1, RefType.ofCoreElem?, RefType.ofCore?, coreRefFunc, coreFuncref]
  · rfl

/-- `Module.ofCore?` is blind to the element retyping. -/
@[simp] theorem Module.ofCore?_binaryRetype (c : Wasm.Module) :
    Module.ofCore? (Module.binaryRetype c) = Module.ofCore? c := by
  simp [Module.ofCore?, Module.binaryRetype, List.mapM_map, Function.comp_def]

/-- `Elem.ofCore?` retracts the binary-faithful embedding as well. -/
theorem Elem.ofCore?_toCoreBinary {e : Elem} {c : Wasm.Elem}
    (h : Elem.toCoreBinary e = some c) : Elem.ofCore? c = some e := by
  simp only [Elem.toCoreBinary, Option.map_eq_some_iff] at h
  obtain ⟨c₀, hc₀, rfl⟩ := h
  rw [Elem.ofCore?_binaryRetype]
  exact Elem.ofCore?_toCore hc₀

/-- Wasm 2.0 element segments are determined by their binary-faithful image. -/
theorem Elem.toCoreBinary_injective {e e' : Elem} {c : Wasm.Elem}
    (h : Elem.toCoreBinary e = some c) (h' : Elem.toCoreBinary e' = some c) : e = e' :=
  Option.some.inj ((Elem.ofCore?_toCoreBinary h).symm.trans (Elem.ofCore?_toCoreBinary h'))

/-- `Module.ofCore?` retracts the binary-faithful embedding as well, because
`RefType.ofCoreElem?` accepts `(ref func)`. -/
theorem Module.ofCore?_toCoreBinary {m : Module} {c : Wasm.Module}
    (h : Module.toCoreBinary m = some c) : Module.ofCore? c = some m := by
  simp only [Module.toCoreBinary, Option.map_eq_some_iff] at h
  obtain ⟨c₀, hc₀, rfl⟩ := h
  rw [Module.ofCore?_binaryRetype]
  exact Module.ofCore?_toCore hc₀

/-- Wasm 2.0 modules are determined by their binary-faithful Core 3.0 image. -/
theorem Module.toCoreBinary_injective {m n : Module} {c : Wasm.Module}
    (hm : Module.toCoreBinary m = some c) (hn : Module.toCoreBinary n = some c) : m = n :=
  Option.some.inj
    ((Module.ofCore?_toCoreBinary hm).symm.trans (Module.ofCore?_toCoreBinary hn))

/-! ## The bridge: validity and instantiation carry over

`m.toCore` and `m.toCoreBinary` differ only in the types of function-index
element segments, `funcref` versus `(ref func)`. Because `(ref func) <: funcref`
and an element type never appears in a module's `moduletype`, validity carries
over with the *same* module type; and because `$runelem_` and the allocation of
`eleminst`s read the element type only to store it
(`Execution/Core/Instantiation.lean:75`, `:145`), instantiation carries over up
to the `TYPE` fields of element instances. -/

/-- Forget the types of all element instances, the only thing in which the two
instantiations of `toCore` and `toCoreBinary` can differ. -/
def Store.eraseElemTypes {H : Type} (s : Silmaril.Wasm.Execution.Core.Store H) :
    Silmaril.Wasm.Execution.Core.Store H :=
  { s with elems := s.elems.map fun e => { e with type := .ref true (.abs .func) } }

/-! ### Retyping a context's element types

The Core 3.0 instruction rules read an element type in exactly four places —
`table.init` and `elem.drop` (`Instr/Table.lean`), `array.new_elem` and
`array.init_elem` (`Instr/Ref.lean`) — and in each of them the type stands on
the *left* of a subtyping premise, or is not read at all. `ElemsRetype` collects
what a replacement element-type list must satisfy, and `instrOk_retypeElems`
pushes the replacement through a whole derivation. The `noArrays` field
discharges the two `array.*` rules outright: a Wasm 2.0 module's type section is
a list of function types, so no `array` type is reachable. -/

namespace Bridge

/-- The side condition of `instrOk_retypeElems`: `E` may replace `C.elems`. -/
structure ElemsRetype (C : Context) (E : List CRefType) : Prop where
  /-- No `array` type is reachable, so `array.new_elem`/`array.init_elem` are
  not typable in `C`. -/
  noArrays : ∀ {x : Wasm.TypeIdx} {d : DefType} {f : CFieldType},
      C.type? x = some d → ¬ Expand d (.array f)
  /-- `elem.drop` only needs the segment to exist. -/
  get : ∀ {y : Nat} {rt : CRefType}, C.elems[y]? = some rt → ∃ rt', E[y]? = some rt'
  /-- `table.init` needs the replacement to stay below the table's element type. -/
  table : ∀ {y : Nat} {rt r : CRefType} {x : Nat} {a : Wasm.AddrType} {l : Wasm.Limits},
      C.elems[y]? = some rt → C.tables[x]? = some ⟨a, l, r⟩ → Sub C.toTypeCtx rt r →
      ∃ rt', E[y]? = some rt' ∧ Sub C.toTypeCtx rt' r

theorem ElemsRetype.congr {C C' : Context} {E : List CRefType} (hE : ElemsRetype C E)
    (ht : C'.toTypeCtx = C.toTypeCtx) (he : C'.elems = C.elems) (htb : C'.tables = C.tables) :
    ElemsRetype C' E where
  noArrays := by
    intro x d f hx
    refine hE.noArrays (x := x) ?_
    simpa [Context.type?, show C'.types = C.types from congrArg TypeCtx.types ht] using hx
  get := by intro y rt hy; exact hE.get (he ▸ hy)
  table := by
    intro y rt r x a l hy hx hs
    obtain ⟨rt', h1, h2⟩ := hE.table (he ▸ hy) (htb ▸ hx) (ht ▸ hs)
    exact ⟨rt', h1, ht ▸ h2⟩

theorem ElemsRetype.withLabel {C : Context} {E : List CRefType} (hE : ElemsRetype C E)
    (ts : List CValType) : ElemsRetype (C.withLabel ts) E := hE.congr rfl rfl rfl

theorem ElemsRetype.initLocals {C : Context} {E : List CRefType} (hE : ElemsRetype C E)
    (xs : List Nat) : ElemsRetype (C.initLocals xs) E := by
  obtain ⟨L, hL, -⟩ := Context.initLocals_spec C xs
  exact hE.congr (by rw [hL]) (by rw [hL]) (by rw [hL])

theorem ElemsRetype.funcBody {C : Context} {E : List CRefType} (hE : ElemsRetype C E)
    (ps rs : List CValType) (lts : List LocalType) :
    ElemsRetype (C.funcBody ps rs lts) E := hE.congr rfl rfl rfl

theorem withLocals_elems (E : List CRefType) :
    ∀ (xs : List Nat) (lts : List LocalType) (C : Context),
      Context.withLocals { C with elems := E } xs lts
        = { Context.withLocals C xs lts with elems := E }
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, lt :: lts, C => by
      show Context.withLocals (Context.setLocal { C with elems := E } x lt) xs lts = _
      rw [show Context.setLocal { C with elems := E } x lt
            = { Context.setLocal C x lt with elems := E } from rfl,
        withLocals_elems E xs lts]
      rfl

theorem initLocals_elems (C : Context) (E : List CRefType) (xs : List Nat) :
    ({ C with elems := E } : Context).initLocals xs = { C.initLocals xs with elems := E } := by
  simp only [Context.initLocals, withLocals_elems]

/-! #### The families that do not mention `C.ELEMS` -/

section Families
variable {C : Context} {E : List CRefType} {i : Wasm.Instr} {it : InstrType}

theorem ParametricInstrOk.retypeElems (h : ParametricInstrOk C i it) :
    ParametricInstrOk { C with elems := E } i it := by
  cases h <;> constructor <;> assumption

theorem NumericInstrOk.retypeElems (h : NumericInstrOk C i it) :
    NumericInstrOk { C with elems := E } i it := by
  cases h <;> constructor
  assumption

theorem VectorInstrOk.retypeElems (h : VectorInstrOk C i it) :
    VectorInstrOk { C with elems := E } i it := by
  cases h <;> constructor <;> assumption

theorem VariableInstrOk.retypeElems (h : VariableInstrOk C i it) :
    VariableInstrOk { C with elems := E } i it := by
  cases h <;> constructor <;> assumption

theorem MemoryInstrOk.retypeElems (h : MemoryInstrOk C i it) :
    MemoryInstrOk { C with elems := E } i it := by
  cases h <;> constructor <;> assumption

theorem BlockTypeOk.retypeElems {bt : Wasm.BlockType} {t₁ t₂ : List CValType}
    (h : BlockTypeOk C bt t₁ t₂) : BlockTypeOk { C with elems := E } bt t₁ t₂ := by
  cases h <;> constructor <;> assumption

theorem CatchOk.retypeElems {c : Wasm.Catch} (h : CatchOk C c) :
    CatchOk { C with elems := E } c := by
  cases h <;> constructor <;> assumption

theorem InstrConst.retypeElems (h : InstrConst C i) : InstrConst { C with elems := E } i := by
  cases h <;> constructor <;> assumption

theorem LocalOk.retypeElems {t : Wasm.ValType} {lt : LocalType} (h : LocalOk C t lt) :
    LocalOk { C with elems := E } t lt := by
  cases h <;> constructor <;> assumption

theorem ExternIdxOk.retypeElems {x : Wasm.ExternIdx} {xt : CExternType}
    (h : ExternIdxOk C x xt) : ExternIdxOk { C with elems := E } x xt := by
  cases h <;> constructor <;> assumption

/-! #### The two families that do -/

theorem TableInstrOk.retypeElems (hE : ElemsRetype C E) (h : TableInstrOk C i it) :
    TableInstrOk { C with elems := E } i it := by
  cases h with
  | tableInit h he hs =>
      obtain ⟨rt', hrt', hs'⟩ := hE.table he h hs
      exact .tableInit h hrt' hs'
  | elemDrop he => obtain ⟨rt', hrt'⟩ := hE.get he; exact .elemDrop hrt'
  | _ => constructor <;> assumption

theorem RefInstrOk.retypeElems (hE : ElemsRetype C E) (h : RefInstrOk C i it) :
    RefInstrOk { C with elems := E } i it := by
  cases h with
  | arrayNewElem hd he _ _ => exact absurd he (hE.noArrays hd)
  | arrayInitElem hd he _ _ => exact absurd he (hE.noArrays hd)
  | _ => constructor <;> assumption

end Families

mutual

/-- Replacing `C.ELEMS` by a list satisfying `ElemsRetype` preserves instruction
typing: an element type is only ever read on the left of a subtyping premise. -/
theorem InstrOk.retypeElems {C : Context} {E : List CRefType} {i : Wasm.Instr}
    {it : InstrType} (hE : ElemsRetype C E) (h : InstrOk C i it) :
    InstrOk { C with elems := E } i it :=
  match h with
  | .parametric h => .parametric (ParametricInstrOk.retypeElems h)
  | .numeric h => .numeric (NumericInstrOk.retypeElems h)
  | .vector h => .vector (VectorInstrOk.retypeElems h)
  | .variable h => .variable (VariableInstrOk.retypeElems h)
  | .memory h => .memory (MemoryInstrOk.retypeElems h)
  | .table h => .table (TableInstrOk.retypeElems hE h)
  | .reference h => .reference (RefInstrOk.retypeElems hE h)
  | .block hbt hb =>
      .block (BlockTypeOk.retypeElems hbt) (InstrsOk.retypeElems (hE.withLabel _) hb)
  | .loop hbt hb =>
      .loop (BlockTypeOk.retypeElems hbt) (InstrsOk.retypeElems (hE.withLabel _) hb)
  | .if_ hbt h₁ h₂ =>
      .if_ (BlockTypeOk.retypeElems hbt) (InstrsOk.retypeElems (hE.withLabel _) h₁)
        (InstrsOk.retypeElems (hE.withLabel _) h₂)
  | .br hl hok => .br hl hok
  | .brIf hl => .brIf hl
  | .brTable hls hl' hok => .brTable hls hl' hok
  | .brOnNull hl hh => .brOnNull hl hh
  | .brOnNonNull hl => .brOnNonNull hl
  | .brOnCast hl h₁ h₂ h₂₁ h₂l => .brOnCast hl h₁ h₂ h₂₁ h₂l
  | .brOnCastFail hl h₁ h₂ h₂₁ hdl => .brOnCastFail hl h₁ h₂ h₂₁ hdl
  | .call hf he => .call hf he
  | .callRef hd he => .callRef hd he
  | .callIndirect ht hs hd he => .callIndirect ht hs hd he
  | .return_ hret hok => .return_ hret hok
  | .returnCall hf he hret hs hok => .returnCall hf he hret hs hok
  | .returnCallRef hd he hret hs hok => .returnCallRef hd he hret hs hok
  | .returnCallIndirect ht hs hd he hret hrs hok =>
      .returnCallIndirect ht hs hd he hret hrs hok
  | .throw hx he hok => .throw hx he hok
  | .throwRef hok => .throwRef hok
  | .tryTable hbt hb hc =>
      .tryTable (BlockTypeOk.retypeElems hbt) (InstrsOk.retypeElems (hE.withLabel _) hb)
        (fun c hc' => CatchOk.retypeElems (hc c hc'))

/-- `InstrOk.retypeElems` for sequences. -/
theorem InstrsOk.retypeElems {C : Context} {E : List CRefType} {is : List Wasm.Instr}
    {it : InstrType} (hE : ElemsRetype C E) (h : InstrsOk C is it) :
    InstrsOk { C with elems := E } is it :=
  match h with
  | .nil => .nil
  | .instr h => .instr (InstrOk.retypeElems hE h)
  | .seq (xs₁ := xs₁) h₁ hx h₂ =>
      .seq (InstrsOk.retypeElems hE h₁) hx
        (by rw [initLocals_elems]; exact InstrsOk.retypeElems (hE.initLocals xs₁) h₂)
  | .cons (xs₁ := xs₁) hi hx hs =>
      .cons (InstrOk.retypeElems hE hi) hx
        (by rw [initLocals_elems]; exact InstrsOk.retypeElems (hE.initLocals xs₁) hs)
  | .sub h hs hok => .sub (InstrsOk.retypeElems hE h) hs hok
  | .frame h hok => .frame (InstrsOk.retypeElems hE h) hok

end

theorem ExprOk.retypeElems {C : Context} {E : List CRefType} {e : Wasm.Expr}
    {ts : List CValType} (hE : ElemsRetype C E) (h : ExprOk C e ts) :
    ExprOk { C with elems := E } e ts := InstrsOk.retypeElems hE h

theorem ExprOkConst.retypeElems {C : Context} {E : List CRefType} {e : Wasm.Expr}
    {t : CValType} (hE : ElemsRetype C E) (h : ExprOkConst C e t) :
    ExprOkConst { C with elems := E } e t :=
  ⟨ExprOk.retypeElems hE h.typed, fun i hi => InstrConst.retypeElems (h.const i hi)⟩

theorem forall₂_imp {α β : Type _} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → List.Forall₂ S as bs
  | _, _, .nil => .nil
  | _, _, .cons hab hs => .cons (h _ _ hab) (forall₂_imp h hs)

theorem forall₂_map_map {α β γ : Type _} {R : β → γ → Prop} (f : α → β) (k : α → γ)
    {l : List α} (h : ∀ a ∈ l, R (f a) (k a)) : List.Forall₂ R (l.map f) (l.map k) := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    exact .cons (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem forall₂_map_right {α β : Type _} {R : α → β → Prop} {f : α → β} {l : List α}
    (h : List.Forall₂ R l (l.map f)) : ∀ a ∈ l, R a (f a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h with
    | cons hab hs =>
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact hab
      · exact ih hs b hb'

theorem map_eq_self {α : Type _} {f : α → α} : ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | a :: l, h => by
      rw [List.map_cons, h a List.mem_cons_self,
        map_eq_self (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem mem_of_mapM {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by simp_all
  | a :: l, l', h, b, hb => by
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨b₀, hb₀, bs, hbs, rfl⟩ := h
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact ⟨a, List.mem_cons_self, hb₀⟩
      · obtain ⟨a', ha', h'⟩ := mem_of_mapM hbs b hb'
        exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem FuncOk.retypeElems {C : Context} {E : List CRefType} {f : Wasm.Func}
    {d : DefType} (hE : ElemsRetype C E) (h : FuncOk C f d) :
    FuncOk { C with elems := E } f d := by
  cases h with
  | @mk ps rs lts hd he hl hb =>
    refine FuncOk.mk (lts := lts) hd he (forall₂_imp (fun _ _ h' => LocalOk.retypeElems h') hl) ?_
    exact ExprOk.retypeElems (hE.funcBody ps.toList rs.toList lts) hb

theorem DataModeOk.retypeElems {C : Context} {E : List CRefType} {m : Wasm.DataMode}
    (hE : ElemsRetype C E) (h : DataModeOk C m) : DataModeOk { C with elems := E } m := by
  cases h with
  | passive => exact .passive
  | active h ho => exact .active h (ExprOkConst.retypeElems hE ho)

theorem ElemModeOk.retypeElems {C : Context} {E : List CRefType} {m : Wasm.ElemMode}
    {rt rt' : CRefType} (hE : ElemsRetype C E)
    (hnull : ∀ tt ∈ C.tables, ∃ h₂, tt.element = Ty.ref true h₂)
    (hS : ∀ h₂ : CHeapType, Sub C.toTypeCtx rt (.ref true h₂) → Sub C.toTypeCtx rt' (.ref true h₂))
    (h : ElemModeOk C m rt) : ElemModeOk { C with elems := E } m rt' := by
  cases h with
  | passive => exact .passive
  | declarative => exact .declarative
  | active htb hsub ho =>
    obtain ⟨h₂, hr⟩ := hnull _ (List.mem_of_getElem? htb)
    simp only at hr
    subst hr
    exact .active htb (hS h₂ hsub) (ExprOkConst.retypeElems hE ho)

/-! ### Subtyping: nullability of a reference type's bound -/

/-- A nullable reference type's supertypes are supertypes of its non-nullable
form as well (`Reftype_sub/null` is the only applicable rule). -/
theorem sub_ref_null_left {Δ : TypeCtx} {h₁ : CHeapType} {r : CRefType} {n : Bool}
    (hs : Sub Δ (.ref true h₁) r) : Sub Δ (.ref n h₁) r := by
  cases hs with | refNull h => exact .refNull h

/-- Under a *nullable* supertype, the subtype's nullability is irrelevant. -/
theorem sub_ref_null_right {Δ : TypeCtx} {h₁ h₂ : CHeapType} {n n' : Bool}
    (hs : Sub Δ (.ref n h₁) (.ref true h₂)) : Sub Δ (.ref n' h₁) (.ref true h₂) := by
  cases hs with | refNull h => exact .refNull h

/-- Subsumption for constant expressions. -/
theorem exprOkConst_sub {C : Context} {e : Wasm.Expr} {t t' : CValType}
    (h : ExprOkConst C e t) (hs : Sub C.toTypeCtx t t') (hok : TyOk C.toTypeCtx t') :
    ExprOkConst C e t' :=
  ⟨InstrsOk.sub h.typed ⟨List.Forall₂.nil, List.Forall₂.cons hs .nil, by simp⟩
    ⟨by simp [ResultOk], by intro u hu; simp only [List.mem_singleton] at hu; subst hu; exact hok,
      by simp⟩, h.const⟩

/-- Only `Instr_ok/ref.func` types `REF.FUNC x`. -/
theorem refFunc_inv {C : Context} {y : Wasm.FuncIdx} {it : InstrType}
    (h : InstrOk C (.refFunc y) it) :
    ∃ d, C.funcs[y.toNat]? = some d ∧ y.toNat ∈ C.refs ∧
      it = .plain [] [.refT false (.defHeap d)] := by
  cases h with
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h with | refFunc hf hr => exact ⟨_, hf, hr, rfl⟩

/-- A `funcref`-typed single `REF.FUNC` constant expression also has the
*non-nullable* type `(ref func)`: its principal type is `(ref $d)` for the
function's defined type, and `$d <: func`. -/
theorem refFunc_const_nonnull {C : Context} {y : Wasm.FuncIdx} (hC : C.Wf)
    (h : ExprOkConst C [.refFunc y] (.refv (.ref true (.abs .func)))) :
    ExprOkConst C [.refFunc y] (.refv (.ref false (.abs .func))) := by
  obtain ⟨ht, hconst⟩ := h
  obtain ⟨ts, it₀, hi, hp, hrs, -⟩ := InstrsOk.single_inv hC ht
  obtain ⟨d, hf, hrefs, rfl⟩ := refFunc_inv hi
  simp only [List.append_nil] at hp hrs
  have hts : ts = [] := List.forall₂_nil_left_iff.mp hp
  subst hts
  simp only [List.nil_append] at hrs
  rcases hrs with _ | ⟨hsub, -⟩
  have hheap : Sub C.toTypeCtx (Ty.defHeap d) (Ty.abs .func) := by
    cases hsub with | refv h => cases h with | refNull h => exact h
  refine ⟨?_, hconst⟩
  refine InstrsOk.sub (InstrsOk.instr (.reference (.refFunc hf hrefs))) ?_ ?_
  · exact ⟨List.Forall₂.nil, List.Forall₂.cons (.refv (.refNonNull hheap)) .nil, by simp⟩
  · exact ⟨by simp [ResultOk], by
      intro t htm
      simp only [List.mem_singleton] at htm
      subst htm
      exact .refv (.ref (.abs _)), by simp⟩

/-! ### A Wasm 2.0 type section defines only function types -/

/-- `Types_ok` on the image of `FuncType.toCoreRec` yields exactly the
`FuncType.toDefType`s, at any starting context. -/
theorem typesOk_toCoreRec : ∀ (ts : List FuncType) {C : Context} {dts : List DefType},
    TypesOk C (ts.map FuncType.toCoreRec) dts → dts = ts.map FuncType.toDefType
  | [], _, _, h => by cases h; rfl
  | t :: ts, C, _, h => by
    cases h with
    | @cons _ _ _ dts' _ hs =>
      have hrg : C.rollGroup t.toCoreRec = [t.toDefType] := by
        simp [Context.rollGroup, FuncType.rolldt_toCoreRec,
          Ty.substAll_closed (FuncType.toDefType_closed t)]
      rw [hrg, typesOk_toCoreRec ts hs]
      simp

/-- `funcIdxInit?` recognises exactly the singleton `REF.FUNC` expressions. -/
theorem funcIdxInit?_eq {ex : Wasm.Expr} (h : (funcIdxInit? ex).isSome = true) :
    ∃ y, ex = [.refFunc y] := by
  unfold funcIdxInit? at h
  split at h
  · exact ⟨_, rfl⟩
  · exact absurd h (by simp)

theorem closeRef_nullable (C : Context) {r : Wasm.RefType} (h : r.nullable = true) :
    ∃ h₂, C.closeRef r = .ref true h₂ := by
  obtain ⟨n, ht⟩ := r; cases h; exact ⟨_, rfl⟩

theorem mem_externTables : ∀ {xs : List CExternType} {tt : CTableType},
    tt ∈ CExternType.tables xs → CExternType.table tt ∈ xs
  | [], _, h => by simp [CExternType.tables] at h
  | x :: xs, tt, h => by
    cases x with
    | table t =>
      rcases List.mem_cons.1 (by simpa [CExternType.tables] using h) with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_externTables h')
    | _ => exact List.mem_cons_of_mem _ (mem_externTables (by simpa [CExternType.tables] using h))

theorem funcIdxNonFuncs_map {c : Wasm.Module} {g : Wasm.Elem → Wasm.Elem}
    (hinit : ∀ e, (g e).init = e.init) (hmode : ∀ e, (g e).mode = e.mode) :
    funcIdxNonFuncs { c with elems := c.elems.map g } = funcIdxNonFuncs c := by
  simp only [funcIdxNonFuncs, List.flatMap_map]
  congr 1
  congr 1
  refine List.flatMap_congr fun e _ => ?_
  rw [hinit, hmode]

/-! ### Transporting a whole `Module_ok` derivation -/

/-- **The element-retyping skeleton.** A `Module_ok` derivation survives
replacing every element segment `e` by `g e`, provided `g` leaves the
initializers and the mode alone (so the context's `REFS` and the segment
programs do not move) and the per-segment obligation `helem` holds in the
module's own context. Both halves of the binary-faithful embedding bridge are instances. -/
theorem ModuleOk.retypeElems {c : Wasm.Module} {mt : CModuleType} {g : Wasm.Elem → Wasm.Elem}
    (hinit : ∀ e, (g e).init = e.init) (hmode : ∀ e, (g e).mode = e.mode)
    (htblN : ∀ t ∈ c.tables, t.type.element.nullable = true)
    (himpN : ∀ im ∈ c.imports, ∀ tt : Wasm.TableType,
      im.type = .table tt → tt.element.nullable = true)
    (hnoArr : ∀ dts : List DefType, TypesOk {} c.types dts →
      ∀ d ∈ dts, ∀ f : CFieldType, ¬ Expand d (.array f))
    (helem : ∀ C : Context, C.Wf → ∀ e ∈ c.elems, ElemOk C e (C.closeRef e.type) →
      TyOk C.toTypeCtx (C.closeRef (g e).type) ∧
      (∀ ex ∈ e.init, ExprOkConst C ex (.refv (C.closeRef (g e).type))) ∧
      (∀ h₂ : CHeapType, Sub C.toTypeCtx (C.closeRef e.type) (.ref true h₂) →
        Sub C.toTypeCtx (C.closeRef (g e).type) (.ref true h₂)))
    (h : ModuleOk c mt) :
    ModuleOk { c with elems := c.elems.map g } mt := by
  cases h with
  | @mk dts xtI jts gts tts fdts rts xtE C' C htypes himports hC' hC htags hglobals hmems
      htables hfuncs hdata helems hstart hexports hnd =>
    have hC'tt : C'.toTypeCtx = ({ types := dts } : TypeCtx) := by rw [hC']
    have hCty : C.types = dts := by rw [hC, hC']
    have hCtt : C.toTypeCtx = ({ types := dts } : TypeCtx) := by rw [hC, hC']
    have hCel : C.elems = rts := by rw [hC]
    have hCtb : C.tables = CExternType.tables xtI ++ tts := by rw [hC]
    have hCtg : C.tags = CExternType.tags xtI ++ jts := by rw [hC]
    have hCgl : C.globals = CExternType.globals xtI ++ gts := by rw [hC, hC']
    have hCfn : C.funcs = CExternType.funcs xtI ++ fdts := by rw [hC, hC']
    have hCloc : C.locals = [] := by rw [hC, hC']
    have hClab : C.labels = [] := by rw [hC, hC']
    have hCret : C.return_ = none := by rw [hC, hC']
    have hΔ : ({ types := dts } : TypeCtx).Ok := ModuleWf.typeCtx_ok htypes
    obtain ⟨hXt, hXg, hXtb, hXf⟩ := ModuleWf.externs_tyOk (Δ := { types := dts }) (xs := xtI)
      (fun xt hxt => by
        obtain ⟨_, _, hi⟩ := ModuleWf.forall₂_mem_right himports xt hxt
        exact hi.2)
    have hFty : ∀ d ∈ fdts, TyOk ({ types := dts } : TypeCtx) d := fun d hd =>
      (hΔ d (hCty ▸ ModuleWf.funcs_mem hfuncs d hd)).2
    have hW : C.Wf := by
      refine ⟨by rw [hCtt]; exact hΔ, ?_, ?_, ?_, ?_, by rw [hCloc]; simp,
        by rw [hClab]; simp, by rw [hCret]; simp, ?_⟩
      · intro d hd
        rw [hCtt]
        rcases List.mem_append.1 (hCtg ▸ hd) with hd' | hd'
        · exact hXt d hd'
        · obtain ⟨_, _, ht⟩ := ModuleWf.forall₂_mem_right htags d hd'
          exact hC'tt ▸ ht.2.1
      · intro gt hg
        rw [hCtt]
        rcases List.mem_append.1 (hCgl ▸ hg) with hg' | hg'
        · exact hXg gt hg'
        · exact ModuleWf.globalsOk_tyOk hglobals hC'tt gt hg'
      · intro t ht
        rw [hCtt]
        rcases List.mem_append.1 (hCtb ▸ ht) with ht' | ht'
        · exact hXtb t ht'
        · obtain ⟨_, _, ht''⟩ := ModuleWf.forall₂_mem_right htables t ht'
          exact hC'tt ▸ ht''.2.1.2
      · intro d hd
        rw [hCtt]
        rcases List.mem_append.1 (hCfn ▸ hd) with hd' | hd'
        · exact hXf d hd'
        · exact hFty d hd'
      · intro rt hrt
        obtain ⟨_, _, he⟩ := ModuleWf.forall₂_mem_right helems rt (hCel ▸ hrt)
        exact he.2.1
    have hrts : rts = c.elems.map fun e => C.closeRef e.type :=
      List.Forall₂.eq_map (fun _ _ he => he.1) helems
    subst hrts
    have hEl := forall₂_map_right helems
    have hnoA : ∀ {x : Wasm.TypeIdx} {d : DefType} {f : CFieldType},
        C.type? x = some d → ¬ Expand d (.array f) := by
      intro x d f hx
      have hx' : dts[x.toNat]? = some d := by rw [← hCty]; exact hx
      exact hnoArr dts htypes d (List.mem_of_getElem? hx') f
    have hnull : ∀ tt ∈ C.tables, ∃ h₂, tt.element = Ty.ref true h₂ := by
      intro tt ht
      rcases List.mem_append.1 (hCtb ▸ ht) with ht' | ht'
      · obtain ⟨im, him, hcl, -⟩ := ModuleWf.forall₂_mem_right himports _ (mem_externTables ht')
        cases hty : im.type with
        | table t0 =>
          rw [hty] at hcl
          simp only [Context.closeExtern?, Option.some.injEq, CExternType.table.injEq] at hcl
          subst hcl
          exact closeRef_nullable ({ types := dts } : Context) (himpN im him t0 hty)
        | tag x => rw [hty] at hcl; simp [Context.closeExtern?] at hcl
        | global gt => rw [hty] at hcl; simp [Context.closeExtern?] at hcl
        | memory mt => rw [hty] at hcl; simp [Context.closeExtern?] at hcl
        | func x => rw [hty] at hcl; simp [Context.closeExtern?] at hcl
      · obtain ⟨t, ht2, hto⟩ := ModuleWf.forall₂_mem_right htables tt ht'
        obtain ⟨h₂, hh₂⟩ := closeRef_nullable C' (htblN t ht2)
        exact ⟨h₂, by rw [hto.1]; exact hh₂⟩
    have hE : ElemsRetype C (c.elems.map fun e => C.closeRef (g e).type) := by
      refine ⟨hnoA, ?_, ?_⟩
      · intro y rt hy
        rw [hCel] at hy
        simp only [List.getElem?_map, Option.map_eq_some_iff] at hy ⊢
        obtain ⟨e, he, -⟩ := hy
        exact ⟨_, e, he, rfl⟩
      · intro y rt r x a l hy hx hs
        rw [hCel] at hy
        simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
        obtain ⟨e, he, rfl⟩ := hy
        obtain ⟨h₂, hr⟩ := hnull ⟨a, l, r⟩ (List.mem_of_getElem? hx)
        simp only at hr
        subst hr
        refine ⟨C.closeRef (g e).type, by simp only [List.getElem?_map, he, Option.map_some], ?_⟩
        exact (helem C hW e (List.mem_of_getElem? he) (hEl e (List.mem_of_getElem? he))).2.2 h₂ hs
    refine ModuleOk.mk (dts := dts) (xtI := xtI) (jts := jts) (gts := gts) (tts := tts)
      (fdts := fdts) (rts := c.elems.map fun e => C.closeRef (g e).type) (xtE := xtE)
      (C' := C') (C := { C with elems := c.elems.map fun e => C.closeRef (g e).type })
      htypes himports ?_ ?_ htags hglobals hmems htables ?_ ?_ ?_ ?_ ?_ hnd
    · rw [funcIdxNonFuncs_map hinit hmode]; exact hC'
    · rw [hC]
    · exact forall₂_imp (fun _ _ h' => FuncOk.retypeElems hE h') hfuncs
    · exact fun d hd => DataModeOk.retypeElems hE (hdata d hd)
    · refine forall₂_map_map g (fun e => C.closeRef (g e).type) ?_
      intro e he
      obtain ⟨-, -, -, hmo⟩ := hEl e he
      obtain ⟨hT, hI, hS⟩ := helem C hW e he (hEl e he)
      refine ⟨rfl, hT, ?_, ?_⟩
      · intro ex hex
        rw [hinit] at hex
        exact ExprOkConst.retypeElems hE (hI ex hex)
      · rw [hmode]
        exact ElemModeOk.retypeElems hE hnull hS hmo
    · exact hstart
    · exact forall₂_imp (fun _ _ h' => ExternIdxOk.retypeElems h') hexports

/-! ### Allocation is blind to element-instance types -/

open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Two stores that differ at most in the TYPE fields of their element
instances. -/
structure StoreElemAgree (s s' : Store H) : Prop where
  /-- Every other field agrees. -/
  base : ({ s with elems := [] } : Store H) = { s' with elems := [] }
  /-- The element instances hold the same references. -/
  refs : s.elems.map ElemInst.refs = s'.elems.map ElemInst.refs

theorem store_elems_congr {s s' : Store H}
    (hb : ({ s with elems := [] } : Store H) = { s' with elems := [] })
    {E E' : List ElemInst} (he : E = E') :
    ({ s with elems := E } : Store H) = { s' with elems := E' } := by
  subst he
  rw [show ({ s with elems := E } : Store H)
        = { ({ s with elems := [] } : Store H) with elems := E } from rfl, hb]

theorem StoreElemAgree.erase {s s' : Store H} (h : StoreElemAgree s s') :
    Store.eraseElemTypes s = Store.eraseElemTypes s' := by
  refine store_elems_congr h.base ?_
  rw [show (fun e => ({ e with type := Ty.ref true (Ty.abs .func) } : ElemInst))
        = (fun r => ({ type := Ty.ref true (Ty.abs .func), refs := r } : ElemInst))
          ∘ ElemInst.refs from rfl,
    ← List.map_map, ← List.map_map, h.refs]

theorem StoreElemAgree.funcs {s s' : Store H} (h : StoreElemAgree s s') : s.funcs = s'.funcs := by
  have := congrArg Store.funcs h.base
  simpa using this

theorem StoreElemAgree.length {s s' : Store H} (h : StoreElemAgree s s') :
    s.elems.length = s'.elems.length := by
  have := congrArg List.length h.refs
  simpa using this

theorem StoreElemAgree.refl (s : Store H) : StoreElemAgree s s := ⟨rfl, rfl⟩

theorem StoreElemAgree.allocElem {s s' : Store H} (h : StoreElemAgree s s') (rt rt' : CRefType)
    (refs : List Ref) :
    StoreElemAgree (Silmaril.Wasm.Execution.Core.allocElem s rt refs).1
      (Silmaril.Wasm.Execution.Core.allocElem s' rt' refs).1 :=
  ⟨h.base, by simp [Silmaril.Wasm.Execution.Core.allocElem, h.refs]⟩

theorem StoreElemAgree.allocFunc {s s' : Store H} (h : StoreElemAgree s s') (d : DefType)
    (code : FuncCode H) (mi : ModuleInst) :
    StoreElemAgree (Silmaril.Wasm.Execution.Core.allocFunc s d code mi).1
      (Silmaril.Wasm.Execution.Core.allocFunc s' d code mi).1 := by
  refine ⟨?_, h.refs⟩
  show ({ s with funcs := s.funcs ++ [⟨d, mi, code⟩], elems := [] } : Store H)
    = { s' with funcs := s'.funcs ++ [⟨d, mi, code⟩], elems := [] }
  rw [h.funcs, show ({ s with funcs := s'.funcs ++ [⟨d, mi, code⟩], elems := [] } : Store H)
        = { ({ s with elems := [] } : Store H) with
            funcs := s'.funcs ++ [⟨d, mi, code⟩] } from rfl, h.base]

/-- The element addresses `$allocelems` hands out depend only on the store's
element count, not on the types allocated. -/
theorem allocMany_allocElem_snd :
    ∀ (ps : List (CRefType × List Ref)) (s : Store H),
      (allocMany (fun t (p : CRefType × List Ref) =>
          Silmaril.Wasm.Execution.Core.allocElem t p.1 p.2) s ps).2
        = List.range' s.elems.length ps.length
  | [], _ => by simp [allocMany]
  | p :: ps, s => by
      have ih := allocMany_allocElem_snd ps
        ({ s with elems := s.elems ++ [⟨p.1, p.2⟩] } : Store H)
      show _ :: _ = _
      rw [ih]
      simp [List.range'_succ]

theorem allocMany_allocElem_agree :
    ∀ (ps ps' : List (CRefType × List Ref)) (s s' : Store H),
      ps.map Prod.snd = ps'.map Prod.snd → StoreElemAgree s s' →
      StoreElemAgree
        (allocMany (fun t (p : CRefType × List Ref) =>
          Silmaril.Wasm.Execution.Core.allocElem t p.1 p.2) s ps).1
        (allocMany (fun t (p : CRefType × List Ref) =>
          Silmaril.Wasm.Execution.Core.allocElem t p.1 p.2) s' ps').1
  | [], ps', s, s', hm, h => by
      rw [show ps' = [] from List.eq_nil_of_map_eq_nil hm.symm]
      exact h
  | p :: ps, ps', s, s', hm, h => by
      cases ps' with
      | nil => exact absurd hm (by simp)
      | cons p' ps'' =>
        simp only [List.map_cons, List.cons.injEq] at hm
        show StoreElemAgree (allocMany _ ({ s with elems := s.elems ++ [⟨p.1, p.2⟩] }) ps).1
          (allocMany _ ({ s' with elems := s'.elems ++ [⟨p'.1, p'.2⟩] }) ps'').1
        refine allocMany_allocElem_agree ps ps'' _ _ hm.2 ?_
        rw [hm.1]
        exact ⟨h.base, by simp [h.refs]⟩

theorem allocMany_allocFunc_agree (mi : ModuleInst) :
    ∀ (fs : List (DefType × Wasm.Func)) (s s' : Store H), StoreElemAgree s s' →
      StoreElemAgree (allocMany (fun t (p : DefType × Wasm.Func) =>
          Silmaril.Wasm.Execution.Core.allocFunc t p.1 (.wasm p.2) mi) s fs).1
        (allocMany (fun t (p : DefType × Wasm.Func) =>
          Silmaril.Wasm.Execution.Core.allocFunc t p.1 (.wasm p.2) mi) s' fs).1
  | [], _, _, h => h
  | f :: fs, s, s', h => by
      show StoreElemAgree
        (allocMany _ (Silmaril.Wasm.Execution.Core.allocFunc s f.1 (.wasm f.2) mi).1 fs).1
        (allocMany _ (Silmaril.Wasm.Execution.Core.allocFunc s' f.1 (.wasm f.2) mi).1 fs).1
      exact allocMany_allocFunc_agree mi fs _ _ (h.allocFunc _ _ _)

theorem zip_map_snd_congr {α β γ : Type _} : ∀ (l : List α) (l' : List β) (r : List γ),
    l.length = l'.length → (l.zip r).map Prod.snd = (l'.zip r).map Prod.snd
  | [], [], _, _ => rfl
  | _ :: l, _ :: l', r, h => by
      cases r with
      | nil => rfl
      | cons x r => simp [zip_map_snd_congr l l' r (by simpa using h)]

/-- **`$allocmodule` is blind to element-segment types.** Changing only the
element segments of a module — keeping their number — gives the same module
instance and a store that differs only in the TYPE fields of the allocated
`eleminst`s (`9-module:77-79`, `Execution/Core/Instantiation.lean:75`). -/
theorem allocModule?_elemTypes {s : Store H} {c : Wasm.Module}
    {E : List Wasm.Elem} {xas : List ExternAddr} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {s₄ : Store H} {mi : ModuleInst}
    (hlen : E.length = c.elems.length)
    (h : allocModule? s c xas valsG refsT refsE = some (s₄, mi)) :
    ∃ s₄', allocModule? s { c with elems := E } xas valsG refsT refsE = some (s₄', mi) ∧
      Store.eraseElemTypes s₄' = Store.eraseElemTypes s₄ := by
  simp only [allocModule?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, allocMany_allocElem_snd, List.length_zip,
    List.length_map, hlen] at h ⊢
  obtain ⟨a, ha, a1, ha1, a2, ha2, hs, hm⟩ := h
  refine ⟨_, ⟨a, ha, a1, ha1, a2, ha2, rfl, hm⟩, ?_⟩
  rw [← hs]
  exact (allocMany_allocFunc_agree _ _ _ _
    (allocMany_allocElem_agree _ _ _ _ (zip_map_snd_congr _ _ _ (by simp [hlen]))
      (StoreElemAgree.refl _))).erase

/-! ### The two retypings -/

theorem binaryRetype_init (e : Wasm.Elem) : (Elem.binaryRetype e).init = e.init := by
  unfold Elem.binaryRetype; split <;> rfl

theorem binaryRetype_mode (e : Wasm.Elem) : (Elem.binaryRetype e).mode = e.mode := by
  unfold Elem.binaryRetype; split <;> rfl

/-- The inverse of `Elem.binaryRetype` on the image of `Elem.toCore`: `(ref func)`
is not in the image of `RefType.toCore`, so it can only have come from a retyped
function-index segment. -/
def Elem.binaryUnretype (e : Wasm.Elem) : Wasm.Elem :=
  if e.type = coreRefFunc then { e with type := coreFuncref } else e

theorem binaryUnretype_init (e : Wasm.Elem) : (Elem.binaryUnretype e).init = e.init := by
  unfold Elem.binaryUnretype; split <;> rfl

theorem binaryUnretype_mode (e : Wasm.Elem) : (Elem.binaryUnretype e).mode = e.mode := by
  unfold Elem.binaryUnretype; split <;> rfl

/-- `$runelem_` reads a segment's mode and the *number* of its initializers, never
its type (`9-module`, `Execution/Core/Instantiation.lean:145`). -/
theorem runElem_retype {g : Wasm.Elem → Wasm.Elem} (hinit : ∀ e, (g e).init = e.init)
    (hmode : ∀ e, (g e).mode = e.mode) (i : Nat) (e : Wasm.Elem) :
    runElem i (g e) = runElem i e := by
  simp only [runElem, hinit, hmode]

theorem runElemCode_retype (c : Wasm.Module) {g : Wasm.Elem → Wasm.Elem}
    (hinit : ∀ e, (g e).init = e.init) (hmode : ∀ e, (g e).mode = e.mode) :
    ((List.range (c.elems.map g).length).zip (c.elems.map g)).flatMap
        (fun (i, e) => runElem i e)
      = ((List.range c.elems.length).zip c.elems).flatMap (fun (i, e) => runElem i e) := by
  rw [List.length_map, List.zip_map_right, List.flatMap_map]
  refine List.flatMap_congr fun p _ => ?_
  obtain ⟨i, e⟩ := p
  exact runElem_retype hinit hmode i e

end Bridge

/-- **binary-faithful embedding, validity half.** The binary-faithful image of a valid 2.0
module image is valid, with the *same* Core 3.0 module type: `(ref func) <: funcref`,
so retyped segments still match their tables, each `ref.func x` initializer
already has the non-nullable type `(ref func)` (its index is in `C.REFS`), and
`C.ELEMS` is only ever used on the left of a subtyping premise. Compare
`Lime1.Validation.ModuleValid.toCoreBinary_ok` (`Binary/Bridge.lean:66`). -/
theorem Module.toCoreBinary_ok {m : Module} {c cb : Wasm.Module} {mt : CModuleType}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : ModuleOk c mt) : ModuleOk cb mt := by
  have hcb : cb = Module.binaryRetype c := by
    rw [Module.toCoreBinary, hc] at hb
    exact (Option.some.inj hb).symm
  subst hcb
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
  obtain ⟨gs, hgs, fs, hfs, es, hes, ds, hds, rfl⟩ := hc
  refine Bridge.ModuleOk.retypeElems Bridge.binaryRetype_init Bridge.binaryRetype_mode ?_ ?_ ?_ ?_ h
  · intro t ht
    obtain ⟨t₀, -, rfl⟩ := List.mem_map.1 ht
    simp only [TableType.toCoreTable, TableType.toCore]
    cases t₀.element <;> rfl
  · intro im him tt hty
    obtain ⟨im₀, -, rfl⟩ := List.mem_map.1 him
    cases h₀ : im₀.desc with
    | table tt₀ =>
      rw [show (Import.toCore im₀).type = ImportDesc.toCore im₀.desc from rfl, h₀] at hty
      simp only [ImportDesc.toCore, Wasm.ExternType.table.injEq] at hty
      subst hty
      simp only [TableType.toCore]
      cases tt₀.element <;> rfl
    | func _ => exact absurd hty (by simp [Import.toCore, ImportDesc.toCore, h₀])
    | memory _ => exact absurd hty (by simp [Import.toCore, ImportDesc.toCore, h₀])
    | global _ => exact absurd hty (by simp [Import.toCore, ImportDesc.toCore, h₀])
  · intro dts htypes' d hd f hExp
    rw [Bridge.typesOk_toCoreRec m.types htypes'] at hd
    obtain ⟨ft, -, rfl⟩ := List.mem_map.1 hd
    have hx := Expand.iff.mp hExp
    rw [FuncType.toDefType_expand] at hx
    exact absurd hx (by simp)
  · intro C hW e he hel
    by_cases hf : Elem.coreFuncIdxForm e = true
    · have hbr : Elem.binaryRetype e = { e with type := coreRefFunc } := by
        simp [Elem.binaryRetype, hf]
      simp only [Elem.coreFuncIdxForm, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hf
      obtain ⟨hty, hall⟩ := hf
      rw [hbr]
      refine ⟨.ref (.abs _), ?_, ?_⟩
      · intro ex hex
        obtain ⟨y, rfl⟩ := Bridge.funcIdxInit?_eq (hall ex hex)
        have hcx := hel.2.2.1 _ hex
        rw [hty] at hcx
        exact Bridge.refFunc_const_nonnull hW hcx
      · intro h₂ hs
        rw [hty] at hs
        exact Bridge.sub_ref_null_left hs
    · rw [show Elem.binaryRetype e = e by simp [Elem.binaryRetype, hf]]
      exact ⟨hel.2.1, hel.2.2.1, fun _ hs => hs⟩

/-- **binary-faithful embedding, validity half**, in the `ModuleValid` form. -/
theorem Module.toCoreBinary_valid {m : Module} {c cb : Wasm.Module}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : ModuleValid c) : ModuleValid cb :=
  let ⟨mt, hok⟩ := h
  ⟨mt, Module.toCoreBinary_ok hc hb hok⟩

/-- **binary-faithful embedding, validity half, converse direction.** A module that Core 3.0
decodes from 2.0 bytes is valid exactly when the syntax-faithful image is, with
the same module type. The retyping is undone by `Elem.binaryUnretype`: a 2.0
element segment's Core type is `RefType.toCore`-nullable, so `(ref func)` can
only have come from `coreFuncIdxForm`. Validity carries back because every table
of a 2.0 image has a *nullable* element type and `Reftype_sub/null` ignores the
subtype's nullability. -/
theorem Module.toCore_ok_of_binary {m : Module} {c cb : Wasm.Module} {mt : CModuleType}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : ModuleOk cb mt) : ModuleOk c mt := by
  have hcb : cb = Module.binaryRetype c := by
    rw [Module.toCoreBinary, hc] at hb
    exact (Option.some.inj hb).symm
  subst hcb
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
  obtain ⟨gs, hgs, fs, hfs, es, hes, ds, hds, rfl⟩ := hc
  have hnotfunc : ∀ e ∈ es, e.type ≠ coreRefFunc := by
    intro e he
    obtain ⟨e₀, -, hec⟩ := Bridge.mem_of_mapM hes e he
    obtain ⟨ty, init, mode⟩ := e₀
    simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hec
    obtain ⟨is, -, md, -, rfl⟩ := hec
    cases ty <;> simp [RefType.toCore, coreRefFunc]
  have hmapback : (es.map Elem.binaryRetype).map Bridge.Elem.binaryUnretype = es := by
    rw [List.map_map]
    refine Bridge.map_eq_self fun e he => ?_
    obtain ⟨ty, init, mode⟩ := e
    by_cases hf : Elem.coreFuncIdxForm ⟨ty, init, mode⟩ = true
    · have hty : ty = coreFuncref := by
        simp only [Elem.coreFuncIdxForm, Bool.and_eq_true, decide_eq_true_eq] at hf
        exact hf.1
      subst hty
      simp [Elem.binaryRetype, Bridge.Elem.binaryUnretype, hf, coreRefFunc, coreFuncref]
    · simp [Elem.binaryRetype, Bridge.Elem.binaryUnretype, hf, hnotfunc _ he]
  have key := Bridge.ModuleOk.retypeElems (g := Bridge.Elem.binaryUnretype)
    Bridge.binaryUnretype_init Bridge.binaryUnretype_mode ?_ ?_ ?_ ?_ h
  · rw [show (Module.binaryRetype _).elems = es.map Elem.binaryRetype from rfl, hmapback] at key
    exact key
  · intro t ht
    obtain ⟨t₀, -, rfl⟩ := List.mem_map.1 ht
    simp only [TableType.toCoreTable, TableType.toCore]
    cases t₀.element <;> rfl
  · intro im him tt hty
    obtain ⟨im₀, -, rfl⟩ := List.mem_map.1 him
    cases h₀ : im₀.desc with
    | table tt₀ =>
      rw [show (Import.toCore im₀).type = ImportDesc.toCore im₀.desc from rfl, h₀] at hty
      simp only [ImportDesc.toCore, Wasm.ExternType.table.injEq] at hty
      subst hty
      simp only [TableType.toCore]
      cases tt₀.element <;> rfl
    | func _ => exact absurd hty (by simp [Import.toCore, ImportDesc.toCore, h₀])
    | memory _ => exact absurd hty (by simp [Import.toCore, ImportDesc.toCore, h₀])
    | global _ => exact absurd hty (by simp [Import.toCore, ImportDesc.toCore, h₀])
  · intro dts htypes' d hd f hExp
    rw [Bridge.typesOk_toCoreRec m.types htypes'] at hd
    obtain ⟨ft, -, rfl⟩ := List.mem_map.1 hd
    have hx := Expand.iff.mp hExp
    rw [FuncType.toDefType_expand] at hx
    exact absurd hx (by simp)
  · intro C _ e he hel
    by_cases hf : e.type = coreRefFunc
    · rw [show Bridge.Elem.binaryUnretype e = { e with type := coreFuncref } by
        simp [Bridge.Elem.binaryUnretype, hf]]
      refine ⟨.ref (.abs _), ?_, ?_⟩
      · intro ex hex
        refine Bridge.exprOkConst_sub (hel.2.2.1 ex hex) ?_ (.refv (.ref (.abs _)))
        rw [hf]
        exact .refv (.refNull .heapRefl)
      · intro h₂ hs
        rw [hf] at hs
        exact Bridge.sub_ref_null_right hs
    · rw [show Bridge.Elem.binaryUnretype e = e by simp [Bridge.Elem.binaryUnretype, hf]]
      exact ⟨hel.2.1, hel.2.2.1, fun _ hs => hs⟩

/-- **binary-faithful embedding, validity half, converse direction**, in the `ModuleValid` form. -/
theorem Module.toCore_valid_of_binary {m : Module} {c cb : Wasm.Module}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : ModuleValid cb) : ModuleValid c :=
  let ⟨mt, hok⟩ := h
  ⟨mt, Module.toCore_ok_of_binary hc hb hok⟩

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics in
/-- **binary-faithful embedding, instantiation half.** Instantiating the binary-faithful image
reaches the same configuration as instantiating the syntax-faithful image, up to
the `TYPE` fields of the allocated element instances: `$runelem_` never reads
them (`Execution/Core/Instantiation.lean:145`) and `$allocelem` only stores them
(`:75`). Compare `Lime1.Execution.Instantiation.toCoreBinary`
(`Binary/BridgeInstantiation.lean:40`). -/
theorem Module.toCoreBinary_instantiate {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : Module} {c cb : Wasm.Module} {xas : List ExternAddr} {cfg : Config H}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : Instantiate P host s c xas cfg) :
    ∃ cfg' : Config H, Instantiate P host s cb xas cfg' ∧
      Store.eraseElemTypes cfg'.store = Store.eraseElemTypes cfg.store ∧
      cfg'.frame = cfg.frame ∧ cfg'.code = cfg.code := by
  have hcb : cb = Module.binaryRetype c := by
    rw [Module.toCoreBinary, hc] at hb
    exact (Option.some.inj hb).symm
  subst hcb
  obtain ⟨hvalid, hbounded, hrun⟩ := h
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, he, halloc, rfl⟩ := hrun
  obtain ⟨s₄', halloc', herase⟩ :=
    Bridge.allocModule?_elemTypes (E := c.elems.map Elem.binaryRetype) (by simp) halloc
  refine ⟨_, ⟨?_, ?_, ⟨s₁, s₂, s₃, s₄', f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, ?_,
    halloc', rfl⟩⟩, herase, rfl, ?_⟩
  · obtain ⟨xtE, xtI, hok, hxas⟩ := hvalid
    exact ⟨xtE, xtI, Module.toCoreBinary_ok hc hb hok, hxas⟩
  · refine ⟨?_, hbounded.2.1, hbounded.2.2.1, ?_⟩
    · simpa [Module.binaryRetype] using hbounded.1
    · intro e hee
      simp only [Module.binaryRetype, List.mem_map] at hee
      obtain ⟨e₀, he₀, rfl⟩ := hee
      rw [Bridge.binaryRetype_init]
      exact hbounded.2.2.2 e₀ he₀
  · rw [show (Module.binaryRetype c).elems.map Wasm.Elem.init = c.elems.map Wasm.Elem.init by
      simp [Module.binaryRetype, List.map_map, Function.comp_def, Bridge.binaryRetype_init]]
    exact he
  · simp only [Module.binaryRetype]
    rw [Bridge.runElemCode_retype c Bridge.binaryRetype_init Bridge.binaryRetype_mode]

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics in
/-- **binary-faithful embedding, instantiation half**, converse direction: what Core 3.0
decodes from 2.0 bytes instantiates exactly as the syntactic image does. -/
theorem Module.toCore_instantiate_of_binary {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {m : Module} {c cb : Wasm.Module} {xas : List ExternAddr} {cfg : Config H}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : Instantiate P host s cb xas cfg) :
    ∃ cfg' : Config H, Instantiate P host s c xas cfg' ∧
      Store.eraseElemTypes cfg'.store = Store.eraseElemTypes cfg.store ∧
      cfg'.frame = cfg.frame ∧ cfg'.code = cfg.code := by
  have hcb : cb = Module.binaryRetype c := by
    rw [Module.toCoreBinary, hc] at hb
    exact (Option.some.inj hb).symm
  subst hcb
  obtain ⟨hvalid, hbounded, hrun⟩ := h
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, he, halloc, rfl⟩ := hrun
  obtain ⟨s₄', halloc', herase⟩ :=
    Bridge.allocModule?_elemTypes (c := Module.binaryRetype c) (E := c.elems)
      (by simp [Module.binaryRetype]) halloc
  rw [show ({ Module.binaryRetype c with elems := c.elems } : Wasm.Module) = c from rfl] at halloc'
  refine ⟨_, ⟨?_, ?_, ⟨s₁, s₂, s₃, s₄', f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, ?_,
    halloc', rfl⟩⟩, herase, rfl, ?_⟩
  · obtain ⟨xtE, xtI, hok, hxas⟩ := hvalid
    exact ⟨xtE, xtI, Module.toCore_ok_of_binary hc hb hok, hxas⟩
  · refine ⟨?_, hbounded.2.1, hbounded.2.2.1, ?_⟩
    · simpa [Module.binaryRetype] using hbounded.1
    · intro e hee
      have := hbounded.2.2.2 (Elem.binaryRetype e) (by
        simp only [Module.binaryRetype, List.mem_map]
        exact ⟨e, hee, rfl⟩)
      rwa [Bridge.binaryRetype_init] at this
  · rw [show c.elems.map Wasm.Elem.init
        = (Module.binaryRetype c).elems.map Wasm.Elem.init by
      simp [Module.binaryRetype, List.map_map, Function.comp_def, Bridge.binaryRetype_init]]
    exact he
  · simp only [Module.binaryRetype]
    rw [Bridge.runElemCode_retype c Bridge.binaryRetype_init Bridge.binaryRetype_mode]

end Silmaril.Wasm.V2
