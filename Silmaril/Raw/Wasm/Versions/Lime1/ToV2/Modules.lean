module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToV2.Instructions
public import Silmaril.Wasm.Lime1.ToCore.Modules
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Wasm.V2.ToCore.Modules

/-!
# Lime1 declarations and modules as WebAssembly 2.0 syntax

The module half of the subset theorem `Lime1 ⊆ 2.0`, and the commuting triangle
that is the point of this directory.

Only two declaration sorts change shape:

* **Tables.** A Lime1 table is implicitly a `funcref` table; 2.0's
  `tabletype ::= limits reftype` (`1-syntax:171`) makes the element type
  explicit, so `TableType.toV2` supplies `FUNCREF` (`Lime1/ToV2/Types.lean`).
* **Element segments.** Lime1's segments are always active and always carry a
  *list of function indices* (`Declaration.ActiveElem`); 2.0's
  `elem ::= ELEM reftype expr* elemmode` (`1-syntax:553`) carries a reference
  type, a list of *initializer expressions* and a mode. `Elem.toV2` therefore
  emits element type `FUNCREF`, mode `ACTIVE tableidx expr`, and the
  initializer `(REF.FUNC y)` for each index `y` — exactly the choices
  `Lime1.Elem.toCore` already makes against Core 3.0.

Everything else is a field-for-field copy.

## The commuting triangle

`Module.toV2_toCore` is

```
V2.Module.toCore (Lime1.Module.toV2 m) = some (Lime1.Module.toCore m)
```

and the same holds at `Instr`, `Expr`, `Func`, `Global`, `Elem`, `Data`,
`Import` and `Export`. The `some` is forced by `V2.Module.toCore` being
`Option`-valued (2.0's `CVTOP` is untyped); the triangle says in particular
that the Lime1 image never meets the undefined part.

## Issue #651: which of `toCore`/`toCoreBinary` the triangle matches

It matches **`toCore`**, the `funcref` reading. `Elem.toV2` assigns element type
`FUNCREF`, `V2.RefType.toCore FUNCREF` is `(ref null func)`, and
`Lime1.Elem.toCore` assigns `V1.funcref = (ref null func)` as well; the
non-nullable `(ref func)` that the Core 3.0 *binary* format decodes for the
function-index element forms (5.4:100-108) appears on neither side.

The binary-faithful variants also commute, and for the same reason:
`V2.Module.toCoreBinary` is `V2.Module.toCore` followed by
`V2.Module.binaryRetype`, and `Elem.binaryRetype_toCore` below shows that
`binaryRetype` retypes *every* element segment in the Lime1 image (each one is
in the function-index form), i.e. that `V2.Module.binaryRetype ∘ Lime1.toCore`
is the `Lime1.Module.toCoreBinary` of `Silmaril/Wasm/Binary/Agreement.lean`.
`Module.binaryRetype_toCore` states that identity in `Agreement`'s own terms; we
do not import the binary layer here, which is why the statement is spelled out
rather than named.

**That last identity is not definitional, and neither is the triangle.**
`V2.Module.binaryRetype m.toCore = Lime1.Module.toCoreBinary m` fails by `rfl`:
`binaryRetype` retypes an element segment only when `V2.funcIdxInit?` holds of
every initializer, and for a variable `m` that guard does not reduce — discharging
it *is* the content of `Elem.binaryRetype_toCore`. Likewise
`V2.Module.toCoreBinary m.toV2 = some (Lime1.Module.toCoreBinary m)` fails by
`rfl`, since `V2.Module.toCore` is a `mapM` over the instruction lists that does
not reduce for a variable module; that is the content of `Module.toV2_toCore`.
What *is* `rfl` is only the final step, after both lemmas have been rewritten
with: the record `{m.toCore with elems := m.elems.map fun e =>
{Elem.toCore e with type := V2.coreRefFunc}}` is `Lime1.Module.toCoreBinary m`
by unfolding. So the triangle is available in the binary layer as the two
rewrites plus `rfl`, which is exactly how
`Silmaril/Wasm/Binary/Lime1V2.lean`'s `toV2_toCoreBinary` proves it.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1

/-! ## Functions -/

/-- `func ::= FUNC typeidx local* expr` (`1-syntax:545`). -/
def Func.toV2 (f : Func) : V2.Func := ⟨f.type, f.locals.map ValType.toV2, Expr.toV2 f.body⟩

/-- The retraction of `Func.toV2`. -/
def Func.ofV2? (f : V2.Func) : Option Func := do
  return ⟨f.type, ← f.locals.mapM ValType.ofV2?, ← Expr.ofV2? f.body⟩

@[simp] theorem Func.ofV2?_toV2 (f : Func) : Func.ofV2? f.toV2 = some f := by
  cases f
  simp [Func.toV2, Func.ofV2?, List.mapM_map, Function.comp_def]

theorem Func.toV2_injective : Function.Injective Func.toV2 :=
  injective_of_ofV2? Func.ofV2?_toV2

@[simp] theorem Func.toV2_toCore (f : Func) : V2.Func.toCore f.toV2 = some f.toCore := by
  cases f
  simp [Func.toV2, V2.Func.toCore, Func.toCore, List.map_map, Function.comp_def]

/-! ## Globals -/

/-- `global ::= GLOBAL globaltype expr` (`1-syntax:547`). -/
def Global.toV2 (g : Global) : V2.Global := ⟨GlobalType.toV2 g.type, Expr.toV2 g.init⟩

/-- The retraction of `Global.toV2`. -/
def Global.ofV2? (g : V2.Global) : Option Global := do
  return ⟨← GlobalType.ofV2? g.type, ← Expr.ofV2? g.init⟩

@[simp] theorem Global.ofV2?_toV2 (g : Global) : Global.ofV2? g.toV2 = some g := by
  cases g
  simp [Global.toV2, Global.ofV2?]

theorem Global.toV2_injective : Function.Injective Global.toV2 :=
  injective_of_ofV2? Global.ofV2?_toV2

@[simp] theorem Global.toV2_toCore (g : Global) : V2.Global.toCore g.toV2 = some g.toCore := by
  cases g
  simp [Global.toV2, V2.Global.toCore, Global.toCore]

/-! ## Tables

A Lime1 table has no initializer and no element type; 2.0 adds the element type
and still has no initializer, so the whole difference is `FUNCREF`. -/

@[simp] theorem TableType.toV2_toCoreTable (t : TableType) :
    V2.TableType.toCoreTable (TableType.toV2 t) = tableToCore t := by
  simp only [V2.TableType.toCoreTable, TableType.toV2_toCore, tableToCore]
  rfl

/-! ## Element segments -/

/-- The 2.0 initializer expression for a Lime1 element-segment entry: 2.0
element segments hold expressions, Lime1 ones hold function indices. -/
def funcRefV2 (f : FuncIdx) : V2.Expr := [.refFunc f]

/-- The retraction of `funcRefV2`. -/
def funcRefV2? : V2.Expr → Option FuncIdx
  | [.refFunc f] => some f
  | _ => none

@[simp] theorem funcRefV2?_funcRefV2 (f : FuncIdx) : funcRefV2? (funcRefV2 f) = some f := rfl

@[simp] theorem funcRefV2_toCore (f : FuncIdx) :
    V2.Expr.toCore (funcRefV2 f) = some (funcRef f) := rfl

/-- `elem ::= ELEM reftype expr* elemmode` (`1-syntax:553`). Lime1 segments are
always active over `funcref`, so the mode is `ACTIVE` and the type `FUNCREF`. -/
def Elem.toV2 (e : Elem) : V2.Elem :=
  ⟨.funcref, e.init.map funcRefV2, .active e.table (Expr.toV2 e.offset)⟩

/-- The retraction of `Elem.toV2`: a passive or declarative segment, an
`externref` segment, or an initializer that is not a single `REF.FUNC` is
outside the Lime1 image. -/
def Elem.ofV2? (c : V2.Elem) : Option Elem :=
  match c.type, c.mode with
  | .funcref, .active table offset => do
      return ⟨table, ← Expr.ofV2? offset, ← c.init.mapM funcRefV2?⟩
  | _, _ => none

@[simp] theorem Elem.ofV2?_toV2 (e : Elem) : Elem.ofV2? e.toV2 = some e := by
  cases e
  simp [Elem.toV2, Elem.ofV2?, List.mapM_map, Function.comp_def]

theorem Elem.toV2_injective : Function.Injective Elem.toV2 :=
  injective_of_ofV2? Elem.ofV2?_toV2

@[simp] theorem Elem.toV2_toCore (e : Elem) : V2.Elem.toCore e.toV2 = some e.toCore := by
  cases e
  simp [Elem.toV2, V2.Elem.toCore, Elem.toCore, V2.ElemMode.toCore, V2.RefType.toCore,
    V1.funcref, mapM_map_some funcRefV2_toCore]

/-! ## Data segments -/

/-- `data ::= DATA byte* datamode` (`1-syntax:555`); Lime1 segments are always
active. -/
def Data.toV2 (d : Data) : V2.Data := ⟨d.bytes, .active d.memory (Expr.toV2 d.offset)⟩

/-- The retraction of `Data.toV2`: a passive segment is outside the Lime1
image. -/
def Data.ofV2? (c : V2.Data) : Option Data :=
  match c.mode with
  | .active memory offset => do return ⟨memory, ← Expr.ofV2? offset, c.bytes⟩
  | .passive => none

@[simp] theorem Data.ofV2?_toV2 (d : Data) : Data.ofV2? d.toV2 = some d := by
  cases d
  simp [Data.toV2, Data.ofV2?]

theorem Data.toV2_injective : Function.Injective Data.toV2 :=
  injective_of_ofV2? Data.ofV2?_toV2

@[simp] theorem Data.toV2_toCore (d : Data) : V2.Data.toCore d.toV2 = some d.toCore := by
  cases d
  simp [Data.toV2, V2.Data.toCore, Data.toCore, V2.DataMode.toCore]

/-! ## Modules -/

/-- `module ::= MODULE type* import* func* global* table* mem* elem* data*
start? export*` (`1-syntax:567`), field for field. -/
def Module.toV2 (m : Module) : V2.Module where
  types := m.types.map FuncType.toV2
  imports := m.imports.map Import.toV2
  funcs := m.funcs.map Func.toV2
  globals := m.globals.map Global.toV2
  tables := m.tables.map TableType.toV2
  memories := m.memories.map MemoryType.toV2
  elems := m.elems.map Elem.toV2
  data := m.data.map Data.toV2
  start := m.start
  exports := m.exports.map Export.toV2

/-- The retraction of `Module.toV2`. -/
def Module.ofV2? (c : V2.Module) : Option Module := do
  return {
    types := ← c.types.mapM FuncType.ofV2?
    imports := ← c.imports.mapM Import.ofV2?
    funcs := ← c.funcs.mapM Func.ofV2?
    globals := ← c.globals.mapM Global.ofV2?
    tables := ← c.tables.mapM TableType.ofV2?
    memories := ← c.memories.mapM MemoryType.ofV2?
    elems := ← c.elems.mapM Elem.ofV2?
    data := ← c.data.mapM Data.ofV2?
    start := c.start
    exports := ← c.exports.mapM Export.ofV2? }

@[simp] theorem Module.ofV2?_toV2 (m : Module) : Module.ofV2? m.toV2 = some m := by
  cases m
  simp [Module.toV2, Module.ofV2?, List.mapM_map, Function.comp_def]

theorem Module.toV2_injective : Function.Injective Module.toV2 :=
  injective_of_ofV2? Module.ofV2?_toV2

/-- **The commuting triangle.** Going through Wasm 2.0 computes exactly the
direct Lime1 → Core 3.0 injection of `Lime1/ToCore/Modules.lean`. -/
@[simp] theorem Module.toV2_toCore (m : Module) :
    V2.Module.toCore m.toV2 = some m.toCore := by
  cases m
  simp [Module.toV2, V2.Module.toCore, Module.toCore, List.map_map, Function.comp_def,
    mapM_map_some Global.toV2_toCore, mapM_map_some Func.toV2_toCore,
    mapM_map_some Elem.toV2_toCore, mapM_map_some Data.toV2_toCore]

/-! ## The binary-faithful variant (issue #651)

`V2.Module.binaryRetype` retypes exactly the element segments in the
function-index form; every Lime1 segment is in that form, so composing it with
the triangle above gives the `Lime1.Module.toCoreBinary` of
`Silmaril/Wasm/Binary/Agreement.lean`. -/

/-- Every Lime1 element segment is in the Core 3.0 function-index form. -/
@[simp] theorem Elem.coreFuncIdxForm_toCore (e : Elem) :
    V2.Elem.coreFuncIdxForm e.toCore = true := by
  cases e
  simp [Elem.toCore, V2.Elem.coreFuncIdxForm, V2.coreFuncref, V1.funcref, funcRef,
    V2.funcIdxInit?, List.all_eq_true]

/-- `V2.Elem.binaryRetype` applied to the Lime1 image is the `Elem.toCoreBinary`
of `Silmaril/Wasm/Binary/Agreement.lean`. -/
@[simp] theorem Elem.binaryRetype_toCore (e : Elem) :
    V2.Elem.binaryRetype e.toCore = { e.toCore with type := V2.coreRefFunc } := by
  simp [V2.Elem.binaryRetype]

/-- `V2.Module.binaryRetype` applied to the Lime1 image is the
`Module.toCoreBinary` of `Silmaril/Wasm/Binary/Agreement.lean`. -/
theorem Module.binaryRetype_toCore (m : Module) :
    V2.Module.binaryRetype m.toCore =
      { m.toCore with
          elems := m.elems.map fun e : Elem => { Elem.toCore e with type := V2.coreRefFunc } } := by
  simp [V2.Module.binaryRetype, Module.toCore, List.map_map, Function.comp_def]

/-- The binary-faithful commuting triangle; see the module documentation. -/
@[simp] theorem Module.toV2_toCoreBinary (m : Module) :
    V2.Module.toCoreBinary m.toV2 = some (V2.Module.binaryRetype m.toCore) := by
  simp [V2.Module.toCoreBinary]

end Silmaril.Wasm.Lime1

namespace Silmaril.Wasm.V1

/-! ## Wasm 1.0 into Wasm 2.0

The 1.0 injection factors through Lime1, with no side condition: `V1 ⊆ Lime1`
is total and `Lime1 ⊆ 2.0` is total. -/

/-- The Wasm 1.0 module as Wasm 2.0 syntax, through Lime1. -/
def Module.toV2 (m : Module) : V2.Module := Lime1.Module.toV2 m.toLime

@[simp] theorem Module.toLime_toV2 (m : Module) : Lime1.Module.toV2 m.toLime = m.toV2 := rfl

theorem Module.toV2_injective : Function.Injective Module.toV2 :=
  Lime1.Module.toV2_injective.comp Module.toLime_injective

/-- The Wasm 1.0 commuting triangle: 1.0 → 2.0 → Core 3.0 is 1.0 → Core 3.0. -/
@[simp] theorem Module.toV2_toCore (m : Module) :
    V2.Module.toCore m.toV2 = some m.toCore := by
  rw [← Module.toLime_toV2, Lime1.Module.toV2_toCore, Module.toLime_toCore]

end Silmaril.Wasm.V1
