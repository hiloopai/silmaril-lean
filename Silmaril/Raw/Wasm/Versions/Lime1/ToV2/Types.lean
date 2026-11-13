module

public import Silmaril.Wasm.Lime1.ToCore.Instructions
public import Silmaril.Wasm.V1.ToCore.Types
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# Lime1 types and immediates as WebAssembly 2.0 syntax

The type half of the subset theorem `Lime1 ⊆ 2.0`. Every Lime1 type, operator
and descriptor is literally a Wasm 2.0 one: Lime1's four scalar value types are
2.0 `numtype`s, its single implicit table is a `funcref` table, its
sign-extension unary operators and its saturating conversions are exactly the
2.0 ones, and its import/export descriptors have the same four alternatives.
`toV2` is therefore **total** at every sort below, and `ofV2?` recognises
exactly its image — 2.0's reference and vector types, multiple tables, and
explicit `select` type annotations are rejected.

**The conversion operators are the one place where the shapes differ.** Lime1
reuses the shared, *typed* `Silmaril.Wasm.ConvertOp`, whereas 2.0 writes
`CVTOP numtype_1 numtype_2 cvtop` with an *untyped* `cvtop` carrying the target
and source separately (`1-syntax:437`, `specification/wasm-2.0` at
WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36`). `ConvertOp.toV2`
is therefore valued in the triple `NumType × NumType × V2.CvtOp` — it is
`V2.CvtOp.ofCore` — and `ConvertOp.ofV2?` is the partial `V2.CvtOp.toCore`.
This is *not* a widening: `V2.CvtOp.ofCore` is total and injective, so Lime1
conversions inject.

## Commuting with the Core 3.0 injections

Each `toV2` here is accompanied by the triangle

```
Lime1.X.toV2 >> V2.X.toCore = V1.X.toCore
```

(`V1` because Lime1 shares the 1.0 types verbatim). These are the lemmas that
make the module-level triangle of `Lime1/ToV2/Modules.lean` a `simp` call, and
they are all definitional: `V2.widen32` and `V1.widen32` are the same function,
`V2.RefType.toCore .funcref` is `V1.funcref`, and `V2.FuncType.toCoreRec` and
`V1.FuncType.toCoreRec` build the same singleton final recursive group.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1

/-! ## Generic plumbing -/

/-- A total map with a partial left inverse is injective; the `ToV2` copy of
`V2.injective_of_ofCore?`. -/
theorem injective_of_ofV2? {α β : Type*} {f : α → β} {g : β → Option α}
    (h : ∀ a, g (f a) = some a) : Function.Injective f :=
  V2.injective_of_ofCore? h

/-- `List.mapM` of a partial map along a total one, when the composite is
everywhere defined. Used for every list-valued module component. -/
theorem mapM_map_some {α β γ : Type*} {g : α → β} {f : β → Option γ} {h : α → γ}
    (hfg : ∀ a, f (g a) = some (h a)) :
    ∀ xs : List α, (xs.map g).mapM f = some (xs.map h)
  | [] => rfl
  | a :: xs => by
      simp only [List.map_cons, List.mapM_cons, hfg a, mapM_map_some hfg xs]
      rfl

/-! ## Value types -/

/-- Lime1's value types are the 2.0 `numtype`s (`1-syntax:126`). -/
def ValType.toV2 (t : ValType) : V2.ValType := .num t

/-- The retraction of `ValType.toV2`: 2.0 vector and reference types are not
Lime1 syntax. -/
def ValType.ofV2? : V2.ValType → Option ValType
  | .num t => some t
  | _ => none

@[simp] theorem ValType.ofV2?_toV2 (t : ValType) : ValType.ofV2? (ValType.toV2 t) = some t := rfl

theorem ValType.toV2_injective : Function.Injective ValType.toV2 :=
  injective_of_ofV2? ValType.ofV2?_toV2

@[simp] theorem ValType.toV2_toCore (t : ValType) :
    (ValType.toV2 t).toCore = V1.ValType.toCore t := rfl

/-! ## Block types -/

/-- Lime1's indexed block signatures are 2.0 block types (`1-syntax:400`). -/
def BlockType.toV2 : BlockType → V2.BlockType
  | .empty => .result none
  | .value t => .result (some (ValType.toV2 t))
  | .typeIdx i => .typeIdx i

/-- The retraction of `BlockType.toV2`. -/
def BlockType.ofV2? : V2.BlockType → Option BlockType
  | .result none => some .empty
  | .result (some t) => (ValType.ofV2? t).map BlockType.value
  | .typeIdx i => some (.typeIdx i)

@[simp] theorem BlockType.ofV2?_toV2 (t : BlockType) : BlockType.ofV2? t.toV2 = some t := by
  cases t <;> rfl

theorem BlockType.toV2_injective : Function.Injective BlockType.toV2 :=
  injective_of_ofV2? BlockType.ofV2?_toV2

@[simp] theorem BlockType.toV2_toCore (t : BlockType) :
    (BlockType.toV2 t).toCore = BlockType.toCore t := by
  cases t <;> rfl

/-! ## External types -/

/-- Both bounds are `u32` in Lime1 and in 2.0 (`1-syntax:164`). -/
def Limits.toV2 (l : Limits) : V2.Limits := ⟨l.min, l.max⟩

/-- The retraction of `Limits.toV2`. -/
def Limits.ofV2? (l : V2.Limits) : Option Limits := some ⟨l.min, l.max⟩

@[simp] theorem Limits.ofV2?_toV2 (l : Limits) : Limits.ofV2? (Limits.toV2 l) = some l := by
  cases l; rfl

theorem Limits.toV2_injective : Function.Injective Limits.toV2 :=
  injective_of_ofV2? Limits.ofV2?_toV2

@[simp] theorem Limits.toV2_toCore (l : Limits) :
    (Limits.toV2 l).toCore = V1.Limits.toCore l := by
  cases l with
  | mk min max => cases max <;> rfl

/-- 2.0 keeps the multi-result function types Lime1 already has
(`1-syntax:169`). -/
def FuncType.toV2 (t : FuncType) : V2.FuncType :=
  ⟨t.params.map ValType.toV2, t.results.map ValType.toV2⟩

/-- The retraction of `FuncType.toV2`. -/
def FuncType.ofV2? (t : V2.FuncType) : Option FuncType := do
  return ⟨← t.params.mapM ValType.ofV2?, ← t.results.mapM ValType.ofV2?⟩

@[simp] theorem FuncType.ofV2?_toV2 (t : FuncType) : FuncType.ofV2? (FuncType.toV2 t) = some t := by
  cases t
  simp [FuncType.toV2, FuncType.ofV2?, List.mapM_map, Function.comp_def]

theorem FuncType.toV2_injective : Function.Injective FuncType.toV2 :=
  injective_of_ofV2? FuncType.ofV2?_toV2

@[simp] theorem FuncType.toV2_toCore (t : FuncType) :
    (FuncType.toV2 t).toCore = V1.FuncType.toCore t := by
  simp [FuncType.toV2, V2.FuncType.toCore, V1.FuncType.toCore, V2.ResultType.toCore,
    List.map_map, Function.comp_def]

@[simp] theorem FuncType.toV2_toCoreRec (t : FuncType) :
    (FuncType.toV2 t).toCoreRec = V1.FuncType.toCoreRec t := by
  simp [V2.FuncType.toCoreRec, V1.FuncType.toCoreRec]

/-- A Lime1 table is a `funcref` table; 2.0 chooses the element type
(`1-syntax:171`). -/
def TableType.toV2 (t : TableType) : V2.TableType := ⟨Limits.toV2 t.limits, .funcref⟩

/-- The retraction of `TableType.toV2`: an `externref` table is not Lime1
syntax. -/
def TableType.ofV2? (t : V2.TableType) : Option TableType :=
  match t.element with
  | .funcref => (Limits.ofV2? t.limits).map V1.TableType.mk
  | .externref => none

@[simp] theorem TableType.ofV2?_toV2 (t : TableType) :
    TableType.ofV2? (TableType.toV2 t) = some t := by
  cases t
  simp [TableType.toV2, TableType.ofV2?]

theorem TableType.toV2_injective : Function.Injective TableType.toV2 :=
  injective_of_ofV2? TableType.ofV2?_toV2

@[simp] theorem TableType.toV2_toCore (t : TableType) :
    (TableType.toV2 t).toCore = V1.TableType.toCore t := by
  simp [TableType.toV2, V2.TableType.toCore, V1.TableType.toCore, V1.funcref,
    V2.RefType.toCore]

/-- `memtype` is the same `u32` pair in both (`1-syntax:173`). -/
def MemoryType.toV2 (t : MemoryType) : V2.MemoryType := ⟨Limits.toV2 t.limits⟩

/-- The retraction of `MemoryType.toV2`. -/
def MemoryType.ofV2? (t : V2.MemoryType) : Option MemoryType :=
  (Limits.ofV2? t.limits).map V1.MemoryType.mk

@[simp] theorem MemoryType.ofV2?_toV2 (t : MemoryType) :
    MemoryType.ofV2? (MemoryType.toV2 t) = some t := by
  cases t
  simp [MemoryType.toV2, MemoryType.ofV2?]

theorem MemoryType.toV2_injective : Function.Injective MemoryType.toV2 :=
  injective_of_ofV2? MemoryType.ofV2?_toV2

@[simp] theorem MemoryType.toV2_toCore (t : MemoryType) :
    (MemoryType.toV2 t).toCore = V1.MemoryType.toCore t := by
  simp [MemoryType.toV2, V2.MemoryType.toCore, V1.MemoryType.toCore]

/-- `globaltype ::= mut valtype` in both (`1-syntax:167`). -/
def GlobalType.toV2 (t : GlobalType) : V2.GlobalType := ⟨t.mutability, ValType.toV2 t.value⟩

/-- The retraction of `GlobalType.toV2`. -/
def GlobalType.ofV2? (t : V2.GlobalType) : Option GlobalType := do
  return ⟨t.mutability, ← ValType.ofV2? t.value⟩

@[simp] theorem GlobalType.ofV2?_toV2 (t : GlobalType) :
    GlobalType.ofV2? (GlobalType.toV2 t) = some t := by
  cases t
  simp [GlobalType.toV2, GlobalType.ofV2?]

theorem GlobalType.toV2_injective : Function.Injective GlobalType.toV2 :=
  injective_of_ofV2? GlobalType.ofV2?_toV2

@[simp] theorem GlobalType.toV2_toCore (t : GlobalType) :
    (GlobalType.toV2 t).toCore = V1.GlobalType.toCore t := by
  simp [GlobalType.toV2, V2.GlobalType.toCore, V1.GlobalType.toCore]

/-! ## Scalar operators -/

/-- Lime1's packed memory widths are the 2.0 ones without `I64`
(`1-syntax:280`); 2.0 reuses the shared `Silmaril.Wasm.PackSize`. -/
def PackSize.toV2 : PackSize → Wasm.PackSize
  | .i8 => .i8
  | .i16 => .i16
  | .i32 => .i32

/-- The retraction of `PackSize.toV2`. -/
def PackSize.ofV2? : Wasm.PackSize → Option PackSize
  | .i8 => some .i8
  | .i16 => some .i16
  | .i32 => some .i32
  | .i64 => none

@[simp] theorem PackSize.ofV2?_toV2 (n : PackSize) : PackSize.ofV2? (PackSize.toV2 n) = some n := by
  cases n <;> rfl

theorem PackSize.toV2_injective : Function.Injective PackSize.toV2 :=
  injective_of_ofV2? PackSize.ofV2?_toV2

theorem PackSize.toV2_eq_toCore (n : PackSize) : PackSize.toV2 n = V1.PackSize.toCore n := by
  cases n <;> rfl

/-- The pointwise `PackSize.toV2_eq_toCore`, for rewriting under `Option.map`. -/
theorem PackSize.toV2_eq_toCore_fun : PackSize.toV2 = V1.PackSize.toCore :=
  funext PackSize.toV2_eq_toCore

/-- Lime1's sign-extension unary operators are the 2.0 ones (`1-syntax:283`);
2.0 reuses the shared `Silmaril.Wasm.IntUnOp`. -/
def IntUnOp.toV2 : IntUnOp → Wasm.IntUnOp
  | .clz => .clz
  | .ctz => .ctz
  | .popcnt => .popcnt
  | .extend n => .extend (PackSize.toV2 n)

/-- The retraction of `IntUnOp.toV2`: `I64` sign extension has no Lime1 form. -/
def IntUnOp.ofV2? : Wasm.IntUnOp → Option IntUnOp
  | .clz => some .clz
  | .ctz => some .ctz
  | .popcnt => some .popcnt
  | .extend n => (PackSize.ofV2? n).map IntUnOp.extend

@[simp] theorem IntUnOp.ofV2?_toV2 (op : IntUnOp) : IntUnOp.ofV2? op.toV2 = some op := by
  cases op <;> simp [IntUnOp.toV2, IntUnOp.ofV2?]

theorem IntUnOp.toV2_injective : Function.Injective IntUnOp.toV2 :=
  injective_of_ofV2? IntUnOp.ofV2?_toV2

theorem IntUnOp.toV2_eq_toCore (op : IntUnOp) : IntUnOp.toV2 op = IntUnOp.toCore op := by
  cases op <;> rfl

/-- 2.0 splits a conversion into a target type, a source type and an untyped
`cvtop` (`1-syntax:437`); this is `V2.CvtOp.ofCore`, which is total. -/
def ConvertOp.toV2 (op : ConvertOp) : NumType × NumType × V2.CvtOp := V2.CvtOp.ofCore op

/-- The retraction of `ConvertOp.toV2`: the 2.0 immediate triples with no
`$cvtop__` equation (`3-numerics:310-320`) are not Lime1 conversions. -/
def ConvertOp.ofV2? : NumType × NumType × V2.CvtOp → Option ConvertOp
  | (target, source, op) => V2.CvtOp.toCore target source op

@[simp] theorem ConvertOp.ofV2?_toV2 (op : ConvertOp) : ConvertOp.ofV2? op.toV2 = some op := by
  cases op with
  | wrap => rfl
  | extend _ => rfl
  | trunc f i _ => cases f <;> cases i <;> rfl
  | truncSat f i _ => cases f <;> cases i <;> rfl
  | convert i f _ => cases i <;> cases f <;> rfl
  | demote => rfl
  | promote => rfl
  | reinterpretInt f => cases f <;> rfl
  | reinterpretFloat i => cases i <;> rfl

theorem ConvertOp.toV2_injective : Function.Injective ConvertOp.toV2 :=
  injective_of_ofV2? ConvertOp.ofV2?_toV2

/-! ## Memory arguments -/

/-- `memarg ::= {ALIGN u32, OFFSET u32}` in both (`1-syntax:383`). -/
def MemArg.toV2 (a : MemArg) : V2.MemArg := ⟨a.align, a.offset⟩

/-- The retraction of `MemArg.toV2`. -/
def MemArg.ofV2? (a : V2.MemArg) : Option MemArg := some ⟨a.align, a.offset⟩

@[simp] theorem MemArg.ofV2?_toV2 (a : MemArg) : MemArg.ofV2? (MemArg.toV2 a) = some a := by
  cases a; rfl

theorem MemArg.toV2_injective : Function.Injective MemArg.toV2 :=
  injective_of_ofV2? MemArg.ofV2?_toV2

@[simp] theorem MemArg.toV2_toCore (a : MemArg) :
    (MemArg.toV2 a).toCore = V1.MemArg.toCore a := rfl

/-- The packed-load immediate of `LOAD` (`1-syntax:507`, `loadop_` at `1-syntax:388`). -/
def loadPackToV2 (p : Option (PackSize × Signedness)) :
    Option (Wasm.PackSize × Signedness) := p.map fun (n, s) => (PackSize.toV2 n, s)

/-- The retraction of `loadPackToV2`. -/
def loadPackOfV2? : Option (Wasm.PackSize × Signedness) →
    Option (Option (PackSize × Signedness))
  | none => some none
  | some (n, s) => (PackSize.ofV2? n).map fun n => some (n, s)

@[simp] theorem loadPackOfV2?_toV2 (p : Option (PackSize × Signedness)) :
    loadPackOfV2? (loadPackToV2 p) = some p := by
  rcases p with _ | ⟨n, s⟩ <;> simp [loadPackToV2, loadPackOfV2?]

theorem loadPackToV2_eq_toCore (p : Option (PackSize × Signedness)) :
    loadPackToV2 p = loadPackToCore p := by
  rcases p with _ | ⟨n, s⟩ <;> simp [loadPackToV2, loadPackToCore, PackSize.toV2_eq_toCore]

/-- The retraction of the packed-store immediate of `STORE` (`1-syntax:508`). -/
def storePackOfV2? : Option Wasm.PackSize → Option (Option PackSize)
  | none => some none
  | some n => (PackSize.ofV2? n).map some

@[simp] theorem storePackOfV2?_toV2 (p : Option PackSize) :
    storePackOfV2? (p.map PackSize.toV2) = some p := by
  cases p <;> simp [storePackOfV2?]

/-! ## Imports and exports -/

/-- `importdesc` has the same four alternatives in both; the function case is a
`typeidx` on both sides (see the deviation recorded in
`Silmaril/Wasm/V2/Modules.lean`). -/
def ImportDesc.toV2 : ImportDesc → V2.ImportDesc
  | .func t => .func t
  | .table t => .table (TableType.toV2 t)
  | .memory t => .memory (MemoryType.toV2 t)
  | .global t => .global (GlobalType.toV2 t)

/-- The retraction of `ImportDesc.toV2`. -/
def ImportDesc.ofV2? : V2.ImportDesc → Option ImportDesc
  | .func t => some (.func t)
  | .table t => (TableType.ofV2? t).map V1.ImportDesc.table
  | .memory t => (MemoryType.ofV2? t).map V1.ImportDesc.memory
  | .global t => (GlobalType.ofV2? t).map V1.ImportDesc.global

@[simp] theorem ImportDesc.ofV2?_toV2 (d : ImportDesc) : ImportDesc.ofV2? (ImportDesc.toV2 d) = some d := by
  cases d <;> simp [ImportDesc.toV2, ImportDesc.ofV2?]

theorem ImportDesc.toV2_injective : Function.Injective ImportDesc.toV2 :=
  injective_of_ofV2? ImportDesc.ofV2?_toV2

@[simp] theorem ImportDesc.toV2_toCore (d : ImportDesc) :
    (ImportDesc.toV2 d).toCore = V1.ImportDesc.toCore d := by
  cases d <;> simp [ImportDesc.toV2, V2.ImportDesc.toCore, V1.ImportDesc.toCore]

/-- `import ::= IMPORT name name externtype` (`1-syntax:564`). -/
def Import.toV2 (i : Import) : V2.Import := ⟨i.moduleName, i.name, ImportDesc.toV2 i.desc⟩

/-- The retraction of `Import.toV2`. -/
def Import.ofV2? (i : V2.Import) : Option Import := do
  return ⟨i.moduleName, i.name, ← ImportDesc.ofV2? i.desc⟩

@[simp] theorem Import.ofV2?_toV2 (i : Import) : Import.ofV2? (Import.toV2 i) = some i := by
  cases i
  simp [Import.toV2, Import.ofV2?]

theorem Import.toV2_injective : Function.Injective Import.toV2 :=
  injective_of_ofV2? Import.ofV2?_toV2

@[simp] theorem Import.toV2_toCore (i : Import) :
    (Import.toV2 i).toCore = V1.Import.toCore i := by
  cases i
  simp [Import.toV2, V2.Import.toCore, V1.Import.toCore]

/-- `externidx` has the same four alternatives in both (`1-syntax:560`); only
the declaration order differs. -/
def ExternIdx.toV2 : ExternIdx → V2.ExternIdx
  | .func i => .func i
  | .table i => .table i
  | .memory i => .memory i
  | .global i => .global i

/-- The retraction of `ExternIdx.toV2`. -/
def ExternIdx.ofV2? : V2.ExternIdx → Option ExternIdx
  | .func i => some (.func i)
  | .table i => some (.table i)
  | .memory i => some (.memory i)
  | .global i => some (.global i)

@[simp] theorem ExternIdx.ofV2?_toV2 (i : ExternIdx) : ExternIdx.ofV2? (ExternIdx.toV2 i) = some i := by
  cases i <;> rfl

theorem ExternIdx.toV2_injective : Function.Injective ExternIdx.toV2 :=
  injective_of_ofV2? ExternIdx.ofV2?_toV2

@[simp] theorem ExternIdx.toV2_toCore (i : ExternIdx) :
    (ExternIdx.toV2 i).toCore = V1.ExternIdx.toCore i := by
  cases i <;> rfl

/-- `export ::= EXPORT name externidx` (`1-syntax:562`). -/
def Export.toV2 (e : Export) : V2.Export := ⟨e.name, ExternIdx.toV2 e.index⟩

/-- The retraction of `Export.toV2`. -/
def Export.ofV2? (e : V2.Export) : Option Export := do
  return ⟨e.name, ← ExternIdx.ofV2? e.index⟩

@[simp] theorem Export.ofV2?_toV2 (e : Export) : Export.ofV2? (Export.toV2 e) = some e := by
  cases e
  simp [Export.toV2, Export.ofV2?]

theorem Export.toV2_injective : Function.Injective Export.toV2 :=
  injective_of_ofV2? Export.ofV2?_toV2

@[simp] theorem Export.toV2_toCore (e : Export) :
    (Export.toV2 e).toCore = V1.Export.toCore e := by
  cases e
  simp [Export.toV2, V2.Export.toCore, V1.Export.toCore]

end Silmaril.Wasm.Lime1
