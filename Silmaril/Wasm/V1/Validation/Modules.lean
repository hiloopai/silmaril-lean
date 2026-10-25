module

public import Silmaril.Wasm.V1.Validation.Instructions
public import Silmaril.Wasm.V1.Modules

/-!
# WebAssembly 1.0 module validation

The context prepass places imports before definitions in each index space.
Unresolved function-type references are rejected by the corresponding import or
function premise. Global initializers use only imported globals; active segment
offsets use the full module context, as in the 2019 Recommendation. In either
context a constant `global.get` requires an immutable global.

These are declarative validation judgments. They do not implement binary decoding,
import linking, instantiation, or an algorithmic instruction validator.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Validation

def LimitsValid (bound : Nat) (limits : Limits) : Prop :=
  limits.min.val ≤ bound ∧
    ∀ max ∈ limits.max, max.val ≤ bound ∧ limits.min.val ≤ max.val

def FuncTypeValid (ft : FuncType) : Prop := ft.results.length ≤ 1

def TableTypeValid (tt : TableType) : Prop := LimitsValid (2 ^ 32) tt.limits

def MemoryTypeValid (mt : MemoryType) : Prop := LimitsValid (2 ^ 16) mt.limits

def ExternTypeValid : ExternType → Prop
  | .func ft => FuncTypeValid ft
  | .table tt => TableTypeValid tt
  | .memory mt => MemoryTypeValid mt
  | .global _ => True

def importType? (types : List FuncType) : ImportDesc → Option ExternType
  | .func i => (types[i.toNat]?).map .func
  | .table tt => some (.table tt)
  | .memory mt => some (.memory mt)
  | .global gt => some (.global gt)

def exportType? (C : Context) : ExternIdx → Option ExternType
  | .func i => (C.funcs[i.toNat]?).map .func
  | .table i => (C.tables[i.toNat]?).map .table
  | .memory i => (C.memories[i.toNat]?).map .memory
  | .global i => (C.globals[i.toNat]?).map .global

def ImportValid (types : List FuncType) (i : Import) : Prop :=
  ∃ et, importType? types i.desc = some et ∧ ExternTypeValid et

def ExportValid (C : Context) (e : Export) : Prop :=
  ∃ et, exportType? C e.index = some et

/-- Imported globals retain their mutability; mutable imports themselves are valid. -/
def importedGlobals (m : Module) : List GlobalType :=
  m.imports.filterMap fun i => match i.desc with
    | .global gt => some gt
    | _ => none

def moduleContext (m : Module) : Context where
  types := m.types
  funcs := (m.imports.filterMap fun i => match i.desc with
      | .func idx => m.types[idx.toNat]?
      | _ => none) ++
    m.funcs.filterMap (fun f => m.types[f.type.toNat]?)
  tables := (m.imports.filterMap fun i => match i.desc with
      | .table tt => some tt
      | _ => none) ++ m.tables
  memories := (m.imports.filterMap fun i => match i.desc with
      | .memory mt => some mt
      | _ => none) ++ m.memories
  globals := importedGlobals m ++ m.globals.map Global.type

/-- No defined global, function, table, or memory is in an initializer's context. -/
def initializerContext (m : Module) : Context where
  globals := importedGlobals m

def functionContext (C : Context) (ft : FuncType) (locals : List ValType) : Context :=
  { C with
    locals := ft.params ++ locals
    labels := [ft.results]
    returnType := some ft.results }

inductive ConstantInstr (C : Context) : Instr → Prop where
  | intConst (t : IntType) (bits : BitVec t.width) : ConstantInstr C (.intConst t bits)
  | floatConst (t : FloatType) (bits : BitVec t.width) : ConstantInstr C (.floatConst t bits)
  | globalGet (i : GlobalIdx) {t : ValType}
      (h : C.globals[i.toNat]? = some ⟨.const, t⟩) : ConstantInstr C (.globalGet i)

def ConstantExpr (C : Context) (body : Expr) : Prop :=
  ∀ i ∈ body, ConstantInstr C i

structure ConstExprType (C : Context) (body : Expr) (t : ValType) : Prop where
  typed : ExprType C body [] [t]
  constant : ConstantExpr C body

def FuncValid (C : Context) (f : Func) : Prop :=
  ∃ ft, C.types[f.type.toNat]? = some ft ∧ FuncTypeValid ft ∧
    ExprType (functionContext C ft f.locals) f.body [] ft.results

def GlobalValid (C : Context) (g : Global) : Prop :=
  ConstExprType C g.init g.type.value

structure ElemValid (C : Context) (e : Elem) : Prop where
  table : ∃ tt, C.tables[e.table.toNat]? = some tt
  offset : ConstExprType C e.offset .i32
  functions : ∀ i ∈ e.init, ∃ ft, C.funcs[i.toNat]? = some ft

structure DataValid (C : Context) (d : Data) : Prop where
  memory : ∃ mt, C.memories[d.memory.toNat]? = some mt
  offset : ConstExprType C d.offset .i32

def StartValid (C : Context) (start : Option FuncIdx) : Prop :=
  ∀ i ∈ start, C.funcs[i.toNat]? = some ⟨[], []⟩

/-- All module components are checked, including the combined imported/defined index spaces. -/
structure ModuleValid (m : Module) : Prop where
  types : ∀ ft ∈ m.types, FuncTypeValid ft
  imports : ∀ i ∈ m.imports, ImportValid m.types i
  functions : ∀ f ∈ m.funcs, FuncValid (moduleContext m) f
  tables : ∀ tt ∈ m.tables, TableTypeValid tt
  memories : ∀ mt ∈ m.memories, MemoryTypeValid mt
  globals : ∀ g ∈ m.globals, GlobalValid (initializerContext m) g
  elements : ∀ e ∈ m.elems, ElemValid (moduleContext m) e
  data : ∀ d ∈ m.data, DataValid (moduleContext m) d
  start : StartValid (moduleContext m) m.start
  exports : ∀ e ∈ m.exports, ExportValid (moduleContext m) e
  uniqueExports : (m.exports.map Export.name).Nodup
  singleTable : (moduleContext m).tables.length ≤ 1
  singleMemory : (moduleContext m).memories.length ≤ 1

namespace ModuleValid

variable {m : Module}

/-- Validation rejects an unresolved defined-function type instead of silently dropping it. -/
theorem function_type_exists (h : ModuleValid m) {f : Func} (hf : f ∈ m.funcs) :
    ∃ ft, m.types[f.type.toNat]? = some ft ∧ ft.results.length ≤ 1 := by
  obtain ⟨ft, hft, hv, _⟩ := h.functions f hf
  exact ⟨ft, hft, hv⟩

/-- Global initializers cannot use a mutable imported global as a constant instruction. -/
theorem initializer_globalGet_immutable (h : ModuleValid m) {g : Global}
    (hg : g ∈ m.globals) {i : GlobalIdx} (hi : Instr.globalGet i ∈ g.init) :
    ∃ t, (importedGlobals m)[i.toNat]? = some ⟨.const, t⟩ := by
  have hc := (h.globals g hg).constant _ hi
  cases hc with
  | globalGet _ hget => exact ⟨_, hget⟩

theorem export_name_injective (h : ModuleValid m) {a b : Export}
    (ha : a ∈ m.exports) (hb : b ∈ m.exports) (hn : a.name = b.name) : a = b := by
  exact List.inj_on_of_nodup_map h.uniqueExports ha hb hn

end ModuleValid

end Silmaril.Wasm.V1.Validation
