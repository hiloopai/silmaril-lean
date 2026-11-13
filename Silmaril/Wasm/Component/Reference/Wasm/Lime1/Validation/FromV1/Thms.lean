module

public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Defs
public import Silmaril.Wasm.Lime1.Validation.Modules
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Wasm.V1.Validation.Modules

/-!
# Validation preservation from WebAssembly 1.0 to Lime1: the laws

The theorems of the copied `Wasm/Lime1/Validation/FromV1`, refined out of
`Silmaril.Raw.Wasm.Component`: every valid WebAssembly 1.0 instruction,
expression, import, export, function, global, element, data segment and module is valid in
Lime1 (`ModuleValid.toLime`). The copies of other Wasm topics (`Raw/Wasm/SpecTec`,
`Raw/Wasm/Versions`) reach them through this header.
-/

@[expose] public section
namespace Silmaril.Wasm.V1.Validation

theorem InstrType.toLime {C : Context} {i : Instr} {a b : ResultType}
     (h : InstrType C i a b) : Lime1.Validation.InstrType C.toLime i.toLime a b := by
  induction h using InstrType.rec
      (motive_2 := fun C es a b _ => Lime1.Validation.ExprType C.toLime (Expr.toLime es) a b) with
  | frame pre _ ih => exact .frame pre ih
  | nop => exact .nop
  | unreachable a b => exact .unreachable a b
  | drop t => exact .drop t
  | select t => exact .select t
  | block bt _ ih =>
    exact .block _ (blockType_toLime _ _) ih
  | loop bt _ ih => exact .loop _ (blockType_toLime _ _) ih
  | if_ bt _ _ ihl ihr => exact .if_ _ (blockType_toLime _ _) ihl ihr
  | @br C i _ h pre out => exact .br (C := C.toLime) i h pre _
  | brIf i h => exact .brIf i h
  | @brTable C is d _ hd hs pre out => exact .brTable (C := C.toLime) is d hd hs pre _
  | @return_ C _ h pre out => exact .return_ (C := C.toLime) h pre _
  | call i h => exact .call i h
  | callIndirect i h table => exact .callIndirect i h table
  | localGet i h => exact .localGet i h
  | localSet i h => exact .localSet i h
  | localTee i h => exact .localTee i h
  | globalGet i h => exact .globalGet i h
  | globalSet i h => exact .globalSet i h
  | intLoad t p arg memory access => exact .intLoad t p arg memory access
  | floatLoad t arg memory aligned => exact .floatLoad t arg memory aligned
  | intStore t p arg memory access => exact .intStore t p arg memory access
  | floatStore t arg memory aligned => exact .floatStore t arg memory aligned
  | memorySize memory => exact .memorySize memory
  | memoryGrow memory => exact .memoryGrow memory
  | intConst t bits => exact .intConst t bits
  | floatConst t bits => exact .floatConst t bits
  | intUnOp t op => exact .intUnOp t op.toLime (intUnOp_toLime_valid t op)
  | intBinOp t op => exact .intBinOp t op
  | intTestOp t op => exact .intTestOp t op
  | intRelOp t op => exact .intRelOp t op
  | floatUnOp t op => exact .floatUnOp t op
  | floatBinOp t op => exact .floatBinOp t op
  | floatRelOp t op => exact .floatRelOp t op
  | @convert C op => simpa only [conversionType_toLime, Instr.toLime] using
      (Lime1.Validation.InstrType.convert (C := C.toLime) op.toCore)
  | nil ts => exact .nil _
  | cons _ _ hi his => exact .cons hi his

theorem ExprType.toLime {C : Context} {es : Expr} {a b : ResultType}
    (h : ExprType C es a b) : Lime1.Validation.ExprType C.toLime (Expr.toLime es) a b := by
  induction es generalizing a with
  | nil => cases h; exact .nil _
  | cons i es ih =>
    cases h with
    | cons hi his => exact .cons hi.toLime (ih his)

theorem ExternTypeValid.toLime {et : ExternType} (h : ExternTypeValid et) :
    Lime1.Validation.ExternTypeValid et := by
  cases et with
  | func _ => trivial
  | table _ => exact h
  | memory _ => exact h
  | global _ => trivial

theorem ImportValid.toLime {types : List FuncType} {i : Import} (h : ImportValid types i) :
    Lime1.Validation.ImportValid types i := by
  obtain ⟨et, he, hv⟩ := h
  exact ⟨et, by simpa using he, hv.toLime⟩

theorem ExportValid.toLime {C : Context} {e : Export} (h : ExportValid C e) :
    Lime1.Validation.ExportValid C.toLime e := by
  obtain ⟨et, h⟩ := h
  exact ⟨et, by simpa using h⟩

theorem ConstantInstr.toLime {C : Context} {i : Instr} (h : ConstantInstr C i) :
    Lime1.Validation.ConstantInstr C.toLime i.toLime := by
  cases h with
  | intConst t bits => exact .intConst t bits
  | floatConst t bits => exact .floatConst t bits
  | globalGet i h => exact .globalGet i h

theorem ConstantExpr.toLime {C : Context} {es : Expr} (h : ConstantExpr C es) :
    Lime1.Validation.ConstantExpr C.toLime (Expr.toLime es) := by
  intro i hi
  rw [Expr.toLime_eq_map] at hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact (h j hj).toLime

theorem ConstExprType.toLime {C : Context} {es : Expr} {t : ValType}
    (h : ConstExprType C es t) : Lime1.Validation.ConstExprType C.toLime (Expr.toLime es) t :=
  ⟨h.typed.toLime, h.constant.toLime⟩

theorem FuncValid.toLime {C : Context} {f : Func} (h : FuncValid C f) :
    Lime1.Validation.FuncValid C.toLime f.toLime := by
  obtain ⟨ft, ht, _, hb⟩ := h
  exact ⟨ft, ht, trivial, hb.toLime⟩

theorem GlobalValid.toLime {C : Context} {g : Global} (h : GlobalValid C g) :
    Lime1.Validation.GlobalValid C.toLime g.toLime := ConstExprType.toLime h

theorem ElemValid.toLime {C : Context} {e : Elem} (h : ElemValid C e) :
    Lime1.Validation.ElemValid C.toLime e.toLime :=
  ⟨h.table, h.offset.toLime, h.functions⟩

theorem DataValid.toLime {C : Context} {d : Data} (h : DataValid C d) :
    Lime1.Validation.DataValid C.toLime d.toLime := ⟨h.memory, h.offset.toLime⟩

/-- Every valid WebAssembly 1.0 module remains valid in Lime1. -/
theorem ModuleValid.toLime {m : Module} (h : ModuleValid m) :
    Lime1.Validation.ModuleValid m.toLime where
  types := fun _ _ => trivial
  imports := fun i hi => (h.imports i hi).toLime
  functions := List.forall_mem_map.mpr fun g hg => by simpa using (h.functions g hg).toLime
  tables := h.tables
  memories := h.memories
  globals := List.forall_mem_map.mpr fun f hf => by simpa using (h.globals f hf).toLime
  elements := List.forall_mem_map.mpr fun f hf => by simpa using (h.elements f hf).toLime
  data := List.forall_mem_map.mpr fun e he => by simpa using (h.data e he).toLime
  start := by
    change Lime1.Validation.StartValid (Lime1.Validation.moduleContext m.toLime) m.start
    rw [moduleContext_toLime]
    exact h.start
  exports := fun e he => by simpa using (h.exports e he).toLime
  uniqueExports := h.uniqueExports
  singleTable := by simpa only [moduleContext_toLime, Context.toLime] using h.singleTable
  singleMemory := by simpa only [moduleContext_toLime, Context.toLime] using h.singleMemory

end Silmaril.Wasm.V1.Validation
