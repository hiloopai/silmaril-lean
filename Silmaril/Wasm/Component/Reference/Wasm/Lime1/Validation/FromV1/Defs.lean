module

public import Silmaril.Wasm.Lime1.Validation.Modules
public import Silmaril.Wasm.Lime1.FromV1
public import Silmaril.Wasm.V1.Validation.Modules

/-! # Validation preservation from WebAssembly 1.0 to Lime1

The two validation judgments are independent inductive definitions. This map
transports source derivations and module obligations to the extended profile;
it does not define Lime validation by reference to Wasm1.
-/

@[expose] public section
namespace Silmaril.Wasm.V1.Validation

def Context.toLime (C : Context) : Lime1.Validation.Context where
  types := C.types
  funcs := C.funcs
  tables := C.tables
  memories := C.memories
  globals := C.globals
  locals := C.locals
  labels := C.labels
  returnType := C.returnType

@[simp] theorem Context.withLabel_toLime (C : Context) (ts : ResultType) :
    (C.withLabel ts).toLime = C.toLime.withLabel ts := rfl

@[simp] theorem blockType_toLime (C : Context) (bt : BlockType) :
    Lime1.Validation.blockType? C.toLime (BlockType.toLime bt) =
      some ⟨[], blockResults bt⟩ := by cases bt <;> rfl

@[simp] theorem intUnOp_toLime_valid (t : IntType) (op : IntUnOp) :
    Lime1.Validation.IntUnOpValid t op.toLime := by cases op <;> trivial

@[simp] theorem conversionType_toLime (op : ConvertOp) :
    Lime1.Validation.conversionType op.toCore = conversionType op := by
  cases op <;> try rfl
  all_goals rename_i t; cases t <;> rfl

@[simp] theorem moduleContext_toLime (m : Module) :
    Lime1.Validation.moduleContext m.toLime = (moduleContext m).toLime := by
  simp [Lime1.Validation.moduleContext, moduleContext, Module.toLime, Context.toLime,
    Lime1.Validation.importedGlobals, importedGlobals, List.filterMap_map, List.map_map,
    Func.toLime, Global.toLime, Function.comp_def]
  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem initializerContext_toLime (m : Module) :
    Lime1.Validation.initializerContext m.toLime = (initializerContext m).toLime := rfl

@[simp] theorem functionContext_toLime (C : Context) (ft : FuncType) (locals : List ValType) :
    Lime1.Validation.functionContext C.toLime ft locals = (functionContext C ft locals).toLime := rfl

@[simp] theorem importType_toLime (types : List FuncType) (d : ImportDesc) :
    Lime1.Validation.importType? types d = importType? types d := by cases d <;> rfl

@[simp] theorem exportType_toLime (C : Context) (i : ExternIdx) :
    Lime1.Validation.exportType? C.toLime i = exportType? C i := by cases i <;> rfl

end Silmaril.Wasm.V1.Validation
