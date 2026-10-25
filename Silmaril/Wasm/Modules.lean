module

public import Silmaril.Wasm.Declaration
public import Silmaril.Wasm.Instructions

@[expose] public section

/-! # WebAssembly modules

Source modules keep imports, definitions, and index spaces distinct. Well-formedness
and instantiation are separate judgements over this syntax.
-/

namespace Silmaril.Wasm

inductive ExternIdx where
  | tag (index : TagIdx)
  | global (index : GlobalIdx)
  | memory (index : MemIdx)
  | table (index : TableIdx)
  | func (index : FuncIdx)
  deriving DecidableEq, Repr

structure Import where
  moduleName : String
  name : String
  type : ExternType
  deriving DecidableEq, Repr

structure Export where
  name : String
  index : ExternIdx
  deriving DecidableEq, Repr

abbrev Func := Declaration.Func ValType Expr

namespace Func
abbrev mk := @Declaration.Func.mk ValType Expr
@[simp] abbrev type (f : Func) := Declaration.Func.type f
@[simp] abbrev locals (f : Func) := Declaration.Func.locals f
@[simp] abbrev body (f : Func) := Declaration.Func.body f
end Func

abbrev Global := Declaration.Global GlobalType Expr

namespace Global
abbrev mk := @Declaration.Global.mk GlobalType Expr
@[simp] abbrev type (g : Global) := Declaration.Global.type g
@[simp] abbrev init (g : Global) := Declaration.Global.init g
end Global

structure Table where
  type : TableType
  init : Expr
  deriving Repr

inductive ElemMode where
  | passive
  | active (table : TableIdx) (offset : Expr)
  | declarative
  deriving Repr

structure Elem where
  type : RefType
  init : List Expr
  mode : ElemMode
  deriving Repr

inductive DataMode where
  | passive
  | active (memory : MemIdx) (offset : Expr)
  deriving Repr

structure Data where
  bytes : ByteArray
  mode : DataMode
  deriving Repr

structure Module where
  types : List RecType := []
  imports : List Import := []
  tags : List TagType := []
  globals : List Global := []
  memories : List MemoryType := []
  tables : List Table := []
  funcs : List Func := []
  data : List Data := []
  elems : List Elem := []
  start : Option FuncIdx := none
  exports : List Export := []
  deriving Repr

/-- Recursive groups contribute one type-index entry per member. -/
def Module.typeDefinitions (module : Module) : List SubType :=
  module.types.flatMap RecType.types

def Module.importedFunctions (module : Module) : List TypeIdx :=
  module.imports.filterMap fun entry => match entry.type with
    | .func t => some t
    | _ => none

/-- Function indices count imported functions before local definitions. -/
def Module.functionTypes (module : Module) : List TypeIdx :=
  module.importedFunctions ++ module.funcs.map Func.type

@[simp] theorem Module.functionTypes_length (module : Module) :
    module.functionTypes.length = module.importedFunctions.length + module.funcs.length := by
  simp [functionTypes]

end Silmaril.Wasm
