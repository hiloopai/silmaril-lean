module

public import Silmaril.Wasm.Declaration
public import Silmaril.Wasm.V1.Types

/-! # Scalar-profile module declarations

V1 and Lime1 share scalar types, import/export descriptors and active segments.
Their module record is parameterized by the expression language. Validation and
instantiation remain profile-specific; constructing this record proves neither.
-/

@[expose] public section
namespace Silmaril.Wasm.V1

inductive ImportDesc where
  | func (type : TypeIdx)
  | table (type : TableType)
  | memory (type : MemoryType)
  | global (type : GlobalType)
  deriving DecidableEq, Repr

structure Import where
  moduleName : String
  name : String
  desc : ImportDesc
  deriving DecidableEq, Repr

inductive ExternIdx where
  | func (index : FuncIdx)
  | table (index : TableIdx)
  | memory (index : MemIdx)
  | global (index : GlobalIdx)
  deriving DecidableEq, Repr

structure Export where
  name : String
  index : ExternIdx
  deriving DecidableEq, Repr

end Silmaril.Wasm.V1

namespace Silmaril.Wasm.Scalar

structure Module (Expr : Type) where
  types : List V1.FuncType := []
  imports : List V1.Import := []
  funcs : List (Declaration.Func V1.ValType Expr) := []
  globals : List (Declaration.Global V1.GlobalType Expr) := []
  tables : List V1.TableType := []
  memories : List V1.MemoryType := []
  elems : List (Declaration.ActiveElem Expr) := []
  data : List (Declaration.ActiveData Expr) := []
  start : Option FuncIdx := none
  exports : List V1.Export := []
  deriving Repr

end Silmaril.Wasm.Scalar
