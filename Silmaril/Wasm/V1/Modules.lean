module

public import Silmaril.Wasm.Scalar.Module
public import Silmaril.Wasm.V1.Instructions

/-! # WebAssembly 1.0 modules

The shared scalar declarations are instantiated with the V1 expression language.
Import type indices, additional locals and active segment offsets remain source
syntax. Validation checks their types and indices; instantiation allocates them.
-/

@[expose] public section
namespace Silmaril.Wasm.V1

abbrev Func := Declaration.Func ValType Expr
abbrev Global := Declaration.Global GlobalType Expr
abbrev Elem := Declaration.ActiveElem Expr
abbrev Data := Declaration.ActiveData Expr
abbrev Module := Scalar.Module Expr

namespace Func
abbrev mk := @Declaration.Func.mk ValType Expr
@[simp] abbrev type (f : Func) := Declaration.Func.type f
@[simp] abbrev locals (f : Func) := Declaration.Func.locals f
@[simp] abbrev body (f : Func) := Declaration.Func.body f
end Func
namespace Global
abbrev mk := @Declaration.Global.mk GlobalType Expr
@[simp] abbrev type (g : Global) := Declaration.Global.type g
@[simp] abbrev init (g : Global) := Declaration.Global.init g
end Global
namespace Elem
abbrev mk := @Declaration.ActiveElem.mk Expr
@[simp] abbrev table (e : Elem) := Declaration.ActiveElem.table e
@[simp] abbrev offset (e : Elem) := Declaration.ActiveElem.offset e
@[simp] abbrev init (e : Elem) := Declaration.ActiveElem.init e
end Elem
namespace Data
abbrev mk := @Declaration.ActiveData.mk Expr
@[simp] abbrev memory (d : Data) := Declaration.ActiveData.memory d
@[simp] abbrev offset (d : Data) := Declaration.ActiveData.offset d
@[simp] abbrev bytes (d : Data) := Declaration.ActiveData.bytes d
end Data

end Silmaril.Wasm.V1
