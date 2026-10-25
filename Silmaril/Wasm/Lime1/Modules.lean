module

public import Silmaril.Wasm.Lime1.Instructions
public import Silmaril.Wasm.V1.Modules

/-! # Lime1 modules

Lime1 uses the shared scalar declarations with its own expression language.
Multivalue signatures and indexed block types are accepted by its separate
validation judgment; raw module construction does not establish validity.
-/

@[expose] public section
namespace Silmaril.Wasm.Lime1

abbrev ImportDesc := V1.ImportDesc
abbrev Import := V1.Import
abbrev ExternIdx := V1.ExternIdx
abbrev Export := V1.Export
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

end Silmaril.Wasm.Lime1
