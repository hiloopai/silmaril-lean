module

public import Silmaril.Wasm.Text.Extensions.BinaryenMemory.RenderInstructions
public import Silmaril.Wasm.Text.Extensions.Structured.RenderFunctions
public import Silmaril.Wasm.Text.Extensions.Structured.Render

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.BinaryenMemory

open Wasm.Extensions.BinaryenMemory

abbrev FuncT := Structured.FuncT LeafT
abbrev ModuleT := Structured.ModuleT FuncT (Wasm.Extensions.Structured.Expr.contextShape Leaf.contextShape)
abbrev Encodes := Structured.Encodes FuncT (Wasm.Extensions.Structured.Expr.contextShape Leaf.contextShape)

def functionSyntax? := Structured.functionSyntax? leafSyntax?
def moduleSyntax? := Structured.moduleSyntax? functionSyntax? (Wasm.Extensions.Structured.Expr.contextShape Leaf.contextShape)

end Silmaril.Wasm.Text.Extensions.BinaryenMemory
