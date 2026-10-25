module

public import Silmaril.Wasm.Text.Extensions.Structured.Functions
public import Silmaril.Wasm.Text.Extensions.Structured.RenderInstructions

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

def functionSyntax? {Leaf : Type} (leaf : Core.IdCtx → Leaf → Option (List SExp))
    (I : Core.IdCtx) (f : Declaration.Func ValType (Wasm.Extensions.Structured.Expr Leaf)) :
    Option SExp := do
  let ft ← Wat.functionType? I f.type
  if f.locals.length ≥ 2 ^ 32 then none else do
    let localContext : Core.IdCtx :=
      { locals := List.replicate ft.params.length none ++ f.locals.map (fun _ => none) }
    if !(decide (I ++ localContext).Ok) then none else do
      let type ← Wat.indexSyntax? f.type
      let locals ← f.locals.mapM Wat.valueSyntax?
      let body ← f.body.mapM (instructionTree? leaf (I ++ localContext))
      pure (L (K "func" :: L [K "type", type] :: L (K "local" :: locals) :: body.flatten))

end Silmaril.Wasm.Text.Extensions.Structured
