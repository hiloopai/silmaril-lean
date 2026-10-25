module

public import Silmaril.Wasm.Text.Extensions.Structured.Modules
public import Silmaril.Wasm.Text.Extensions.SharedMemory.Render

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.Structured

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

def moduleSyntax? {Body : Type} (function : Core.IdCtx → Declaration.Func ValType Body → Option SExp)
    (shape : Body → Wasm.Expr) (m : Wasm.Extensions.Structured.FunctionModule Body) : Option SExp := do
  let I := Wat.moduleContextAll (m.contextShape shape).coreShape
  if !(decide I.Ok) then none else do
    let ts ← m.types.mapM Wat.typeSyntax?
    let ims ← m.imports.mapM (SharedMemory.importSyntax? I)
    let tags ← m.tags.mapM (Wat.tagSyntax? I)
    let ms ← m.memories.mapM SharedMemory.memorySyntax?
    let gs ← m.globals.mapM Wat.globalSyntax?
    let tables ← m.tables.mapM Wat.tableSyntax?
    let fs ← m.funcs.mapM (function I)
    let ds ← m.data.mapM Wat.dataSyntax?
    let elems ← m.elems.mapM Wat.elemSyntax?
    let ss ← m.start.toList.mapM Wat.startSyntax?
    let es ← m.exports.mapM Wat.exportSyntax?
    pure (doc [L (K "module" :: (ts ++ ims ++ tags ++ ms ++ gs ++ tables ++ fs ++ ds ++ elems ++ ss ++ es))])

end Silmaril.Wasm.Text.Extensions.Structured
