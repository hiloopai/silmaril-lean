module

public import Silmaril.Wasm.Text.Extensions.SharedMemory.Modules
public import Silmaril.Wasm.Text.Extensions.SharedMemory.RenderTypes

@[expose] public section

namespace Silmaril.Wasm.Text.Extensions.SharedMemory

open Silmaril Silmaril.Formats.SExpEncoding
open Binaryen.Toolkit

def liftCoreFields (xs : List Core.FieldOut) : List FieldOut :=
  xs.map fun o => (o, coreImportFlags o.1, coreMemoryFlags o.1)

def importFields (ims : List Wasm.Extensions.SharedMemory.Import) : List FieldOut :=
  ims.map fun im => (([.import_ im.coreShape], Wat.importContext im.coreShape, []), [im.type.isShared], [])

def memoryFields (ms : List MemoryType) : List FieldOut :=
  ms.map fun m => (([.mem m.core], { mems := [none] }, []), [], [m.shared])

def moduleFields (m : Wasm.Extensions.SharedMemory.Module) : List FieldOut :=
  liftCoreFields (Wat.typeFields m.types) ++ importFields m.imports ++
    liftCoreFields (Wat.tagFields m.tags) ++ memoryFields m.memories ++
    liftCoreFields (Wat.globalFields m.globals) ++ liftCoreFields (Wat.tableFields m.tables) ++
    liftCoreFields (Wat.functionFields m.funcs) ++ liftCoreFields (Wat.dataFields m.data) ++
    liftCoreFields (Wat.elemFields m.elems) ++ liftCoreFields (Wat.startFields m.start) ++
    liftCoreFields (Wat.exportFields m.exports)

def importSyntax? (I : Core.IdCtx) (im : Wasm.Extensions.SharedMemory.Import) : Option SExp :=
  match im.type with
  | .memory m => do
    let source ← Wat.nameSyntax? im.moduleName
    let field ← Wat.nameSyntax? im.name
    let type ← memoryTypeSyntax? m
    pure (L [K "import", source, field, L (K "memory" :: type)])
  | _ => Wat.importSyntax? I im.coreShape

/-- Canonical serialization retains every shared flag. It does not run a Core
validator on the erased shape or claim a concurrent operational semantics. -/
def moduleSyntax? (m : Wasm.Extensions.SharedMemory.Module) : Option SExp := do
  let I := Wat.moduleContextAll m.coreShape
  if !(decide I.Ok) then none else do
    let ts ← m.types.mapM Wat.typeSyntax?
    let ims ← m.imports.mapM (importSyntax? I)
    let tags ← m.tags.mapM (Wat.tagSyntax? I)
    let ms ← m.memories.mapM memorySyntax?
    let gs ← m.globals.mapM Wat.globalSyntax?
    let tables ← m.tables.mapM Wat.tableSyntax?
    let fs ← m.funcs.mapM (Wat.functionSyntax? I)
    let ds ← m.data.mapM Wat.dataSyntax?
    let elems ← m.elems.mapM Wat.elemSyntax?
    let ss ← m.start.toList.mapM Wat.startSyntax?
    let es ← m.exports.mapM Wat.exportSyntax?
    pure (doc [L (K "module" :: (ts ++ ims ++ tags ++ ms ++ gs ++ tables ++ fs ++ ds ++ elems ++ ss ++ es))])

end Silmaril.Wasm.Text.Extensions.SharedMemory
