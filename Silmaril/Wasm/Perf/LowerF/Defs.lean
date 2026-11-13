module

public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# `Binary.parseComponent` over the fast Core decoder

`Binary.lower` decodes every embedded core module with silmaril's decoder (through
`Lower.coreMod`, compiled in `Component/Binary/Lower`). `sectionF`, `lowerF` and
`parseComponentF` are verbatim copies of `Lower.section_`, `Binary.lower` and
`Binary.parseComponent`, except that `sectionF` calls `CoreMod.coreModF` (which decodes with
`CoreDecode.decodeF`) where `Lower.section_` calls `Lower.coreMod`.
`Thms.lean` proves each equal to its original and registers
`parseComponent = parseComponentF` with `@[csimp]`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.LowerF

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower

/-- `Lower.section_`, compiled with the fast decoder. -/
def sectionF (sec : Section) : M Unit := do
  match sec with
  | .custom _ _ => pure ()
  | .coreModule b =>
    let m ← (Silmaril.Wasm.Perf.CoreMod.coreModF b : Except String CoreMod)
    modify fun s => { s with modules := s.modules.push m }
  | .coreInstances xs => xs.forM coreInstance
  | .coreTypes _ => pure ()
  | .component _ => throw "nested components are not supported"
  | .instances xs => xs.forM instance_
  | .aliases xs => xs.forM alias_
  | .types xs => xs.forM fun t => modify fun s => { s with types := s.types.push (typeEntry s.types t) }
  | .canons xs => xs.forM canon
  | .start _ => throw "the start section is not supported"
  | .imports xs => xs.forM import_
  | .exports xs => xs.forM export_
  | .values _ => throw "values are not supported"

/-- `Binary.lower`, compiled with the fast decoder. -/
def lowerF (c : Ast) : Except String (Comp CoreMod) := do
  let imports ← Lower.importsPass c.sections
  let (_, s) ← (c.sections.forM sectionF).run { env := imports.length }
  if s.nextImport ≠ imports.length then
    throw "internal: the import passes disagree"
  pure (.mk imports s.nodes.toList s.exports.toList)

/-- `Binary.parseComponent`, compiled with the fast decoder. -/
def parseComponentF (bytes : ByteArray) : Except String (Comp CoreMod) := do
  let ast ← match parse bytes with
    | .ok a => pure a
    | .error e => throw s!"component binary: {repr e.kind} at byte {e.pos}"
  lowerF ast

end Silmaril.Wasm.Perf.LowerF
