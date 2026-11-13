module

public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Defs

/-!
# `Lower.coreMod` over the fast Core decoder

`coreModF` is `Silmaril.Wasm.Component.Binary.Lower.coreMod` (copied verbatim) with silmaril's
`decode?` replaced by `CoreDecode.decodeF`. `Thms.lean` proves `coreModF = Lower.coreMod` and
registers the equation with `@[csimp]`, so code compiled in a module that imports it calls
`coreModF` where its source says `Lower.coreMod`; the definitions the theorems are about do
not change.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.CoreMod

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower

/-- `Lower.coreMod` with `CoreDecode.decodeF`. -/
def coreModF (bytes : ByteArray) : Except String CoreMod := do
  let some m := Silmaril.Wasm.Perf.CoreDecode.decodeF bytes
    | throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"
  let mut names := #[]
  let mut imps := #[]
  for i in m.imports do
    match i.type with
    | .func t =>
      names := names.push (i.moduleName, i.name)
      imps := imps.push (i.name, ← coreFuncTy m t)
    | _ => throw s!"core module imports a non-function ({i.moduleName} {i.name}); unsupported"
  let fts := m.functionTypes
  let mut exps := #[]
  for e in m.exports do
    match e.index with
    | .func f =>
      match fts[f.value.val]? with
      | some t => exps := exps.push (e.name, ← coreFuncTy m t)
      | none => throw s!"core export {e.name}: function {f.value.val} out of range"
    | _ => pure ()
  pure ⟨bytes, names.toList, imps.toList, exps.toList⟩

end Silmaril.Wasm.Perf.CoreMod
