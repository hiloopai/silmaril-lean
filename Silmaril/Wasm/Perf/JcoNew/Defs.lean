module

public import Silmaril.Wasm.JcoTool.LayoutRef.Defs
public import Silmaril.Wasm.Perf.CoreMod.Defs
public import Silmaril.Wasm.Perf.XEncodeB.Defs

/-!
# `wasm-jco new` with the core module decoded once

`ToolV.newFullR` (the function `wasm-jco new` runs in thin-wrapper mode) decodes the input core
module six times: `NewI.plan` decodes it twice (`Lower.coreMod`, `New.hasMemory`), and the plan
is computed twice (`ToolI.newI`, then `ToolV.checkLayout`). On a module of a few MB the decoder
is nearly all of the run time.

* `planF`: `NewI.plan` with one decode (`CoreDecode.decodeF`); `coreModOf` and `hasMemoryOf`
  are the bodies of `Lower.coreMod` and `New.hasMemory` after the decode (copied verbatim);
* `newIP`, `checkLayoutP`: `ToolI.newI` and `ToolV.checkLayout` after the plan;
* `newFullLF`, `newFullRF`: `ToolV.newFullL` and `ToolV.newFullR` computing the plan once.

`Thms.lean` proves `planF = NewI.plan` and `newFullRF = ToolV.newFullR`, so the entry-point
theorems about `newFullR` (`LayoutRef.newFullR_correct`, …) hold for `newFullRF`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.JcoNew

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (WorldFull)

/-- The body of `Lower.coreMod` after the decode. -/
def coreModOf (bytes : ByteArray) (m : Silmaril.Wasm.Module) : Except String CoreMod := do
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

/-- The body of `New.hasMemory` after the decode. -/
def hasMemoryOf (m : Silmaril.Wasm.Module) : Bool :=
  m.exports.any fun e => e.name == "memory" && (match e.index with
    | .memory _ => true
    | _ => false)

/-- **`NewI.plan` with one decode** (`planF_eq`). -/
def planF (core : ByteArray) (wf : WorldFull) : Except String NewI.Plan := do
  let some dm := Silmaril.Wasm.Perf.CoreDecode.decodeF core
    | throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"
  let m ← coreModOf core dm
  let tb : NewI.Tables := ⟨NewI.funcTable wf, NewI.resourcesOf wf⟩
  let reqs ← (m.importNames.zip m.imports).mapM (NewI.reqOf wf tb)
  let fns := NewI.exportFns wf
  let lifts ← fns.mapM (NewI.liftOf wf m)
  let exported := tb.resources.filter fun r => match r.1 with
    | .iface k => (NewI.ifaces wf).any fun i => i.key == k && !i.imported
    | .world => false
  let dtors ← exported.mapM fun r => do pure (r, ← NewI.dtorOf m r)
  let (mem, ra) ← NewI.needs wf fns (reqs.map (·.2))
  New.require (!mem || hasMemoryOf dm) "the world needs linear memory: export it as `memory`"
  New.reallocOk m ra
  pure ⟨core, m, wf, tb, reqs, fns, lifts, dtors, if mem then some "memory" else none,
    if ra then some "cabi_realloc" else none⟩

/-- `ToolI.newI` after the plan. -/
def newIP (p : NewI.Plan) : Except String Tool.Out := do
  let c ← NewI.emit p
  let b ← New.mustEncode "the component" (Silmaril.Wasm.Perf.XEncodeB.xencodeF c)
  pure ⟨b, c.toAst, false, "interfaces, named types, resources (NewI)" :: ToolI.summarize p,
    c.coreModules⟩

/-- `ToolV.checkLayout` (outside the old fragment) after the plan. -/
def checkLayoutP (p : NewI.Plan) (o : Tool.Out) : Except String Unit :=
  match xparse o.bytes with
  | .ok x =>
    if Layout.layoutOk p x then pure ()
    else throw s!"the emitted component's layout differs from the world's: read {repr (Layout.read p.mod.importNames x)}, expected {repr (Layout.expected p)}"
  | _ => throw "the emitted component does not parse back"

/-- `ToolV.newFullL` with the plan computed once. -/
def newFullLF (core : ByteArray) (wf : WorldFull) : Except String Tool.Out :=
  if ToolI.inOld wf.world then ToolV.newFullL core wf else do
  let p ← planF core wf
  let o ← newIP p
  New.require (Helpers.helpersOk o)
    "a helper core module (shim or fixup) failed the check against its specification"
  let o := { o with summary := o.summary ++
    [s!"helpers: {o.cores.length - 1} shim/fixup module(s) decoded by silmaril and checked (Helpers.newFullV_correct)"] }
  checkLayoutP p o
  pure { o with summary := o.summary ++
    ["layout: the component's exports, lifts, lowers, resource built-ins and shim indirections are those the world describes (Layout.newFullL_correct)"] }

/-- **`ToolV.newFullR` with the plan computed once** (`newFullRF_eq`). -/
def newFullRF (core : ByteArray) (wf : WorldFull) : Except String Tool.Out := do
  let o ← newFullLF core wf
  let _ ← ToolV.refOf o
  pure { o with summary := o.summary ++ (if ToolI.inOld wf.world then [] else
    ["reference: the output read as a reference component (Syntax.Component) has the layout the world describes, its index spaces filled by Definition.sort (LayoutRef.newFullR_correct)"]) ++
    [ToolV.refCheckLine o.bytes] }

end Silmaril.Wasm.Perf.JcoNew
