module

public import Silmaril.Wasm.JcoTool.Front.Defs
public import Silmaril.Wasm.Perf.LowerF.Defs
public import Silmaril.Wasm.Perf.ValidateComp.Defs

/-!
# `component new` and `validate` of wasm-jco, each core module decoded once, without streams

The part of `Silmaril.Wasm.Perf.JcoMain` that does not depend on the streams development: the
memo decoders, the `…With dec` functions (the decoder as an argument), the reference check with
one decode, and `wasm-jco validate`. `JcoMain` adds `wasm-jco new`'s **stream report**
(`StreamSem.report`, which reads the plan against the `Proc` model of
`Silmaril.Wasm.Component.Streams`) on top of this module; `wasm-tools component new` writes no
report, so it imports this module only and its runtime closure has no streams development.

The declarations keep the namespace `Silmaril.Wasm.Perf.JcoMain` (they were defined in that module
first). New here:

* `newStage1C`, `newDefaultC`, `newDefaultDC`: `JcoMain.newStage1`, `newDefault`,
  `newDefaultD` without the stream report. `Thms`: `newDefaultC_eq` (the world, then
  `Front.newValid` with `fixSummary`); `JcoMain.Thms`: `newDefault_fst` (`newDefault`'s
  component is `newDefaultC`'s).

`Thms.lean`: the decoder lemmas (`memo_self`, `…With_eq`), `newValidWith_eq`, `newDefaultC_eq`,
`validateLines_eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.JcoMain

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Lower
open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (WorldFull World)

/-- A Core decoder. -/
abbrev Dec : Type := ByteArray → Option Silmaril.Wasm.Module

/-- **The memo**: `v` on the bytes `k`, `d` on any other bytes. Not inlined: inlined, the
compiler moves the computation of `v` into the returned function, which then decodes again at
every call (measured: `wasm-jco validate` decoded twice). -/
@[noinline] def memo (k : ByteArray) (v : Option Silmaril.Wasm.Module) (d : Dec) : Dec :=
  fun b => if b == k then v else d b

/-- Every key of `ks` with its decoded module (a list of data: each decoded once, when the
list is built). -/
def decodeAll (ks : List ByteArray) (d : Dec) : List (ByteArray × Option Silmaril.Wasm.Module) :=
  ks.map fun k => (k, d k)

/-- A memo of several keys: the module recorded for the bytes `b` in `t`, else `d b`. (A fold
of `memo` would not do: the compiler eta-expands the folded function and decodes at every
call.) -/
@[noinline] def lookup (t : List (ByteArray × Option Silmaril.Wasm.Module)) (d : Dec) : Dec :=
  fun b => match t.find? (·.1 == b) with
    | some kv => kv.2
    | none => d b

/-! ## The decoding functions, with the decoder as an argument -/

/-- `Lower.coreMod` with the decoder `dec`. -/
def coreModWith (dec : Dec) (b : ByteArray) : Except String CoreMod :=
  match dec b with
  | some m => Silmaril.Wasm.Perf.JcoNew.coreModOf b m
  | none => throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"

/-- `New.hasMemory` with the decoder `dec`. -/
def hasMemoryWith (dec : Dec) (b : ByteArray) : Bool :=
  match dec b with
  | some m => Silmaril.Wasm.Perf.JcoNew.hasMemoryOf m
  | none => false

/-- `Front.worldFullOf` with the decoder `dec`. -/
def worldFullOfWith (dec : Dec) (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String WorldFull := do
  let names ← (do let m ← coreModWith dec core; pure m.importNames : Except String _)
  let wfs ← Front.worldsOf core wit
  Front.checkUtf8 (← WorldMerge.liveWorld wfs names)

/-- `NewI.plan` with the decoder `dec` (`JcoNew.planF` with `dec` for `decodeF`). -/
def planWith (dec : Dec) (core : ByteArray) (wf : WorldFull) : Except String NewI.Plan := do
  let some dm := dec core
    | throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"
  let m ← Silmaril.Wasm.Perf.JcoNew.coreModOf core dm
  let tb : NewI.Tables := ⟨NewI.funcTable wf, NewI.resourcesOf wf⟩
  let reqs ← (m.importNames.zip m.imports).mapM (NewI.reqOf wf tb)
  let fns := NewI.exportFns wf
  let lifts ← fns.mapM (NewI.liftOf wf m)
  let exported := tb.resources.filter fun r => match r.1 with
    | .iface k => (NewI.ifaces wf).any fun i => i.key == k && !i.imported
    | .world => false
  let dtors ← exported.mapM fun r => do pure (r, ← NewI.dtorOf m r)
  let (mem, ra) ← NewI.needs wf fns (reqs.map (·.2))
  New.require (!mem || Silmaril.Wasm.Perf.JcoNew.hasMemoryOf dm)
    "the world needs linear memory: export it as `memory`"
  New.reallocOk m ra
  pure ⟨core, m, wf, tb, reqs, fns, lifts, dtors, if mem then some "memory" else none,
    if ra then some "cabi_realloc" else none⟩

/-- `JcoNew.newFullLF` with the decoder `dec`. -/
def newFullLWith (dec : Dec) (core : ByteArray) (wf : WorldFull) : Except String Tool.Out :=
  if ToolI.inOld wf.world then ToolV.newFullL core wf else do
  let p ← planWith dec core wf
  let o ← Silmaril.Wasm.Perf.JcoNew.newIP p
  New.require (Helpers.helpersOk o)
    "a helper core module (shim or fixup) failed the check against its specification"
  let o := { o with summary := o.summary ++
    [s!"helpers: {o.cores.length - 1} shim/fixup module(s) decoded by silmaril and checked (Helpers.newFullV_correct)"] }
  Silmaril.Wasm.Perf.JcoNew.checkLayoutP p o
  pure { o with summary := o.summary ++
    ["layout: the component's exports, lifts, lowers, resource built-ins and shim indirections are those the world describes (Layout.newFullL_correct)"] }

/-- `ToolV.refCore3X` with the decoder `dec`. -/
def refCore3XWith (dec : Dec) (b : ByteArray) :
    Except String Silmaril.Wasm.Component.Reference.Core3Component :=
  match xparse b with
  | .error _ => .error "the component does not parse (xparse)"
  | .ok x => match LayoutRefX.toRefX dec x with
    | some c => .ok c
    | none => .error "the component is outside the translation to the reference syntax (a shape the Component Model rejects, or a core module that does not decode)"

/-- `ToolV.refCheckX` with the decoder `dec`, and the Core validator with array lookups and a
reversed operand stack (`ValidateR.checkCore3R`, equal to `Reference.check?`). -/
def refCheckXWith (dec : Dec) (b : ByteArray) :
    Except String Silmaril.Wasm.Component.Reference.ComponentType := do
  let c ← refCore3XWith dec b
  match Silmaril.Wasm.Perf.ValidateR.checkCore3R Silmaril.Wasm.Component.Features.all c with
  | .ok ct => pure ct
  | .error e => throw s!"the reference validator rejects the component: {repr e}"

/-- The verdict line of an accepted `refCheckX` (`ToolV.refCheckXLine`). -/
def refXYes : String :=
  "reference-valid: yes (the bytes, read as a reference Core3Component with core module types, pass Reference.check? with Features.all; LayoutRefX.refCheckX_valid)"

/-- The line `ToolV.newFullR` adds after the layout check outside the old fragment. -/
def refLine : String :=
  "reference: the output read as a reference component (Syntax.Component) has the layout the world describes, its index spaces filled by Definition.sort (LayoutRef.newFullR_correct)"

/-- `Front.newValid` on a prepared module, with the decoder `dec`, the reference validator run
once (`refCheckX`), and its verdict as the last summary line. -/
def newValidWith (dec : Dec) (core : ByteArray) (wf : WorldFull) : Except String Tool.Out := do
  let o ← newFullLWith dec core wf
  let _ ← ToolV.refOf o
  match refCheckXWith dec o.bytes with
  | .ok _ =>
    pure { o with summary := o.summary ++ (if ToolI.inOld wf.world then [] else [refLine]) ++
      [refXYes] }
  | .error e => throw s!"refusing to write an output the reference validator rejects: {e}"

/-- `New.plan` with the decoder `dec`. -/
def newPlanWith (dec : Dec) (core : ByteArray) (w : World) : Except String New.Plan := do
  let m ← coreModWith dec core
  let imps ← New.worldFuncs "world import" w.imports
  let exps ← New.worldFuncs "world export" w.exports
  let reqs ← (m.importNames.zip m.imports).mapM (New.reqOf imps exps)
  let lifts ← exps.mapM (New.liftOf m)
  let (mem, ra) ← New.needs exps (reqs.map (·.2))
  New.require (!mem || hasMemoryWith dec core) "the world needs linear memory: export it as `memory`"
  New.reallocOk m ra
  pure ⟨core, m, imps, exps, reqs, lifts, if mem then some "memory" else none,
    if ra then some "cabi_realloc" else none⟩

/-! ## `wasm-jco new` -/

/-- The summary `Front.newValid`'s output gets here: its last line (`refCheckLine`'s verdict)
replaced by `refCheckX`'s. -/
def fixSummary (o : Tool.Out) : Tool.Out :=
  { o with summary := o.summary.dropLast ++ [refXYes] }

/-- `JcoMain.newStage1` without the stream report: the world, the prepared module, and the
input's decoded module when the prepared module is the input (`none` otherwise, so that it is not
kept alive while the prepared module is decoded and validated). Not inlined, as `newStage1`. -/
@[noinline] def newStage1C (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (WorldFull × ByteArray × Option (Option Silmaril.Wasm.Module)) := do
  let d₀ := Silmaril.Wasm.Perf.CoreDecode.decodeF core
  let dec₀ := memo core d₀ Silmaril.Wasm.Perf.CoreDecode.decodeF
  let wf ← worldFullOfWith dec₀ core wit
  let core' ← Front.prepareCore core
  pure (wf, core', if core' == core then some d₀ else none)

/-- The decoded prepared module: the one `newStage1` kept, else decoded now. -/
def pick (d' : Option (Option Silmaril.Wasm.Module)) (core' : ByteArray) :
    Option Silmaril.Wasm.Module :=
  match d' with
  | some v => v
  | none => Silmaril.Wasm.Perf.CoreDecode.decodeF core'

/-- **The component of `wasm-jco new`'s default mode** (`JcoMain.newDefault` without the
stream report): each core module decoded once and validated once (`newDefaultC_eq`). -/
def newDefaultC (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String Tool.Out := do
  let (wf, core', d') ← newStage1C core wit
  newValidWith (memo core' (pick d' core') Silmaril.Wasm.Perf.CoreDecode.decodeF) core' wf

/-- `newStage1C` with the input's decoded module `d₀` given by the caller. -/
@[noinline] def newStage1DC (core : ByteArray) (d₀ : Option Silmaril.Wasm.Module)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (WorldFull × ByteArray × Option (Option Silmaril.Wasm.Module)) := do
  let dec₀ := memo core d₀ Silmaril.Wasm.Perf.CoreDecode.decodeF
  let wf ← worldFullOfWith dec₀ core wit
  let core' ← Front.prepareCore core
  pure (wf, core', if core' == core then some d₀ else none)

/-- `newDefaultC` with the input's decoded module `d₀` given (`newDefaultDC_eq`: on
`decodeF core` it is `newDefaultC core`). -/
def newDefaultDC (core : ByteArray) (d₀ : Option Silmaril.Wasm.Module)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String Tool.Out := do
  let (wf, core', d') ← newStage1DC core d₀ wit
  newValidWith (memo core' (pick d' core') Silmaril.Wasm.Perf.CoreDecode.decodeF) core' wf

/-! ## `wasm-jco validate` -/

/-- `Lower.section_` with the decoder `dec`. -/
def sectionWith (dec : Dec) (sec : Section) : M Unit := do
  match sec with
  | .custom _ _ => pure ()
  | .coreModule b =>
    let m ← (coreModWith dec b : Except String CoreMod)
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

/-- `Binary.parseComponent` with the decoder `dec`. -/
def parseComponentWith (dec : Dec) (bytes : ByteArray) : Except String (Comp CoreMod) := do
  let ast ← match parse bytes with
    | .ok a => pure a
    | .error e => throw s!"component binary: {repr e.kind} at byte {e.pos}"
  let imports ← Lower.importsPass ast.sections
  let (_, s) ← (ast.sections.forM (sectionWith dec)).run { env := imports.length }
  if s.nextImport ≠ imports.length then
    throw "internal: the import passes disagree"
  pure (.mk imports s.nodes.toList s.exports.toList)

/-- The core modules of a component (its top-level core module sections). -/
def coreModulesOf (b : ByteArray) : List ByteArray :=
  match xparse b with
  | .ok x => x.sections.filterMap fun
    | .sec (.coreModule m) => some m
    | _ => none
  | .error _ => []

/-- `Tool.validate b ++ [ToolV.refCheckXLine b]` with the decoder `dec`. -/
def validateLinesWith (dec : Dec) (b : ByteArray) : List String :=
  let p := match parse b with
    | .ok (.mk ss) => s!"parse:  ok ({ss.length} sections, verified grammar)"
    | .error e => s!"parse:  rejected at byte {e.pos} (async built-ins are outside the verified grammar)"
  let l := match parseComponentWith dec b with
    | .ok c => s!"lower:  ok (component IR: {c.imports.length} imports, {c.nodes.length} instances, {c.exports.length} exports)"
    | .error e => s!"lower:  not in the IR fragment ({e})"
  let x := match xparse b with
    | .ok c => s!"xparse: ok ({c.sections.length} sections, {c.builtins.length} async built-ins, {c.canons.length} canon definitions)"
    | .error e => s!"xparse: rejected at byte {e.pos}"
  let r := match refCheckXWith dec b with
    | .ok _ => refXYes
    | .error e => s!"reference-valid: no ({e})"
  [p, x, l, r]

/-- **`wasm-jco validate`**: its output lines, every core module decoded once
(`validateLines_eq`). -/
def validateLines (b : ByteArray) : List String :=
  validateLinesWith
    (lookup (decodeAll (coreModulesOf b) Silmaril.Wasm.Perf.CoreDecode.decodeF)
      Silmaril.Wasm.Perf.CoreDecode.decodeF) b

end Silmaril.Wasm.Perf.JcoMain
