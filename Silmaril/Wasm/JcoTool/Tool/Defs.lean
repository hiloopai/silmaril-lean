module

public import Silmaril.Wasm.JcoTool.New.Defs
public import Silmaril.Wasm.JcoTool.Check.Defs
public import Silmaril.Wasm.JcoTool.Adaptor.Defs
public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasm.Wit.Binary.DecodeLax.Defs
public import Silmaril.Wasm.JcoTool.XParse.Defs
public import Silmaril.Wasm.Perf.LowerF.Defs

/-!
# `wasm-jco`: the pure core of the command-line tool

Each subcommand of `tools/wasm-jco` is one function here; the executable only reads and
writes files.

| subcommand | function | |
|---|---|---|
| `new CORE.wasm` | `newEmbedded` | the world of the `component-type` section of the module |
| `new CORE.wasm --wit W.wit --world W` | `newWit` | the world of WIT text (`Wit.Tool.embedText`) |
| `print COMP.wasm` | `printWat` | `Wit.Tool.printWat` (verified grammar only) |
| `validate COMP.wasm` | `validate` | the verified parser, the parser with async built-ins (`xparse`) and the IR reader |

`newWith` builds the plan, emits the component and records, next to the bytes, the abstract
syntax of the verified grammar when the output has no async built-ins (`Out.ast`) and the
result of the IR check (`Out.ir`). The theorems at this entry point are in
`Silmaril.Wasm.JcoTool.Tool.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Tool

open Silmaril.Wasm.Wit.Binary (World)
open Silmaril.Wasm.Component.Binary

/-- The output of `new`. -/
structure Out where
  bytes : ByteArray
  /-- The component in the verified grammar, when there are no async built-ins. -/
  ast : Option Ast
  /-- Whether the output reads back as the thin wrapper of the input (`Check.irCheck`). -/
  ir : Bool
  /-- The plan's summary, for the report. -/
  summary : List String
  /-- The core modules of the output, in order. -/
  cores : List ByteArray

/-- A one-line description of each world function and core import of a plan. -/
def summarize (p : New.Plan) : List String :=
  (p.exports.zip p.lifts).map (fun (f, l) => s!"export {f.name}: " ++ match l with
    | .sync c none => s!"canon lift of {c}"
    | .sync c (some pr) => s!"canon lift of {c}, post-return {pr}"
    | .stackful c => s!"async canon lift of {c} (stackful)"
    | .callback c cb => s!"async canon lift of {c}, callback {cb}") ++
  p.reqs.map (fun ((m, n), r) => s!"core import {m} {n}: " ++ match r with
    | .lower _ f => s!"canon lower of {f.name}"
    | .lowerAsync _ f => s!"async canon lower of {f.name}"
    | .chan _ _ _ f => s!"stream/future built-in of {f.name}"
    | .taskReturn f => s!"task.return of {f.name}"
    | _ => "built-in")

/-- **`wasm-jco new`** with a world. -/
def newWith (core : ByteArray) (w : World) : Except String Out := do
  let p ← New.plan core w
  let c ← New.emit p
  let b ← New.mustEncode "the component" c.encode
  pure ⟨b, c.toAst, Check.irCheck core b, summarize p, c.coreModules⟩

/-- `wasm-jco new CORE.wasm`: the world embedded in the module. -/
def newEmbedded (core : ByteArray) : Except String Out := do
  let (_, _, w, se) ← Silmaril.Wasm.Wit.Binary.extractWorldTypeLax core
  if se ≠ .utf8 then throw "only the utf8 string encoding is supported"
  newWith core w

/-- `wasm-jco new CORE.wasm --wit SRC --world W`: a world of WIT text. -/
def newWit (core : ByteArray) (main : String × String) (deps : List (String × String))
    (world : String) : Except String Out := do
  let pl ← Silmaril.Wasm.Wit.Tool.embedText main deps [] world .utf8
  let (_, _, w, _) ← Silmaril.Wasm.Wit.Binary.decodeWorldTypeLax pl
  newWith core w

/-- The world of `wasm-jco new`: embedded in the module, or from WIT text. -/
def worldOf (core : ByteArray) (wit : Option ((String × String) × List (String × String) × String)) :
    Except String World := do
  match wit with
  | some (main, deps, world) =>
    let pl ← Silmaril.Wasm.Wit.Tool.embedText main deps [] world .utf8
    let (_, _, w, _) ← Silmaril.Wasm.Wit.Binary.decodeWorldTypeLax pl
    pure w
  | none =>
    let (_, _, w, se) ← Silmaril.Wasm.Wit.Binary.extractWorldTypeLax core
    if se ≠ .utf8 then throw "only the utf8 string encoding is supported"
    pure w

/-- `wasm-jco new --adaptor [--alloc NAME]`: adaptor mode (`Silmaril.Wasm.JcoTool.Adaptor`). -/
def newAdaptor (core : ByteArray) (w : World) (alloc : String) : Except String Out := do
  let o ← Adaptor.newAdaptor core w alloc
  pure ⟨o.bytes, o.ast, false,
    s!"adaptor: adaptorLime of {o.plan.md.world.length} functions, {o.adaptor.size} bytes, allocator {alloc}" ::
    o.plan.md.world.map (fun s => s!"export {s.name}: canon lift of the adaptor's {s.name}, which calls the module's {s.name}"),
    [core, o.adaptor]⟩

/-- `wasm-jco print`. -/
def printWat (b : ByteArray) : Except String String := Silmaril.Wasm.Wit.Tool.printWat b

/-- `wasm-jco validate`: what the verified parser and the IR reader say. -/
def validate (b : ByteArray) : List String :=
  let p := match parse b with
    | .ok (.mk ss) => s!"parse:  ok ({ss.length} sections, verified grammar)"
    | .error e => s!"parse:  rejected at byte {e.pos} (async built-ins are outside the verified grammar)"
  let l := match Silmaril.Wasm.Perf.LowerF.parseComponentF b with
    | .ok c => s!"lower:  ok (component IR: {c.imports.length} imports, {c.nodes.length} instances, {c.exports.length} exports)"
    | .error e => s!"lower:  not in the IR fragment ({e})"
  let x := match xparse b with
    | .ok c => s!"xparse: ok ({c.sections.length} sections, {c.builtins.length} async built-ins, {c.canons.length} canon definitions)"
    | .error e => s!"xparse: rejected at byte {e.pos}"
  [p, x, l]

end Silmaril.Wasm.JcoTool.Tool
