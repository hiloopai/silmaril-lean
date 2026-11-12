module

public import Silmaril.Wasm.JcoTool.Lime.Defs
public import Silmaril.Wasm.JcoTool.NewI.Defs

/-!
# `wasm-jco new`: the entry point for every world

`newFull core wf` is what `wasm-jco new` computes (thin-wrapper mode). Worlds of
freestanding functions over anonymous types (`inOld`) go through `Tool.newWith` (an earlier step,
with its IR read-back); every other world (interfaces, named types, resources) through
`NewI`. `newLimeFull` is `--lime` on top of it. The world comes with its declarations and
interface bodies (`WorldFull`), from the module's `component-type` section or from WIT text
(`worldFullOf`), read by `Silmaril.Wasm.Wit.Binary.DecodeLax`.

The theorem at this entry point is `Silmaril.Wasm.JcoTool.ToolI.Thms.newFull_correct`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.ToolI

open Silmaril.Wasm.Wit.Binary (Ty Func World WorldItem WorldFull)

mutual
/-- An anonymous type: no named type and no resource handle inside. -/
def anon : Silmaril.Wasm.Wit.Binary.Ty → Bool
  | .prim _ => true
  | .ref _ | .own _ | .borrow _ => false
  | .list t | .option t | .fixedList t _ => anon t
  | .map k v => anon k && anon v
  | .result a b => anonOpt a && anonOpt b
  | .tuple ts => anonList ts
  | .stream t | .future t => anonOpt t
def anonOpt : Option Silmaril.Wasm.Wit.Binary.Ty → Bool
  | none => true
  | some t => anon t
def anonList : List Silmaril.Wasm.Wit.Binary.Ty → Bool
  | [] => true
  | t :: ts => anon t && anonList ts
end

/-- A world item 's fragment: a freestanding function over anonymous types. -/
def oldItem : WorldItem → Bool
  | .func f => f.kind == .freestanding && anonList (f.params.map (·.2)) && anonOpt f.result
  | _ => false

/-- The world is in the fragment of `New`. -/
def inOld (w : World) : Bool := w.imports.all oldItem && w.exports.all oldItem

/-- A summary of a `NewI` plan. -/
def summarize (p : NewI.Plan) : List String :=
  (p.fns.zip p.lifts).map (fun (x, l) => s!"export {x.core}: " ++ match l with
    | .sync c none => s!"canon lift of {c}"
    | .sync c (some pr) => s!"canon lift of {c}, post-return {pr}"
    | .stackful c => s!"async canon lift of {c} (stackful)"
    | .callback c cb => s!"async canon lift of {c}, callback {cb}") ++
  p.dtors.map (fun (r, d) => s!"resource {r.2}: defined" ++ match d with
    | some c => s!", destructor {c}"
    | none => "") ++
  p.reqs.map (fun ((m, n), r) => s!"core import {m} {n}: " ++ match r with
    | .lower _ _ f false => s!"canon lower of {f.name}"
    | .lower _ _ f true => s!"async canon lower of {f.name}"
    | .taskReturn _ f => s!"task.return of {f.name}"
    | .resNew r => s!"resource.new of {r.2}"
    | .resRep r => s!"resource.rep of {r.2}"
    | .resDrop r _ => s!"resource.drop of {r.2}"
    | .chan _ _ _ _ f => s!"stream/future built-in of {f.name}"
    | .gen _ => "built-in")

/-- `wasm-jco new` through `NewI`. -/
def newI (core : ByteArray) (wf : WorldFull) : Except String Tool.Out := do
  let p ← NewI.plan core wf
  let c ← NewI.emit p
  let b ← New.mustEncode "the component" c.encode
  pure ⟨b, c.toAst, false, "interfaces, named types, resources (NewI)" :: summarize p, c.coreModules⟩

/-- **`wasm-jco new`** (thin-wrapper mode) for every world. -/
def newFull (core : ByteArray) (wf : WorldFull) : Except String Tool.Out :=
  if inOld wf.world then Tool.newWith core wf.world else newI core wf

/-- `wasm-jco new --lime` (thin-wrapper mode) for every world. -/
def newLimeFull (core : ByteArray) (wf : WorldFull) : Except String Tool.Out := do
  let core' ← Lime.toLime core
  let o ← newFull core' wf
  New.require (o.cores.all Lime.isLime)
    s!"output core modules outside Lime1 (0 = the input): {(o.cores.zipIdx.filter (!Lime.isLime ·.1)).map (·.2)}"
  pure { o with summary := "lime: every core module of the output is in Lime1" :: o.summary }

/-- The full world of `wasm-jco new`: embedded in the module, or from WIT text. -/
def worldFullOf (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String WorldFull := do
  let wf ← match wit with
    | some (main, deps, world) =>
      let pl ← Silmaril.Wasm.Wit.Tool.embedText main deps [] world .utf8
      Silmaril.Wasm.Wit.Binary.decodeWorldFull pl
    | none => Silmaril.Wasm.Wit.Binary.extractWorldFull core
  if wf.encoding ≠ .utf8 then throw "only the utf8 string encoding is supported"
  pure wf

end Silmaril.Wasm.JcoTool.ToolI
