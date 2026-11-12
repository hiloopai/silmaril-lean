module

public import Silmaril.Wasm.JcoTool.ToolI.Defs
public import Silmaril.Wasm.JcoTool.WorldMerge.Defs
public import Silmaril.Wasm.JcoTool.LayoutRefX.Defs
public import Silmaril.Wasm.Perf.JcoNew.Defs

/-!
# The world `wasm-jco new` works on

`worldFullOf core wit` is the world `wasm-jco new` passes to `ToolV.newFullR` (and the other
modes): the world of `--wit SRC --world W`, or every `component-type` section of the module,
merged, deduplicated by semantic version and restricted to its live imports as wit-component
does (`WorldMerge.liveWorld`). With one section whose imports are all live, it is the world
`ToolI.worldFullOf` decodes, unchanged. The entry-point theorems (`ToolI.newFull_correct`,
`ToolV.newFullR_correct`, …) are stated for any world, so they hold for this one.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Front

open Silmaril.Wasm.Wit.Binary

/-- The string encoding the canonical ABI code of `NewI` implements. -/
def checkUtf8 (wf : WorldFull) : Except String WorldFull :=
  if wf.encoding = .utf8 then pure wf else throw "only the utf8 string encoding is supported"

/-- The decoded worlds: the `--wit` world, or every `component-type` section of the module. -/
def worldsOf (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (List WorldFull) :=
  match wit with
  | some _ => (fun w => [w]) <$> ToolI.worldFullOf core wit
  | none => WorldMerge.sectionWorlds core

/-- The world of a core module (see the module docstring). -/
def worldFullOf (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String WorldFull := do
  let names ← WorldMerge.coreImportNames core
  let wfs ← worldsOf core wit
  checkUtf8 (← WorldMerge.liveWorld wfs names)

/-! ## The embedded module's custom sections -/

/-- What `wasm-jco` records in the module's `producers` section. -/
def extraJcoProducer : String × String := ("wasm-jco", "0.1.0")

/-- Add `processed-by: wasm-jco` to a producers record (as wit-component adds itself): to the
`processed-by` field if there is one, else as a new field; an entry of the same tool replaced. -/
def addProcessedBy (p : Producers) : Producers :=
  if p.any (·.1 == "processed-by") then
    p.map fun (f, vs) =>
      if f == "processed-by" then (f, vs.filter (·.1 != extraJcoProducer.1) ++ [extraJcoProducer])
      else (f, vs)
  else p ++ [("processed-by", [extraJcoProducer])]

/-- Does the module (sections `ss`) have a custom section named `component-type…`? -/
def hasComponentType (core : ByteArray) (ss : List (UInt8 × Nat × Nat)) : Bool :=
  ss.any fun (id, st, en) => id = 0 &&
    match (Silmaril.Parse.ByteParse.name : Silmaril.Parse.ByteParse.Parser String) core en st with
    | .ok n _ => n.startsWith componentTypeSection
    | .err _ => false

/-- **The core module as `wasm-jco` embeds it** (wit-component's custom-section handling):
the `component-type…` sections removed (the world is the component's type now), and
`processed-by: wasm-jco` added to the `producers` section (a section appended when there is
none). Every other section is kept, byte for byte and in order.

A module with no `component-type…` section (the `--wit` mode on a bare module, as the stream
generators write them) is embedded **unchanged**: its bytes are the verified encoding that the
stream certificates (`κ`, `wasm-wac shapes`) read back from the component. wit-component's
`embed` + `new` would add `processed-by` here too; this is the one deliberate difference. -/
def prepareCore (core : ByteArray) : Except String ByteArray := do
  let ss ← coreSections core
  if !hasComponentType core ss then return core
  let mut out : ByteArray := ⟨coreHeader.toArray⟩
  let mut sawProducers := false
  for (id, st, en) in ss do
    if id = 0 then
      match (Silmaril.Parse.ByteParse.name : Silmaril.Parse.ByteParse.Parser String) core en st with
      | .ok n j =>
        if n.startsWith componentTypeSection then continue
        if n == "producers" then
          sawProducers := true
          match Producers.parse (core.extract j en) with
          | .ok p =>
            match (addProcessedBy p).encode.bind fun l => customSection "producers" ⟨l.toArray⟩ with
            | some b => out := out ++ b; continue
            | none => throw "producers section too large"
          | .error _ => pure ()  -- an unreadable producers section is kept as it is
      | .err _ => throw s!"malformed custom section name at offset {st}"
    -- the section as it is: id, size, contents
    match Silmaril.Parse.ByteParse.Enc.u32 (en - st) with
    | some sz => out := out ++ ⟨(id :: sz).toArray⟩ ++ core.extract st en
    | none => throw "section too large"
  if !sawProducers then
    match (addProcessedBy []).encode.bind fun l => customSection "producers" ⟨l.toArray⟩ with
    | some b => out := out ++ b
    | none => throw "producers section too large"
  pure out

/-! ## What `wasm-jco new` runs (thin wrapper) -/

/-- **`wasm-jco new` in its default mode**: the module prepared (`prepareCore`), the component
of `ToolV.newFullR` (its layout certificate checked), and the output refused unless the
reference validator accepts it (`ToolV.refCheckX`): every component the tool writes is
`Reference.Valid` at `Features.all` (`Front.newValid_valid`). -/
def newValid (core : ByteArray) (wf : WorldFull) : Except String Tool.Out := do
  let core' ← prepareCore core
  let o ← Silmaril.Wasm.Perf.JcoNew.newFullRF core' wf  -- = ToolV.newFullR (`JcoNew.newFullRF_eq`)
  match ToolV.refCheckX o.bytes with
  | .ok _ => pure o
  | .error e => throw s!"refusing to write an output the reference validator rejects: {e}"

end Silmaril.Wasm.JcoTool.Front
