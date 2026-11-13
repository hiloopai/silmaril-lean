module

public import Silmaril.Wasm.Tools.Component.WitPkg.Defs
public import Silmaril.Wasm.Wac.WitDir.Defs
public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasm.Wit.Binary.Embed.Defs
public import Silmaril.Wasm.JcoTool.WitOf.Defs
public import Silmaril.Wasm.Wac.TargetsT.Defs
public import Silmaril.Wasm.JcoTool.NewCore.Defs
public import Silmaril.Wasm.JcoTool.AdaptLayout.Defs
public import Silmaril.Wasm.JcoTool.Cm32.Defs
public import Silmaril.Wasm.Wac.AsyncNames.Defs
public import Silmaril.Wasm.Tools.Component.Dummy.Defs
public import Silmaril.Wasm.Tools.Component.DummyFast.Defs
public import Silmaril.Wasm.Tools.Component.Budget.Defs
public import Silmaril.Wasm.Tools.Component.WitText.Defs
public import Silmaril.Wasm.Tools.Component.WitFast.Defs
public import Silmaril.Wasm.Tools.Component.Ize.Defs
public import Silmaril.Wasm.Tools.Component.Semver.Defs
public import Silmaril.Wasm.Tools.Component.Rename.Defs

/-!
# The cores of `wasm-tools component new / embed / wit / targets`

Pure functions behind the `component` subcommands of the Lean `wasm-tools`
(`tools/wasm-tools/WasmTools/Component.lean`). Each is the composition of verified cores that
already exist (`wasm-jco`, `wasm-wit`, `wasm-wac`) with the selection rules and the
conventions of upstream's CLI (`src/bin/wasm-tools/component.rs` of wasm-tools 1.262.0):

* `WitSrc`: a WIT source as wit-parser's `Resolve::push_path` reads a path: a directory (one
  package of several files, with `deps/`), a single `.wit` file (no `deps/`), or a WIT
  package in binary form. `pkgBytes` is its package binary (`WitDir.encodeTextX`).
* `selectWorld`: `Resolve::select_world` on the main package, with upstream's messages.
* `embed`: `wasm-tools component embed` (`Wit.Tool.embedBytes`, `Wit.Binary.embedPayload`);
  async functions renamed to wit-component 0.262's plain names (`Wac.AsyncNames.fixBytes`,
  the identity on payloads without async functions) and the producers retagged, both checked
  to keep the decoded world (`postPayload`).
* `witText`, `witWasm`: `wasm-tools component wit` (`WitOf.componentWit`, `Wit.Tool.witAll`).
* `targets`: `wasm-tools component targets` (`Wac.TargetsT.check`, WIT subtyping).
* `new`: `wasm-tools component new` (`wasm-jco new`'s default mode without its stream report:
  `NewCore.newMainC`, the general layout `AdaptLayout.newAdaptL` as fallback and for `--adapt`).
* `retag`: the `producers` field these encoders write names wit-component `0.263.0`;
  upstream 1.262.0 writes `0.262.0`. `retag` rewrites the last seven bytes when they are that
  version string after the name `wit-component` (same length, so no size changes).

Theorems: `Silmaril.Wasm.Tools.Component.Cmd.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Cmd

open Silmaril.Wasm.Wit

/-! ## WIT sources and worlds

`WitSrc`, `pkgBytes`, `selectWorld`, `retag`, `postPayload` and `postPackage` are in
`Silmaril.Wasm.Tools.Component.WitPkg.Defs`. -/

/-- The package binary of a source with the features `fs` enabled (`--features`); a binary
package is taken as it is. Computed by the fast path `WitFast.encodeTextXFast`, equal to
`WitText.encodeTextXF` (`WitFast.encodeTextXFast_eq`). -/
def pkgBytesF (fs : List String) : WitSrc → Except String ByteArray
  | .dir m ds => WitFast.encodeTextXFast m ds fs
  | .file n t => WitFast.encodeTextXFast [(n, t)] [] fs
  | .binary b => .ok b

/-- The source with its line comments read as documentation (`WitText.commentsAsDocs`). -/
def docSrc : WitSrc → WitSrc
  | .dir m ds =>
    .dir (m.map fun (n, t) => (n, WitText.commentsAsDocs t))
      (ds.map (·.map fun (n, t) => (n, WitText.commentsAsDocs t)))
  | .file n t => .file n (WitText.commentsAsDocs t)
  | .binary b => .binary b

/-- The features of every `@unstable` gate of a source (`--all-features`). -/
def srcFeatures : WitSrc → List String
  | .dir m ds => WitText.allFeatures m ds
  | .file n t => WitText.allFeatures [(n, t)] []
  | .binary _ => []

/-! ## `component embed` -/

/-- What `embed` writes: the module with the section, or the section only. -/
inductive EmbedInput where
  | module (m : ByteArray)
  | onlyCustom

/-- **`wasm-tools component embed`**: the payload of the selected world (`embedBytes`), appended
to the module as a `component-type` custom section (`embedPayload`), or alone with
`--only-custom`; the producers version retagged. -/
def embed (src : WitSrc) (world : Option String) (se : Binary.StringEncoding)
    (inp : EmbedInput) : Except String ByteArray := do
  let pb ← pkgBytes src
  let d ← Tool.decode pb
  let w ← selectWorld d.pkg world
  let pl ← Tool.embedBytes pb w se
  -- wit-component 0.262's names of async functions and producers version, checked
  let pl := postPayload pl
  match inp with
  | .onlyCustom => pure pl
  | .module m => Binary.embedPayload m pl

/-- **`wasm-tools component embed --dummy`** (`--dummy-names M`): `embed` into the dummy module
of the selected world (wit-component's `dummy_module`), computed with bounded flattening
(`DummyFast.dummyOfPayloadFast`, equal to `Dummy.dummyOfPayload` wherever that succeeds:
`DummyFast.dummyOfPayloadFast_eq`). -/
def embedDummy (src : WitSrc) (world : Option String) (se : Binary.StringEncoding)
    (m : Dummy.Mangling) : Except String ByteArray := do
  let pb ← pkgBytes src
  let d ← Tool.decode pb
  let w ← selectWorld d.pkg world
  let pl ← Tool.embedBytes pb w se
  let core ← DummyFast.dummyOfPayloadFast pl m
  Binary.embedPayload core (postPayload pl)

/-- The merge check of `embed` into a module that has `component-type` sections already
(`WitText.mergeConflict`): `some message` when upstream refuses the merge. -/
def embedConflict (m pl : ByteArray) : Option String :=
  match Binary.customSections m with
  | .error _ => none
  | .ok cs =>
    let olds := (cs.filter (·.1.startsWith Binary.componentTypeSection)).map (·.2)
    if olds.isEmpty then none
    else match olds.mapM Binary.decodeWorldFull, Binary.decodeWorldFull pl with
      | .ok ws, .ok w => WitText.mergeConflict ws w
      | _, _ => none

/-- `--encoding`: upstream's names. -/
def encodingOf : String → Option Binary.StringEncoding
  | "utf8" => some .utf8
  | "utf16" => some .utf16
  | "compact-utf16" => some .compactUtf16
  | _ => none

/-! ## `component wit` -/

/-- Is this a component binary (layer 1)? -/
def isComponent (b : ByteArray) : Bool :=
  b.size ≥ 8 && b[0]! == 0x00 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d &&
    b[6]! == 0x01 && b[7]! == 0x00

/-- Is this a core module binary (layer 0)? -/
def isCoreModule (b : ByteArray) : Bool :=
  b.size ≥ 8 && b[0]! == 0x00 && b[1]! == 0x61 && b[2]! == 0x73 && b[3]! == 0x6d &&
    b[6]! == 0x00 && b[7]! == 0x00

def noWitInfo : String :=
  "input is a core wasm module with no `component-type*` custom sections meaning that there " ++
  "is not WIT information; is the information not embedded or is this supposed to be a component?"

/-- **`wasm-tools component wit` on a binary** (a WIT package or a component): its WIT text. -/
def witOfBinary (b : ByteArray) : Except String String :=
  if isComponent b then WitText.componentWit b
  else if isCoreModule b then
    match Binary.customSections b with
    | .error e => .error e
    | .ok cs =>
      match (cs.filter (·.1.startsWith Binary.componentTypeSection)).map (·.2) with
      | [] => .error noWitInfo
      | [pl] => WitText.witOfPayload pl
      | pls => WitText.witOfSections pls
  else .error "input is not a WebAssembly binary"

/-- **`wasm-tools component wit` on WIT text**: the package printed back. -/
def witOfSrc (src : WitSrc) : Except String String := do
  let pb ← pkgBytes src
  Tool.witAll pb

/-- **`component wit --importize[-world]` / `--exportize[-world]`** on WIT text: the world selected
in the elaborated package (`selectWorld`), transformed in the source (`Ize`), and the source
elaborated and encoded again. -/
def izeBytes (src : WitSrc) (fs : List String) (world : Option String)
    (f : Wit.World → Except String Wit.World) : Except String ByteArray := do
  let pb ← pkgBytesF fs src
  let d ← Tool.decode pb
  let w ← selectWorld d.pkg world
  match src with
  | .dir m ds => Ize.encodeTransformed m ds fs w f
  | .file n t => Ize.encodeTransformed [(n, t)] [] fs w f
  | .binary _ => throw "--importize/--exportize of a binary input (a component or a WIT package binary) is not implemented by this wasm-tools (see docs/projects/wasm-components.md)"

/-! ## `component targets` -/

/-- **`wasm-tools component targets`**: `.ok ()` when the component's type is a subtype of the
world's (`TargetsT.fitsB`), else the misfits. -/
def targets (src : WitSrc) (world : Option String) (comp : ByteArray) : Except String Unit := do
  let pb ← pkgBytes src
  let d ← Tool.decode pb
  let w ← selectWorld d.pkg world
  let (fits, mis) ← Wac.TargetsT.check comp pb (some w)
  if fits then pure ()
  else throw ("failed to validate encoded bytes\n\nCaused by:\n    0: type mismatch for import `" ++
    w ++ "`\n" ++ String.join (mis.map fun m => "       " ++ m ++ "\n")).trimAsciiEnd.toString

/-- **`wasm-tools component targets --semver-compatible`**: as `targets`, on the canonical views
(`Semver.targetsSemver`). -/
def targetsSemver (src : WitSrc) (world : Option String) (comp : ByteArray) : Except String Unit := do
  let pb ← pkgBytes src
  let d ← Tool.decode pb
  let w ← selectWorld d.pkg world
  let (fits, mis) ← Semver.targetsSemver comp pb w
  if fits then pure ()
  else throw ("failed to validate encoded bytes\n\nCaused by:\n    0: type mismatch for import `" ++
    w ++ "`\n" ++ String.join (mis.map fun m => "       " ++ m ++ "\n")).trimAsciiEnd.toString

/-! ## `component semver-check` -/

/-- **`wasm-tools component semver-check --prev P --new N`**: both worlds selected in the main
package (`selectWorld`), then `Semver.semverCheck`. -/
def semverCheck (src : WitSrc) (prev new : String) : Except String Unit := do
  let pb ← pkgBytes src
  let d ← Tool.decode pb
  let p ← selectWorld d.pkg (some prev)
  let n ← selectWorld d.pkg (some new)
  Semver.semverCheck pb p n

/-! ## `component new` -/

/-- The message when both layouts refuse a module. -/
def newErr (r : Except String (Option JcoTool.Tool.Out)) (e2 : String) : String :=
  match r with
  | .error e => if e == e2 then e else s!"{e} (general layout: {e2})"
  | _ => e2

/-- `new` on the prepared module. -/
def newWith (bytes : ByteArray) (adapters : List (String × ByteArray)) (growRealloc : Bool) :
    Except String ByteArray :=
  if !adapters.isEmpty then
    Prod.fst <$> JcoTool.AdaptLayout.newAdaptL bytes none adapters growRealloc
  else match JcoTool.NewCore.newMainC bytes none with
    | .ok (some o) =>
      .ok (JcoTool.Adapt.withMeta o (JcoTool.Adapt.certifiedNames o.cores.length)).bytes
    | r =>
      match JcoTool.AdaptLayout.newAdaptL bytes none [] growRealloc with
      | .ok (b, _) => .ok b
      | .error e2 => .error (newErr r e2)

/-- The type-size check of `component new` (wit-component's `decode` validates every
`component-type` section with wasmparser first): upstream's message for the first section whose
payload exceeds wasmparser's type-size or depth limit (`Budget.problem`). -/
def newBudget (core : ByteArray) : Option String :=
  match Binary.customSections core with
  | .error _ => none
  | .ok cs => (Budget.coreProblem cs).map fun (n, e) =>
    s!"decoding custom section {n}\n\nCaused by:\n    0: {e}"

/-- **`wasm-tools component new`**: the component of a core module whose world is embedded in
its `component-type` section. The certified thin-wrapper layout (`NewCore.newMainC`, with
wasm-jco's custom sections) when the module is in its fragment, else the general layout
(`AdaptLayout.newAdaptL`, checked by the reference validator); with adapters, the general
layout with them. -/
def new (core : ByteArray) (adapters : List (String × ByteArray)) (growRealloc : Bool) :
    Except String ByteArray :=
  if isComponent core then .error "decoding a component is not supported"
  else (JcoTool.Cm32.prepare core).bind fun bytes => newWith bytes adapters growRealloc

/-- `[NAME=]MODULE` of `--adapt`: the name, else the file name up to its first `.`. -/
def adapterName (spec : String) : String × String :=
  match spec.splitOn "=" with
  | n :: rest@(_ :: _) => (n, "=".intercalate rest)
  | _ =>
    let base := (spec.splitOn "/").getLastD spec
    ((base.splitOn ".").headD base, spec)

end Silmaril.Wasm.Tools.Component.Cmd
