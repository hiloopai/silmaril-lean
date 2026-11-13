import WasmTools.Component.Run
import Silmaril.Wasm.Tools.Component.Unbundle.Defs
import Silmaril.Wasm.Tools.Component.SemverMerge.Defs

/-!
# `wasm-tools component new / embed / wit / targets`: the bodies

Each subcommand is a body on the record of its arguments (`WasmTools.Component.Opts`: what the
specification read)
that reads the inputs, calls one core function of `Silmaril.Wasm.Tools.Component.Cmd` and writes the output. Options that
would change the output and are not implemented are refused (`refuse`), never ignored; options
without effect on this implementation's output are listed in docs/projects/wasm-components.md.
-/

namespace WasmTools.Component

open Silmaril.Wasm.Tools.Component

/-! ## `component new` -/

def newBody (a : NewArgs) : M Unit := do
  refuse [("emit-canonical-names", a.emitCanonicalNames), ("reject-legacy-names", a.rejectLegacyNames)]
  let mut names : List (String × String) := []
  for v in a.importName do
    match Rename.parsePair v with
    | some p => names := names ++ [p]
    | none => throw (.usage (s!"error: invalid value '{v}' for '--import-name <OLD=NEW>': " ++
        "expected `--import-name` option to be of the form `OLD=NEW`\n\nFor more information, try '--help'.\n"))
  if a.returnCallRef.getD false then
    fail "option `--return-call-ref` is not implemented by this wasm-tools (see docs/projects/wasm-components.md)"
  let core ← readWasm a.io
  let mut ads : List (String × ByteArray) := []
  for spec in a.adapt do
    let (n, path) := Cmd.adapterName spec
    let raw ← match ← (IO.FS.readBinFile path).toBaseIO with
      | .ok b => pure b
      | .error e => fail s!"failed to read from `{path}`\n\nCaused by:\n    0: {osCause e}"
    ads := ads ++ [(n, ← liftE (Text.toBinary raw))]
  if Cmd.isComponent core then fail "decoding a component is not supported"
  -- wasmparser's type-size limit on the `component-type` sections, before any expansion
  if let some e := Cmd.newBudget core then fail e
  let b ← match Cmd.new core ads a.reallocViaMemoryGrow with
    | .ok b => pure b
    | .error e => fail s!"failed to encode a component from module\n\nCaused by:\n    0: {e}"
  let b ← liftE (Rename.renameBytes names b)
  writeWasm a.io.output b a.wat

/-! ## `component embed` -/

/-- `--encoding`, with clap's message for an unknown value (exit 2). -/
def encodingArg (enc : Option String) : M Silmaril.Wasm.Wit.Binary.StringEncoding := do
  match enc with
  | none => pure .utf8
  | some e =>
    match Cmd.encodingOf e with
    | some se => pure se
    | none => throw (.usage (s!"error: invalid value '{e}' for '--encoding <ENCODING>': " ++
        s!"unknown string encoding `{e}`\n\nFor more information, try '--help'.\n"))

/-- The features of `--features F,…` / `--all-features` for a source. -/
def featureList (f : FeatureArgs) (src : Cmd.WitSrc) : List String :=
  if f.allFeatures then f.features ++ Cmd.srcFeatures src else f.features

/-- `--features F,…` / `--all-features` applied to a WIT source: the source elaborated with
those features, as a package binary (`Cmd.pkgBytesF`); unchanged without them. -/
def withFeatures (f : FeatureArgs) (src : Cmd.WitSrc) : M Cmd.WitSrc := do
  let fs := featureList f src
  match src with
  | .binary _ => pure src
  | _ =>
    -- comments are documentation, as wit-parser reads them (`Cmd.docSrc`); the source as
    -- written when the rewritten one does not elaborate
    match Cmd.pkgBytesF fs (Cmd.docSrc src) with
    | .ok b => pure (.binary b)
    | .error _ =>
      match Cmd.pkgBytesF fs src with
      | .ok b => pure (.binary b)
      | .error e =>
        -- wit-parser's message for a source without a `package` header (e.g. empty stdin)
        if e.startsWith "no `package` header in" then
          fail "no `package` header was found in any WIT file for this package"
        else fail e

def embedBody (a : EmbedArgs) : M Unit := do
  refuse [("emit-canonical-names", a.emitCanonicalNames)]
  let se ← encodingArg a.encoding
  let src ← withFeatures a.feats (← readWitSrc a.wit)
  let async := a.asyncCallback || a.asyncStackful
  -- `--dummy` is standard32; `--dummy-names M` is M (upstream's checks, in its order)
  let dummy : Option Silmaril.Wasm.Tools.Component.Dummy.Mangling ←
    if a.dummy then
      if async then fail "non-legacy mangling not yet supported when generating async dummy modules"
      pure (some .standard32)
    else match a.dummyNames with
      | some "standard32" =>
        if async then fail "non-legacy mangling not yet supported when generating async dummy modules"
        pure (some .standard32)
      | some _ =>
        if async then fail "options `--async-callback`/`--async-stackful` (async dummy modules) are not implemented by this wasm-tools (see docs/projects/wasm-components.md)"
        pure (some .legacy)
      | none => pure none
  if a.onlyCustom then
    let b ← liftE (Cmd.embed src a.world se .onlyCustom)
    writeWasm a.io.output b false
  else if let some mg := dummy then
    let b ← liftE (Cmd.embedDummy src a.world se mg)
    writeWasm a.io.output b a.wat
  else
    let m ← readWasm a.io
    -- a module with a world embedded already: upstream's merge check
    if let .ok pl := Cmd.embed src a.world se .onlyCustom then
      if let some e := Cmd.embedConflict m pl then fail e
    let b ← liftE (Cmd.embed src a.world se (.module m))
    writeWasm a.io.output b a.wat

/-! ## `component wit` -/

/-- The input of `component wit`: a directory or a non-Wasm file is WIT text. -/
def witBody (a : WitArgs) : M Unit := do
  refuse [("json", a.json), ("generate-nominal-type-ids", a.generateNominalTypeIds.isSome),
    ("emit-canonical-names", a.emitCanonicalNames)]
  let input := a.io.input
  -- a directory, or a file that is not Wasm (binary or text), is WIT text
  let isDir ← match input with
    | some p => (System.FilePath.mk p).isDir
    | none => pure false
  let src ← if isDir then readWitSrc input.get!
    else
      -- `WitSource::from_path`'s message for an unreadable file (not `InputArg`'s)
      let raw ← match input with
        | none | some "-" => readRaw input
        | some path =>
          match ← (IO.FS.readBinFile path).toBaseIO with
          | .ok b => pure b
          | .error e => fail s!"failed to read {repr path}\n\nCaused by:\n    0: {osCause e}"
      if Text.hasMagic raw then pure (Cmd.WitSrc.binary raw)
      else match String.fromUTF8? raw with
        | none => fail "input was not valid utf-8"
        | some t =>
          let t0 := t.trimAsciiStart.toString
          if t0.startsWith "(" || t0.startsWith ";;" then
            pure (.binary (← liftE (Text.toBinary raw)))
          else pure (.file (input.getD "<stdin>") t)
  let text := match src with
    | .binary _ => false
    | _ => true
  -- `--importize[-world]`, `--exportize[-world]`: the world transformed in the source
  let ize : Option (Option String × (Silmaril.Wasm.Wit.World → Except String Silmaril.Wasm.Wit.World)) :=
    if a.importize || a.importizeWorld.isSome then
      some (a.importizeWorld,
        fun w => Ize.importizeWorld w a.importizeOutWorldName)
    else if a.exportize || a.exportizeWorld.isSome then
      some (a.exportizeWorld,
        fun w => Ize.exportizeWorld w a.exportizeOutWorldName a.exportizeImport)
    else none
  let src ← match ize with
    | none => pure src
    | some (world, f) =>
      let fs := featureList a.feats src
      match Cmd.izeBytes (Cmd.docSrc src) fs world f with
      | .ok b => pure (.binary b)
      | .error e =>
        match Cmd.izeBytes src fs world f with
        | .ok b => pure (.binary b)
        | .error _ => fail e
  -- `--merge-world-imports-based-on-semver WORLD`: the world's imports merged on the source
  if let some world := a.mergeWorldImportsBasedOnSemver then
    let fs := featureList a.feats src
    let run (s : Cmd.WitSrc) : Except String (ByteArray × String) := match s with
      | .dir m ds => SemverMerge.mergeOut m ds fs (some world)
      | .file n t => SemverMerge.mergeOut [(n, t)] [] fs (some world)
      | .binary b =>
        if Silmaril.Wasm.JcoTool.WitOf.isWitPackage b then
          .error "--merge-world-imports-based-on-semver of a WIT package binary is not implemented by this wasm-tools (see docs/projects/wasm-components.md)"
        else .error "the `--merge-world-imports-based-on-semver` flag is not compatible with a component input"
    let (b, t) ← match run (Cmd.docSrc src) with
      | .ok r => pure r
      | .error e =>
        match run src with
        | .ok r => pure r
        | .error _ => fail e
    if a.wasm || a.wat then writeWasm a.io.output (Cmd.postPackage b) a.wat
    else writeText a.io.output (if a.noDocs then WitText.stripDocs t else t)
    return
  let src ← withFeatures a.feats src
  if let some dir := a.outDir then
    let pb ← match src with
      | .binary b =>
        if Silmaril.Wasm.JcoTool.WitOf.isWitPackage b then pure b
        else fail "--out-dir of a component's or core module's WIT is not implemented by this wasm-tools (see docs/projects/wasm-components.md)"
      | src => liftE (Cmd.pkgBytes src)
    let files ← liftE (WitText.outDirFiles pb)
    let base := System.FilePath.mk dir
    match ← (IO.FS.createDirAll base).toBaseIO with
    | .ok () => pure ()
    | .error e => fail s!"failed to create directory: {repr dir}\n\nCaused by:\n    0: {osCause e}"
    for (dep, stem, text) in files do
      let d := if dep then base / "deps" else base
      match ← (IO.FS.createDirAll d).toBaseIO with
      | .ok () => pure ()
      | .error e => fail s!"failed to create directory: {repr d.toString}\n\nCaused by:\n    0: {osCause e}"
      let path := d / (stem ++ ".wit")
      let text := if a.noDocs then WitText.stripDocs text else text
      match ← (IO.FS.writeFile path text).toBaseIO with
      | .ok () => pure ()
      | .error e => fail s!"failed to write file: {repr path.toString}\n\nCaused by:\n    0: {osCause e}"
      (← IO.getStdout).putStrLn s!"Writing: {path}"
    return
  if a.wasm || a.wat then
    let b ← match src with
      | .binary b =>
        -- WIT text, elaborated: the bytes as `Cmd.witWasmOfSrc` writes them
        if text then liftE (Cmd.witWasmOfSrc (.binary b))
        else if Cmd.isCoreModule b then fail "--wasm/--wat of a core module's WIT is not implemented by this wasm-tools"
        else if Silmaril.Wasm.JcoTool.WitOf.isWitPackage b then pure b
        else fail "--wasm/--wat of a component's WIT is not implemented by this wasm-tools"
      | src => liftE (Cmd.witWasmOfSrc src)
    -- upstream validates the package it encoded: wasmparser's type-size limit
    if text then
      if let some e := Budget.problem b then fail e
    writeWasm a.io.output b a.wat
  else
    let t ← match src with
      | .binary b => liftE (Cmd.witOfBinary b)
      | src => liftE (Cmd.witOfSrc src)
    writeText a.io.output (if a.noDocs then WitText.stripDocs t else t)

/-! ## `component targets` -/

def targetsBody (a : TargetsArgs) : M Unit := do
  let src ← withFeatures a.feats (← readWitSrc a.wit)
  let comp ← readWasm a.io
  if a.semverCompatible then
    liftE (Cmd.targetsSemver src a.world comp)
  else
    liftE (Cmd.targets src a.world comp)

/-! ## `component semver-check` -/

def semverBody (a : SemverArgs) : M Unit := do
  let src ← withFeatures a.feats (← readWitSrc a.wit)
  liftE (Cmd.semverCheck src a.prev a.new)

/-! ## `component unbundle` -/

def unbundleBody (a : UnbundleArgs) : M Unit := do
  let v := a.threshold
  let th ← match v.toNat? with
    | some n => pure n
    | none => throw (.usage (s!"error: invalid value '{v}' for '--threshold <SIZE>': " ++
        "invalid digit found in string\n\nFor more information, try '--help'.\n"))
  let dir := System.FilePath.mk a.moduleDir
  let input ← readWasm a.io
  let (out, mods) ← liftE (Unbundle.unbundle input th)
  if !mods.isEmpty then
    match ← (IO.FS.createDirAll dir).toBaseIO with
    | .ok () => pure ()
    | .error _ => fail s!"failed to create directory {repr dir.toString}"
  for (m, i) in mods.zipIdx do
    let dst := dir / s!"unbundled-module{i}.wasm"
    match ← (IO.FS.writeBinFile dst m).toBaseIO with
    | .ok () => pure ()
    | .error _ => fail s!"failed to write file {repr dst.toString}"
  writeWasm a.io.output out a.wat

end WasmTools.Component
