module

public import Silmaril.Wasm.Wac.WitDir.Defs
public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasm.Wit.Binary.Embed.Defs
public import Silmaril.Wasm.Wac.AsyncNames.Defs
public import Silmaril.Wasm.Wit.Binary.DecodeLax.Defs
public import Silmaril.Wasm.Component.Codec.Defs

/-!
# WIT sources, worlds and package binaries of `wasm-tools component`

The part of the `component` subcommands' cores (`Silmaril.Wasm.Tools.Component.Cmd`) that reads a
WIT source and writes its package binary, without the componentizer (`wasm-jco new`), the
composer or the targets check, so that `wasm-tools wit-smith` (`Gen.WitSmith`,
`WasmTools.GenWitSmith`) links only wasm-wit's resolver and encoder:

* `WitSrc`: a WIT source as wit-parser's `Resolve::push_path` reads a path: a directory (one
  package of several files, with `deps/`), a single `.wit` file (no `deps/`), or a WIT
  package in binary form. `pkgBytes` is its package binary (`WitDir.encodeTextX`).
* `selectWorld`: `Resolve::select_world` on the main package, with upstream's messages.
* `retag`: the `producers` field these encoders write names wit-component `0.263.0`;
  upstream 1.262.0 writes `0.262.0`. `retag` rewrites the last seven bytes when they are that
  version string after the name `wit-component` (same length, so no size changes).
* `postPayload`, `postPackage`: the checked rewrites of the encoders' outputs.
* `witWasmOfSrc`: `wasm-tools component wit --wasm` on WIT text.

The names stay in the namespace `Silmaril.Wasm.Tools.Component.Cmd`; `Cmd.Defs` re-exports this
module. Theorems: `Silmaril.Wasm.Tools.Component.Cmd.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Cmd

open Silmaril.Wasm.Wit

/-! ## WIT sources and worlds -/

/-- A WIT source, as `Resolve::push_path` reads a path. -/
inductive WitSrc where
  /-- A directory: its `.wit` files (one package), and `deps/` (one package per entry). -/
  | dir (files : List (String × String)) (deps : List (List (String × String)))
  /-- One `.wit` file (`deps/` is not read for a file). -/
  | file (name text : String)
  /-- A WIT package in binary form. -/
  | binary (b : ByteArray)

/-- The package binary of a source. -/
def pkgBytes : WitSrc → Except String ByteArray
  | .dir fs ds => Wac.WitDir.encodeTextX fs ds
  | .file n t => Wac.WitDir.encodeTextX [(n, t)] []
  | .binary b => .ok b

def PkgName.show (n : Binary.PackageName) : String :=
  s!"{n.ns}:{n.name}" ++ (n.version.map ("@" ++ ·)).getD ""

/-- A WIT identifier as written: `%x` is `x`. -/
def unescape (s : String) : String := if s.startsWith "%" then (s.drop 1).toString else s

/-- `ns:pkg/w@v` as the package `ns:pkg@v` and the world `w`; a bare `w` has no package. -/
def parseWorldName (s : String) : Option String × String :=
  match s.splitOn "/" with
  | [a, b] =>
    match b.splitOn "@" with
    | [x, v] => (some (a ++ "@" ++ v), unescape x)
    | _ => (some a, unescape b)
  | _ => (none, unescape s)

/-- The world `n` of the main package (named `q`, when given). -/
def checkWorld (p : Binary.Package) (q : Option String) (n : String) : Except String String :=
  let pn := PkgName.show p.name
  match q with
  | some q =>
    if q != pn then .error s!"unknown package `{q}`"
    else if p.worlds.any (·.1 == n) then .ok n
    else .error s!"World `{n}` not found in package `{pn}`"
  | none =>
    if p.worlds.any (·.1 == n) then .ok n
    else .error s!"World `{n}` not found in package `{pn}`"

/-- `Resolve::select_world` on the main package: `none` takes its only world; `w` names a world
of it; `ns:pkg/w[@v]` names a world of the package `ns:pkg[@v]`, here only the main package. -/
def selectWorld (p : Binary.Package) (w : Option String) : Except String String :=
  let pn := PkgName.show p.name
  match w with
  | none =>
    match p.worlds with
    | [(n, _)] => .ok n
    | [] => .error s!"The main package `{pn}` contains no worlds"
    | ws => .error (s!"There are multiple worlds in `{pn}`; one must be explicitly chosen:" ++
        String.join (ws.map fun (n, _) => s!"\n  {pn.splitOn "@" |>.headD pn}/{n}" ++
          (p.name.version.map ("@" ++ ·)).getD ""))
  | some s =>
    let (q, n) := parseWorldName s
    checkWorld p q n

/-! ## Producers -/

/-- `name("wit-component")`: the length byte and the bytes of the name. -/
def wcName : List UInt8 := 13 :: "wit-component".toUTF8.toList

/-- `name("0.263.0")`. -/
def verOurs : List UInt8 := [7, 0x30, 0x2e, 0x32, 0x36, 0x33, 0x2e, 0x30]
/-- `name("0.262.0")`. -/
def verUpstream : List UInt8 := [7, 0x30, 0x2e, 0x32, 0x36, 0x32, 0x2e, 0x30]

/-- Rewrite the trailing producers version `0.263.0` (after `wit-component`) to upstream's
`0.262.0`; any other input is unchanged. -/
def retag (b : ByteArray) : ByteArray :=
  if b.size ≥ 22 && (b.extract (b.size - 22) b.size).toList == wcName ++ verOurs then
    b.extract 0 (b.size - 7) ++ ⟨(verUpstream.drop 1).toArray⟩
  else b

/-! ## Checked post-processing of encoder outputs

`retag` and `AsyncNames.fixBytes` rewrite bytes of the verified encoders' outputs (the producers
version; the old names of async functions). They are applied **checked** (translation
validation): the rewritten bytes are kept only when they decode to the same world (payloads) or
the same package and environment (WIT packages) as the encoder's bytes, else the encoder's bytes
are kept (payloads are read with `decodeWorldTypeLax`, which reads wit-component 0.262's plain
names of async functions). So every theorem about what the encoders' bytes decode to holds for what is written
(`postPayload_world`, `postPackage_decode`). -/

/-- What a `component-type` payload decodes to, for comparison. -/
def payloadWorld (b : ByteArray) :
    Option (Binary.PackageName × String × Binary.World × Binary.StringEncoding) :=
  (Binary.decodeWorldType b).toOption

/-- What a payload decodes to when async functions may carry plain names
(`decodeWorldTypeLax`, the reading of wit-component 0.262's payloads). -/
def payloadWorldLax (b : ByteArray) :
    Option (Binary.PackageName × String × Binary.World × Binary.StringEncoding) :=
  (Binary.decodeWorldTypeLax b).toOption

/-- **The payload as written**: async names fixed and the producers retagged, when the result,
read with plain async names allowed (`decodeWorldTypeLax`), is the world the encoder's payload
decodes to; else the payload unchanged. -/
def postPayload (pl : ByteArray) : ByteArray :=
  let q := retag (Wac.AsyncNames.fixBytes pl)
  if payloadWorldLax q = payloadWorld pl then q else pl

/-- What a WIT package binary decodes to, for comparison. -/
def packageView (b : ByteArray) : Option (Binary.Package × Binary.Env) :=
  (Tool.decode b).toOption.map fun d => (d.pkg, d.env)

/-- What a WIT package binary decodes to when async functions may carry plain names: the
async names restored (`Binary.normSections`, as `decodeWorldTypeLax` does for payloads), then
`Tool.decode`'s two readers (`decodeSections`, and `decodeEnv`'s `itemViews`) on the sections. -/
def packageViewLax (b : ByteArray) : Option (Binary.Package × Binary.Env) :=
  match Silmaril.Wasm.Component.Codec.decodeMvp b with
  | .ok (.mk ss) =>
    let ss' := Binary.normSections ss
    match Binary.decodeSections ss', Binary.itemViews (Binary.splitCustom ss').1 with
    | .ok p, .ok (full, typesOnly) => some (p, full ++ typesOnly)
    | _, _ => none
  | .error _ => none

/-- **The package binary as written**: async names fixed and retagged, when the result, read
with plain async names allowed (`packageViewLax`, wit-component 0.262's spelling, which
wasmparser 1.262.0 requires), is the package and environment the encoder's bytes decode to;
else unchanged. -/
def postPackage (pb : ByteArray) : ByteArray :=
  let q := retag (Wac.AsyncNames.fixBytes pb)
  if packageViewLax q = packageView pb then q else pb


/-! ## `component wit --wasm` -/

/-- **`wasm-tools component wit --wasm` on WIT text**: the package binary. -/
def witWasmOfSrc (src : WitSrc) : Except String ByteArray :=
  postPackage <$> pkgBytes src

end Silmaril.Wasm.Tools.Component.Cmd
