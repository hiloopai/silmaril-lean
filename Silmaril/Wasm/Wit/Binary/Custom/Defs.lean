module

public import Silmaril.Wasm.Wit.Binary.Docs.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# WIT binaries: custom sections and the byte-level codec

* `producers` (the tool-conventions producers section): fields of versioned
  names, read with a verified grammar (`producersG`); wit-component writes
  `processed-by: wit-component 0.263.0` (`witComponentProducers`);
* `package-docs` (`Silmaril.Wasm.Wit.Binary.Docs`);
* `wit-component-encoding`: the format version `0x04` and the string encoding
  of a world embedded in a core module;
* `component-type…`: a world embedded in a core module (wit-component
  `src/metadata.rs`, `encode`): a component with the encoding section, one
  component type wrapping the world (as in a package) exported under the
  world's name, and the producers section.

`encodePackage` is wit-component's `encode` (bytes of the type-only component
of a package); `decodePackage` reads it back, docs included.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary
open Silmaril.Parse.ByteParse (Grammar GrammarE Bytes)

/-! ## `producers` -/

/-- The producers section: field names with their versioned names. -/
abbrev Producers := List (String × List (String × String))

section
open Silmaril.Parse.ByteParse.Grammar

def versionedG : Grammar (String × String) := name.seq name

def producerFieldG : Grammar (String × List (String × String)) :=
  name.seq (vec versionedG (seq_nonEmpty name_nonEmpty))

def producersG : Grammar Producers := vec producerFieldG (seq_nonEmpty name_nonEmpty)
end

def Producers.encode (p : Producers) : Option Bytes :=
  Silmaril.Parse.ByteParse.Enc.vec (fun (f : String × List (String × String)) => do
    let a ← Silmaril.Parse.ByteParse.Enc.name f.1
    let b ← Silmaril.Parse.ByteParse.Enc.vec (fun (v : String × String) => do
      let x ← Silmaril.Parse.ByteParse.Enc.name v.1
      let y ← Silmaril.Parse.ByteParse.Enc.name v.2
      pure (x ++ y)) f.2
    pure (a ++ b)) p

def Producers.parse (b : ByteArray) : Except Silmaril.Parse.ByteParse.Error Producers :=
  Silmaril.Parse.ByteParse.runAll (GrammarE.ofGrammar producersG).parse b

/-- What wit-component `0.263.0` records. -/
def witComponentProducers : Producers := [("processed-by", [("wit-component", "0.263.0")])]

def producersSection (p : Producers) : Option Section :=
  (p.encode).map fun l => .custom "producers" ⟨l.toArray⟩

/-! ## Packages as bytes -/

/-- The sections of a package: items, `package-docs`, `producers`. -/
def packageSections (deps : Env) (p : Package) : Except String (List Section) := do
  let items ← encodeItems deps p
  let some prod := producersSection witComponentProducers | throw "producers"
  pure (items ++ [.custom "package-docs" (docsSection p), prod])

/-- wit-component's `encode`: the type-only component of a package. -/
def encodePackage (deps : Env) (p : Package) : Except String ByteArray := do
  let ss ← packageSections deps p
  match encode (.mk ss) with
  | some b => pure b
  | none => throw "a number or size exceeds 2^32"

/-- The item sections and the custom sections of a component, if the custom
sections all come last. -/
def splitCustom : List Section → List Section × List (String × ByteArray)
  | [] => ([], [])
  | .custom n d :: ss =>
    let (items, cs) := splitCustom ss
    if items = [] then ([], (n, d) :: cs) else (.custom n d :: items, cs)
  | s :: ss =>
    let (items, cs) := splitCustom ss
    (s :: items, cs)

/-- Read the sections of a WIT package: items, then custom sections (docs
are taken from `package-docs`, other custom sections are ignored). -/
def decodeSections (ss : List Section) : Except String Package := do
  let (items, cs) := splitCustom ss
  let p ← decodeItems items
  match cs.find? (·.1 = "package-docs") with
  | none => pure p
  | some (_, d) =>
    match readDocsSection d with
    | some m => pure (p.inject m)
    | none => throw "malformed package-docs section"

/-- Read a WIT package from bytes. -/
def decodePackage (b : ByteArray) : Except String Package := do
  match parse b with
  | .ok (.mk ss) => decodeSections ss
  | .error _ => throw "malformed component"

/-! ## The interfaces a package's binary shows

Besides the package, a WIT binary shows the interfaces it uses: the types of
every interface an interface uses types from, and the full bodies of the
interfaces a world imports or exports. `decodeEnv` collects them (world
views first, as they carry functions), so that a decoded package can be
encoded again (`encodePackage (decodeEnv b) (decodePackage b)`). -/

def DItem.view : DItem → Option (IfaceName × Interface)
  | .iface (.inl j) b => some (j, b)
  | _ => none

/-- The views of one exported component type: (full, types only). -/
def topViews (ds : List ComponentDecl) : DecM (Env × Env) := do
  match ds with
  | [.inst (.type (.component wds)), .inst (.export _ (.component 0))] => do
    let s ← compSteps {} wds
    pure ((s.imports ++ s.exports).filterMap DItem.view, [])
  | ds => do
    let s ← compSteps {} ds
    pure ([], s.imports.filterMap DItem.view)

def itemViews : List Section → DecM (Env × Env)
  | .types [.component ds] :: _ :: rest => do
    let (a, b) ← topViews ds
    let (c, d) ← itemViews rest
    pure (a ++ c, b ++ d)
  | _ => pure ([], [])

/-- The interfaces a WIT binary shows (see above). -/
def decodeEnv (b : ByteArray) : Except String Env := do
  match parse b with
  | .ok (.mk ss) => do
    let (full, typesOnly) ← itemViews (splitCustom ss).1
    pure (full ++ typesOnly)
  | .error _ => throw "malformed component"

/-! ## A world embedded in a core module -/

/-- String encodings of `wit-component-encoding`. -/
inductive StringEncoding where
  | utf8 | utf16 | compactUtf16
  deriving Repr, DecidableEq, Inhabited

def StringEncoding.byte : StringEncoding → UInt8
  | .utf8 => 0 | .utf16 => 1 | .compactUtf16 => 2

def StringEncoding.ofByte? : UInt8 → Option StringEncoding
  | 0 => some .utf8 | 1 => some .utf16 | 2 => some .compactUtf16 | _ => none

/-- The sections of the `component-type` payload of world `n` of package `p`. -/
def worldTypeSections (env : Env) (p : PackageName) (n : String) (w : World) (se : StringEncoding) :
    Except String (List Section) := do
  let decls ← encodeWorld env w
  let some prod := producersSection witComponentProducers | throw "producers"
  pure [.custom "wit-component-encoding" ⟨#[0x04, se.byte]⟩,
    .types [.component (worldWrapper p n decls)], .exports [⟨↑n, ⟨.type, 0⟩, none⟩], prod]

/-- The contents of a `component-type` custom section (wit-component's
`metadata::encode`). -/
def encodeWorldType (env : Env) (p : PackageName) (n : String) (w : World) (se : StringEncoding) :
    Except String ByteArray := do
  let ss ← worldTypeSections env p n w se
  match encode (.mk ss) with
  | some b => pure b
  | none => throw "a number or size exceeds 2^32"

/-- Read the sections of a `component-type` payload. -/
def decodeWorldTypeSections : List Section → Except String (PackageName × String × World × StringEncoding)
  | .custom "wit-component-encoding" d :: .types [.component ds] ::
      .exports [⟨⟨n, .plain0⟩, ⟨.type, 0⟩, none⟩] :: _ => do
    let se ← match d.data.toList with
      | [0x04, b] => match StringEncoding.ofByte? b with
        | some se => pure se
        | none => throw "unknown string encoding"
      | _ => throw "unsupported wit-component-encoding"
    match ← decTop n ds with
    | .world p m w => pure (p, m, w, se)
    | .iface .. => throw "not a world"
  | _ => throw "malformed component-type payload"

def decodeWorldType (b : ByteArray) : Except String (PackageName × String × World × StringEncoding) := do
  match parse b with
  | .ok (.mk ss) => decodeWorldTypeSections ss
  | .error _ => throw "malformed component"

end Silmaril.Wasm.Wit.Binary
