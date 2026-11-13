module

public import Silmaril.Compiler.Clang.AST.Defs
public import Lean.Data.Json.Basic
public import Lean.Data.Json.Parser
public import Lean.Data.Json.Printer

/-! # Decoding and encoding Clang's JSON AST

`decode` reads the output of `clang -Xclang -ast-dump=json` into `Silmaril.Clang.Node`;
`encode` prints a node back. The pair is exact: `encode (decode j) = j` as JSON values (up to
the order of object keys) for every document of the subset, which the campaign checks on the
corpus (`cfront decode FILE.json`, metric `json_roundtrip`).

Fail-closed: a node of an unknown kind, an unknown key, or a value of an unexpected shape is a
decoding error that names the node's id and the key. Nothing is skipped or guessed.
The sole opaque case is `FullComment`: documentation and all its descendants are stored as
raw JSON, reproduced exactly by encoding, and excluded from semantic child traversal.
-/

@[expose] public section

namespace Silmaril.Clang.Json

open Lean (Json JsonNumber)

/-- A decoding result. -/
abbrev D := Except String

/-! ## Object helpers -/

/-- The keys and values of an object. -/
def fields (j : Json) (what : String) : D (List (String × Json)) :=
  match j with
  | .obj kvs => return kvs.toList
  | _ => throw s!"{what}: object expected, got {j.compress.take 80}"

def look (fs : List (String × Json)) (k : String) : Option Json :=
  (fs.find? (·.1 == k)).map (·.2)

def checkKeys (fs : List (String × Json)) (known : List String) (what : String) : D Unit := do
  for (k, _) in fs do
    unless known.contains k do throw s!"{what}: unknown key {k}"

def optStr (fs : List (String × Json)) (k what : String) : D (Option String) :=
  match look fs k with
  | none => return none
  | some (.str s) => return some s
  | some j => throw s!"{what}: {k}: string expected, got {j.compress.take 80}"

def optNat (fs : List (String × Json)) (k what : String) : D (Option Nat) :=
  match look fs k with
  | none => return none
  | some j => match j.getNat? with
    | .ok n => return some n
    | .error _ => throw s!"{what}: {k}: natural number expected, got {j.compress.take 80}"

def optBool (fs : List (String × Json)) (k what : String) : D (Option Bool) :=
  match look fs k with
  | none => return none
  | some (.bool b) => return some b
  | some j => throw s!"{what}: {k}: boolean expected, got {j.compress.take 80}"

def optWith {α : Type} (fs : List (String × Json)) (k : String) (f : Json → D α) :
    D (Option α) :=
  match look fs k with
  | none => return none
  | some j => some <$> f j

/-! ## Locations, types, references -/

def bareLocKeys : List String :=
  ["offset", "file", "line", "presumedFile", "presumedLine", "col", "tokLen", "includedFrom",
    "isMacroArgExpansion"]

def decodeBareLoc (j : Json) : D BareLoc := do
  let fs ← fields j "location"
  checkKeys fs bareLocKeys "location"
  let includedFrom ← optWith fs "includedFrom" fun j => do
    let gs ← fields j "includedFrom"
    checkKeys gs ["file"] "includedFrom"
    match look gs "file" with
    | some (.str s) => return s
    | _ => throw "includedFrom: file expected"
  return { offset := ← optNat fs "offset" "location", file := ← optStr fs "file" "location",
           line := ← optNat fs "line" "location",
           presumedFile := ← optStr fs "presumedFile" "location",
           presumedLine := ← optNat fs "presumedLine" "location",
           col := ← optNat fs "col" "location", tokLen := ← optNat fs "tokLen" "location",
           includedFrom,
           isMacroArgExpansion := ← optBool fs "isMacroArgExpansion" "location" }

def decodeLoc (j : Json) : D Loc := do
  let fs ← fields j "location"
  match look fs "spellingLoc", look fs "expansionLoc" with
  | some s, some e =>
    checkKeys fs ["spellingLoc", "expansionLoc"] "location"
    return .macro (← decodeBareLoc s) (← decodeBareLoc e)
  | none, none => return .bare (← decodeBareLoc j)
  | _, _ => throw "location: spellingLoc without expansionLoc"

def decodeRange (j : Json) : D Range := do
  let fs ← fields j "range"
  checkKeys fs ["begin", "end"] "range"
  let some b := look fs "begin" | throw "range: begin expected"
  let some e := look fs "end" | throw "range: end expected"
  return ⟨← decodeLoc b, ← decodeLoc e⟩

def decodeQualType (j : Json) : D QualType := do
  let fs ← fields j "type"
  checkKeys fs ["qualType", "desugaredQualType", "typeAliasDeclId"] "type"
  let some q ← optStr fs "qualType" "type" | throw "type: qualType expected"
  return { qualType := q, desugaredQualType := ← optStr fs "desugaredQualType" "type",
           typeAliasDeclId := ← optStr fs "typeAliasDeclId" "type" }

def decodeDeclRef (j : Json) : D DeclRef := do
  let fs ← fields j "declaration reference"
  checkKeys fs ["id", "kind", "name", "type"] "declaration reference"
  let some id ← optStr fs "id" "declaration reference" | throw "declaration reference: id expected"
  let some kind ← optStr fs "kind" "declaration reference"
    | throw "declaration reference: kind expected"
  return { id, kind, name := ← optStr fs "name" "declaration reference",
           type := ← optWith fs "type" decodeQualType }

def decodeValue (j : Json) : D Value :=
  match j with
  | .str s => return .str s
  | j => match j.getInt? with
    | .ok n => return .int n
    | .error _ => throw s!"value: string or integer expected, got {j.compress.take 80}"

/-! ## Nodes -/

/-- Every key a node of the subset may have. -/
def nodeKeys : List String :=
  ["id", "kind", "loc", "range", "type", "valueCategory", "name", "mangledName", "storageClass",
    "tls", "isImplicit", "isUsed", "isReferenced", "previousDecl", "parentDeclContextId", "variadic",
    "inline", "init", "nrvo", "tagUsed", "completeDefinition", "isBitfield", "castKind",
    "isPartOfExplicitCast", "opcode", "isPostfix", "canOverflow", "computeLHSType",
    "computeResultType", "value", "referencedDecl", "nonOdrUseReason", "isArrow",
    "referencedMemberDecl", "argType", "hasElse", "hasVar", "hasInit", "targetLabelDeclId",
    "declId", "size", "numElements", "vectorKind", "decl", "ownedTagDecl", "isTagOwned", "cc", "implicit", "inherited", "field",
    "storageDuration", "fixedUnderlyingType", "qualifiers", "visibility", "inner",
    "array_filler"]

def decodeHeader (fs : List (String × Json)) : D Header := do
  let some id ← optStr fs "id" "node" | throw "node without id"
  let w := s!"node {id}"
  let some kindName ← optStr fs "kind" w | throw s!"{w}: no kind"
  let some kind := Kind.ofString? kindName | throw s!"{w}: unknown node kind {kindName}"
  let w := s!"{kindName} {id}"
  checkKeys fs nodeKeys w
  return {
    id, kind
    loc := ← optWith fs "loc" decodeLoc
    range := ← optWith fs "range" decodeRange
    type := ← optWith fs "type" decodeQualType
    valueCategory := ← optStr fs "valueCategory" w
    name := ← optStr fs "name" w
    mangledName := ← optStr fs "mangledName" w
    storageClass := ← optStr fs "storageClass" w
    tls := ← optStr fs "tls" w
    isImplicit := ← optBool fs "isImplicit" w
    isUsed := ← optBool fs "isUsed" w
    isReferenced := ← optBool fs "isReferenced" w
    previousDecl := ← optStr fs "previousDecl" w
    parentDeclContextId := ← optStr fs "parentDeclContextId" w
    variadic := ← optBool fs "variadic" w
    inline := ← optBool fs "inline" w
    init := ← optStr fs "init" w
    nrvo := ← optBool fs "nrvo" w
    tagUsed := ← optStr fs "tagUsed" w
    completeDefinition := ← optBool fs "completeDefinition" w
    isBitfield := ← optBool fs "isBitfield" w
    castKind := ← optStr fs "castKind" w
    isPartOfExplicitCast := ← optBool fs "isPartOfExplicitCast" w
    opcode := ← optStr fs "opcode" w
    isPostfix := ← optBool fs "isPostfix" w
    canOverflow := ← optBool fs "canOverflow" w
    computeLHSType := ← optWith fs "computeLHSType" decodeQualType
    computeResultType := ← optWith fs "computeResultType" decodeQualType
    value := ← optWith fs "value" decodeValue
    referencedDecl := ← optWith fs "referencedDecl" decodeDeclRef
    nonOdrUseReason := ← optStr fs "nonOdrUseReason" w
    isArrow := ← optBool fs "isArrow" w
    referencedMemberDecl := ← optStr fs "referencedMemberDecl" w
    argType := ← optWith fs "argType" decodeQualType
    hasElse := ← optBool fs "hasElse" w
    hasVar := ← optBool fs "hasVar" w
    hasInit := ← optBool fs "hasInit" w
    targetLabelDeclId := ← optStr fs "targetLabelDeclId" w
    declId := ← optStr fs "declId" w
    size := ← optNat fs "size" w
    numElements := ← optNat fs "numElements" w
    vectorKind := ← optStr fs "vectorKind" w
    decl := ← optWith fs "decl" decodeDeclRef
    ownedTagDecl := ← optWith fs "ownedTagDecl" decodeDeclRef
    isTagOwned := ← optBool fs "isTagOwned" w
    cc := ← optStr fs "cc" w
    implicit := ← optBool fs "implicit" w
    inherited := ← optBool fs "inherited" w
    field := ← optWith fs "field" decodeDeclRef
    storageDuration := ← optStr fs "storageDuration" w
    fixedUnderlyingType := ← optWith fs "fixedUnderlyingType" decodeQualType
    qualifiers := ← optStr fs "qualifiers" w
    visibility := ← optStr fs "visibility" w }

partial def decodeNode (j : Json) : D Node := do
  let fs ← fields j "node"
  if fs.isEmpty then return .absent
  if look fs "kind" == some (.str "FullComment") then return .comment j
  if let some (.str ak) := look fs "associationKind" then
    if (look fs "id").isSome then throw "generic association with an id"
    checkKeys fs ["associationKind", "selected", "inner"] "generic association"
    let inner ← match look fs "inner" with
      | none => pure none
      | some (.arr xs) => some <$> xs.mapM decodeNode
      | some _ => throw "generic association: inner: array expected"
    return .association ak (← optBool fs "selected" "generic association") inner
  let h ← decodeHeader fs
  let children (k : String) : D (Option (Array Node)) :=
    match look fs k with
    | none => return none
    | some (.arr xs) => some <$> xs.mapM decodeNode
    | some _ => throw s!"{h.kind} {h.id}: {k}: array expected"
  return .mk h (← children "inner") (← children "array_filler")

/-- Decode a whole `-ast-dump=json` document (a `TranslationUnitDecl`). -/
def decode (text : String) : D Node := do
  let j ← Json.parse text
  let n ← decodeNode j
  unless n.kind? == some .translationUnitDecl do
    throw "the document is not a TranslationUnitDecl"
  return n

/-! ## Encoding -/

def opt {α : Type} (k : String) (f : α → Json) : Option α → List (String × Json)
  | none => []
  | some a => [(k, f a)]

def encodeBareLoc (l : BareLoc) : Json :=
  .mkObj <| opt "offset" (fun n : Nat => (n : Json)) l.offset ++ opt "file" Json.str l.file
    ++ opt "line" (fun n : Nat => (n : Json)) l.line ++ opt "presumedFile" Json.str l.presumedFile
    ++ opt "presumedLine" (fun n : Nat => (n : Json)) l.presumedLine
    ++ opt "col" (fun n : Nat => (n : Json)) l.col ++ opt "tokLen" (fun n : Nat => (n : Json)) l.tokLen
    ++ opt "includedFrom" (fun f => .mkObj [("file", .str f)]) l.includedFrom
    ++ opt "isMacroArgExpansion" Json.bool l.isMacroArgExpansion

def encodeLoc : Loc → Json
  | .bare l => encodeBareLoc l
  | .macro s e => .mkObj [("spellingLoc", encodeBareLoc s), ("expansionLoc", encodeBareLoc e)]

def encodeRange (r : Range) : Json :=
  .mkObj [("begin", encodeLoc r.begin), ("end", encodeLoc r.end)]

def encodeQualType (q : QualType) : Json :=
  .mkObj <| [("qualType", .str q.qualType)] ++ opt "desugaredQualType" Json.str q.desugaredQualType
    ++ opt "typeAliasDeclId" Json.str q.typeAliasDeclId

def encodeDeclRef (r : DeclRef) : Json :=
  .mkObj <| [("id", .str r.id), ("kind", .str r.kind)] ++ opt "name" Json.str r.name
    ++ opt "type" encodeQualType r.type

def encodeValue : Value → Json
  | .str s => .str s
  | .int n => (n : Json)

def encodeHeader (h : Header) : List (String × Json) :=
  let s := fun (k : String) (v : Option String) => opt k Json.str v
  let b := fun (k : String) (v : Option Bool) => opt k Json.bool v
  let q := fun (k : String) (v : Option QualType) => opt k encodeQualType v
  [("id", .str h.id), ("kind", .str h.kind.toString)]
    ++ opt "loc" encodeLoc h.loc ++ opt "range" encodeRange h.range ++ q "type" h.type
    ++ s "valueCategory" h.valueCategory ++ s "name" h.name ++ s "mangledName" h.mangledName
    ++ s "storageClass" h.storageClass ++ s "tls" h.tls ++ b "isImplicit" h.isImplicit ++ b "isUsed" h.isUsed
    ++ b "isReferenced" h.isReferenced ++ s "previousDecl" h.previousDecl
    ++ s "parentDeclContextId" h.parentDeclContextId ++ b "variadic" h.variadic
    ++ b "inline" h.inline ++ s "init" h.init ++ b "nrvo" h.nrvo ++ s "tagUsed" h.tagUsed
    ++ b "completeDefinition" h.completeDefinition ++ b "isBitfield" h.isBitfield
    ++ s "castKind" h.castKind ++ b "isPartOfExplicitCast" h.isPartOfExplicitCast
    ++ s "opcode" h.opcode ++ b "isPostfix" h.isPostfix ++ b "canOverflow" h.canOverflow
    ++ q "computeLHSType" h.computeLHSType ++ q "computeResultType" h.computeResultType
    ++ opt "value" encodeValue h.value ++ opt "referencedDecl" encodeDeclRef h.referencedDecl
    ++ s "nonOdrUseReason" h.nonOdrUseReason ++ b "isArrow" h.isArrow
    ++ s "referencedMemberDecl" h.referencedMemberDecl ++ q "argType" h.argType
    ++ b "hasElse" h.hasElse ++ b "hasVar" h.hasVar ++ b "hasInit" h.hasInit
    ++ s "targetLabelDeclId" h.targetLabelDeclId ++ s "declId" h.declId
    ++ opt "size" (fun n : Nat => (n : Json)) h.size
    ++ opt "numElements" (fun n : Nat => (n : Json)) h.numElements ++ s "vectorKind" h.vectorKind
    ++ opt "decl" encodeDeclRef h.decl
    ++ opt "ownedTagDecl" encodeDeclRef h.ownedTagDecl
    ++ b "isTagOwned" h.isTagOwned ++ s "cc" h.cc ++ b "implicit" h.implicit
    ++ b "inherited" h.inherited ++ opt "field" encodeDeclRef h.field
    ++ s "storageDuration" h.storageDuration ++ q "fixedUnderlyingType" h.fixedUnderlyingType
    ++ s "qualifiers" h.qualifiers ++ s "visibility" h.visibility

partial def encodeNode : Node → Json
  | .absent => .mkObj []
  | .comment raw => raw
  | .association ak sel inner =>
    .mkObj <| [("associationKind", .str ak)] ++ opt "selected" Json.bool sel
      ++ opt "inner" (fun xs => .arr (xs.map encodeNode)) inner
  | .mk h inner filler =>
    .mkObj <| encodeHeader h ++ opt "inner" (fun xs => .arr (xs.map encodeNode)) inner
      ++ opt "array_filler" (fun xs => .arr (xs.map encodeNode)) filler

/-- The compact JSON text of a node. -/
def encode (n : Node) : String := (encodeNode n).compress

end Silmaril.Clang.Json
