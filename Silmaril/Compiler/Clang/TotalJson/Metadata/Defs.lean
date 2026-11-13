module

public import Silmaril.Compiler.Clang.Defs
/-! Kernel-visible nonrecursive Clang metadata parsing. The field vocabulary
and header construction are adapted from Silmaril/Clang/Json.lean at
288ee492ad09224b78ac44f8456e2ffcd6482384. Source trees are inspected directly;
Lean.Json's hidden object/access/equality helpers are never used to recognize
metadata. Diagnostics use the existing total standard-JSON renderer. -/
@[expose] public section
namespace Silmaril.Compiler.Clang.TotalJson.Metadata
open Silmaril.Formats
open Silmaril.Clang
abbrev Tree := Json.Tree Json.Decimal
abbrev D := Except String

def snippet (tree : Tree) : String :=
  String.ofList ((Json.render Json.Decimal.literal tree.toAst).toList.take 80)

def string? : Tree → Option String
  | .scalar (some (.string value)) => Json.unitsString? value
  | _ => none

def fields (tree : Tree) (what : String) : D (List (String × Tree)) :=
  match tree with
  | .object members => members.mapM fun (name, value) => do
    let some name := Json.unitsString? name | throw s!"{what}: invalid scalar Unicode object name"
    return (name, value)
  | _ => throw s!"{what}: object expected, got {snippet tree}"

def look (fs : List (String × Tree)) (key : String) : Option Tree :=
  (fs.find? (·.1 == key)).map (·.2)

def checkKeys (fs : List (String × Tree)) (known : List String) (what : String) : D Unit := do
  for (key, _) in fs do
    unless known.contains key do throw s!"{what}: unknown key {key}"

def optStr (fs : List (String × Tree)) (key what : String) : D (Option String) :=
  match look fs key with
  | none => return none
  | some tree => match string? tree with
    | some s => return some s
    | none => throw s!"{what}: {key}: string expected, got {snippet tree}"

/-- Match the imported Json.getNat? representation policy: a nonnegative
mantissa with exponent zero after the standard exact-decimal bridge. -/
def optNat (fs : List (String × Tree)) (key what : String) : D (Option Nat) :=
  match look fs key with
  | none => return none
  | some tree => match tree with
    | .scalar (some (.number d)) => match Json.Decode.numberToLean d with
      | ⟨.ofNat n, 0⟩ => return some n
      | _ => throw s!"{what}: {key}: natural number expected, got {snippet tree}"
    | _ => throw s!"{what}: {key}: natural number expected, got {snippet tree}"

def optBool (fs : List (String × Tree)) (key what : String) : D (Option Bool) :=
  match look fs key with
  | none => return none
  | some (.scalar (some (.bool value))) => return some value
  | some tree => throw s!"{what}: {key}: boolean expected, got {snippet tree}"

def optWith {A : Type} (fs : List (String × Tree)) (key : String) (f : Tree → D A) : D (Option A) :=
  match look fs key with
  | none => return none
  | some tree => some <$> f tree

abbrev bareLocKeys := Silmaril.Clang.Json.bareLocKeys

def decodeBareLoc (j : Tree) : D BareLoc := do
  let fs ← fields j "location"
  checkKeys fs bareLocKeys "location"
  let includedFrom ← optWith fs "includedFrom" fun j => do
    let gs ← fields j "includedFrom"
    checkKeys gs ["file"] "includedFrom"
    match (look gs "file").bind string? with
    | some s => return s
    | none => throw "includedFrom: file expected"
  return { offset := ← optNat fs "offset" "location", file := ← optStr fs "file" "location",
           line := ← optNat fs "line" "location",
           presumedFile := ← optStr fs "presumedFile" "location",
           presumedLine := ← optNat fs "presumedLine" "location",
           col := ← optNat fs "col" "location", tokLen := ← optNat fs "tokLen" "location",
           includedFrom,
           isMacroArgExpansion := ← optBool fs "isMacroArgExpansion" "location" }

def decodeLoc (j : Tree) : D Loc := do
  let fs ← fields j "location"
  match look fs "spellingLoc", look fs "expansionLoc" with
  | some s, some e =>
    checkKeys fs ["spellingLoc", "expansionLoc"] "location"
    return .macro (← decodeBareLoc s) (← decodeBareLoc e)
  | none, none => return .bare (← decodeBareLoc j)
  | _, _ => throw "location: spellingLoc without expansionLoc"

def decodeRange (j : Tree) : D Range := do
  let fs ← fields j "range"
  checkKeys fs ["begin", "end"] "range"
  let some b := look fs "begin" | throw "range: begin expected"
  let some e := look fs "end" | throw "range: end expected"
  return ⟨← decodeLoc b, ← decodeLoc e⟩

def decodeQualType (j : Tree) : D QualType := do
  let fs ← fields j "type"
  checkKeys fs ["qualType", "desugaredQualType", "typeAliasDeclId"] "type"
  let some q ← optStr fs "qualType" "type" | throw "type: qualType expected"
  return { qualType := q, desugaredQualType := ← optStr fs "desugaredQualType" "type",
           typeAliasDeclId := ← optStr fs "typeAliasDeclId" "type" }

def decodeDeclRef (j : Tree) : D DeclRef := do
  let fs ← fields j "declaration reference"
  checkKeys fs ["id", "kind", "name", "type"] "declaration reference"
  let some id ← optStr fs "id" "declaration reference" | throw "declaration reference: id expected"
  let some kind ← optStr fs "kind" "declaration reference"
    | throw "declaration reference: kind expected"
  return { id, kind, name := ← optStr fs "name" "declaration reference",
           type := ← optWith fs "type" decodeQualType }

def decodeValue (j : Tree) : D Value :=
  match string? j with
  | some s => return .str s
  | none => match j with
    | .scalar (some (.number d)) =>
      match Json.Decode.numberToLean d with
      | ⟨n, 0⟩ => return .int n
      | _ => throw s!"value: string or integer expected, got {snippet j}"
    | _ => throw s!"value: string or integer expected, got {snippet j}"

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

def decodeHeader (fs : List (String × Tree)) : D Header := do
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

end Silmaril.Compiler.Clang.TotalJson.Metadata
