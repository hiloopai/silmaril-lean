module

public import Silmaril.Compiler.Clang.TotalJson.Metadata.Defs
/-! A structurally recursive Clang node decoder from standard JSON values.
The imported Raw snapshot remains unchanged. Header/location
helpers inspect the source tree; recursive child decoding has an independent schema. -/
@[expose] public section
namespace Silmaril.Compiler.Clang.TotalJson
open Silmaril.Formats
abbrev Tree := Json.Tree Json.Decimal
abbrev Members := List (Json.Units × Tree)
abbrev Nodes := List Node

inductive Error where
  | syntax
  | bridge
  | node (message : String)
  | root (message : String)
  deriving DecidableEq, Repr

/-- One node's nonrecursive shape. Association boolean diagnostics are delayed
until after children, retaining the imported decoder's exact error order. -/
inductive Head where
  | absent
  | comment (json : Lean.Json)
  | association (kind : String) (selected : Except Error (Option Bool))
  | node (header : Silmaril.Clang.Header)

def keyMatches (units : Json.Units) (key : String) : Bool :=
  Json.unitsString? units == some key

/-- Inspect source fields directly; semantic children are not traversed while
classifying metadata. The public wrapper first validates the shared strict bridge. -/
def classify (members : Members) : Except Error Head := do
  let fs ← (Metadata.fields (.object members) "node").mapError Error.node
  if fs.isEmpty then return .absent
  if (Metadata.look fs "kind").bind Metadata.string? == some "FullComment" then
    let some full := Json.Decode.objectToLean? members | throw .bridge
    return .comment (Lean.Json.mkObj full)
  if let some kind := (Metadata.look fs "associationKind").bind Metadata.string? then
    if (Metadata.look fs "id").isSome then throw (.node "generic association with an id")
    let _ ← (Metadata.checkKeys fs ["associationKind", "selected", "inner"] "generic association").mapError Error.node
    return .association kind ((Metadata.optBool fs "selected" "generic association").mapError Error.node)
  return .node (← (Metadata.decodeHeader fs).mapError Error.node)

/-- A nonobject receives a total source-tree object-shape diagnostic. -/
def nonObject (tree : Tree) : Except Error Node :=
  .error (.node s!"node: object expected, got {Metadata.snippet tree}")

mutual
  def decodeTreeCore : Tree → Except Error Node
    | .scalar value => nonObject (.scalar value)
    | .array values => nonObject (.array values)
    | .object members => do
      match ← classify members with
      | .absent => return .absent
      | .comment json => return .comment json
      | .association kind selected =>
        let inner ← decodeChildren "generic association" "inner" members
        return .association kind (← selected) inner
      | .node header =>
        let inner ← decodeChildren s!"{header.kind} {header.id}" "inner" members
        let filler ← decodeChildren s!"{header.kind} {header.id}" "array_filler" members
        return .mk header inner filler

  def decodeNodes : List Tree → Except Error Nodes
    | [] => return []
    | tree :: rest => return (← decodeTreeCore tree) :: (← decodeNodes rest)

  def decodeChildren (context key : String) : Members → Except Error (Option (Array Node))
    | [] => return none
    | (name, tree) :: members =>
      if keyMatches name key then decodeChild context key tree
      else decodeChildren context key members

  def decodeChild (context key : String) : Tree → Except Error (Option (Array Node))
    | .array values => return some (← decodeNodes values).toArray
    | .scalar _ | .object _ => throw (.node s!"{context}: {key}: array expected")
end

/- Recursive schema for successful Clang nodes. Header classification is
nonrecursive and inspect the original metadata fields; child derivations
are explicit and never assume success of the opaque imported decodeNode. -/
mutual
  inductive DecodesTree : Tree → Node → Prop where
    | absent {members} : classify members = .ok .absent → DecodesTree (.object members) .absent
    | comment {members json} : classify members = .ok (.comment json) → DecodesTree (.object members) (.comment json)
    | association {members kind selected selectedResult inner} :
        classify members = .ok (.association kind selectedResult) →
        DecodesChildren "inner" members inner → selectedResult = .ok selected →
        DecodesTree (.object members) (.association kind selected inner)
    | node {members header inner filler} :
        classify members = .ok (.node header) →
        DecodesChildren "inner" members inner → DecodesChildren "array_filler" members filler →
        DecodesTree (.object members) (.mk header inner filler)

  inductive DecodesNodes : List Tree → Nodes → Prop where
    | nil : DecodesNodes [] []
    | cons {tree node trees nodes} : DecodesTree tree node → DecodesNodes trees nodes →
        DecodesNodes (tree :: trees) (node :: nodes)

  inductive DecodesChildren : String → Members → Option (Array Node) → Prop where
    | nil {key} : DecodesChildren key [] none
    | skip {key name tree members nodes} : keyMatches name key = false → DecodesChildren key members nodes →
        DecodesChildren key ((name, tree) :: members) nodes
    | found {key name trees members nodes} : keyMatches name key = true → DecodesNodes trees nodes →
        DecodesChildren key ((name, .array trees) :: members) (some nodes.toArray)
end

/-- Validate the full standard bridge exactly once before semantic recursion.
Recursive metadata decoding only inspects header fields. -/
def decodeTree (tree : Tree) : Except Error Node := do
  let some _ := Json.Decode.treeToLean? tree | throw .bridge
  decodeTreeCore tree

/-- The independent recursive schema together with the explicit input policy. -/
def DecodesValue (tree : Tree) (node : Node) : Prop :=
  (∃ json, Json.Decode.treeToLean? tree = some json) ∧ DecodesTree tree node

/-- Complete result policy on standard JSON trees. Success has an independent
recursive schema; semantic diagnostics are the concrete total core's result,
conditional on the shared strict bridge validation. -/
inductive Result : Tree → Except Error Node → Prop where
  | success {tree node} : DecodesValue tree node → Result tree (.ok node)
  | bridge {tree} : Json.Decode.treeToLean? tree = none → Result tree (.error .bridge)
  | semantic {tree json error} : Json.Decode.treeToLean? tree = some json →
      decodeTreeCore tree = .error error → Result tree (.error error)

def decode (json : Json.Ast) : Except Error Node := decodeTree (Json.Tree.ofAst json)
def Decodes : Json.Decode.Schema Node := fun json node => DecodesValue (Json.Tree.ofAst json) node

def decode? (json : Json.Ast) : Option Node := (decode json).toOption

def parse (bytes : Bytes) : Except Error Node := do
  let some json := Json.parse? bytes | throw .syntax
  decode json

def Parses : Silmaril.EncRel Bytes Node := Json.Decode.text Decodes

def ParsesTranslationUnit : Silmaril.EncRel Bytes Node := Parses.restrict IsTranslationUnit

def translationUnit (bytes : Bytes) : Except Error Node := do
  let node ← parse bytes
  if IsTranslationUnit node then return node
  else throw (.root "the document is not a TranslationUnitDecl")

end Silmaril.Compiler.Clang.TotalJson
