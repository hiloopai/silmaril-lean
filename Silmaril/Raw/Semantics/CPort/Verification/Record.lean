module

public import Lean

/-! # Discoverable software-verification records

`@[verification_record]` registers an ordinary `VerificationRecord` definition.
The tag survives imports and supports architecture-neutral discovery. Every
reference is an explicit Lean declaration name; the description and trust fields
are supplied by the author. Neither the tag nor a claim's role proves a link
between a theorem, a specification, an artifact, or a particular block.

Registration checks the record's data shape. Consumers must independently resolve
the references, require theorem declarations for claims and discharge references,
and obtain theorem types and transitive axioms from the Lean environment. Artifact
provenance remains the separate `program_provenance` tag on `artifact`. No command
metadata is executed by this module. Duplicate record IDs are checked by consumers
over the selected collection, rather than by the import-local registry.
-/

@[expose] public section

namespace Silmaril.Verification

open Lean

inductive ClaimScope where
  | function
  /-- Stable emitted block identifier, for example `block_0`. -/
  | block (id : String)
  deriving Inhabited, Repr, BEq

/-- An author-stated assumption. A discharge reference is descriptive metadata;
consumers check that it names a theorem but must not infer its meaning from this field. -/
structure TrustAssumption where
  id : String
  description : String
  dischargedBy : Option Name := none
  deriving Inhabited, Repr, BEq

/-- A theorem selected by its real declaration name, with author-supplied context. -/
structure Claim where
  theoremName : Name
  role : String
  scope : ClaimScope := .function
  description : String := ""
  /-- IDs in the enclosing record's assumption list. -/
  assumptions : List String := []
  deriving Inhabited, Repr, BEq

/-- Author-written reading guide. These descriptions are not formal statements;
the referenced theorem types remain the source of the precise claims. -/
structure Explanation where
  summary : String := ""
  proofMethod : String := ""
  preconditions : List String := []
  guarantees : List String := []
  deriving Inhabited, Repr, BEq

/-- References to source data, specifications and checked theorem declarations.
All optional references are architecture-neutral; consumers inspect their actual types. -/
structure VerificationRecord where
  id : String
  title : String
  architecture : String
  explanation : Explanation := {}
  /-- Declaration carrying the separate program-provenance metadata, when present. -/
  artifact : Option Name := none
  code : Option Name := none
  program : Option Name := none
  blocks : Option Name := none
  listBlocks : Option Name := none
  graph : Option Name := none
  /-- A literal assembly definition, optionally checked against `program`. -/
  assemblySource : Option Name := none
  specification : Option Name := none
  entry : Option Name := none
  post : Option Name := none
  claims : List Claim := []
  assumptions : List TrustAssumption := []
  deriving Inhabited, Repr, BEq

end Silmaril.Verification

public meta section

namespace Silmaril.Verification

open Lean

/-- Pure shape validation, shared by registration and record consumers.
This does not resolve any referenced declaration or establish semantic linkage. -/
def VerificationRecord.validate (record : VerificationRecord) : Except String Unit := do
  for (field, value) in [("id", record.id), ("title", record.title),
      ("architecture", record.architecture)] do
    if value.trimAscii.isEmpty then
      throw s!"{field} must not be blank"
  if record.claims.isEmpty then
    throw "claims must not be empty"
  for (field, reference) in [("artifact", record.artifact), ("code", record.code),
      ("program", record.program), ("blocks", record.blocks), ("listBlocks", record.listBlocks),
      ("graph", record.graph), ("assemblySource", record.assemblySource), ("specification", record.specification),
      ("entry", record.entry), ("post", record.post)] do
    if reference == some .anonymous then
      throw s!"{field} must name a declaration"
  for description in record.explanation.preconditions ++ record.explanation.guarantees do
    if description.trimAscii.isEmpty then
      throw "explanation entries must not be blank"
  let mut assumptionIds : List String := []
  for assumption in record.assumptions do
    if assumption.id.trimAscii.isEmpty then
      throw "assumption id must not be blank"
    if assumption.description.trimAscii.isEmpty then
      throw s!"assumption {assumption.id}: description must not be blank"
    if assumptionIds.contains assumption.id then
      throw s!"duplicate assumption id: {assumption.id}"
    if assumption.dischargedBy == some .anonymous then
      throw s!"assumption {assumption.id}: dischargedBy must name a theorem"
    assumptionIds := assumption.id :: assumptionIds
  for claim in record.claims do
    if claim.theoremName.isAnonymous then
      throw "claim theoremName must name a theorem"
    if claim.role.trimAscii.isEmpty then
      throw "claim role must not be blank"
    if let .block id := claim.scope then
      if id.trimAscii.isEmpty then
        throw "claim block id must not be blank"
    let mut referencedIds : List String := []
    for id in claim.assumptions do
      unless assumptionIds.contains id do
        throw s!"claim {claim.theoremName}: unknown assumption id: {id}"
      if referencedIds.contains id then
        throw s!"claim {claim.theoremName}: duplicate assumption id: {id}"
      referencedIds := id :: referencedIds

end Silmaril.Verification

namespace Silmaril.Verification.Records

open Lean

syntax (name := verification_record) "verification_record" : attr

private unsafe def validateDeclaration (decl : Name) : AttrM Unit := do
  let .defnInfo info ← getConstInfo decl
    | throwError "verification_record requires a definition of VerificationRecord"
  unless info.levelParams.isEmpty && info.type == mkConst ``VerificationRecord &&
      info.safety == .safe do
    throwError "verification_record requires a closed, safe definition of VerificationRecord"
  -- The type and safety were checked above. Ordinary record data is deliberately
  -- evaluated without requiring the declaration itself to be a `meta` definition.
  let record ← evalConst (checkMeta := false) VerificationRecord decl
  match record.validate with
  | .error message => throwError "verification_record: {message}"
  | .ok () => pure ()

unsafe initialize verificationRecordAttribute : ParametricAttribute Unit ← do
  let ext ← registerParametricAttributeExt (α := Unit)
    `Silmaril.Verification.Records.verificationRecordAttribute
  registerParametricAttributeForExt {
    name := `verification_record
    descr := "register descriptive software-verification data (not a proof certificate)"
    applicationTime := .afterCompilation
    getParam := fun decl stx => do
      let `(attr| verification_record) := stx
        | throwError "verification_record does not accept arguments"
      if (ParametricAttribute.getParamFromExt? ext false (← getEnv) decl).isSome then
        throwError "verification_record is already set on `{decl}`"
      validateDeclaration decl
  } ext

/-- Membership is discovery metadata, not a theorem-validity predicate. -/
def contains (env : Environment) (decl : Name) : Bool :=
  (verificationRecordAttribute.getParam? env decl).isSome

/-- Registered record constants, including imports, sorted by declaration name. -/
def entries (env : Environment) : Array Name := Id.run do
  let ext := verificationRecordAttribute.ext
  let mut out := #[]
  for moduleIndex in [0:env.header.modules.size] do
    out := out ++ (ext.getModuleEntries env moduleIndex).map Prod.fst
  for entry in (ext.getState env).2 do
    out := out.push entry.1
  return out.qsort Name.quickLt

end Silmaril.Verification.Records
