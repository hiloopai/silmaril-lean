module

public import Lean

/-!
# Program provenance metadata

`@[program_provenance "SHA256" "GENERATOR" "VERSION" "COMMAND"]` records
where a declaration's generated data came from. For example, a binary-to-Lean
tool can annotate its embedded ELF bytes with the input digest, the tool's
identity and version, and the command that reproduces the output.

This attribute records **claims supplied by the author or generator**. It does
not read an artifact, recompute its digest, run the command, or certify the
declaration's value or type. Byte extraction and execution theorems are separate
obligations. Digest validation here checks only the lowercase SHA-256 spelling.

Metadata on public declarations survives module imports and is available through
`Provenance.of?`, `Provenance.entries` and `#print_program_provenance declaration`.
-/

public meta section

namespace Silmaril.Verification.Provenance

open Lean

/-- Author-supplied provenance; none of these fields is a checked certificate. -/
structure Record where
  /-- Lowercase hexadecimal SHA-256 claimed for the input artifact. -/
  artifactSha256 : String
  /-- Generator name or other stable identifier. -/
  generator : String
  /-- Generator version, such as a release identifier or source commit. -/
  generatorVersion : String
  /-- Command supplied for reproducing the generated output. -/
  reproductionCommand : String
  deriving Inhabited, Repr, BEq

/-- Check the representation of a SHA-256 digest, without hashing any data. -/
def validSha256 (digest : String) : Bool :=
  digest.length == 64 && digest.all (fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

/-- Attach author-supplied artifact and generator metadata to a declaration. -/
syntax (name := program_provenance)
  "program_provenance" str str str str : attr

initialize programProvenanceAttribute : ParametricAttribute Record ← do
  let ext ← registerParametricAttributeExt (α := Record)
    `Silmaril.Verification.Provenance.programProvenanceAttribute
  registerParametricAttributeForExt {
    name := `program_provenance
    descr := "record artifact digest, generator, version and reproduction command (metadata only)"
    getParam := fun decl stx => do
      if (ParametricAttribute.getParamFromExt? ext false (← getEnv) decl).isSome then
        throwError "program_provenance is already set on `{decl}`"
      let `(attr| program_provenance $digest:str $generator:str $version:str $command:str) := stx
        | throwError "expected `@[program_provenance \"SHA256\" \"GENERATOR\" \"VERSION\" \"COMMAND\"]`"
      let digest := digest.getString
      unless validSha256 digest do
        throwError "program_provenance: SHA-256 must be exactly 64 lowercase hexadecimal characters"
      let generator := generator.getString
      let version := version.getString
      let command := command.getString
      for (field, value) in [("generator", generator), ("generator version", version),
          ("reproduction command", command)] do
        if value.trimAscii.toString.isEmpty then
          throwError "program_provenance: {field} must not be blank"
      return ⟨digest, generator, version, command⟩
  } ext

/-- Retrieve recorded metadata; its presence does not imply verification. -/
def of? (env : Environment) (decl : Name) : Option Record :=
  programProvenanceAttribute.getParam? env decl

/-- Recorded declarations and metadata, including imports, sorted by name. -/
def entries (env : Environment) : Array (Name × Record) := Id.run do
  let ext := programProvenanceAttribute.ext
  let mut out := #[]
  for modIdx in [0:env.header.modules.size] do
    out := out ++ ext.getModuleEntries env modIdx
  for entry in (ext.getState env).2 do
    out := out.push entry
  return out.qsort fun a b => Name.quickLt a.1 b.1

/-- Display recorded metadata for one declaration; this performs no verification. -/
elab "#print_program_provenance " decl:ident : command => do
  let name ← Lean.Elab.Command.liftCoreM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo decl
  let some record := of? (← getEnv) name
    | throwError "no program_provenance metadata is recorded for `{name}`"
  logInfo m!"{name}: author-supplied program provenance (metadata only)\n{repr record}"

end Silmaril.Verification.Provenance
