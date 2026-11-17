module

public import Silmaril.Cerberus.TV.Profile.Defs

/-!
# Stages, provenance and evidence of a C translation-validation pipeline

A C program passes through **representations** (`Stage`): its source text, the output of the
preprocessor, Clang's JSON AST dump, Cerberus's Cabs, Ail and typed Ail, Cerberus Core, and an
object file. Each representation of one program is an `Artifact`: its stage, the SHA-256 of its
exact bytes and the run that produced it (`Producer`: the tool, its version, its arguments, the
target triple). An artifact without a producer is input data (the source).

Two representations are related only by an explicit **edge** (`Edge`): which relation is claimed
(`Relation`), and what the claim rests on (`Evidence`). The evidence kinds are not ranked into
each other:

| `Evidence` | what it is |
|---|---|
| `kernel decl` | a kernel-checked theorem `decl` whose statement *is* the edge (checked by `sil project check` against the edge's problem instance) |
| `compiled decl` | the result of running the Lean function `decl` compiled (trusts the Lean compiler and runtime, not only the kernel) |
| `oracle what` | agreement with another implementation on this input (for example the Cerberus OCaml executable): testing, not proof |
| `external tool` | output of an external tool taken as given (a Clang AST dump) |
| `missing` | no evidence: the edge is a gap of the pipeline, shown as such |

So "source → Clang AST → typed Ail → Core" is three edges, each with its own evidence. Clang's JSON
AST is **untrusted frontend output**: the edge from the source to it is `external`, and the edge
from it to typed Ail is the Lean importer `cfront` (a `compiled` run of a fail-closed decoder),
not a semantic theorem. A pipeline never fabricates a stage: a representation that was not
produced is absent, and an edge with no evidence is `missing`.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

/-- Representations of a C program. -/
inductive Stage where
  | source
  | preprocessed
  | clangAst
  | cabs
  | ail
  | typedAil
  | core
  | object
  deriving DecidableEq, Repr

/-- A run that produced an artifact. -/
structure Producer where
  tool : String
  version : String
  args : List String := []
  target : String
  deriving DecidableEq, Repr

/-- One representation of one program. -/
structure Artifact where
  stage : Stage
  /-- Lower-case hex SHA-256 of the exact bytes. -/
  sha256 : String
  bytes : Nat
  producer : Option Producer := none
  /-- SHA-256 of the artifacts it was produced from. -/
  inputs : List String := []
  deriving DecidableEq, Repr

/-- The relation an edge claims. -/
inductive Relation where
  /-- The target representation is what the producer emitted for the source representation. -/
  | produces
  /-- The target is the Lean elaborator's (or importer's) result on the source. -/
  | elaborates
  /-- Whole-program refinement (`TV.Refines`). -/
  | refines
  /-- Whole-program equivalence (`TV.Equivalent`). -/
  | equivalent
  deriving DecidableEq, Repr

/-- What an edge rests on (module docstring). -/
inductive Evidence where
  | kernel (decl : String)
  | compiled (decl : String)
  | oracle (what : String)
  | external (tool : String)
  | missing
  deriving DecidableEq, Repr

/-- An edge between two artifacts (by SHA-256). -/
structure Edge where
  source : String
  target : String
  relation : Relation
  evidence : Evidence
  /-- The profile the relation is stated under (`Profile.name`), when it depends on one. -/
  profile : Option String := none
  deriving DecidableEq, Repr

end Silmaril.Cerberus.TV
