module

public import Silmaril.Wasm.Wac.ElabExample.Defs

/-!
# WAC elaboration: the examples of `LANGUAGE.md`, checked

Each statement is checked by `decide +kernel` on the elaborator (no native evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.ElabExample

open Silmaril.Wasm.Wac Silmaril.Wasm.Wac.Syntax

/-- The arguments of the instantiations of a graph. -/
def instArgs (g : CGraph) : List (String × List (String × Nat)) :=
  g.nodes.filterMap fun nd => match nd.op with
    | .inst p _ args => some (p, args)
    | _ => none

/-- The error of a failed elaboration. -/
def errOf : Except ElabError CGraph → Option ElabError
  | .error e => some e
  | .ok _ => none

/-- The imports and exports of a graph, by name. -/
def externNames (g : CGraph) : List String × List String := (g.imports.map (·.1), g.exports.map (·.1))

/-- **Implicit imports merge** (`LANGUAGE.md`): one import `i` exporting `f` and `g`,
shared by both instantiations. -/
theorem implicit_merged : (elabDoc implicitEnv implicitDoc).toOption = some { nodes := [
    ⟨.inst "example:my-component" [("i", .inst none [("f", fUnit)])] [("i", 2)], .inst none []⟩,
    ⟨.inst "example:my-other-component" [("i", .inst none [("g", fStr)])] [("i", 2)], .inst none []⟩,
    ⟨.implicit "i", .inst none [("f", fUnit), ("g", fStr)]⟩] } := by
  decide +kernel

/-- **The four inferred-argument rules**: `baz` by its interface path, `c-fn` by its
import name `c`, `input-stream` (an alias of export `wasi:io/input-stream`) by its
alias name, `d` by its local name; `export run` is named `run` by its access. -/
theorem infer_names : ((elabDoc inferEnv inferDoc).toOption.map fun g => (instArgs g, externNames g)) =
    some ([("my:stream", []),
      ("a:b", [("foo:bar/baz", 0), ("c", 1), ("wasi:io/input-stream", 3), ("d", 4)])],
      (["foo:bar/baz", "c", "d"], ["run"])) := by
  decide +kernel

/-- **Named arguments**: `"c": …` verbatim, `input-stream: …` by the unique import path
ending with `input-stream`. -/
theorem named_names : ((elabDoc inferEnv namedDoc).toOption.map instArgs) =
    some [("my:stream", []),
      ("a:b", [("foo:bar/baz", 0), ("c", 1), ("wasi:io/input-stream", 4), ("d", 3)])] := by
  decide +kernel

/-- **Spread arguments** match the semver-compatible export `wasi:io/streams@0.2.3` to
the import `wasi:io/streams@0.2.0`. -/
theorem spread_semver : ((elabDoc spreadEnv spreadDoc).toOption.map instArgs) =
    some [("x:src", []), ("x:dst", [("wasi:io/streams@0.2.0", 1)])] := by
  decide +kernel

/-- **Spread exports** skip `run`, exported before from `b:c` (node 2 is the alias of
`b:c`'s `run`). -/
theorem export_spread : ((elabDoc spreadEnv exportSpreadDoc).toOption.map fun g => g.exports) =
    some [("run", 2), ("setup", 3)] := by
  decide +kernel

/-! ## Errors -/

theorem fill_not_last : errOf (elabDoc inferEnv fillNotLastDoc) = some .fillArgumentNotLast := by decide +kernel
theorem duplicate_arg : errOf (elabDoc inferEnv duplicateArgDoc) = some (.duplicateInstantiationArg "d") := by
  decide +kernel
theorem missing_arg : errOf (elabDoc inferEnv missingArgDoc) = some (.missingInstantiationArg "a:b" "foo:bar/baz") := by
  decide +kernel
theorem mismatch : errOf (elabDoc inferEnv mismatchDoc) = some (.mismatchedInstantiationArg "d") := by decide +kernel
theorem implicit_conflict : errOf (elabDoc implicitEnv conflictDoc) = some (.implicitImportConflict "i") := by
  decide +kernel
theorem merge_conflict : errOf (elabDoc mergeEnv mergeConflictDoc) = some (.importTypeMergeConflict "f") := by
  decide +kernel
theorem export_requires_as : errOf (elabDoc spreadEnv exportRequiresAsDoc) = some .exportRequiresAs := by
  decide +kernel

/-! ## Targets -/

/-- The composition fits `wasi:cli/command`: it imports `wasi:io/streams@0.2.0` and
exports `run`. -/
theorem targets_ok : ((elabDoc targetsEnv targetsDoc).toOption.map externNames) =
    some (["wasi:io/streams@0.2.0"], ["run"]) := by
  decide +kernel

theorem targets_missing : errOf (elabDoc targetsEnv targetsMissingDoc) = some (.missingTargetExport "run") := by
  decide +kernel

end Silmaril.Wasm.Wac.ElabExample
