module

public import Silmaril.Wasm.Wac.Valid.Defs
public import Silmaril.Wasm.Wac.WacTests.Defs
public import Silmaril.Wasm.Wac.Bridge.Compose.Defs

/-!
# WAC validation on wac's failure tests

`decide +kernel` checks of `Valid.elabDocV` on documents transcribed from wac's
resolution failure tests (wac `5a7480c`, `crates/wac-parser/tests/resolution/fail`)
that `elabDoc` accepts: one per kind of validation, with the error wac reports, and
`targets-interface-use` (`targets_interface_use_accepted` of
`Silmaril.Wasm.Wac.WacTests.Thms` records that `elabDoc` accepts it). The definition
table of each document is `Bridge.docNom`; package tables are written by hand from the
`.wat` dependencies. `semver_ok` checks that validation keeps an accepted composition.
The tool runs the same checks on all 26 documents (`tests/wasm-wac/compose.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.ValidTests

open Silmaril.Wasm.Wac Silmaril.Wasm.Wac.Syntax Silmaril.Wasm.Wac.WacTests Silmaril.Wasm.Wac.Valid
open Silmaril.Wasm.Wit.Binary (Ty TyRef Owner)

/-- The validation error of a result, if any. -/
def vErrOf : Except VElabError CGraph → Option VError
  | .error (.valid e) => some e
  | _ => none

/-- Whether a result is a graph. -/
def okOf : Except VElabError CGraph → Bool
  | .ok _ => true
  | .error _ => false

/-- Elaborate with the document's own definitions and package tables `pkgs`. -/
def run (env : PkgEnv) (pkgs : List (String × Bridge.NomTable)) (d : Document) :
    Except VElabError CGraph :=
  elabDocV { doc := Bridge.docNom d, pkgs } env d

/-- A document of the package `test:comp`. -/
def doc (stmts : List Stmt) (targets : Option PkgPath := none) : Document :=
  { pkg := ⟨"test:comp", none⟩, targets, stmts }

/-- `fail/invalid-alias`: `interface a {} type x = a;` -/
theorem invalid_alias :
    vErrOf (run [] [] (doc [.type (.iface { name := "a", items := [] }),
      .type (.type (tyI "x" (.alias (.named "a"))))])) = some (.invalidAlias "a") := by
  decide +kernel

/-- `fail/invalid-borrow`: `type x = u32; type y = borrow<x>;` -/
theorem invalid_borrow :
    vErrOf (run [] [] (doc [.type (.type (tyI "x" (.alias .u32))),
      .type (.type (tyI "y" (.alias (.borrow "x"))))])) = some (.notResourceType "x") := by
  decide +kernel

/-- `fail/duplicate-record-field`. -/
theorem duplicate_record_field :
    vErrOf (run [] [] (doc [.type (.type (tyI "x" (.alias .string))),
      .type (.type (tyI "r" (.record [{ name := "a", ty := .s8 }, { name := "b", ty := .u8 },
        { name := "c", ty := .named "x" }, { name := "b", ty := .string }])))])) =
      some (.duplicateField "r" "b") := by
  decide +kernel

/-- `fail/duplicate-resource-method`: a method and a static function `x`. -/
theorem duplicate_resource_method :
    vErrOf (run [] [] (doc [.type (.world { name := "foo", items := [.type (tyI "x" (.resource [
      { kind := .method "x", func := {} }, { kind := .static "x", func := {} }]))] })])) =
      some (.duplicateMethod "x" "x") := by
  decide +kernel

/-- `fail/borrow-in-func-result`: through the alias `a`. -/
theorem borrow_in_func_result :
    vErrOf (run [] [] (doc [.type (.iface { name := "foo", items := [
      .type (tyI "x" (.resource [])), .type (tyI "a" (.alias (.borrow "x"))),
      fnI "f" [] (some (.result (some (.named "a")) none))] })])) = some .borrowInResult := by
  decide +kernel

/-- `fail/export-invalid-name`. -/
theorem export_invalid_name :
    vErrOf (run [] [] (doc [.import { id := "f", ty := .func {} },
      .export (.ident "f") (.rename "INVALID!")])) = some (.invalidExportName "INVALID!") := by
  decide +kernel

/-- `fail/export-url-name`: an extern name, but not one an export may have. -/
theorem export_url_name :
    vErrOf (run [] [] (doc [.import { id := "f", ty := .func {} },
      .export (.ident "f") (.rename "url=<https://example.com/foo>")])) =
      some (.invalidExportName "url=<https://example.com/foo>") := by
  decide +kernel

/-- `fail/mismatched-enum-cases/foo`: `foo:bar` imports `x` with `enum e { a, b, c }`. -/
def enumEnv : PkgEnv := [("foo:bar", { imports := [("x", .inst none [("e", .type (.value (.ref ⟨.local, "e"⟩)))])] })]

/-- `fail/mismatched-enum-cases`: the document's `e` has the cases `a, c, b`. -/
theorem mismatched_enum_cases :
    vErrOf (run enumEnv [("foo:bar", [("e", .enum ["a", "b", "c"])])]
      (doc [.import { id := "x", ty := .iface [.type (tyI "e" (.enum [{ name := "a" }, { name := "c" }, { name := "b" }]))] },
        .let "i" (.new ⟨"foo:bar", none⟩ [.inferred "x"])])) = some (.mismatchedArg "foo:bar" "x") := by
  decide +kernel

/-- The same with equal cases is accepted. -/
theorem matched_enum_cases :
    okOf (run enumEnv [("foo:bar", [("e", .enum ["a", "b", "c"])])]
      (doc [.import { id := "x", ty := .iface [.type (tyI "e" (.enum [{ name := "a" }, { name := "b" }, { name := "c" }]))] },
        .let "i" (.new ⟨"foo:bar", none⟩ [.inferred "x"])])) = true := by
  decide +kernel

/-- **`fail/targets-interface-use`**: the package's `my-variant` has one case, the
document's two; wac rejects the target, and so does validation (structurally), where
`elabDoc` alone accepts it. -/
theorem targets_interface_use_valid :
    vErrOf (run ifaceUseEnv [("foo:bar", [("my-variant", .variant [("foo", none)])])] ifaceUseDoc) =
      some (.targetMismatch "test:comp/indirect-dependency") := by
  decide +kernel

/-- Validation keeps the composition of `semver-highest-version-retained`. -/
theorem semver_ok : okOf (run semverEnv [] higherDoc) = true := by
  decide +kernel

end Silmaril.Wasm.Wac.ValidTests
