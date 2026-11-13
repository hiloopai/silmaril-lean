module

public import Silmaril.Wasm.Wac.WacTests.Defs

/-!
# WAC: wac's test cases, checked

Each statement is checked by `decide +kernel` on the elaborator (no native evaluation).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WacTests

open Silmaril.Wasm.Wac Silmaril.Wasm.Wac.Syntax

/-- The error of a failed elaboration. -/
def errOf : Except ElabError CGraph → Option ElabError
  | .error e => some e
  | .ok _ => none

/-- The merged exports of `foo:bar/types`. -/
def typesMerged : Kind := .inst none [("w", .type (.resource "w")), ("x", .type (.value xRef)),
  ("y", .func ⟨false, [("x", xRef)], none⟩), ("z", .type (.resource "z"))]

/-- **`semver-highest-version-retained`**: one implicit import `foo:bar/types@0.2.1`
with the union of the exports; each instantiation passes it under its own import
name (as in wac's `encoded.wat`). -/
theorem semver_highest_retained : (elabDoc semverEnv higherDoc).toOption = some { nodes := [
    ⟨.inst "test:higher" [("foo:bar/types@0.2.1", typesHigh)] [("foo:bar/types@0.2.1", 2)], .inst none []⟩,
    ⟨.inst "test:lower" [("foo:bar/types@0.2.0", typesLow)] [("foo:bar/types@0.2.0", 2)], .inst none []⟩,
    ⟨.implicit "foo:bar/types@0.2.1", typesMerged⟩] } := by
  decide +kernel

/-- Lower version first: the merged import is renamed to the higher version. -/
theorem semver_renamed : (elabDoc semverEnv lowerFirstDoc).toOption.map CGraph.imports =
    some [("foo:bar/types@0.2.1", .inst none [("x", .type (.value xRef)),
      ("y", .func ⟨false, [("x", xRef)], none⟩), ("z", .type (.resource "z")), ("w", .type (.resource "w"))])] := by
  decide +kernel

/-- An implicit import compatible with an explicit one is rejected (wac would merge them). -/
theorem semver_explicit_rejected :
    errOf (elabDoc semverEnv explicitSemverDoc) = some (.implicitImportConflict "foo:bar/types@0.2.0") := by
  decide +kernel

/-! ## Declarations -/

/-- The kind of the type declaration `n`. -/
def kindNamed (g : CGraph) (n : String) : Option Kind := (g.nodes.find? (·.op == .defn n)).map (·.kind)

/-- The import and export names of a world type. -/
def worldNames : Kind → Option (List String × List String)
  | .type (.comp _ is es) => some (is.map (·.1), es.map (·.1))
  | _ => none

/-- The kind of the declaration `n` of a document. -/
def declOf (env : PkgEnv) (d : Document) (n : String) : Option Kind :=
  (elabDoc env d).toOption.bind (kindNamed · n)

/-- The world names of the declaration `n` of a document. -/
def worldOf (env : PkgEnv) (d : Document) (n : String) : Option (List String × List String) :=
  (declOf env d n).bind worldNames

/-- **`resource.wac`**: `x2` is an alias of the resource `x`, so `x2` and `borrow<x2>`
are `own<x>` and `borrow<x>`. -/
theorem resource_alias : declOf [] resourceDoc "foo" = some (.type (.inst (some "test:comp/foo") [
    ("x", .type (.resource "x")), ("x2", .type (.value (.own ⟨.local, "x"⟩))),
    ("f3", .func ⟨false, [("x", .own ⟨.local, "x"⟩), ("x2", .own ⟨.local, "x"⟩),
      ("x3", .borrow ⟨.local, "x"⟩), ("x4", .borrow ⟨.local, "x"⟩)], none⟩)])) := by
  decide +kernel

/-- The type `r` of the interface `ns:name/i`. -/
def usedR (ns name i : String) : Kind :=
  .type (.value (.ref ⟨.iface ⟨{ ns, name }, i⟩, "r"⟩))

/-- **`types.wac`, `use` in an interface**: `use i.{r}` and `use i.{r as z}` export
aliases of `test:comp/i`'s `r`. -/
theorem types_use_iface :
    declOf typesEnv typesDoc "i2" = some (.type (.inst (some "test:comp/i2")
      [("r", usedR "test" "comp" "i"), ("z", usedR "test" "comp" "i")])) := by
  decide +kernel

/-- **Top-level aliases are expanded**: `type t2 = x` with `type x = u32` is `u32`. -/
theorem types_root_alias : declOf typesEnv typesDoc "t2" = some (.type (.value (.prim .u32))) := by
  decide +kernel

/-- **`types.wac`, `use` in a world**: the used interface `foo:bar/i` is imported
implicitly, in front; `test:comp/i` is imported explicitly. -/
theorem types_world_use : worldOf typesEnv typesDoc "w1" =
    some (["foo:bar/i", "r", "a", "test:comp/i"], ["d", "test:comp/i2"]) := by
  decide +kernel

/-- **`types.wac`, `include`**: the items of `w2` first, then those of `w1` and of
`foo:bar/baz`. -/
theorem types_include : worldOf typesEnv typesDoc "w2" =
    some (["res", "[constructor]res", "foo:bar/i", "r", "a", "test:comp/i", "b"], ["d", "test:comp/i2", "e"]) := by
  decide +kernel

/-- **`package-use-item`**: `use` of package interfaces in an interface and a world. -/
theorem package_use_item :
    (declOf pkgItemsEnv pkgUseDoc "i").map (fun k => match k with
      | .type (.inst _ es) => es.map (·.1) | _ => []) = some ["a", "b", "c"] ∧
    worldOf pkgItemsEnv pkgUseDoc "w" = some (["foo:bar/qux", "x", "y", "z"], []) := by
  decide +kernel

/-- **`package-world-include`** and **`package-world-item`**. -/
theorem package_world_items :
    worldOf pkgItemsEnv pkgIncludeDoc "w" = some (["f"], []) ∧
    worldOf pkgItemsEnv pkgWorldItemDoc "w" = some (["foo:bar/baz"], ["bar:baz/qux"]) := by
  decide +kernel

/-- **The `use`, `include` and world-item failures of wac's `fail/` tests**, with wac's
errors. -/
theorem decl_failures :
    errOf (elabDoc [] dupIfaceExportDoc) = some (.duplicateInterfaceExport "x") ∧
    errOf (elabDoc [] dupIncludeNameDoc) = some (.duplicateWorldIncludeName "a") ∧
    errOf (elabDoc [] dupUseIfaceDoc) = some (.useConflict "x") ∧
    errOf (elabDoc [] dupUseWorldDoc) = some (.useConflict "x") ∧
    errOf (elabDoc [] dupWorldExportDoc) = some (.duplicateWorldItem "x") ∧
    errOf (elabDoc [] dupWorldImportDoc) = some (.duplicateWorldItem "x") ∧
    errOf (elabDoc [] invalidUseAliasDoc) = some (.useConflict "b") ∧
    errOf (elabDoc [] invalidUseDoc) = some (.notInterface "x") ∧
    errOf (elabDoc [] invalidIncludeDoc) = some (.notWorld "x") ∧
    errOf (elabDoc [] missingUseTypeDoc) = some (.undefinedInterfaceType "x" "test:comp/a") ∧
    errOf (elabDoc [] missingIncludeNameDoc) = some (.missingWorldInclude "a") ∧
    errOf (elabDoc [] includeConflictDoc) = some (.worldIncludeConflict "a") ∧
    errOf (elabDoc [] includeWithConflictDoc) = some (.worldIncludeConflict "x") ∧
    errOf (elabDoc [] redefinedDoc) = some (.declarationConflict "x") := by
  decide +kernel

/-! ## Alias expansion in type checking -/

/-- **Aliases are expanded in argument checking**: on the document side always; on the
package side with `elabDocA` (plain `elabDoc` compares `ref t` with `u32`). -/
theorem alias_expanded :
    errOf (elabDoc aliasEnv aliasDocSide) = none ∧
    errOf (elabDoc aliasEnv aliasPkgSide) = some (.mismatchedInstantiationArg "x") ∧
    errOf (elabDocA aliasEnv aliasPkgSide) = none := by
  decide +kernel

/-! ## `targets` -/

/-- **`targets-world`** and **`targets-empty-world`**: worlds of the document. -/
theorem targets_local_ok :
    errOf (elabDoc targetsEnv targetsWorldDoc) = none ∧ errOf (elabDoc targetsEnv targetsEmptyDoc) = none := by
  decide +kernel

/-- **The `fail/target*` tests**, with wac's errors. -/
theorem targets_failures :
    errOf (elabDoc targetsEnv targetExportMismatchDoc) = some (.targetMismatch "foo") ∧
    errOf (elabDoc targetsEnv targetExtraneousDoc) = some (.importNotInTarget "bar") ∧
    errOf (elabDoc targetsEnv targetResourceDoc) = some (.targetMismatch "foo") ∧
    errOf (elabDoc targetsEnv targetKindDoc) = some (.targetMismatch "foo") ∧
    errOf (elabDoc targetsEnv targetParamNameDoc) = some (.targetMismatch "foo") ∧
    errOf (elabDoc targetsEnv targetParamTypeDoc) = some (.targetMismatch "foo") ∧
    errOf (elabDoc targetsEnv targetMethodDoc) = some (.targetMismatch "foo") ∧
    errOf (elabDoc targetsEnv targetNotWorldDoc) = some (.notWorld "test:comp/foo") ∧
    errOf (elabDoc targetsEnv unknownTargetsDoc) = some (.undefinedName "foo") ∧
    errOf (elabDoc [] unknownTargetPkgDoc) = some (.unknownPackage "foo:bar") ∧
    errOf (elabDoc missingExportEnv missingExportDoc) = some (.missingTargetExport "hello") := by
  decide +kernel

/-- **`fail/targets-world-use`**: the interface the world `use`s is imported implicitly
by the target world, and the composition's import of it (exporting `other-resource`)
does not match (wac: "instance has unexpected resource export `other-resource`"). -/
theorem targets_world_use :
    errOf (elabDoc worldUseEnv worldUseDoc) = some (.targetMismatch "test:comp/indirect-dependency") := by
  decide +kernel

/-- **`fail/targets-interface-use`, a known difference**: wac rejects it because the
variant `my-variant` has one case in the package and two in the document. Variants are
compared by reference here (`docs/projects/wasm-components.md`), so the composition is accepted. -/
theorem targets_interface_use_accepted : errOf (elabDoc ifaceUseEnv ifaceUseDoc) = none := by
  decide +kernel

end Silmaril.Wasm.Wac.WacTests
