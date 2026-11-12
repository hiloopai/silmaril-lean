module

public import Silmaril.Wasm.Tools.Component.Rename.Defs

/-!
# Theorems of `--import-name`

* `renameBytes_nil`: without pairs the component is unchanged.
* `renameAst_nil`: renaming with no pairs is the identity on the component.
* `newName_of_lookup`, `newName_of_not`: an import named `OLD` with a pair `OLD=NEW` is named
  `NEW` (the last pair of that name); any other import keeps its name.
* `renameSection_imports`, `renameSection_other`: only the import sections change; the
  descriptions of the imports are kept (`renameImport_desc`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Rename

open Silmaril.Wasm.Component.Binary (Import)
open Silmaril.Wasm.Component.BinaryP3 (Section Ast)

theorem renameBytes_nil (b : ByteArray) : renameBytes [] b = .ok b := rfl

theorem newName_nil (n : String) : newName [] n = n := rfl

theorem renameImport_nil (i : Import) : renameImport [] i = i := by
  cases i
  rfl

theorem map_renameImport_nil (is : List Import) : is.map (renameImport []) = is := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [List.map_cons, renameImport_nil, ih]

theorem renameSection_nil (s : Section) : renameSection [] s = s := by
  cases s <;> first | rfl | exact congrArg Section.imports (map_renameImport_nil _)

theorem map_renameSection_nil (ss : List Section) : ss.map (renameSection []) = ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => rw [List.map_cons, renameSection_nil, ih]

theorem renameAst_nil (c : Ast) : renameAst [] c = c := by
  cases c with
  | mk ss => exact congrArg Ast.mk (map_renameSection_nil ss)

theorem newName_of_lookup {m : List (String × String)} {n n' : String}
    (h : m.reverse.lookup n = some n') : newName m n = n' := by
  simp [newName, h]

theorem newName_of_not {m : List (String × String)} {n : String}
    (h : m.reverse.lookup n = none) : newName m n = n := by
  simp [newName, h]

theorem renameImport_desc (m : List (String × String)) (i : Import) :
    (renameImport m i).desc = i.desc := rfl

theorem renameImport_form (m : List (String × String)) (i : Import) :
    (renameImport m i).name.form = i.name.form := rfl

theorem renameSection_imports (m : List (String × String)) (is : List Import) :
    renameSection m (.imports is) = .imports (is.map (renameImport m)) := rfl

theorem renameSection_other (m : List (String × String)) (s : Section)
    (h : ∀ is, s ≠ .imports is) : renameSection m s = s := by
  cases s <;> first | rfl | exact absurd rfl (h _)

end Silmaril.Wasm.Tools.Component.Rename
