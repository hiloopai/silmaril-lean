module

public import Silmaril.Wasm.Wac.Names.Thms
public import Silmaril.Wasm.Wac.Types.Thms
public import Silmaril.Wasm.Wac.Infer.Thms
public import Silmaril.Wasm.Wac.Implicit.Thms
public import Silmaril.Wasm.Wac.Elab.Thms
public import Silmaril.Wasm.Wac.ElabTyped.Thms
public import Silmaril.Wasm.Wac.ElabComplete.Thms
public import Silmaril.Wasm.Wac.ElabExample.Thms
public import Silmaril.Wasm.Wac.WitKind.Thms
public import Silmaril.Wasm.Wac.Alias.Thms
public import Silmaril.Wasm.Wac.WitDeclSpec.Thms
public import Silmaril.Wasm.Wac.WacTests.Thms

/-!
# WAC: the surface language and its elaboration

The umbrella of the surface track of the WAC formalization (`docs/projects/wasm-components.md`):

* `Wac/Syntax`: the WAC AST (package declaration with `targets`, imports, WIT type
  statements, `let`, exports with `as` and spread; `new` with inferred, named, spread
  and implicit arguments, access, named access, parentheses);
* `Wac/Names`, `Wac/Infer`: extern names and the name-inference rules, as functions
  and relations (`inferArg_iff`, …);
* `Wac/Types`: item kinds over WIT types and WIT subtyping (`sub_iff`, a preorder),
  merging of implicit imports (`merge_wit`, `merge_not_lower`);
* `Wac/CGraph`, `Wac/Elab`: the elaborator into composition graphs; `Wac/Implicit`:
  implicit imports (`resolve_complete`, `resolve_typed`);
* `Wac/ElabSpec`: elaboration as relations; `elabDoc_iff` (sound and complete),
  `elabDoc_typed` (fully explicit and well typed);
* `Wac/WitKind`: kinds of resolved WIT packages (`elabDoc_typed_wit`);
* `Wac/ElabExample`: the examples of `LANGUAGE.md`.
-/
