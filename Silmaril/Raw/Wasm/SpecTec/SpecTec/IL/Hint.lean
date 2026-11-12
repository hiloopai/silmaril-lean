module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast

/-!
# SpecTec hints

A transcription of `hintdef'` and `hint` from `spectec/src/il/ast.ml:164-172`
at `608711107b7f1edb13efd57b7d79b49477462d36`.

Hints are the `hint` annotations an elaborated SpecTec script carries for the
benefit of the Latex, prose and interpreter backends; they have no semantic
content.  `Silmaril.SpecTec.IL.Def` deliberately has *no* `hint` constructor,
even though OCaml's `def'` has `HintD of hintdef`
(`spectec/src/il/ast.ml:138`), because the S-expression backend erases hint
definitions completely: `spectec/src/backend-ast/print.ml:218-219` renders
`HintD _` as the empty atom `Atom ""`, and
`Backend_ast.Print.script` (`spectec/src/backend-ast/print.ml:225`) then drops
every `Atom ""` from the stream with
`List.filter ((<>) (Atom "")) (List.map def ds)`.  So a `--ast` file contains
neither the hints nor any trace that they were there, and a `Def` with a
`hint` constructor could never be decoded.

The declarations below exist only so that the shape of `ast.ml` is recorded
in full.  They are not reachable from `Silmaril.SpecTec.IL.Def` and nothing
in the decoder produces them.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

/-- The payload of a hint, `El.Ast.exp` (`spectec/src/il/ast.ml:172`), which
is an *external* language expression and is not transcribed.

Nothing can constrain this type.  A hint's payload reaches the S-expression
stream only through `HintD`, and `spectec/src/backend-ast/print.ml:218-219`
renders a `HintD` as the empty atom, which
`Backend_ast.Print.script` (`spectec/src/backend-ast/print.ml:225`) filters
out of the stream; so no `--ast` file mentions a hint expression, and no
`--ast` file could distinguish one choice of this type from another.  It is
therefore the single-element type, with `erased` standing for the discarded
`El.Ast.exp`. -/
inductive ElExp where
  /-- The erased `El.Ast.exp` payload of a hint. -/
  | erased
  deriving DecidableEq, Repr, Inhabited

/-- `hint = {hintid : id; hintexp : El.Ast.exp}`
(`spectec/src/il/ast.ml:172`), with the payload erased to `ElExp`. -/
structure Hint where
  /-- `hintid : id`, the name of the hint. -/
  hintid : Id
  /-- `hintexp : El.Ast.exp`, the hint's payload; see `ElExp`. -/
  hintexp : ElExp
  deriving DecidableEq, Repr, Inhabited

/-- `hintdef'`, the hint definitions (`spectec/src/il/ast.ml:165-170`).

Each constructor attaches a list of hints to a previously declared entity. -/
inductive HintDef where
  /-- `TypH of id * hint list` (`spectec/src/il/ast.ml:166`): hints for a
  type definition. -/
  | typH (x : Id) (hints : List Hint)
  /-- `RelH of id * hint list` (`spectec/src/il/ast.ml:167`): hints for a
  relation. -/
  | relH (x : Id) (hints : List Hint)
  /-- `DecH of id * hint list` (`spectec/src/il/ast.ml:168`): hints for a
  function definition. -/
  | decH (x : Id) (hints : List Hint)
  /-- `GramH of id * hint list` (`spectec/src/il/ast.ml:169`): hints for a
  grammar. -/
  | gramH (x : Id) (hints : List Hint)
  /-- `RuleH of id * id * hint list` (`spectec/src/il/ast.ml:170`): hints for
  the rule named by the second identifier within the relation named by the
  first. -/
  | ruleH (x : Id) (y : Id) (hints : List Hint)
  deriving DecidableEq, Repr, Inhabited

end Silmaril.SpecTec.IL
