module

public import Silmaril.Cerberus.Frontend.Typing.Definitions.Defs

/-! # The Cerberus C frontend: typing Ail

`typecheck` is what `cerb-lean parse --level tail` runs after `Frontend.desugar`, and what
`cerb-lean typecheck` runs on an oracle Ail document: a port of Cerberus's
`GenTyping.annotate_program` (`frontend/model/ail/genTyping.lem:2412-2452`) at `b3e11ea3`.
It annotates every expression with its `GenTypeCategory`, inserts the lvalue conversions
and decays, and checks the constraints of ISO C11 §6.5-6.9; it returns typed Ail or the
`Errors.error` that Cerberus reports, at the stage `typing` (some at a `$loc_regions`
location).

The expression port and a minimal program/statement path are implemented in `Typing/`.
Unported constructors and diagnostics return explicit typing rejects.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- Type untyped Ail, or reject it at the stage `typing`. -/
def typecheck (prog : Ail.Program Unit) : Except Ail.Reject Ail.TypedProgram :=
  ((Typing.annotateProgram prog).run []).map Prod.fst

end Silmaril.Cerberus.Frontend
