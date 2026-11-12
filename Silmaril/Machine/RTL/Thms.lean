module

public import Silmaril.Raw.Machine.RTL.OfLambdaSSA
public import Silmaril.Raw.Machine.RTL.Behaviour
public import Silmaril.Raw.Machine.RTL.BigStep

/-!
# The SSA-form RTL and its lambda-SSA translations

A header over Raw modules: it re-exports the SSA-form RTL, its big-step
semantics, and the translations `toLambdaSSA` (RTL to lambda-SSA, with a
semantic `iff`) and `ofLambdaSSA` (lambda-SSA to RTL), together with their
import cone (machine words and memory, `Lir` syntax, IEEE 754 numerics,
dominance), which live unrefined in `Silmaril.Raw.Machine.RTL`. Lambda-SSA, behaviours and traces come from the
`SSA` and `Semantics` headers.
-/
