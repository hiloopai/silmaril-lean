module

public import Silmaril.LogicGraph.Consequence.Matrix.Defs
public meta import Silmaril.LogicGraph.Consequence.Matrix.Defs

/-!
# The logic graph: the coverage matrix as a record

Registers `Silmaril.LogicGraph.Consequence.coverageRows` (defined in a module of its own, so that it
can be evaluated here) as the evidence matrix `logic.consequence.coverage`. Lean checks that every
named declaration exists and records its module. The explorer shows the matrix on
`#/logic-consequence/`.
-/

silmaril consequence_matrix logic.consequence.coverage := Silmaril.LogicGraph.Consequence.coverageRows
