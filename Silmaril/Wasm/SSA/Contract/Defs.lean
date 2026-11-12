module

public import Silmaril.Wasm.SSA.Dialect.Defs
public import Silmaril.Compile.PassAPI.Category

/-!
# The semantic domain shared by the fragment and the SSA dialect

Both languages denote a function from argument lists to the set of call
outcomes of terminating runs (`FOut`: a return value or a trap). The
replacement preorder `behDomain.Rel src tgt` says that **every terminating
outcome of the source is an outcome of the target**, for every argument
list. Both semantics are deterministic (`Thms`), so a target related to a
terminating source has exactly the source's outcome on that input.

This relation by itself says nothing about inputs on which the source
diverges or is stuck (ill-typed). The translations and passes of this
development are proved to be equivalences on terminating outcomes
(`compileFunc_iff`, `ssaPipeline_iff`, `decompileFunc_iff`,
`optimize?_equiv`), which do transfer divergence and stuckness.

`fragIR` and `ssaIR` are the two IRs over this domain in silmaril's pass
category (`Silmaril.Compile.PassAPI.IR`), with trivial invariants.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Compile.PassAPI

/-- The semantic carrier: terminating outcomes per argument list. -/
abbrev Beh := List WVal → Set FOut

/-- Preservation of terminating outcomes. -/
def behDomain : Domain Beh where
  Rel a b := ∀ args o, o ∈ a args → o ∈ b args
  refl _ _ _ h := h
  trans h₁ h₂ args o h := h₂ args o (h₁ args o h)

/-- The fragment as an IR. -/
def fragIR : IR behDomain where
  Prog := FragFunc
  den f args := {o | f.Run args o}
  Inv _ := True

/-- The SSA dialect as an IR. -/
def ssaIR : IR behDomain where
  Prog := SFunc
  den f args := {o | f.Run args o}
  Inv _ := True

end Silmaril.Wasm.SSA
