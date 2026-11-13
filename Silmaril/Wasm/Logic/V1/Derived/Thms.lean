module

public import Silmaril.Proofs.Wasm.Logic.V1.Derived

/-!
# Derived Wasm Logic rules

The forms of the rules a proof uses (`Triple.conseq`, `Triple.cons`, `Triple.seq3`,
`Triple.falseLabels`, `Triple.frameStraight`, and the per-instruction rules on a
non-empty stack and heap `Triple.constOn` … `Triple.selectOn`), derived from the
primitive rules of `Silmaril.Wasm.Logic.V1.Judgement.Defs`.
-/