module

public import Silmaril.Proofs.Wasm.Examples.WatSpecSt.Acc

/-!
# Annotated WAT over the store: results

`wat_spec_st!` functions that write globals, verified by `wat_vc`: the G accessors `rget`,
`rset`, `fset6` of the x86 simulator (`rget_valid`, `rset_valid`, `fset6_valid`, every profile
and host relation) and the read-back `rset_gv`. Proofs in
`Silmaril.Proofs.Wasm.Examples.WatSpecSt.Acc`.
-/

/-- info: 'Silmaril.Wasm.Examples.WatSpecSt.rset_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.Examples.WatSpecSt.rset_valid
