module

public import Silmaril.Wasm.Spec.Temporal.Defs
public import Silmaril.Proofs.Wasm.Spec.Temporal.Basic
public import Silmaril.Proofs.Wasm.Spec.Temporal.Max

@[expose] public section

/-!
# Temporal logics: results

Proofs in `Silmaril.Proofs.Wasm.Spec.Temporal.{Basic,Max}`.

* `everyPos_iff_get`, `everyPos_iff_mem`, `everyPos_prefixList_iff`: positions of traces and
  words.
* `LTL.holdsFin_alw`, `LTL.holdsInf_alw`, `LTL.holdsFin_alw_atom`, `LTL.holdsInf_alw_atom`: the
  meaning of `□`.
* `exists_maximal_or_limit`: in a good trace set every trace extends to a maximal finite trace
  or lies on an infinite limit (dependent choice).
* `ltlFin_alw_atom_iff`: `□ A` in finite-trace LTL is the action invariant `A`;
  `ltlMax_alw_atom_iff`: on good sets, so is `□ A` over maximal behaviours; `ltlInf_of_act`: the
  action invariant implies `□ A` on every infinite limit (the converse fails for trace sets
  with maximal finite traces).
-/
