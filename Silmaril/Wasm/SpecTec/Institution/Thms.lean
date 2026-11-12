module

public import Silmaril.Wasm.SpecTec.Institution.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Basic

/-!
# The institution of SpecTec specifications: results

Namespace `Silmaril.Wasm.SpecTec.Institution`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Basic`; see `docs/projects/spectec/README.md`.

* `satisfaction`: the satisfaction condition along signature inclusions, from the locality of
  rule bodies (`premW_mono`, `ruleBodyA_mono`, `sat_restrict_iff`).
* `inst alts : Silmaril.Logic.Institution.Inst`: the institution of SpecTec specifications at a
  conclusion reading (`decl` for `Sim.DDerives`, `backend` for `Round6.Reading.DDerivesB`).
* `canon_sat`, `canonB_sat`: `DDerives env O` and `DDerivesB env O` satisfy `theoryOf env` at
  every `otherwise` reading `O`.
* `canon_least`, `canonB_least`: at `O = noElse` they are contained in every interpretation that
  satisfies `theoryOf env` with evaluator `env`: the least models. Corollaries
  `dderives_noElse_le`, `dderivesB_noElse_le`.
* `retained_sat_reduct`: versions as partial theory morphisms (the retained rules).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec

/-- info: 'Silmaril.Wasm.SpecTec.Institution.satisfaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.satisfaction

/-- info: 'Silmaril.Wasm.SpecTec.Institution.inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.inst

/-- info: 'Silmaril.Wasm.SpecTec.Institution.canon_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.canon_least

/-- info: 'Silmaril.Wasm.SpecTec.Institution.canonB_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.canonB_least
