module

public import Silmaril.Wasm.SpecTec.Institution.Perm.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermBackend

/-!
# The SpecTec specification institution with renamings of identifiers: results

Proofs in `Silmaril.Proofs.Wasm.SpecTec.Institution.Perm*`; see `docs/projects/spectec/README.md`
("Pass 3, grammar-comorph").

* `eqvAt`: the evaluator's 29 mutually recursive functions commute with renaming every
  identifier by a permutation `π` fixing `"_"` (`PermEval`); `typEqvAt`: so do the seven of the
  type-membership test (`PermType`). Hence `evalExp_rn`, `hasTyp_rn`.
* `sat_rnS_iff`: satisfaction of sentences is equivariant at every equivariant reading
  (`PermSat`); `decl_equivariant`.
* `ruleFuns_rnRule`: free identifiers commute with renaming (`PermFree`).
* `SigHomP`: signature morphisms renaming type, function and relation names (and variables);
  `rnSen`, `reductP`; the satisfaction condition `satisfactionP`; the institution `instP`,
  `instPDecl` (`PermInst`), `instPBackend` (`backend_equivariant`, `PermBackend`). Along inclusions it is `Institution.inst` (`reductP_ofLe`,
  `rnSen_ofLe`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Perm.eqvAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Perm.eqvAt

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Perm.sat_rnS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Perm.sat_rnS_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Perm.satisfactionP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Perm.satisfactionP

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Perm.instPDecl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Perm.instPDecl

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Perm.instPBackend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Perm.instPBackend
