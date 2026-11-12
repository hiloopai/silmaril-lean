module

public import Silmaril.Wasm.SpecTec.Institution.Rename.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Rename

/-!
# The SpecTec specification institution with renamings: results

Proofs in `Silmaril.Proofs.Wasm.SpecTec.Institution.Rename`; see `docs/projects/spectec/README.md`.

* `sat_renameS_iff`: `(renameS f φ).Sat alts env D ↔ φ.Sat alts env (renameI f D)`.
* `satisfactionR`: the satisfaction condition along a renaming `σ : SigHom Σ Σ'`.
* `instR alts`: the institution with renamings of relation names; along an inclusion its reduct
  and sentence translation are those of `inst alts` (`Model.reductR_ofLe`, `renameSen_ofLe`).
* `ruleFuns_renameRule`: renaming relation names keeps the functions a rule calls, so the
  function-name restriction of `SSen.InSig` is preserved.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec

/-- info: 'Silmaril.Wasm.SpecTec.Institution.satisfactionR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.satisfactionR

/-- info: 'Silmaril.Wasm.SpecTec.Institution.instR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.instR
