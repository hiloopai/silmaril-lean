module

public import Silmaril.Wasm.Spec.Joint.Defs

@[expose] public section

/-!
# Joint institutions: results

All in `Silmaril.Wasm.Spec.Joint.Defs` (short proofs over `Silmaril.Wasm.Spec.Joint.Base.Thms`):

* `push_sat_iff`: the satisfaction condition of a change of base;
* `pushCoHom L' S α β hτ : Inst.CoHom (inst (L'.pull τ α β) S) (inst L' (S.push τ α β))`, the
  comorphism of a change of base along an injective type map; `pushCoHom_modelExpansive`
  (`pushModel_surjective`), hence borrowing `push_entails_iff`; `models_push_iff`;
* joint models: `sumInlCoHom`, `sumInrCoHom` and `sum_entails_iff` (a sentence follows in the
  institution of joint models iff it follows for each kind of program).
-/
