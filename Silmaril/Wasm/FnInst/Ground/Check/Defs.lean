module

public import Silmaril.Logic.Inst.Builders.Defs
public import Silmaril.Wasm.Auto.Front.Defs
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-! # wasm-check's statements as sentences of a function institution

`wasm-check` (`Silmaril.Wasm.Auto.Front`) decides three questions about export `j` of
two modules: refinement `ModRefines R P impl spec j`, equivalence `ModEquiv R P m₁ m₂ j`
(silmaril-lean's behaviour sets, no host) and meeting a reference function. `checkInst` is
the function institution whose focus is one export:

* signatures: the export index `j`, as a discrete category (the focus does not move);
* sentences (`CSen`): `m ⊑ m'` (refinement), `m ≐ m'` (equivalence) and conjunctions, where
  `m`, `m'` are whole modules, the candidate "bodies" of the focused export;
* models: a numerical profile and the relation between behaviours (`Rel.eq` or `Rel.trap`);
* satisfaction: `ModRefines` and `ModEquiv` at the model's profile and relation.

The checker's verdicts are then statements about satisfaction
(`Silmaril.Wasm.FnInst.Ground.Check.Thms`): `proved` is validity of `m ≐ m'` (every model of
the relation), `refuted` is non-satisfaction at the reference profile.
-/

namespace Silmaril.Wasm.FnInst.Ground.Check

open CategoryTheory Silmaril.Inst Silmaril.Wasm.Auto.Front
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)

/-- Sentences about the focused export of candidate modules. -/
inductive CSen where
  /-- `m ⊑ m'`: the export of `m` refines that of `m'`. -/
  | le (m m' : Module)
  /-- `m ≐ m'`: the exports are equivalent. -/
  | eqv (m m' : Module)
  /-- Conjunction. -/
  | and (φ ψ : CSen)

/-- Satisfaction at export `j`, profile `P`, relation `R`. -/
def CSen.Holds (j : ℕ) (P : Profile) (R : Rel) : CSen → Prop
  | .le m m' => ModRefines R.toProp P m m' j
  | .eqv m m' => ModEquiv R.toProp P m m' j
  | .and φ ψ => φ.Holds j P R ∧ ψ.Holds j P R

/-- The plain presentation: export indices as a discrete category of signatures. -/
def checkPlain : Plain.{0, 0, 0, 0} (Discrete ℕ) where
  Sen _ := CSen
  map _ φ := φ
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  Mod _ := Profile × Rel
  reduct _ M := M
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat {S} M φ := φ.Holds S.as M.1 M.2
  sat_map {S S'} σ M φ := by
    obtain rfl : S = S' := Discrete.ext (Discrete.eq_of_hom σ)
    exact Iff.rfl

/-- **The function institution of wasm-check**, focused on one export. -/
abbrev checkInst : Institution₀ := checkPlain.toInst

end Silmaril.Wasm.FnInst.Ground.Check
