module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxTyp.Rule

/-!
# Round 8, REH route 2: typing goes to the erased side without a swap set (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp`; see `docs/projects/spectec/README.md`. Definitions are in `Round8/NxTyp/Defs.lean`; the proofs are unrefined, in
`Silmaril/Raw/…/Round8/NxTyp/`, and the kernel checks in `Silmaril/Proofs/…/Round8/NxTyp/`.

* **`typFwdN_utf8Env : TypFwdN (utf8Env B)`**, for every choice of primitives `B`: in a rule of a
  relation `Step` reaches, quantifiers that `Sim.QuantsOk` types in the instance's scope are typed
  in the erased scope. This is round 7's `EraseDer.typFwd_utf8Env` at rule instances without the
  swap set and without `QInj`.
* The proof does not use the evaluator-level erasure copy (`NxErase.nAt`, `NxClause.defsE_all`).
  The expressions inside the reachable types read only variables of export-free type, whose values
  are their own erasures, so they evaluate alike on both sides (`Sem.evalExp_agreeOn`). The
  induction (`tfAt`) runs over the seven members of the typing block; below a type instance both
  sides share the instance's scope, and a field or case with premises carries an export-free value.
* **`nTypMap_fixed`, `nRelQuants_fixed`** (kernel, three slices each): every type over `tyB` and
  every quantifier type of every reachable rule passes the check `nTy`.
* `hasTyp_fwd`: the general form, on scopes that agree on the variables a checked type reads.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.typFwdN_utf8Env' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms typFwdN_utf8Env

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.nTypMap_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms nTypMap_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp.nRelQuants_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms nRelQuants_fixed

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
