module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxRule.Eok
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims.Thms

/-!
# Round 7, REH route 2, part (a) at runtime: rule instances (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxRule`; see `docs/projects/spectec/README.md`. Definitions are in `Round7/NxRule/Defs.lean`; the proofs are unrefined, in
`Silmaril/Raw/…/Round7/NxRule/`, and the kernel checks in `Silmaril/Proofs/…/Round7/NxRule/`.

* `ruleAuxRels_fixed` (kernel, sixteen slices): every rule of every relation `Step` reaches passes
  the side conditions `ruleAux`.
* **Declarative rule instances** (`Round6.Reading.DDerivesB`, where `Step` is read): in
  `utf8Env B` with definitions conforming at every fuel, for a rule of a reachable relation whose
  quantifiers `Sim.QuantsOk` types in the scope `VarEnv.empty.bindVals σ`:
  * `scopeVT_qScope`, `agreeOn_qScope`: the quantifier part of the scope conforms, and the rule's
    expressions evaluate alike in the scope and in its quantifier part (the rule is closed,
    `EraseDer.closedRels_fixed`);
  * `eOk_alt`, `eOk_ifPr`, `eOk_rulePr`: every conclusion alternative, every top-level `if`
    condition and the asserted instance of every top-level relation premise conform
    (`NxFlow.EOk`); the instance conforms to the named relation's type;
  * **`nxB_site`**: at every top-level equality, inequality or membership premise that is not
    one of the six binding sites of `NxSites.bindSites_fixed`, one operand's value is
    export-free.
* **Rules matched by `Sem.derives`** (relations of `NxSites.matchedRel`, which definitions call
  through relation premises): `scope_match`, `scope_prems`: matching the conclusion against a
  conforming value gives a conforming scope, and the premises keep it so.
* `nxB_site_BI` etc.: the same at round 4's primitives (`NxPrims.envBI`), with no hypothesis.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxRule

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB)

/-- **Part (a) at a top-level comparison premise, at round 4's primitives.** -/
theorem nxB_site_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : HostSemantics H) {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
    {prems : List Prem} (hx : reach 0 x = true)
    (hrel : (NxPrims.envBI P hn host).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) qs)
    {c e₁ e₂ : Exp} (hpr : Prem.ifPr c ∈ prems)
    (hc : (∃ o ty, (o = CmpOp.eqOp ∨ o = CmpOp.neOp) ∧ c = .cmpE o ty e₁ e₂) ∨ c = .memE e₁ e₂)
    (hb : bindSite sigX (quantsΓ qs) (.ifPr c) = false) {v₁ v₂ : Value}
    (hv₁ : EvalExp (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) e₁ v₁)
    (hv₂ : EvalExp (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) e₂ v₂) :
    nxB v₁ = true ∨ nxB v₂ = true :=
  nxB_site (NxPrims.defsVT_BI P hn host) hx hrel hrule hq hpr hc hb hv₁ hv₂

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.ruleAuxRels_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ruleAuxRels_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.nxB_site_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms nxB_site_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.eOk_rulePr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms eOk_rulePr

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.scope_prems' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms scope_prems

end Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
