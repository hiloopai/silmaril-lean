module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Script
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.BindFwd
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Sites.Thms

/-!
# Round 8, REH route 2: the clause half of the erasure copy (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.NxClause`; see `docs/projects/spectec/README.md`.
Definitions are in `Round7/NxClause/Defs.lean`; the proofs are unrefined, in
`Silmaril/Raw/…/Round7/NxClause/`, and the kernel check in `Silmaril/Proofs/…/Round7/NxClause/`.

* **`clauseErase : NxErase.Task.clauseErase`.** In `utf8Env B`, with primitives that conform
  (`NxSound.BuiltinsVT`) and commute with erasure on `EraseAll.gdE` (`EraseAll.BIErase QT`),
  clause bodies commute with export erasure at every call the flow check passes, in a scope
  without definition and type bindings.
* The proof, in order:
  * `simpAt`: variables, literals, `unE`, `cvtE` and iterations of them commute with erasure
    with no hypothesis; so do the lengths `patLen` reads (`patLen_erase`);
  * `linAt`, `matchArgs_erase`: argument patterns that pass the pattern check `linE` match alike
    before and after erasure. No type is read; a comparison happens only at a variable already
    bound, and the check makes one side export-free;
  * `callE_clause`: inside a clause, calls are answered by `DefsE` below the fuel (as
    `NxFlow.callH_clause` answers conformance);
  * `prems_erase`: premises `if e`, `otherwise` and `(if e)^iter` commute with erasure, by
    round 7's expression half (`NxErase.nAt`);
  * `clause_erase`, `tryClauses_erase`, `defsE_all`: one clause, the clause list, every fuel;
  * `envFactsE_utf8Env`: the static facts at `utf8Env B`.
* **`yItems_fixed`** (kernel, twenty slices): every reachable clause passes the pattern and
  premise check, and every definition of `gdE` has a parameter entry in `tsigFixed`.
* **`ifPr_fwd`, `ifPr_fwd_BI`** (part (b) forward): every top-level `if` premise of a rule
  instance that holds, holds on the erased scope, the six binding sites included. At a binding
  site each operand commutes with erasure separately, and equality and membership survive any
  function. Part (b) needs recomputation only backward.
* **`defsE_BI`, `erase_ifPr_BI`**: the results at round 4's primitives with no hypothesis, using
  round 3's `EraseAll.biErase_BI'` at the swap set of every value (`biErase_QT_BI`) and round 7's
  `NxPrims.builtinsVT_BI`.
* **`erase_ifPr_rule`**: round 7's `NxErase.erase_ifPr_of_task` without the task. In a rule
  instance of a reachable relation whose quantifiers `Sim.QuantsOk` types, every top-level `if`
  condition other than the six binding sites commutes with erasure, given conforming primitives
  that commute with erasure on `gdE`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound

/-- **`Round7.NxErase.Task.clauseErase` holds.** -/
theorem clauseErase : NxErase.Task.clauseErase := clauseErase'

/-- **Round 7's `erase_ifPr_of_task`, unconditionally**: every top-level `if` condition of a rule
instance other than the six binding sites commutes with erasure. -/
theorem erase_ifPr_rule {B : Builtins} (hB : BuiltinsVT sigX tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B))
    {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : reach 0 x = true) (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (utf8Env B) (VarEnv.empty.bindVals σ) qs) {c : Exp}
    (hpr : Prem.ifPr c ∈ prems) (hbs : bindSite sigX (quantsΓ qs) (.ifPr c) = false)
    (hxc : EraseAll.xExp EraseAll.grE EraseAll.gdE c = true) (n : Nat) :
    evalExp n (utf8Env B) (Erase.eraseScope (VarEnv.empty.bindVals σ)) c =
      Swap.eraseV <$> evalExp n (utf8Env B) (VarEnv.empty.bindVals σ) c :=
  NxErase.erase_ifPr_of_task clauseErase hB H hx hrel hrule hq hpr hbs hxc n

/-! ## At round 4's primitives, with no hypothesis -/

section BI
variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- `$hostcall` is not a name of `EraseAll.gdE`. -/
theorem gdE_hostcall : EraseAll.gdE "hostcall" = false := by decide

/-- **Round 4's primitives commute with erasure on `gdE` with every value in the swap set.** This
is round 3's `EraseAll.biErase_BI'`, which holds at every swap set, at `QT`. -/
theorem biErase_QT_BI : EraseAll.BIErase NxErase.QT EraseAll.gdE (NxPrims.envBI P hn host) :=
  EraseAll.biErase_BI' P hn host fun x hx h => by subst h; rw [gdE_hostcall] at hx; cases hx

/-- **Clause bodies commute with erasure at every fuel**, in the round-7 environment at round 4's
primitives, with no hypothesis. -/
theorem defsE_BI : ∀ n, DefsE (NxPrims.envBI P hn host) n :=
  defsE_all (NxFlow.sigFacts NxFlow.sigsAux_fixed) (envFactsE_utf8Env _) (biErase_QT_BI P hn host)
    (NxFlow.flowSound _ (NxPrims.builtinsVT_BI P hn host))

/-- **`erase_ifPr_rule` at round 4's primitives, with no hypothesis on them.** -/
theorem erase_ifPr_BI {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : reach 0 x = true)
    (hrel : (NxPrims.envBI P hn host).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) qs) {c : Exp}
    (hpr : Prem.ifPr c ∈ prems) (hbs : bindSite sigX (quantsΓ qs) (.ifPr c) = false)
    (hxc : EraseAll.xExp EraseAll.grE EraseAll.gdE c = true) (n : Nat) :
    evalExp n (NxPrims.envBI P hn host) (Erase.eraseScope (VarEnv.empty.bindVals σ)) c =
      Swap.eraseV <$> evalExp n (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) c :=
  erase_ifPr_rule (NxPrims.builtinsVT_BI P hn host) (biErase_QT_BI P hn host) hx hrel hrule hq
    hpr hbs hxc n

/-- **Part (b) forward, at round 4's primitives**: every top-level `if` premise of a rule
instance that holds, holds on the erased scope, the six binding sites included. -/
theorem ifPr_fwd_BI {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    (hx : reach 0 x = true)
    (hrel : (NxPrims.envBI P hn host).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) {σ : List (IL.Id × Value)}
    (hq : Sim.QuantsOk (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) qs) {c : Exp}
    (hpr : Prem.ifPr c ∈ prems) (hxc : EraseAll.xExp EraseAll.grE EraseAll.gdE c = true)
    (h : EvalExp (NxPrims.envBI P hn host) (VarEnv.empty.bindVals σ) c (.bool true)) :
    EvalExp (NxPrims.envBI P hn host) (Erase.eraseScope (VarEnv.empty.bindVals σ)) c
      (.bool true) :=
  ifPr_fwd (NxFlow.flowSound _ (NxPrims.builtinsVT_BI P hn host)) (biErase_QT_BI P hn host) hx
    hrel hrule hq
    (fun k => clauseErase _ (NxPrims.builtinsVT_BI P hn host) (biErase_QT_BI P hn host) _ k rfl rfl)
    hpr hxc h

end BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.ifPr_fwd_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ifPr_fwd_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.defsE_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms defsE_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.erase_ifPr_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms erase_ifPr_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.clauseErase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms clauseErase

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.yItems_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms yItems_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.NxClause.erase_ifPr_rule' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms erase_ifPr_rule

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
