module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs

/-!
# Round 7, REH route 2, part (a) at runtime: rule instances

`Round7.NxFlow.flowSound` says that definitions return conforming values (`NxTyped.vtB`). This
header states what route 2 needs on top of it at the level of relation rules, which is where
SpecTec's `Step` is read (`Round6.Reading.DDerivesB`).

**The scope of a rule instance.** `DDerivesB` fires rule `ruleD nm qs op e prems` of a relation
in the scope `VarEnv.empty.bindVals σ`, for an assignment `σ` that `Sim.QuantsOk` types on the
quantifiers `qs`. The assignment may bind other names too, and may bind `_`. Such a scope does
not satisfy `NxFlow.ScopeVT`, which wants every bound name declared. `qScope qs ρ` keeps only
the bindings of `ρ` at quantifier names. The rule is closed over its quantifiers
(`Round7.EraseDer.closedRels_fixed`), so every expression of the rule evaluates alike in `ρ`
and in `qScope qs ρ` (`Sem.evalExp_agreeOn`).

Reading `Step`'s conclusion as a pattern through `NxTyped.patTy` (the relations of
`NxSites.matchedRel`) is not a way to get this scope: the conclusions of the `Step`,
`Step_pure` and `Step_read` rules evaluate their right-hand sides, and `patTy` rejects 83 of
them. The quantifier types are what types the scope.

**The side conditions on rules** (`ruleAux`, checked in the kernel on every rule of every
relation `Step` reaches, `ruleAuxRels`):

* the relation has no parameters;
* no quantifier is named `_`;
* every alternative of the conclusion (`Round6.Reading.conclAlts`) passes the flow check
  (`NxTyped.tyOk`), the side conditions `NxFlow.auxE`, and has no failing comparison site
  (`NxSites.badE`). The flow check and the site check (`NxTyped.flowItems`,
  `NxSites.itemsOk`) read the conclusion only;
* every premise passes the flow check (`NxTyped.premTy`) and `premAuxR`: `NxFlow.auxE` on every
  expression the premise evaluates, distinct domain variables in premise iterations;
* the comparison sites of the rule, under `NxTyped.sigX` (the signature the soundness proof
  uses), are the binding sites of `NxSites.bindSites_fixed` and nothing else
  (`NxSites.ruleSites`);
* for a relation of `NxSites.matchedRel`, the conclusion passes `NxTyped.patTy` at the
  relation's type.

`NxFlow.auxItems` checks the same side conditions on definitions only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxRule

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

/-! ## The scope of a rule instance -/

/-- **The quantifier part of a scope**: the term bindings of `ρ` at quantifier names of `qs`. -/
def qScope (qs : List Param) (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.filter fun p => (Determ.quantNames qs).contains p.1 }

/-! ## The side conditions on rules -/

/-- The context of the side conditions inside a rule: no type or definition parameters. -/
abbrev ctx0 : AuxCtx := ([], [])

/-- **The side conditions on a premise**: `NxFlow.auxE` on every expression it evaluates, and
distinct domain variables in iterations. -/
def premAuxR : Prem → Bool
  | .ifPr e => auxE ctx0 e
  | .letPr e₁ e₂ => auxE ctx0 e₁ && auxE ctx0 e₂
  | .rulePr _ args _ e => typArgsOk ctx0 args && auxA ctx0 args && auxE ctx0 e
  | .elsePr => true
  | .iterPr pr (.mk it ds) =>
    premAuxR pr && nodupB (ds.map domVar) && auxI ctx0 it && auxD ctx0 ds

/-- **One conclusion alternative passes**: the flow check, the side conditions and the site
check. -/
def altOk (S : Sig) (T : TSig) (Γ : List (String × AT)) (e : Exp) : Bool :=
  tyOk S T Γ e && auxE ctx0 e && badE S Γ e == 0

/-- **The side conditions on one rule** of a relation without parameters, with conclusion type
`t`; `matched` says that the relation is also matched by `Sem.derives`. -/
def ruleAux (S : Sig) (T : TSig) (t : AT) (matched : Bool) : Rule → Bool
  | r@(.ruleD _ qs _ e prems) =>
    let Γ := quantsΓ qs
    !(Determ.quantNames qs).contains "_" &&
    (Round6.Reading.conclAlts e).all (altOk S T Γ) &&
    prems.all (fun pr => premTy S T Γ pr && premAuxR pr) &&
    (ruleSites S [] matched r).2 == 0 &&
    (!matched || patTy S T Γ t e)

/-- **The side conditions on every reachable relation of a map**: no parameters, and every rule
passes `ruleAux` under `sigX` and `tsigFixed`. -/
def ruleAuxRels (m : Map RelDef) : Bool :=
  m.all fun p => !reach 0 p.1 ||
    (p.2.1.isEmpty && p.2.2.2.2.all (ruleAux sigX tsigFixed (toAT p.2.2.2.1) (matchedRel p.1)))

/-- `ruleAuxRels` on the rules `k` to `k + c - 1` of each relation, which has at most `112`
rules. The kernel checks the fixed script in sixteen such slices. -/
def ruleAuxRelsAt (m : Map RelDef) (k c : Nat) : Bool :=
  m.all fun p => !reach 0 p.1 ||
    (p.2.1.isEmpty && decide (p.2.2.2.2.length ≤ 112) &&
      ((p.2.2.2.2.drop k).take c).all (ruleAux sigX tsigFixed (toAT p.2.2.2.1) (matchedRel p.1)))

end Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
