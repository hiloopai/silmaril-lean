module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxDer.Defs

/-!
# Round 8, REH: SpecTec's `otherwise` goes to the erased side

`Round8.NxDer.derFwdN` moves a derivation of a checked relation (`EraseAll.grE`) across export
erasure, given that `otherwise` read on the original side is read on the erased side (`hO`). With
SpecTec's reading (`Round6.Reading.otherwiseB`) that hypothesis says that no earlier rule fires on
the erased left-hand side when none fires on the original one: the backward direction.

This topic discharges `hO` without the backward direction. In the fixed script, every rule of a
`grE` relation with an `otherwise` premise (seven rules, all of `Step_pure`) has a conclusion
`lhs ~> rhs` whose left-hand side reads only quantifiers of export-free type. When such a rule
fires, its left-hand side is export-free, so erasure leaves it unchanged, and `otherwiseB` reads
the erased value exactly as the original one (it depends on the value only through its left-hand
side, `Sim.SameLhs`).

* `elseIn`: a premise is `otherwise`, possibly under iterations.
* `lhsNx qs e'`: `e'` is a pair `(l, r)` and `l` reads only quantifiers of export-free type
  (`Round8.NxTyp.nxNames`).
* `elseLhs m`: every rule of a `grE` relation of `m` with an `otherwise` premise has `lhsNx` at
  every conclusion alternative. The kernel checks it on the fixed script
  (`Round8.NxElse.elseLhs_fixed`).
* `Fired env x args i v`: rule `i` of `x` has an `otherwise` premise, and its conclusion evaluates
  to `v` in a typed instance. `elseF env O` is `O` together with `grE x` and `Fired`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-- A premise is `otherwise`, possibly under iterations. -/
def elseIn : Prem → Bool
  | .elsePr => true
  | .iterPr pr _ => elseIn pr
  | _ => false

/-- **A conclusion is a pair whose left-hand side reads only quantifiers of export-free type.** -/
def lhsNx (qs : List Param) : Exp → Bool
  | .tupE [l, _] => EraseDer.varsIn (NxTyp.nxNames qs) (freeExp l)
  | _ => false

/-- **Every `otherwise` rule of a `grE` relation has an export-free left-hand side**, at every
conclusion alternative. -/
def elseLhs (m : Map RelDef) : Bool :=
  m.all fun p => !EraseAll.grE p.1 || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ e prems => !prems.any elseIn || (Round6.Reading.conclAlts e).all (lhsNx qs)

/-- **Rule `i` of `x` has an `otherwise` premise and its conclusion evaluates to `v`** in an
instance whose quantifiers are typed. -/
def Fired (env : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) : Prop :=
  ∃ (ps : List Param) (op : MixopS) (t : Typ) (rules : List Rule) (nm : IL.Id) (qs : List Param)
    (e : Exp) (prems : List Prem) (e' : Exp) (ρ₀ : VarEnv) (σ : List (IL.Id × Value)),
    env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some (.ruleD nm qs op e prems) ∧
    prems.any elseIn = true ∧ e' ∈ Round6.Reading.conclAlts e ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧ QuantsOk env (ρ₀.bindVals σ) qs ∧
    EvalExp env (ρ₀.bindVals σ) e' v

/-- `O`, at a `grE` relation whose rule fired with an `otherwise` premise. -/
def elseF (env : Env) (O : ElseI) : ElseI :=
  fun x args i v => O x args i v ∧ EraseAll.grE x = true ∧ Fired env x args i v

end Silmaril.Wasm.SpecTec.Sim.Round8.NxElse
