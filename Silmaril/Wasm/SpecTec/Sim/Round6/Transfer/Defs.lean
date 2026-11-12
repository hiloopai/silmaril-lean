module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track transfer: definitions

Track transfer proves the transfer lemma `Round6.Target.Transfer` at the backend reading
`Round6.Int.backend` (`docs/projects/spectec/README.md`). Away from cast redexes the
two readings of SpecTec's `Step` must agree; the proof goes by recursion on the code through
`Step`'s rules 1–5, each of which has one relational premise (`Step_read` or `Step`) followed by
premises that consult no relation. This header names what that recursion consults:

* `TailFree rest`: the premises after a rule's leading one consult no relation and have no
  `otherwise`.
* `Inst env D els r v w`: `w` is an instance of the leading premise of rule `r` at the conclusion
  value `v` (a well-typed assignment evaluates the conclusion to `v`, the leading premise's
  argument to `w`, and the other premises hold under `D`).
* `plainExceptB S K rules`: every rule of `rules` outside the indices `K` is plain for `S`
  (`Round6.Reading.plainRuleB`); a kernel check over the pinned script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The premises after the leading one consult no relation and have no `otherwise`. -/
def TailFree (rest : List Prem) : Prop :=
  ∀ pr ∈ rest, Reading.premRels pr = [] ∧ Reading.noElsePr pr = true

/-- **The instances of a rule's leading premise.** For a rule `qs ⊢ e` whose first premise is
`x(pe)`: `w` is the value `pe` takes under a well-typed assignment at which `e` evaluates to `v`
and the remaining premises hold under `D`. -/
def Inst (env : Env) (D : Interp) (els : Prop) (r : Rule) (v w : Value) : Prop :=
  match r with
  | .ruleD _ qs _ e (.rulePr _ _ _ pe :: rest) => ∃ σ : List (IL.Id × Value),
      QuantsOk env (VarEnv.empty.bindVals σ) qs ∧ EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      EvalExp env (VarEnv.empty.bindVals σ) pe w ∧
      ∀ pr ∈ rest, PremW env D els (VarEnv.empty.bindVals σ) pr
  | _ => False

/-- Every rule of a list is plain for `S`, except those at the indices `K`. -/
def plainExceptB (S : List IL.Id) (K : List Nat) (rules : List Rule) : Bool :=
  rules.zipIdx.all fun p => K.contains p.2 || Reading.plainRuleB S p.1

end Silmaril.Wasm.SpecTec.Sim.Round6.Transfer
