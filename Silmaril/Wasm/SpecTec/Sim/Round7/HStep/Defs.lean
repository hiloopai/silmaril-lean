module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Thms

/-!
# Round 7, `BD`: the whole step across `$hostcall` (definitions)

`Round7.HAgree` moves single rules between builtins that agree off `$vbytes_` and `$hostcall`
(`HAgree.AgreeOff`), for every rule of `Step` outside `HAgree.stepBad = [1, 2, 3, 4, 5, 8, 9, 23]`.
`Round7.VDecl` moved the whole step across `withVBytes` under a value invariant (`VDecl.StepInv`)
that keeps rules 43 and 23 silent and passes through the context rules 1–5. This header states the
same for `HAgree.AgreeOff`, where rules 8 and 9 (`call_ref` into a host function, the only rules
calling `$hostcall`) must be kept silent too.

* `ctxPremOkH`, `stepCtxOkH`: `VDecl.ctxPremOk`/`stepCtxOk` with `HAgree.rgB` (`$hostcall`
  excluded), and rules 8 and 9 ending in `CALL_REF` on every conclusion alternative. Checked by the
  kernel (`HStep.step_ctxOkH`).
* `StepInvH Q`: `VDecl.StepInv Q` (rules 43 and 23 silent at `Q` values, `Q` passes through the
  context rules) and rules 8 and 9 silent at `Q` values.
* `hAtoms`: the four memory SIMD atoms and `CALL_REF`. `LhsNoAtoms hAtoms` is the concrete
  invariant: no memory SIMD instruction and no `call_ref` instruction or administrative
  `CALL_REF` in the left-hand side, at any depth (code and store function bodies).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evExp)
open Round7.VDecl (altAtomOk)

/-- `VDecl.ctxPremOk` with `HAgree.rgB`. -/
def ctxPremOkH : Prem → Bool
  | .rulePr y args op e =>
      ((y == "Step" || y == "Step_read") && HAgree.rgB (Round7.Script.evArgs args ++ evExp e)) ||
        HAgree.rgB (Round7.Script.evPrem (.rulePr y args op e))
  | pr => HAgree.rgB (Round7.Script.evPrem pr)

/-- **The premises of `Step` rules 1–5 pass `ctxPremOkH`**, rule 23 ends in `VSTORE`, and rules 8
and 9 end in `CALL_REF`, on every conclusion alternative. -/
def stepCtxOkH (rules : List Rule) : Bool :=
  [1, 2, 3, 4, 5].all (fun j => match (rules[j]? : Option Rule) with
    | some (.ruleD _ _ _ _ prems) => prems.all ctxPremOkH
    | none => false) &&
  (match rules[23]? with
    | some r => altAtomOk r "VSTORE"
    | none => false) &&
  (match rules[8]? with
    | some r => altAtomOk r "CALL_REF"
    | none => false) &&
  match rules[9]? with
  | some r => altAtomOk r "CALL_REF"
  | none => false

/-- **A value invariant under which the whole step moves across `HAgree.AgreeOff`.** -/
structure StepInvH (Q : Value → Prop) : Prop where
  /-- Rules 43 and 23 silent, and `Q` through the context rules. -/
  inv : VDecl.StepInv Q
  /-- Rule 8 of `Step` derives no `Q` value. -/
  step8 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → rules[8]? = some r →
    ¬ RuleBody (simEnv B) D els ps args op' r w
  /-- Rule 9 of `Step` derives no `Q` value. -/
  step9 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → rules[9]? = some r →
    ¬ RuleBody (simEnv B) D els ps args op' r w

/-- The memory SIMD atoms and `CALL_REF`. -/
def hAtoms : List MixopS := ["VLOAD", "VLOAD_LANE", "VSTORE", "VSTORE_LANE", "CALL_REF"]

end Silmaril.Wasm.SpecTec.Sim.Round7.HStep
