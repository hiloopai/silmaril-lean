module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HStep.Thms

/-!
# Round 7, `BD`: the backend whole step across `$hostcall`, and the cast leaf at `BD`
(definitions)

`Round7.HStep` moved the declarative whole step between builtins that agree off `$vbytes_` and
`$hostcall` under `HStep.StepInvH`. The cast leaf (`RMD.OpenRMRestD.castsFwd`/`castsBwd`) is
read at round 6's **backend** reading (`Round6.Int.backend`, `Reading.SStepB`). This header
states the invariant for that reading.

* `StepInvBH Q`: round 7's `VInv.StepInvB Q` (rules 43 and 23 silent under `RuleBodyB`, `Q`
  through the context rules' conclusion alternatives) and rules 8 and 9 silent under `RuleBodyB`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCasts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- **A value invariant under which the backend whole step moves across `HAgree.AgreeOff`.** -/
structure StepInvBH (Q : Value → Prop) : Prop where
  /-- Rules 43 and 23 silent, and `Q` through the context rules. -/
  inv : VInv.StepInvB Q
  /-- Rule 8 of `Step` derives no `Q` value under the backend reading. -/
  step8 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → rules[8]? = some r →
    ¬ Round6.Reading.RuleBodyB (simEnv B) D els ps args op' r w
  /-- Rule 9 of `Step` derives no `Q` value under the backend reading. -/
  step9 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → rules[9]? = some r →
    ¬ Round6.Reading.RuleBodyB (simEnv B) D els ps args op' r w

end Silmaril.Wasm.SpecTec.Sim.Round7.HCasts
