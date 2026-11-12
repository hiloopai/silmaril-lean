module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HCasts.Defs

/-!
# Round 7, `BD`: `LhsNoAtoms hAtoms` is a `StepInvBH`

* `lhsAtom_of_stepAtB`, `lhsAtom_of_step8B`, `lhsAtom_of_step9B`: under the backend reading,
  rules 8 and 9 of `Step` fire only on left-hand sides ending in `CALL_REF` (every conclusion
  alternative ends in `CALL_REF`, the kernel fact `HStep.step_ctxOkH`).
* `stepInvBH_h`: **`LhsNoAtoms hAtoms` is a `StepInvBH`**. Rules 43 and 23 by round 7's
  `VDecl.lhsAtom_of_read43B` and `VInv.lhsAtom_of_step23B`, the context rules by
  `HStep.lhsNoAtomsH_ctx`, rules 8 and 9 as above.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HCasts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round6.Reading (RuleBodyB)
open Round7.VDecl (lhsAtom altAtomOk)
open Round7.VInv (LhsNoAtoms)
open Round7.HStep (hAtoms)

/-- A rule whose conclusion alternatives all end in `a` fires, under the backend reading, only on
left-hand sides ending in `a`. -/
theorem lhsAtom_of_stepAtB {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {r : Rule} {args : List ArgV} {op' : MixopS} {w : Value} {a : MixopS}
    (hk : altAtomOk r a = true) (hb : RuleBodyB (simEnv B) D els ps args op' r w) :
    lhsAtom w = some a := by
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨e', he', -, ρ₀, σ, -, -, hev, -⟩ := hb
  exact VDecl.lhsAtom_of_eval (VDecl.altAtom hk he') hev

/-- **Rule 8 of `Step` fires, under the backend reading, only on left-hand sides ending in
`CALL_REF`.** -/
theorem lhsAtom_of_step8B {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[8]? = some r) (hb : RuleBodyB (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "CALL_REF" := by
  have hok := HStep.stepCtxOkH_of h
  simp only [HStep.stepCtxOkH, Bool.and_eq_true, hr] at hok
  exact lhsAtom_of_stepAtB hok.1.2 hb

/-- **Rule 9 of `Step` fires, under the backend reading, only on left-hand sides ending in
`CALL_REF`.** -/
theorem lhsAtom_of_step9B {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step" = some (ps, op, t, rules))
    (hr : rules[9]? = some r) (hb : RuleBodyB (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "CALL_REF" := by
  have hok := HStep.stepCtxOkH_of h
  simp only [HStep.stepCtxOkH, Bool.and_eq_true, hr] at hok
  exact lhsAtom_of_stepAtB hok.2 hb

/-- **No memory SIMD instruction and no `CALL_REF` in the left-hand side is a `StepInvBH`.** -/
theorem stepInvBH_h : StepInvBH (LhsNoAtoms hAtoms) where
  inv :=
    { read43 := fun _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb =>
        VInv.lhsAtom_ne_of_noAtoms hw (by decide) (VDecl.lhsAtom_of_read43B hrel hr hb)
      step23 := fun _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb =>
        VInv.lhsAtom_ne_of_noAtoms hw (by decide) (VInv.lhsAtom_of_step23B hrel hr hb)
      ctx := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrel hj hr he₁ hev hv hp hy hw =>
        HStep.lhsNoAtomsH_ctx hrel hj hr he₁ hev hv hp hy hw }
  step8 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb :=
    VInv.lhsAtom_ne_of_noAtoms hw (by decide) (lhsAtom_of_step8B hrel hr hb)
  step9 _ _ _ _ _ _ _ _ _ _ _ hw hrel hr hb :=
    VInv.lhsAtom_ne_of_noAtoms hw (by decide) (lhsAtom_of_step9B hrel hr hb)

end Silmaril.Wasm.SpecTec.Sim.Round7.HCasts
