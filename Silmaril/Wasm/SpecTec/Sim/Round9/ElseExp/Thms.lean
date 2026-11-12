module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseExp.Left

/-!
# Round 9, RE: `otherwise` pairs whose earlier rule has an `Expand` premise (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp`; see `docs/projects/spectec/README.md`. Definitions are in `Round9/ElseExp/Defs.lean`, the kernel check in
`Silmaril/Proofs/…/Round9/ElseExp/Check`, and the proofs, unrefined, in
`Silmaril/Raw/…/Round9/ElseExp/{Core,Reflect,Pairs}`.

* **`expPairs_fixed`** (kernel): at `(101, 100)`, `(102, 100)`, `(102, 101)` and `(92, 91)` the
  `otherwise` rule has `ElseBwd.lhsRule` and the earlier rule passes `simpleRuleR`: its premises
  are `if`s, `otherwise`, and relation premises without arguments whose expression is export-free
  (`NxSites.nxE`), here `Expand: $type(z, x) ~~ ARRAY (mut? zt)`.
* **`erase_rulePr`, `rulePr_self`, `rulePr_self_fwd`**: in a rule instance the asserted expression
  of a relation premise commutes with erasure, and when it is export-free its value is the same on
  both sides, so a derivation of the premise serves on both sides.
* **`reflect_coreR`**, **`fireFwdR`**: round 9 pass 1's backward reading (`reflect_core`) and
  forward firing (`fireFwd_elseRule`) for rules passing `simpleRuleR`.
* **`else_back`**: the chain argument of pass 1 stated once, from a cover of the earlier rules.
* **`pairReflect_exp`, `pairReflect_expChain`, `pairReflect_expChain2`**: `PairReflectB` along
  `eraseV` at the four pairs. **`elseBwdBLeft''_of_left3`**: `ElseBwdBLeft''` (9 pairs) from
  `ElseBwdBLeft3` (5 pairs: the four `Ref_ok` pairs and `(21, 9)`).
* **`innerPairs_fixed`** (kernel), **`pairReflectB_inner`**, **`pairReflectD_inner`**: `(21, 9)`
  holds vacuously, for RE (`eraseV`) and RM (`eraseC`): rule 21's handler holds
  `REF.EXN_ADDR a; THROW_REF`, rule 9's needs a `RETURN_CALL_REF`, and both erasures keep heads
  elementwise. **`elseBwdBLeft3_of_ref`**: `ElseBwdBLeft3` from `ElseBwdBRef` (the 4 `Ref_ok`
  pairs).
* **`stepFwdS_left3`, `sStepB_fwd_BI_left3`, `sReadB_fwd_BI_left3`**: round 8's `stepFwdS`,
  `sStepB_fwd_BI` and `sReadB_fwd_BI` with `BadFwd` replaced by `BadFwdE` (8 rules) and
  `ElseBwdBLeft3` (5 pairs).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB otherwiseB SStepB SReadB)

/-- **`Step` and `Step_read` go to the erased side**, given `BadFwdE` (8 rules) and the backward
firing at the 5 pairs of `leftPairs3`. -/
theorem stepFwdS_left3 {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hL : ElseBwdBLeft3 (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_left'' hB H hE (elseBwdBLeft''_of_left3 hB H hL) hx h

/-- **`Step` and `Step_read` go to the erased side**, given `BadFwdE` (8 rules) and the backward
firing at the 4 `Ref_ok` pairs. -/
theorem stepFwdS_ref {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hR : ElseBwdBRef (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_left3 hB H hE (elseBwdBLeft3_of_ref hR) hx h

section BI

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdBLeft3`. -/
theorem sStepB_fwd_BI_left3 (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft3 (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_left'' P hn host hE
    (elseBwdBLeft''_of_left3 (NxPrims.builtinsVT_BI P hn host)
      (NxClause.biErase_QT_BI P hn host) hL) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdBLeft3`. -/
theorem sReadB_fwd_BI_left3 (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft3 (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_left'' P hn host hE
    (elseBwdBLeft''_of_left3 (NxPrims.builtinsVT_BI P hn host)
      (NxClause.biErase_QT_BI P hn host) hL) h

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdBRef`. -/
theorem sStepB_fwd_BI_ref (hE : BadFwdE (NxPrims.envBI P hn host))
    (hR : ElseBwdBRef (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_left3 P hn host hE (elseBwdBLeft3_of_ref hR) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdBRef`. -/
theorem sReadB_fwd_BI_ref (hE : BadFwdE (NxPrims.envBI P hn host))
    (hR : ElseBwdBRef (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_left3 P hn host hE (elseBwdBLeft3_of_ref hR) h

end BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.expPairs_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms expPairs_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.elseBwdBLeft''_of_left3' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms elseBwdBLeft''_of_left3

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.sStepB_fwd_BI_left3' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_left3

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.sReadB_fwd_BI_left3' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_left3

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.pairReflectD_inner' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms pairReflectD_inner

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.sReadB_fwd_BI_ref' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_ref

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.sStepB_fwd_BI_ref' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_ref

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
