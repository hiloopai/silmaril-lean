module

public import Silmaril.Wasm.SpecTec.Sim.Round9.BadN.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.BadN.Rule
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.Thms

/-!
# Round 9, RE: `BadFwdE` at `vload-pack-val` (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.BadN`; see `docs/projects/spectec/README.md`. Definitions are in `Round9/BadN/Defs.lean`, the kernel check in
`Silmaril/Proofs/…/Round9/BadN/Check`, and the proofs, unrefined, in `Silmaril/Raw/…/Round9/BadN/{Iter,
Rule}`.

* **`stepBadN_fixed`** (kernel): of the eight rules of `BadFwdE`, `vload-pack-val` passes
  `goodRuleN` (indexed iterations `pr^(k<eₙ)` allowed); seven are left.
* **`iterN_fwd`**: an indexed list iteration goes to the erased side (the `listN` case of round
  8's `NxDer.dpremB_fwd`).
* **`ruleFwdN`**, **`badFwdE_of_N`**: `BadFwdE` from `BadFwdN` (seven rules).
* **`stepFwdS_N`, `sStepB_fwd_BI_N`, `sReadB_fwd_BI_N`**: round 8's `stepFwdS`, `sStepB_fwd_BI` and
  `sReadB_fwd_BI` with `BadFwd` (36 rules) replaced by `BadFwdN` (7 rules): the two `$hostcall`
  rules, `table.grow-succeed`, `memory.grow-succeed`, `block`, `loop` and `try_table`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.BadN

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB otherwiseB SStepB SReadB)

/-- **`Step` and `Step_read` go to the erased side**, given conforming primitives that commute
with erasure on `gdE` and `BadFwdN` (7 rules). -/
theorem stepFwdS_N {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hN : BadFwdN (utf8Env B))
    {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  ElseRef.stepFwdS_E hB H (badFwdE_of_N hB H hN) hx h

section BI

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdN`. -/
theorem sStepB_fwd_BI_N (hN : BadFwdN (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  ElseRef.sStepB_fwd_BI_E P hn host
    (badFwdE_of_N (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hN) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given
`BadFwdN`. -/
theorem sReadB_fwd_BI_N (hN : BadFwdN (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  ElseRef.sReadB_fwd_BI_E P hn host
    (badFwdE_of_N (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hN) h

end BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadN.stepBadN_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stepBadN_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadN.badFwdE_of_N' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms badFwdE_of_N

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadN.sStepB_fwd_BI_N' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_N

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.BadN.sReadB_fwd_BI_N' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_N

end Silmaril.Wasm.SpecTec.Sim.Round9.BadN
