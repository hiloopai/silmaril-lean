module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseRef.Pairs

/-!
# Round 9, RE: the four `Ref_ok` pairs, and `ElseBwdB` (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef`; see `docs/projects/spectec/README.md`. Definitions are in `Round9/ElseRef/Defs.lean`, the kernel checks in
`Silmaril/Proofs/…/Round9/ElseRef/Check`, and the proofs, unrefined, in
`Silmaril/Raw/…/Round9/ElseRef/{Base,RefOk,Pairs}`.

* **`refRel_fixed`** (kernel): every rule of `Ref_ok` passes `refRule`: it concludes
  `(s, e₂, e₃)` with `s` its one `store` quantifier, its other quantifiers are of export-free named
  type, and its premises are closed `if`s, relation premises on closed export-free expressions,
  and `Ref_ok` premises `(s, e₂', e₃')`.
* **`refBwd`**: a derivation of `Ref_ok` at `(eraseV sv, r, t)`, for a store `sv`, gives one at
  `(sv, r, t)`.
* **`refPairs_fixed`** (kernel), **`reflect_SF`**, **`pairReflect_ref`**: at `(3, 2)`, `(5, 4)`,
  `(66, 65)` and `(68, 67)` the earlier rule `s; f; L ~> R -- Ref_ok: (s, e₂, e₃)` fires backward:
  `s` and `f` are rebound to the original store and frame, and the premise goes back by `refBwd`.
* **`elseBwdB_holds`**: `ElseBwd.ElseBwdB`, the backward firing at all 94 pairs of `elsePairs`,
  holds given conforming primitives that commute with erasure on `gdE`.
* **`stepFwdS_E`, `sStepB_fwd_BI_E`, `sReadB_fwd_BI_E`**: round 8's `stepFwdS`, `sStepB_fwd_BI` and
  `sReadB_fwd_BI` with `BadFwd` (36 rules) replaced by `BadFwdE` (8 rules) and nothing else. At
  round 4's primitives `BadFwdE` is the only hypothesis left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB otherwiseB SStepB SReadB)

/-- **`Step` and `Step_read` go to the erased side**, given conforming primitives that commute
with erasure on `gdE` and `BadFwdE` (8 rules). -/
theorem stepFwdS_E {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_else hB H hE (elseBwdB_holds hB H) hx h

section BI

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **`ElseBwdB` at round 4's primitives.** -/
theorem elseBwdB_BI : ElseBwdB (NxPrims.envBI P hn host) :=
  elseBwdB_holds (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE`. -/
theorem sStepB_fwd_BI_E (hE : BadFwdE (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_else P hn host hE (elseBwdB_BI P hn host) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given
`BadFwdE`. -/
theorem sReadB_fwd_BI_E (hE : BadFwdE (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_else P hn host hE (elseBwdB_BI P hn host) h

end BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.refBwd' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms refBwd

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.elseBwdB_holds' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms elseBwdB_holds

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.sStepB_fwd_BI_E' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_E

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef.sReadB_fwd_BI_E' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_E

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef
