module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxStep.Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxStep.Check

/-!
# Round 8, REH: `Step` and `Step_read` go to the erased side, rule by rule (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.NxStep`; see `docs/projects/spectec/README.md`. Definitions are in `Round8/NxStep/Defs.lean`; the proof is unrefined, in
`Silmaril/Raw/…/Round8/NxStep/Fwd.lean`, and the kernel check in `Silmaril/Proofs/…/Round8/NxStep/`.

* **`stepFwdS`**: in `utf8Env B`, with primitives that conform and commute with erasure on `gdE`,
  every derivation of `Step` or `Step_read` under SpecTec's `otherwise` gives one of the erased
  value from the erased arguments, given `BadFwd`: the same statement at the rules that fail
  `goodRule`, for a single rule application whose premises hold. No swap set.
* **`sStepB_fwd_BI`, `sReadB_fwd_BI`**: SpecTec's `Step` and `Step_read` at round 4's primitives,
  with `BadFwd` as the only hypothesis.
* **`stepBad_fixed`** (kernel): the rules that `BadFwd` covers: four of the 36 rules of `Step`
  (two host calls, `table.grow-succeed`, `memory.grow-succeed`) and 32 of the 103 rules of
  `Step_read` (`block`, `loop`, `try_table`, `vload-pack-val`, and the 28 rules with an
  `otherwise` premise). None of them has a premise of `Step` or `Step_read`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB otherwiseB SStepB SReadB)

/-- **`Step` and `Step_read` go to the erased side**, given conforming primitives that commute
with erasure on `gdE`, and the obligation `BadFwd` at the rules that fail the check. -/
theorem stepFwdS {B : Builtins} (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hBad : BadFwd (utf8Env B))
    {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} (hx : stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwd hB H hBad hx h

section BI

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwd`. -/
theorem sStepB_fwd_BI (hBad : BadFwd (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') := by
  unfold SStepB at h ⊢
  have : DDerivesB (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host)) "Step" "%~>%"
      (([] : List ArgV).map Swap.eraseA) (Swap.eraseV (.tuple [c, c'])) := stepFwdS (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hBad
    (x := "Step") (by decide) h
  simpa [Swap.eraseV, Swap.eraseVs] using this

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwd`. -/
theorem sReadB_fwd_BI (hBad : BadFwd (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) := by
  unfold SReadB at h ⊢
  have : DDerivesB (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host)) "Step_read"
      "%~>%" (([] : List ArgV).map Swap.eraseA) (Swap.eraseV (.tuple [c, .list js])) := stepFwdS (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hBad
    (x := "Step_read") (by decide) h
  simpa [Swap.eraseV, Swap.eraseVs, Swap.eraseVs_eq_map] using this

end BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.sStepB_fwd_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.sReadB_fwd_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.stepBad_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stepBad_fixed

end Silmaril.Wasm.SpecTec.Sim.Round8.NxStep
