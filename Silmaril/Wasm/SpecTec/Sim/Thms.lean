module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Basic
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Provenance
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Lift
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly
public import Silmaril.Wasm.SpecTec.Sim.Whole.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Whole.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Whole.Findings

/-!
# SpecTec ↔ Core 3.0: what is proved so far

* `relsOfDefs_fixed`, `simEnv_findRel`, `hasRuleAt_simEnv`, `hasStepRules_simEnv`: the fixed script
  has the pinned script's relations, so the 218 rule transcriptions of `Equiv.Exec*` hold of every
  `simEnv B`.
* `dderives_iff`, `dderives_iff_fires`, `dderives_of_ruleAt`: unfolding and building declarative
  derivations.
* `sstep_pure`, `sstep_read`, `sstep_ctxtInstrs`, `sstep_ctxtLabel`, `sstep_ctxtHandler`,
  `sstep_ctxtFrame`: the six store-independent rules of `Step`, constructed for arbitrary values
  of their IL types. `sstep_ctxtInstrs` holds for every split, which the evaluator reading cannot
  give.
* `forward` and its instance `simEnv_forward` below: Core's `Step` is simulated by SpecTec's,
  given the families' per-constructor obligations `Forward` and the encoding's `TypingFacts`.

**The integrated result** (families C, M, N, R, X merged; `Sim/Whole/`):

* `Whole.forward_covered` and its spec-profile instance `wholeStep_forward_covered` below: under
  the families' undischarged interface assumptions `Whole.Assumptions B hn host` and the float
  track's `Floats.FloatB P B` (B extends the float primitives of the profile), every Core step
  from a configuration in the fragment `Whole.Covered` (no SIMD
  operator, memory instruction other than `data.drop`, table instruction other than
  `table.get`/`table.set`/`elem.drop`, GC aggregate instruction or `return_call_ref` in the active
  code) is a SpecTec step of the images, between typed configurations.
* `Whole.floatTyping_num`, `Whole.vecTyping_vec`: after the typing track's fix to the ported IL
  semantics, the fields of family V's `FloatTyping`/`VecTyping` that round 1 refuted
  (`not_floatTyping`, `not_vecTyping`) are proved; every encoded float and vector is typed
  (`Sim.Typing`). Family V's results stay out of the assembly until the float track revisits the
  remaining fields.

Open: `Task.wholeStep` itself; the assumptions in `Whole.Assumptions` (and whether they hold
together for one `B`); `Typed` for real configurations; the uncovered instructions; the backward
direction (per-rule lemmas exist for some rules, but neither the generic inversion of rules 0–5
nor `Backward` is assembled). See `docs/projects/spectec/README.md`.
-/

public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core

/-- **Forward simulation in `simEnv B`.** For any primitives `B`, the families' obligations and
the encoding's typing facts give: every Core step between typed configurations is a SpecTec step
of their images. -/
theorem simEnv_forward {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
    {host : HostSemantics H} (B : Builtins) (F : Forward (simEnv B) hn P host)
    (T : TypingFacts (simEnv B) hn) {c c' : Config H} (h : Step P host c c') :
    FwdP (simEnv B) hn c c' :=
  forward F T (hasStepRules_simEnv B) h

/-- **The forward half of `Task.wholeStep`, on the covered fragment.** For the spec profile with
any `nd` and `r`, any primitives `B` meeting the families' `Whole.Assumptions` and extending the
float primitives of the profile (`Floats.FloatB`, e.g. `Floats.floatIntB`), every Core step
from a covered configuration between typed configurations is a SpecTec step of the images. -/
theorem wholeStep_forward_covered {H : Type} {hn : H → String} {host : HostSemantics H}
    (B : Builtins) (A : Whole.Assumptions B hn host) (nd : Bool)
    (r : Silmaril.Wasm.Numerics.RelaxedChoice)
    (hF : Floats.FloatB (Silmaril.Wasm.Numerics.Profile.spec nd r) B) (c c' : Config H)
    (hcov : Whole.Covered c)
    (hc : Typed (simEnv B) hn c) (hc' : Typed (simEnv B) hn c')
    (h : Step (Silmaril.Wasm.Numerics.Profile.spec nd r) host c c') :
    SStep (simEnv B) (configV hn c) (configV hn c') :=
  Whole.forward_covered A hF h hcov hc hc'

end Silmaril.Wasm.SpecTec.Sim

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim
/-- info: 'Silmaril.Wasm.SpecTec.Sim.wholeStep_forward_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wholeStep_forward_covered

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Whole.forward_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Whole.forward_covered

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Whole.floatTyping_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Whole.floatTyping_num

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Whole.vecTyping_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Whole.vecTyping_vec

/-- info: 'Silmaril.Wasm.SpecTec.Sim.forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms forward
