module

public import Silmaril.Wasm.Auto.Front.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Verify.Kernel.Thms
public import Silmaril.Wasm.Spec.Run.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Execution.Core.SpecProfile
public import Silmaril.Wasm.Auto.Bridge.Thms
import Silmaril.Proofs.Wasm.Auto.Front.Extended

@[expose] public section

/-!
# The front end: results

Proofs in `Silmaril.Proofs.Wasm.Auto.Front.Basic`. For start-free modules with scalar function
imports and exports (`Silmaril.Wasm.Verify.instance?`), export index `j`, relation `R : Rel`:

* **`refutes_of_cexWith`**: `cexWith runC R impl spec j vs = true` (a differential test on the
  verified interpreter) implies `¬ ModRefines R.toProp (profile refOracle) impl spec j`;
  `refutes_of_cexK`: the same from the kernel-reducible check `cexK`, provable by
  `decide +kernel`;
* `not_modEquiv_of_cexWith`, `not_modEquiv_of_cexWith_symm` (and `…K`): equivalence;
* **`not_modMeets_of_specCexWith`**: a reference-function counterexample refutes `ModMeets` at
  every profile `P` admitting the deterministic steps; `not_modMeets_of_specCexK`;
* `not_modMeets_spec_of_specCexK`: the kernel form at every specification profile
  `Profile.spec nd {}`;
* `checkRefinesBase_refuted`, `checkEquivBase_refuted`, `checkMeets_refuted`: a `refuted` report of
  the
  front end is a refutation;
* `modRefines_refl`, `modEquiv_refl`: the `identical` verdict;
* **`checkRefinesBase_proved`**, `checkEquivBase_proved`: a `proved` report proves `ModEquiv`
  (hence `ModRefines`) at **every** profile, from the function-level stage of
  `Silmaril.Wasm.Auto.Bridge` (`Silmaril.Proofs.Wasm.Auto.Front.Prove`).

The tactic `wasm_diff_refute vs` closes `¬ ModRefines …`, `¬ ModEquiv …` and `¬ ModMeets …` goals
at the deterministic profile from a counterexample `vs`, by kernel evaluation.
-/

namespace Silmaril.Wasm.Auto.Front

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.Front` -/

section
-- from Silmaril/Proofs/Wasm/Auto/Front/Basic.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Front
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement
open Silmaril.Wasm.Verify (instance? instOf refOracle isInstance_of_instance?)
open Silmaril.Wasm.Spec (typedB typedB_sound invokeOk_of_wellFormed)

theorem Rel.refl (R : Rel) (b : Behaviour Val) : R.toProp b b :=
  Silmaril.Proofs.Wasm.Auto.Front.Rel.refl (R := R) (b := b)

theorem addrOf_eq {m : Module} {mt : Validation.CModuleType} {I : ScalarInstance}
    (h : instance? m = some (mt, I)) (j : Nat) : addrOf m j = I.addrs.getD j 0 :=
  Silmaril.Proofs.Wasm.Auto.Front.addrOf_eq (m := m) (mt := mt) (I := I) (h := h) (j := j)

theorem runK_eq : runK = Front.runC :=
  Silmaril.Proofs.Wasm.Auto.Front.runK_eq

/-- **A counterexample refutes refinement** at the deterministic profile: on the arguments of
the hit, the implementation's result is a behaviour, and the specification's behaviours are its
result and possibly divergence (silmaril-lean's `behaviours_subset_of_runInvoke?`), neither
related to the implementation's result. -/
theorem refutes_of_cexWith {R : Rel} {impl spec : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC R impl spec j vs = true) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.refutes_of_cexWith (R := R) (impl := impl) (spec := spec) (j := j)
    (vs := vs) (h := h)

/-- The same with the kernel-reducible interpreter (for `decide +kernel`). -/
theorem refutes_of_cexK {R : Rel} {impl spec : Module} {j : Nat} {vs : List Val}
    (h : cexK R impl spec j vs = true) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.refutes_of_cexK (R := R) (impl := impl) (spec := spec) (j := j)
    (vs := vs) (h := h)

/-- **A counterexample refutes equivalence** (either direction, for equality). -/
theorem not_modEquiv_of_cexWith {R : Rel} {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC R m₁ m₂ j vs = true) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modEquiv_of_cexWith (R := R) (m₁ := m₁) (m₂ := m₂) (j := j)
    (vs := vs) (h := h)

theorem not_modEquiv_of_cexWith_symm {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexWith Front.runC .eq m₂ m₁ j vs = true) :
    ¬ ModEquiv Rel.eq.toProp (profile refOracle) m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modEquiv_of_cexWith_symm (m₁ := m₁) (m₂ := m₂) (j := j)
    (vs := vs) (h := h)

theorem not_modEquiv_of_cexK {R : Rel} {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexK R m₁ m₂ j vs = true) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modEquiv_of_cexK (R := R) (m₁ := m₁) (m₂ := m₂) (j := j)
    (vs := vs) (h := h)

theorem not_modEquiv_of_cexK_symm {m₁ m₂ : Module} {j : Nat} {vs : List Val}
    (h : cexK .eq m₂ m₁ j vs = true) :
    ¬ ModEquiv Rel.eq.toProp (profile refOracle) m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modEquiv_of_cexK_symm (m₁ := m₁) (m₂ := m₂) (j := j) (vs := vs)
    (h := h)

theorem steps_mono {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {c d : Config Nat} (h : Steps (profile refOracle) Det.noHost c d) : Steps P Det.noHost c d :=
  Silmaril.Proofs.Wasm.Auto.Front.steps_mono (P := P) (hP := hP) (c := c) (d := d) (h := h)

/-- **A counterexample refutes a reference function** at every profile admitting the
deterministic steps (every specification profile `Profile.spec nd {}` in particular): only the
soundness of the interpreter is needed. -/
theorem not_modMeets_of_specCexWith {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {R : Rel} {m : Module} {j : Nat} {f : List Val → Option Result} {vs : List Val}
    (h : specCexWith Front.runC R m j f vs = true) :
    ¬ ModMeets R.toProp P m j f :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modMeets_of_specCexWith (P := P) (hP := hP) (R := R) (m := m)
    (j := j) (f := f) (vs := vs) (h := h)

theorem not_modMeets_of_specCexK {R : Rel} {m : Module} {j : Nat}
    {f : List Val → Option Result} {vs : List Val} (h : specCexK R m j f vs = true) :
    ¬ ModMeets R.toProp (profile refOracle) m j f :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modMeets_of_specCexK (R := R) (m := m) (j := j) (f := f)
    (vs := vs) (h := h)

/-- A reference-function counterexample from the kernel check, at every specification profile
`Profile.spec nd {}` (silmaril-lean's `Step.deterministic_refines_spec`). -/
theorem not_modMeets_spec_of_specCexK (nd : Bool) {R : Rel} {m : Module} {j : Nat}
    {f : List Val → Option Result} {vs : List Val} (h : specCexK R m j f vs = true) :
    ¬ ModMeets R.toProp (Profile.spec nd {}) m j f :=
  Silmaril.Proofs.Wasm.Auto.Front.not_modMeets_spec_of_specCexK (nd := nd) (R := R) (m := m) (j := j)
    (f := f) (vs := vs) (h := h)

/-- **A `refuted` report of the front end refutes the refinement.** -/
theorem checkRefinesBase_refuted {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (h : (checkRefinesBase R impl spec j n idt).verdict = .refuted) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkRefinesBase_refuted (R := R) (impl := impl) (spec := spec)
    (j := j)
    (n := n) (idt := idt) (h := h)

/-- **A `refuted` report of the front end refutes the equivalence** (for `Rel.eq` either
direction may be the refuted one). -/
theorem checkEquivBase_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquivBase R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkEquivBase_refuted (R := R) (m₁ := m₁) (m₂ := m₂) (j := j)
    (n := n)
    (idt := idt) (h := h)

/-- **A `refuted` report against a reference function** refutes `ModMeets` at every profile
admitting the deterministic steps. -/
theorem checkMeets_refuted {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {R : Rel} {m : Module} {j : Nat} {f : List Val → Option Result} {n : Nat}
    (h : (checkMeets R m j f n).verdict = .refuted) : ¬ ModMeets R.toProp P m j f :=
  Silmaril.Proofs.Wasm.Auto.Front.checkMeets_refuted (P := P) (hP := hP) (R := R) (m := m) (j := j)
    (f := f) (n := n) (h := h)

theorem modRefines_refl (R : Rel) (P : Profile) (m : Module) (j : Nat) :
    ModRefines R.toProp P m m j :=
  Silmaril.Proofs.Wasm.Auto.Front.modRefines_refl (R := R) (P := P) (m := m) (j := j)

theorem modEquiv_refl (R : Rel) (P : Profile) (m : Module) (j : Nat) :
    ModEquiv R.toProp P m m j :=
  Silmaril.Proofs.Wasm.Auto.Front.modEquiv_refl (R := R) (P := P) (m := m) (j := j)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Front/Prove.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Front
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **A `proved` verdict of the proving stage is an equivalence**, every profile. -/
theorem modEquiv_of_proveStageBase {m₁ m₂ : Module} {j n : Nat}
    (h : (proveStageBase m₁ m₂ j n).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.modEquiv_of_proveStageBase (m₁ := m₁) (m₂ := m₂) (j := j) (n := n)
    (h := h) (R := R) (P := P)

/-- **A `proved` report of `checkRefinesBase` proves the equivalence**, hence the refinement, at
every profile (`hid`: the `identical` flag is only set for identical modules). -/
theorem checkRefinesBase_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesBase R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkRefinesBase_proved (R := R) (impl := impl) (spec := spec)
    (j := j)
    (n := n) (idt := idt) (hid := hid) (h := h) (P := P)

/-- **A `proved` report of `checkEquivBase` proves the equivalence**, every profile. -/
theorem checkEquivBase_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquivBase R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkEquivBase_proved (R := R) (m₁ := m₁) (m₂ := m₂) (j := j)
    (n := n)
    (idt := idt) (hid := hid) (h := h) (P := P)

end



/-- Close `¬ ModRefines R.toProp (profile refOracle) impl spec j`, `¬ ModEquiv …` or
`¬ ModMeets …` from the counterexample arguments `vs`, by kernel evaluation of the verified
interpreter on both sides. -/
macro "wasm_diff_refute " vs:term : tactic =>
  `(tactic| first
    | exact Silmaril.Wasm.Auto.Front.refutes_of_cexK (vs := $vs) (by decide +kernel)
    | exact Silmaril.Wasm.Auto.Front.not_modEquiv_of_cexK (vs := $vs) (by decide +kernel)
    | exact Silmaril.Wasm.Auto.Front.not_modEquiv_of_cexK_symm (vs := $vs) (by decide +kernel)
    | exact Silmaril.Wasm.Auto.Front.not_modMeets_of_specCexK (vs := $vs) (by decide +kernel)
    | exact Silmaril.Wasm.Auto.Front.not_modMeets_spec_of_specCexK _ (vs := $vs) (by decide +kernel))

/-- Close `ModEquiv R.toProp P m₁ m₂ j` (any front-end relation, any profile) by the
function-level proving stage, evaluated by the kernel: equal normal forms of the summarised
results, or residual goals in the lemma library. -/
macro "wasm_prove_base" : tactic =>
  `(tactic| exact Silmaril.Wasm.Auto.Front.modEquiv_of_proveStageBase (n := 0) (by decide +kernel) _ _)

/-! ## The extended summaries -/

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Verify (refOracle)

/-- **A `proved` report of `checkRefines` proves the equivalence**, every profile (`hid`: the
`identical` flag is only set for identical modules). -/
theorem checkRefines_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefines R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkRefines_proved hid h P

/-- **A `proved` report of `checkEquiv` proves the equivalence**, every profile. -/
theorem checkEquiv_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquiv R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkEquiv_proved hid h P

/-- **A `proved` verdict of the proving stages is an equivalence**, every profile. -/
theorem modEquiv_of_proveStage {m₁ m₂ : Module} {j : Nat}
    (h : (proveStage m₁ m₂ j).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.modEquiv_of_proveStage h R P

/-- A `refuted` report of `checkRefines` is a refutation. -/
theorem checkRefines_refuted {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (h : (checkRefines R impl spec j n idt).verdict = .refuted) :
    ¬ ModRefines R.toProp (profile refOracle) impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkRefines_refuted h

/-- A `refuted` report of `checkEquiv` is a refutation. -/
theorem checkEquiv_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquiv R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (profile refOracle) m₁ m₂ j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkEquiv_refuted h

/-- Close `ModEquiv R.toProp P m₁ m₂ j` (any front-end relation, any profile) by kernel
evaluation of the proving stages: the function summaries of `Silmaril.Wasm.Auto.Bridge`, then the
extended summaries (memory, globals, conversions, trap guards). -/
macro "wasm_prove" : tactic =>
  `(tactic| exact Silmaril.Wasm.Auto.Front.modEquiv_of_proveStage (by decide +kernel) _ _)

/-! ## Results used by `Silmaril.Wasm.Auto2` -/

section
-- A lemma of `Silmaril.Proofs.Wasm.Auto.Front` that the proofs of `Silmaril.Wasm.Auto2` use.

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Front
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem checkRefinesBase_proved_refines {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesBase R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModRefines R.toProp P impl spec j :=
  Silmaril.Proofs.Wasm.Auto.Front.checkRefinesBase_proved_refines hid h P

end

end Silmaril.Wasm.Auto.Front
