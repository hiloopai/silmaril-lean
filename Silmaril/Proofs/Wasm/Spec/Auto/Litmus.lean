module

public import Silmaril.Proofs.Wasm.Spec.Auto.Tactic
public import Silmaril.Wasm.Verify.Litmus.Thms
public import Silmaril.Wasm.Spec.Component.Litmus.Thms

@[expose] public section

/-!
# Automation litmus tests

On the verifier's litmus modules (`Silmaril.Wasm.Verify.Litmus`; import `0` is `assert`), every
profile:

* `modDead_ltlMax`, `modDead_ltlFin`, `modDead_tla`: temporal images of "never calls `assert`",
  by `wasm_spec` (rewritten back along the logic maps, then the verifier);
* `modDead_neverCallFrom`: through `neverCall`;
* `modOne_tla_assert`, `modOne_ltlMax_assert`: temporal images of "assert never false";
* `modDead_and`: a conjunction in the property registry, by evaluating `ModProp.verdict`;
* `modZero_not_assert`, `modZero_not_and`: refutations at every specification profile;
* `reduce_neverCallFrom`: the normaliser;
* `modTwo_verdict_b`, `modTwo_from_b_and`: `neverCallFrom (assert, b)` of `modTwo` by the
  per-export verifier (`checkFrom`; `neverCall` is refuted there), in the registry dispatch;
  `modTwo_not_from_a`: the refutation for export `a`;
* components (loose semantics): `greet_task` (a `retTyped` task holds) and `greet_info` (the
  registry records the shape at level `2`, strings and lists).
-/

namespace Silmaril.Wasm.Spec.Auto

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Verify Silmaril.Wasm.Verify.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-- `assert` in `modDead`. -/
abbrev deadA : (ifaceOf (instOf modDead)).Imp := ⟨0, modDead_imports⟩

/-- `assert` in `modOne`. -/
abbrev oneA : (ifaceOf (instOf modOne)).Imp := ⟨0, modOne_imports⟩

/-- `assert` in `modZero`. -/
abbrev zeroA : (ifaceOf (instOf modZero)).Imp := ⟨0, modZero_imports⟩

theorem modDead_ltlMax (P : Profile) :
    Models (ltlMax FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modDead)
      (LTL.alw (LTL.atom fun _ e => ∀ a, e ≠ Event.icall deadA a)) := by
  wasm_spec

theorem modDead_ltlFin (P : Profile) :
    Models (ltlFin FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modDead)
      (LTL.alw (LTL.atom fun _ e => ∀ a, e ≠ Event.icall deadA a)) := by
  wasm_spec

theorem modDead_tla (P : Profile) :
    Models (tla FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modDead)
      (TLA.box fun _ e => ∀ a, e ≠ Event.icall deadA a) := by
  wasm_spec

theorem modDead_neverCallFrom (P : Profile) (e : (ifaceOf (instOf modDead)).Exp) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modDead)
      (deadA, e) := by
  wasm_spec

theorem modOne_tla_assert (P : Profile) :
    Models (tla FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modOne)
      (TLA.box fun _ e => ∀ a, e = Event.icall oneA a → assertOk a) := by
  wasm_spec

theorem modOne_ltlMax_assert (P : Profile) :
    Models (ltlMax FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modOne)
      (LTL.alw (LTL.atom fun _ e => ∀ a, e = Event.icall oneA a → assertOk a)) := by
  wasm_spec

theorem modDead_and (P : Profile) :
    (ModProp.and (.neverCall deadA) (.assertNeverFalse deadA)).Satisfies P (progOf modDead) := by
  wasm_spec

theorem modZero_not_assert (nd : Bool) :
    ¬ (ModProp.assertNeverFalse zeroA).Satisfies (Profile.spec nd {}) (progOf modZero) := by
  wasm_spec_refute

theorem modZero_not_and (nd : Bool) :
    ¬ (ModProp.and (.assertNeverFalse zeroA) (.neverCall zeroA)).Satisfies (Profile.spec nd {})
      (progOf modZero) := by
  wasm_spec_refute

/-- `assert` in `modTwo`. -/
abbrev twoA : (ifaceOf (instOf modTwo)).Imp := ⟨0, modTwo_imports⟩

theorem modTwo_verdict_b :
    (ModProp.neverCallFrom twoA ⟨1, modTwo_exports⟩).verdict modTwo = .proved := by
  decide +kernel

/-- **`modTwo` never calls `assert` while `b` is active**, through the registry dispatch, as a
conjunction with "`assert` is never called with `0`" (every profile). -/
theorem modTwo_from_b_and (P : Profile) :
    (ModProp.and (.neverCallFrom twoA ⟨1, modTwo_exports⟩) (.assertNeverFalse twoA)).Satisfies P
      (progOf modTwo) := by
  wasm_spec

theorem modTwo_not_from_a (nd : Bool) :
    ¬ (ModProp.neverCallFrom twoA ⟨0, by decide +kernel⟩).Satisfies (Profile.spec nd {})
      (progOf modTwo) := by
  wasm_spec_refute

theorem reduce_neverCallFrom (P : Profile) (e : (ifaceOf (instOf modDead)).Exp) :
    (Task.module P (progOf modDead) (.neverCallFrom deadA e)).reduce =
      .module P (progOf modDead) (.neverCall deadA) := rfl

open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Spec.Component.Litmus in
theorem greet_task :
    (Task.component Component.Litmus.S (Component.Litmus.progOf greetRun) (.retTyped greetE)).Holds :=
  greetRun_retTyped

open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Spec.Component.Litmus in
theorem greet_info :
    (Task.component Component.Litmus.S (Component.Litmus.progOf greetRun) (.retTyped greetE)).info =
      ⟨"retTyped", .component, Level.memory, false, false⟩ := by
  show ShapeInfo.mk _ _ Xs.level _ _ = _
  rw [Xs_level]

end Silmaril.Wasm.Spec.Auto
