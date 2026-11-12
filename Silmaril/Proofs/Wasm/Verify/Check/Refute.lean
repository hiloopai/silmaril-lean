module

public import Silmaril.Proofs.Wasm.Verify.Check.Flow
public import Silmaril.Proofs.Wasm.Verify.Refute.Basic
public import Silmaril.Wasm.Execution.Core.SpecProfile

/-!
# Soundness of `refuted` verdicts

A `refuted` verdict of `check` on a module with instance `I` carries a counterexample
(`Reason.counterexample x`) that is a trace of `wasmSem P` calling the import (with `i32 0` first,
for assertions), for every profile `P` admitting the deterministic steps of the refuter's profile
`profile refOracle` (`check_refuted_trace`); so the property fails (`check_refuted_sound`,
`check_assert_refuted_sound`), in particular at every specification profile `Profile.spec nd {}`
(`check_refuted_sound_spec`, `check_assert_refuted_sound_spec`). Closed world: against every
environment, a Core run of the counterexample's export call reaches the callout
(`check_refuted_closed_world`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {m : Module} {mt : CModuleType} {I : ScalarInstance}

/-- The counterexample of a `refuted` verdict for "never calls import `i`". -/
theorem check_refuted_cex (hI : IsInstance m mt I) {i : Nat}
    (h : (check m (.neverCall i)).verdict = .refuted) :
    ∃ imp x, importType? mt i = some imp ∧ refuteStore I.store I.addrs imp i anyCall = some x ∧
      (check m (.neverCall i)).reason = .counterexample x := by
  rcases check_neverCall_cases hI i with hc | ⟨fs, hc⟩
  · rw [hc] at h
    cases h
  · rw [hc] at h ⊢
    obtain ⟨x, hx, hd⟩ := decideStore_refuted h
    obtain ⟨imp, himp, hr⟩ := Option.bind_eq_some_iff.1 hx
    exact ⟨imp, x, himp, hr, by rw [hd]⟩

/-- The counterexample of a `refuted` verdict for assertions. -/
theorem check_assert_refuted_cex (hI : IsInstance m mt I) {i : Nat}
    (h : (check m (.assertNeverFalse i)).verdict = .refuted) :
    ∃ imp x, importType? mt i = some imp ∧ refuteStore I.store I.addrs imp i falseCall = some x ∧
      (check m (.assertNeverFalse i)).reason = .counterexample x := by
  rcases check_assert_cases hI i with hc | ⟨-, fs, hc⟩
  · rw [hc] at h
    cases h
  · rw [hc] at h ⊢
    obtain ⟨x, hx, hd⟩ := decideAssert_refuted h
    obtain ⟨imp, himp, hr⟩ := Option.bind_eq_some_iff.1 hx
    exact ⟨imp, x, himp, hr, by rw [hd]⟩

/-- **A `refuted` verdict comes with a counterexample trace** (every profile `P` admitting the
deterministic steps of `profile refOracle`): the reason is `counterexample x`, and some trace of
`wasmSem P` calls import `i` with the arguments `x.callArgs`. -/
theorem check_refuted_trace (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.neverCall i.val)).verdict = .refuted) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∃ x, (check m (.neverCall i.val)).reason = .counterexample x ∧
      ∃ t ∈ (wasmSem P).traces (WasmProg.ofInstance I), Event.icall i x.callArgs ∈ t := by
  obtain ⟨imp, x, himp, hr, hreason⟩ := check_refuted_cex hI h
  obtain ⟨t, ht, hc, -⟩ := refute_trace hI himp hr hP
  exact ⟨x, hreason, t, ht, hc⟩

/-- **Soundness of `refuted` for "never calls import `i`"**: the program of the instance calls
import `i`, at every profile `P` admitting the deterministic steps of `profile refOracle`. -/
theorem check_refuted_sound (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.neverCall i.val)).verdict = .refuted) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  intro hm
  obtain ⟨x, -, t, ht, hc⟩ := check_refuted_trace hI h hP
  exact (models_iff _ _ _ _).1 hm t ht x.callArgs hc

/-- `check_refuted_sound` at the specification profiles. -/
theorem check_refuted_sound_spec (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.neverCall i.val)).verdict = .refuted) (nd : Bool) :
    ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (WasmProg.ofInstance I) i :=
  check_refuted_sound hI h fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- **Soundness of `refuted` for assertions**: the program of the instance calls the assertion
`i` with first argument `i32 0`, at every profile `P` admitting the deterministic steps of
`profile refOracle`. -/
theorem check_assert_refuted_sound (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.assertNeverFalse i.val)).verdict = .refuted) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  intro hm
  obtain ⟨imp, x, himp, hr, -⟩ := check_assert_refuted_cex hI h
  obtain ⟨t, ht, hc, hbad⟩ := refute_trace hI himp hr hP
  have hok : assertOk x.callArgs := (models_iff _ _ _ _).1 hm t ht x.callArgs hc
  have hhead : x.callArgs.head? = some (Val.i32 0) := by
    simpa only [falseCall, beq_iff_eq] using hbad
  exact hok hhead

/-- `check_assert_refuted_sound` at the specification profiles. -/
theorem check_assert_refuted_sound_spec (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.assertNeverFalse i.val)).verdict = .refuted) (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (WasmProg.ofInstance I) i :=
  check_assert_refuted_sound hI h fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- **Closed world**: for a `refuted` verdict, some export call, against **every** environment
`K`, has a Core run reaching a callout of import `i` (every profile admitting the deterministic
steps of `profile refOracle`). -/
theorem check_refuted_closed_world (hI : IsInstance m mt I) {i : Nat}
    (h : (check m (.neverCall i)).verdict = .refuted) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∃ (j : Fin I.exports.length) (args : Typed (I.exports.get j).params), ∀ K : Env I.E,
      ∃ c : Config Nat, Steps P (hostOf I.imports K) (invoke I.store (I.addr j) args.1) c ∧
        ∃ E a args', decompose? c.store c.code = some (E, a, i, args') := by
  obtain ⟨imp, x, -, hr, -⟩ := check_refuted_cex hI h
  obtain ⟨j, w, -, hw⟩ := refute_closed_world hI hr hP
  refine ⟨j, w, fun K => ?_⟩
  obtain ⟨c, hrun, E, a, hd⟩ := hw K
  exact ⟨c, hrun, E, a, x.callArgs, hd⟩

/-- **Refutation on a module**: if the module's instance is computed and `check` refutes "never
calls import `i`", the module's program calls `i`, at every specification profile. -/
theorem check_refuted_neverCall {m : Module} (hm : (instance? m).isSome = true)
    {i : (ifaceOf (instOf m)).Imp} (h : (check m (.neverCall i.val)).verdict = .refuted)
    (nd : Bool) :
    ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) i :=
  check_refuted_sound_spec (isInstance_instOf hm).choose_spec h nd

/-- **Refutation on a module, for assertions** (every specification profile). -/
theorem check_refuted_assertNeverFalse {m : Module} (hm : (instance? m).isSome = true)
    {i : (ifaceOf (instOf m)).Imp} (h : (check m (.assertNeverFalse i.val)).verdict = .refuted)
    (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) i :=
  check_assert_refuted_sound_spec (isInstance_instOf hm).choose_spec h nd

end Silmaril.Wasm.Verify
