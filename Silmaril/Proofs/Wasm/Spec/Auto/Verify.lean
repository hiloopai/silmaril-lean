module

public import Silmaril.Wasm.Spec.Auto.Verify.Defs
public import Silmaril.Proofs.Wasm.Spec.Auto.Basic

@[expose] public section

/-!
# Automation: soundness of the verifier dispatch

* `atomVerdict_neverCall`, `atomVerdict_assert`: a `proved` atom verdict gives the sentence at
  every profile (`check_neverCall`, `check_assertNeverFalse`); `atomVerdict_neverCall_refuted`,
  `atomVerdict_assert_refuted`: a `refuted` one refutes it at every specification profile
  (`check_refuted_neverCall`, `check_refuted_assertNeverFalse`);
* **`ModProp.verdict_proved`**: a `proved` verdict on a module property means the property holds
  of the module's program at every profile;
* **`ModProp.verdict_refuted`**: a `refuted` verdict means it fails at every specification
  profile `Profile.spec nd {}`;
* `fromVerdict_proved`, `fromVerdict_refuted`, `neverCallFrom_verdict_proved`,
  `neverCallFrom_verdict_refuted`: `neverCallFrom (i, e)` by the per-export verifier
  (`checkFrom_neverCallFrom`, `checkFrom_refuted_neverCallFrom`), else through `neverCall i`;
* `Request.sound`, `Request.refuted_sound`: the same for requests (as tasks).
-/

namespace Silmaril.Wasm.Spec.Auto

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Verify (check instance? instOf progOf)
open Silmaril.Wasm.Numerics (Profile)

variable {m : Module}

/-- An atom verdict other than `unknown` comes with a computed instance. -/
theorem instance_of_atomVerdict {q : Silmaril.Wasm.Verify.Property} (h : atomVerdict m q ≠ .unknown) :
    (instance? m).isSome = true ∧ atomVerdict m q = (check m q).verdict := by
  unfold atomVerdict at h ⊢
  by_cases hm : (instance? m).isSome = true
  · exact ⟨hm, by simp only [hm, ite_true]⟩
  · simp only [hm, ite_false, Bool.false_eq_true] at h
    exact absurd rfl h

theorem atomVerdict_neverCall {i : (ifaceOf (instOf m)).Imp}
    (h : atomVerdict m (.neverCall i.val) = .proved) (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf m) i := by
  obtain ⟨hm, heq⟩ := instance_of_atomVerdict (h ▸ by decide : atomVerdict m (.neverCall i.val) ≠ .unknown)
  exact Silmaril.Wasm.Verify.check_neverCall hm (heq ▸ h) P

theorem atomVerdict_assert {i : (ifaceOf (instOf m)).Imp}
    (h : atomVerdict m (.assertNeverFalse i.val) = .proved) (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf m) i := by
  obtain ⟨hm, heq⟩ :=
    instance_of_atomVerdict (h ▸ by decide : atomVerdict m (.assertNeverFalse i.val) ≠ .unknown)
  exact Silmaril.Wasm.Verify.check_assertNeverFalse hm (heq ▸ h) P

theorem atomVerdict_neverCall_refuted {i : (ifaceOf (instOf m)).Imp}
    (h : atomVerdict m (.neverCall i.val) = .refuted) (nd : Bool) :
    ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) i := by
  obtain ⟨hm, heq⟩ := instance_of_atomVerdict (h ▸ by decide : atomVerdict m (.neverCall i.val) ≠ .unknown)
  exact Silmaril.Wasm.Verify.check_refuted_neverCall hm (heq ▸ h) nd

theorem atomVerdict_assert_refuted {i : (ifaceOf (instOf m)).Imp}
    (h : atomVerdict m (.assertNeverFalse i.val) = .refuted) (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) i := by
  obtain ⟨hm, heq⟩ :=
    instance_of_atomVerdict (h ▸ by decide : atomVerdict m (.assertNeverFalse i.val) ≠ .unknown)
  exact Silmaril.Wasm.Verify.check_refuted_assertNeverFalse hm (heq ▸ h) nd

theorem fromVerdict_proved {i : (ifaceOf (instOf m)).Imp} {e : (ifaceOf (instOf m)).Exp}
    (h : fromVerdict m i.val e.val = .proved) (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf m) (i, e) := by
  unfold fromVerdict at h
  by_cases hm : (instance? m).isSome = true
  · simp only [hm, ↓reduceIte] at h
    exact Silmaril.Wasm.Verify.checkFrom_neverCallFrom hm h P
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
    cases h

theorem fromVerdict_refuted {i : (ifaceOf (instOf m)).Imp} {e : (ifaceOf (instOf m)).Exp}
    (h : fromVerdict m i.val e.val = .refuted) (nd : Bool) :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) (i, e) := by
  unfold fromVerdict at h
  by_cases hm : (instance? m).isSome = true
  · simp only [hm, ↓reduceIte] at h
    exact Silmaril.Wasm.Verify.checkFrom_refuted_neverCallFrom hm h nd
  · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- The `neverCallFrom` arm of `ModProp.verdict`: the per-export verdict, or `neverCall`. -/
theorem neverCallFrom_verdict_proved {i : (ifaceOf (instOf m)).Imp}
    {e : (ifaceOf (instOf m)).Exp} (h : (ModProp.neverCallFrom i e).verdict m = .proved)
    (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf m) (i, e) := by
  have hcases : fromVerdict m i.val e.val = .proved ∨
      atomVerdict m (.neverCall i.val) = .proved := by
    revert h
    unfold ModProp.verdict
    split <;> (try split) <;> simp_all
  rcases hcases with hf | hn
  · exact fromVerdict_proved hf P
  · exact neverCallFrom_of_neverCall (atomVerdict_neverCall hn P) e

theorem neverCallFrom_verdict_refuted {i : (ifaceOf (instOf m)).Imp}
    {e : (ifaceOf (instOf m)).Exp} (h : (ModProp.neverCallFrom i e).verdict m = .refuted)
    (nd : Bool) :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf m) (i, e) := by
  have hf : fromVerdict m i.val e.val = .refuted := by
    revert h
    unfold ModProp.verdict
    split <;> (try split) <;> simp_all
  exact fromVerdict_refuted hf nd

/-- A proved conjunction has proved parts. -/
theorem andVerdict_proved {v w : Verdict} (h : andVerdict v w = .proved) :
    v = .proved ∧ w = .proved := by
  cases v <;> cases w <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- A refuted conjunction has a refuted part. -/
theorem andVerdict_refuted {v w : Verdict} (h : andVerdict v w = .refuted) :
    v = .refuted ∨ w = .refuted := by
  cases v <;> cases w <;> first | exact .inl rfl | exact .inr rfl | cases h

/-- **A `proved` verdict is sound** (every profile). -/
theorem ModProp.verdict_proved :
    ∀ {φ : ModProp (ifaceOf (instOf m))}, φ.verdict m = .proved → ∀ P, φ.Satisfies P (progOf m)
  | .neverCall _, h, P => atomVerdict_neverCall h P
  | .assertNeverFalse _, h, P => atomVerdict_assert h P
  | .neverCallFrom i e, h, P => neverCallFrom_verdict_proved h P
  | .and _ _, h, P =>
    ⟨ModProp.verdict_proved (andVerdict_proved h).1 P, ModProp.verdict_proved (andVerdict_proved h).2 P⟩
  | .callPre _ _, h, _ => by cases h
  | .retPost _ _, h, _ => by cases h
  | .hist _, h, _ => by cases h
  | .terminates _, h, _ => by cases h
  | .ltl _, h, _ => by cases h
  | .ctl _, h, _ => by cases h
  | .tla _, h, _ => by cases h

/-- **A `refuted` verdict is sound** (every specification profile). -/
theorem ModProp.verdict_refuted :
    ∀ {φ : ModProp (ifaceOf (instOf m))}, φ.verdict m = .refuted →
      ∀ nd, ¬ φ.Satisfies (Profile.spec nd {}) (progOf m)
  | .neverCall _, h, nd => atomVerdict_neverCall_refuted h nd
  | .assertNeverFalse _, h, nd => atomVerdict_assert_refuted h nd
  | .neverCallFrom _ _, h, nd => neverCallFrom_verdict_refuted h nd
  | .and _ _, h, nd => by
    rcases andVerdict_refuted h with h₁ | h₂
    · exact fun hs => ModProp.verdict_refuted h₁ nd hs.1
    · exact fun hs => ModProp.verdict_refuted h₂ nd hs.2
  | .callPre _ _, h, _ => by cases h
  | .retPost _ _, h, _ => by cases h
  | .hist _, h, _ => by cases h
  | .terminates _, h, _ => by cases h
  | .ltl _, h, _ => by cases h
  | .ctl _, h, _ => by cases h
  | .tla _, h, _ => by cases h

/-- **A proved request holds** as a task, at every profile. -/
theorem Request.sound (r : Request) (h : r.verdict = .proved) (P : Profile) : (r.task P).Holds :=
  ModProp.verdict_proved h P

/-- **A refuted request fails** at every specification profile. -/
theorem Request.refuted_sound (r : Request) (h : r.verdict = .refuted) (nd : Bool) :
    ¬ (r.task (Profile.spec nd {})).Holds :=
  ModProp.verdict_refuted h nd

end Silmaril.Wasm.Spec.Auto
