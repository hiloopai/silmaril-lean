module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Conv

/-!
# Non-vacuity: a generator that suspends has exactly one `StepFX'` behaviour

The generator example `exW` of `Silmaril.Proofs.Wasm.Models.FXAsyncFX` (function `0` yields `1`
with `suspend`, function `2` handles the yield by resuming it under a fresh handler and adding
the yielded value to its result) suspends with exactly its payload on the frame. So it is in the
tight fragment (`ex_tight`, by a closed evaluation `checkTight`), and **`ex_beh`**: the WasmFX
program `fxInit (exS P noHost) 1 []` has exactly one `StepFX'` behaviour in the deterministic
profile, returning `[3]`. Before this pass only `[3] ∈ …` was known (`ex_fx`); the other splits
of its `suspend` (`suspend_nondet`) are dead ends.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SV SFrame SCfg Ins Prog sstep runN beh Res Obs Outcome sInit
  allVals)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (exW exS exFx exOk ex_kernel_run supported_of_checkRun
  ex_check)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- Check `tightCfg` along at most `fuel` steps of the kernel run, which must stop. -/
def checkTight (W : Prog (Ins Val)) : Nat → SCfg Val → Bool
  | 0, _ => false
  | fuel + 1, x =>
    tightCfg x &&
      match sstep W i32Test x with
      | .next y => checkTight W fuel y
      | .stop _ => true

theorem tight_of_checkTight {W : Prog (Ins Val)} :
    ∀ (fuel : Nat) (x : SCfg Val), checkTight W fuel x = true →
      ∀ n y, runN (sstep W i32Test) n x = .next y → tightCfg y = true
  | 0, _, h => nomatch h
  | fuel + 1, x, h => by
    have h' : tightCfg x = true ∧ (match sstep W i32Test x with
        | .next y => checkTight W fuel y
        | .stop _ => true) = true := by
      simpa only [checkTight, Bool.and_eq_true] using h
    intro n y hy
    cases n with
    | zero => cases hy; exact h'.1
    | succ n =>
      cases hx : sstep W i32Test x with
      | next x' =>
        have h'' : checkTight W fuel x' = true := by simpa only [hx] using h'.2
        exact tight_of_checkTight fuel x' h'' n y (by simpa only [runN, hx] using hy)
      | stop o => simp only [runN, hx, reduceCtorEq] at hy

/-- The generator's kernel run is in the tight fragment. -/
theorem ex_tight : TightSupported exW (sInit 1 (([] : List Val).map .val)) :=
  ⟨supported_of_checkRun 40 _ ex_check, tight_of_checkTight 40 _ rfl⟩

/-- **A suspending WasmFX program with exactly one `StepFX'` behaviour.** -/
theorem ex_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost exFx
      (fxInit (exS (Profile.deterministic o) noHost) 1 []) = {.returns [Val.i32 3]} := by
  have h := beh_eq_tight (exS (Profile.deterministic o) noHost) (o := o) rfl rfl
    (exOk _ _) (rel_init (exS (Profile.deterministic o) noHost) 1 []) ex_tight
  rw [show behavioursFX' (Profile.deterministic o) noHost exFx
      (fxInit (exS (Profile.deterministic o) noHost) 1 []) = _ from h,
    show sInit 1 (([] : List Val).map SV.val) = sInit 1 [] from rfl,
    Silmaril.Proofs.Wasm.Models.FXAsync.beh_of_stop ex_kernel_run]
  simp [obsB, Outcome.toObs, allVals]

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
