module

public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Execution.Callout.Progress.Defs

public import Silmaril.Wasm.Lime1.Execution.Callout.Properties

/-!
# Progress of the executable Lime1 stepper

`Callout/Properties.lean` proves `step?_sound`: every step of the executable host-free stepper
`Lime1.Execution.step?` is a step of `Internal = Step noHostCalls`. This file proves the
converse direction at the level of *enabledness*:

* `step?_progress`: if a configuration has some `Internal` step, `step?` finds a step (possibly a
  different one, see below);
* `step?_eq_none_iff`: `step? cfg = none` exactly when `cfg` has no `Internal` step, i.e. the
  configuration is terminal (a value sequence or a lone trap), parked at a host callout
  (`CalloutAt`, see `CalloutAt.not_internal`), or stuck (ill-typed or dangling runtime state);
* `run_stuck` and `run_stuck_iff`: the driver `run` reports `Status.stuck` only for a
  configuration that is not terminal, not a callout and has no `Internal` step, and on such a
  configuration (with fuel left) it reports exactly that.

The proof is by induction on the `Step` derivation: `Internal.head_not_branch` shows that the
first non-value instruction of code that steps is never a bare `br`/`return` (those only reduce
through an enclosing label or frame), which rules out the cases where `stepHead?` declines a
label or frame; `Internal.stepFrom?_isSome` then shows the scan of `stepFrom?` reaches a redex
for any operand stack prefix and any trailing code. No `stepInstr?` case was missing, so
`Callout.lean` is unchanged.

## Deterministic choices of `stepInstr?`

`Step` is nondeterministic in three places; `step?` resolves each deterministically, and each
resolution is one of the permitted transitions (this is already part of `step?_sound`; the
lemmas `floatUnOp_choice_permitted`, `floatBinOp_choice_permitted`,
`convert_choice_permitted` and `memoryGrow_choice_permitted` restate it for readers):

* float unary/binary operators and conversions (the rules `floatUnary`, `floatBinary`,
  `convert` admit any permitted NaN payload via `Numerics.floatUnOpRel`, `floatBinOpRel`,
  `convertRel`): `step?` returns the deterministic results `Numerics.floatUnOp`,
  `Numerics.floatBinOp`, `Numerics.convert`;
* `memory.grow` (the rule `memoryGrow` with `Memory.Grow`, which always admits failure with
  result `-1` and the memory unchanged): `step?` grows exactly when `Memory.grow?` succeeds,
  returning the old size in pages, and fails otherwise.

Hence `step?_progress` is progress, not completeness: a nondeterministic `Internal` step (a
different NaN payload, or a `memory.grow` failure where growth was possible) is not claimed to
be the step `step?` takes. Not claimed either: anything about fuel exhaustion (`run` with fuel
`0` never reports `stuck`), or about host callouts, which are not `Internal` steps.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-! ## Scanning lemmas -/

section Scan

variable {H : Type*} (s : Store H) (f : Frame)

end Scan

/-! ## Progress -/

theorem step?_isSome_iff {H : Type*} {cfg : Config H} :
    (step? cfg).isSome ↔ ∃ cfg', Internal cfg cfg' := by
  constructor
  · intro h
    obtain ⟨cfg', h'⟩ := Option.isSome_iff_exists.mp h
    exact ⟨cfg', step?_sound h'⟩
  · rintro ⟨cfg', h⟩
    exact step?_progress h

/-- `step?` fails exactly on configurations without a host-free step: terminal ones, those
parked at a callout, and stuck ones. -/
theorem step?_eq_none_iff {H : Type*} {cfg : Config H} :
    step? cfg = none ↔ ¬ ∃ cfg', Internal cfg cfg' := by
  rw [← step?_isSome_iff, Option.not_isSome_iff_eq_none]

/-! ## Deterministic choices (restated from `step?_sound`) -/

/-- Float unary results: the deterministic `Numerics.floatUnOp` is permitted. -/
theorem floatUnOp_choice_permitted (t : FloatType) (op : FloatUnOp) (x : BitVec t.width) :
    Numerics.floatUnOpRel t op x (Numerics.floatUnOp t op x) :=
  Numerics.floatUnOpRel_self t op x

/-- Float binary results: the deterministic `Numerics.floatBinOp` is permitted. -/
theorem floatBinOp_choice_permitted (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width) :
    Numerics.floatBinOpRel t op x y (Numerics.floatBinOp t op x y) :=
  Numerics.floatBinOpRel_self t op x y

/-- Conversions: the deterministic `Numerics.convert` is permitted. -/
theorem convert_choice_permitted (op : ConvertOp) (x : Numerics.NumValue op.source) :
    Numerics.convertRel op x (Numerics.convert op x) :=
  Numerics.convertRel_self op x

/-- `memory.grow`: `stepInstr?` grows exactly when `Memory.grow?` succeeds (result: the old size
in pages) and fails otherwise (result `-1`, memory unchanged); both are `Memory.Grow`
outcomes. -/
theorem memoryGrow_choice_permitted (memory : Memory.Bytes) (maximum : Option Nat)
    (delta : Nat) :
    Memory.Grow memory maximum delta ((Memory.grow? memory maximum delta).getD memory)
      (if (Memory.grow? memory maximum delta).isSome then
        BitVec.ofNat 32 (Memory.size memory) else -1) := by
  cases h : Memory.grow? memory maximum delta with
  | none => exact .failure
  | some bytes => exact .success bytes h

/-! ## Terminal configurations and the driver -/

private theorem value_ne_trap (v : Value) : value v ≠ .trap := by
  rcases v with ⟨(t | t), b⟩ <;> simp [value]

theorem terminal?_result (r : Result) : terminal? (result r) = some r := by
  cases r with
  | trap => rfl
  | values vs =>
    unfold terminal?
    split
    · next h =>
      cases vs with
      | nil => simp [result, values] at h
      | cons v vs =>
        simp only [result, values, List.map_cons, List.cons.injEq] at h
        exact (value_ne_trap v h.1).elim
    · simp [result]

/-- `terminal?` fails exactly on code that is not a final result. -/
theorem terminal?_eq_none_iff {code : List Admin} :
    terminal? code = none ↔ ∀ r, code ≠ result r := by
  constructor
  · rintro h r rfl
    simp [terminal?_result] at h
  · intro h
    cases ht : terminal? code with
    | none => rfl
    | some r => exact (h r (terminal?_sound ht)).elim

/-- What `Status.stuck` means: the configuration `run` stops at is not terminal, not parked at
a callout, and has no host-free step. -/
theorem run_stuck {H : Type*} {n : Nat} {cfg final : Config H}
    (h : run n cfg = (final, .stuck)) :
    terminal? final.code = none ∧ (∀ c, ¬ CalloutAt final c) ∧ ¬ ∃ cfg', Internal final cfg' := by
  induction n generalizing cfg with
  | zero =>
    rw [run] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | succ m ih =>
    rw [run] at h
    split at h
    · simp at h
    · next hterm =>
      split at h
      · simp at h
      · next hdec =>
        split at h
        · next next hs => exact ih h
        · next hs =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          refine ⟨hterm, fun c hc => ?_, step?_eq_none_iff.mp hs⟩
          have := exists_callout_iff.mp ⟨c, hc⟩
          simp [hdec] at this

/-- **Characterisation of `Status.stuck`.** With fuel left, `run` stops at `cfg` itself with
status `stuck` iff `cfg` is not terminal, not parked at a callout, and has no host-free step. -/
theorem run_stuck_iff {H : Type*} (n : Nat) (cfg : Config H) :
    run (n + 1) cfg = (cfg, .stuck) ↔
      terminal? cfg.code = none ∧ (∀ c, ¬ CalloutAt cfg c) ∧ ¬ ∃ cfg', Internal cfg cfg' := by
  constructor
  · exact run_stuck
  · rintro ⟨hterm, hcall, hstep⟩
    have hdec : decompose? cfg = none := by
      cases hd : decompose? cfg with
      | none => rfl
      | some c => exact (hcall c (decompose?_sound hd)).elim
    rw [run, hterm, hdec, step?_eq_none_iff.mpr hstep]

/-! ## Tests -/

namespace CalloutExamples

/-- The initial configuration of the callout example takes an invocation step, so `step?`
steps it. -/
theorem start_progress (x : BitVec 32) : (step? (start x)).isSome :=
  step?_progress (Step.invokeWasm callerStore ⟨[], callerInst⟩ ⟨1⟩ unaryType callerInst callerCode
    [.int .i32 x] rfl rfl)

/-- The parked configuration has no host-free step, so `step?` fails there. -/
theorem parked_step?_none (x : BitVec 32) : step? (parked x) = none :=
  step?_eq_none_iff.mpr fun ⟨cfg, h⟩ => parked_no_internal x cfg h

/-- The same fact, computed. -/
theorem parked_step?_none' (x : BitVec 32) : step? (parked x) = none := rfl

end CalloutExamples

end Silmaril.Wasm.Lime1.Execution
