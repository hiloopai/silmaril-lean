module

public import Silmaril.Wasm.Examples.RustInst.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Verify.From.Thms
public import Silmaril.Wasm.Spec.Attest.Core.Thms

@[expose] public section

/-!
# Institutions from Rust: theorems about compiled modules

The modules of `Silmaril.Wasm.Examples.RustInst.Defs` are `rustc` 1.98.1 release builds for
`wasm32-unknown-unknown` of the crates in `examples/wasm-demos/rust-institutions`, quoted with
`wat3!`. The Rust programs call the imports of an institution (`spec.alarm`, `spec.assert`,
`spec.attest`, `door.unlock`, ...) to state their own properties; the sentences below are about
those import calls, in the specification institutions of `Silmaril.Wasm.Spec`, over Silmaril's game
semantics of Core 3.0 (`wasmSem P`).

Every verdict is computed by kernel evaluation (`wasm_check`, `wasm_refute`, `decide +kernel`) of
the verifier `Silmaril.Wasm.Verify.check`/`checkFrom` on the quoted module; its soundness theorems
turn verdicts into `Models` statements. No native evaluation.

* `adder` (exports `add` (0), `add_comm` (1), `checked_add` (2); imports `spec.assert` (0),
  `spec.alarm` (1)): `adder_neverCallFrom_add`: `alarm` is never called while `add` is active;
  `adder_assertNeverFalse`: `assert` never receives `0` (every profile).
* `door` (the PIN door lock; exports `enter` (0), `lock` (1), `status` (2); imports
  `spec.assert` (0), `spec.attest` (1), `door.unlock` (2), `door.alarm` (3), `door.lock` (4)):
  `door_assertNeverFalse` (every profile); `door_neverCallFrom_unlock_status`,
  `door_neverCallFrom_unlock_lock` (every profile).
* `doorBuggy` (PIN comparison inverted): `doorBuggy_not_assertNeverFalse`: `assert` receives `0`
  (the play `enter(0)`), every specification profile.
* Attest (`Silmaril.Wasm.Spec.Attest`): the leaves `leafDoorOpens` ("the buggy lock opens for some
  PIN") and `leafOverflow` ("`checked_add(a, i32::MAX)` overflows for some `a`") import only
  `env.attest`. `leafDoorOpens_attests`, `leafOverflow_attests`: both may attest (verifier
  refutations, every specification profile). `rust_and`: their conjunction, linked through the
  gate, may attest; `rust_and_ff`: the conjunction with the `false` module `ffMod` never does
  (every profile); `rust_or_ff`: the disjunction with `ffMod` may attest.

New (no source). The quoted modules are trusted to be the binaries' decodings (see the Defs
module).
-/

namespace Silmaril.Wasm.Examples.RustInst

open Silmaril.Games Silmaril.Wasm.Verify Silmaril.Wasm.Spec Silmaril.Wasm.Game Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Spec.Attest Silmaril.Wasm.Spec.Attest.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## The adder -/

theorem adder_imports : 1 < (ifaceOf (instOf adder)).imports.length := by decide +kernel

theorem adder_exports : 0 < (ifaceOf (instOf adder)).exports.length := by decide +kernel

/-- **`spec.alarm` is never called while `add` is active**, every profile. -/
theorem adder_neverCallFrom_add (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf adder)
      (⟨1, adder_imports⟩, ⟨0, adder_exports⟩) := by
  wasm_check

/-- **`spec.assert` never receives `0`**, every profile. -/
theorem adder_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf adder)
      ⟨0, by decide +kernel⟩ := by
  wasm_check

/-! ## The door lock -/

theorem door_imports : 4 < (ifaceOf (instOf door)).imports.length := by decide +kernel

theorem door_exports : 2 < (ifaceOf (instOf door)).exports.length := by decide +kernel

/-- **The door lock's `spec.assert` never receives `0`** ("the bolt is released only on the right
PIN", as the program states it), every profile. -/
theorem door_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf door)
      ⟨0, by decide +kernel⟩ := by
  wasm_check

/-- **`door.unlock` is never called while `status` is active**, every profile. -/
theorem door_neverCallFrom_unlock_status (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf door)
      (⟨2, by decide +kernel⟩, ⟨2, door_exports⟩) := by
  wasm_check

/-- **`door.unlock` is never called while `lock` is active**, every profile. -/
theorem door_neverCallFrom_unlock_lock (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf door)
      (⟨2, by decide +kernel⟩, ⟨1, by decide +kernel⟩) := by
  wasm_check

theorem doorBuggy_imports : 0 < (ifaceOf (instOf doorBuggy)).imports.length := by
  decide +kernel

/-- **The buggy lock's `spec.assert` receives `0`** (counterexample: `enter(0)`), every
specification profile. -/
theorem doorBuggy_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf doorBuggy) ⟨0, doorBuggy_imports⟩ := by
  wasm_refute

/-! ## Rust propositions for the Attest encoding -/

/-- The leaf of a module whose only import is `attest` has the module's instance. -/
theorem leafOf_inst {m : Module} (h : (instOf m).imports = [unitFn]) :
    (leafOf m).prog.inst = instOf m := by
  show (⟨[unitFn], (instOf m).exports, (instOf m).addrs, (instOf m).store⟩ : ScalarInstance) =
    instOf m
  rw [← h]

/-- A module whose only import is `attest`, and whose `neverCall attest` the verifier refutes,
may attest, at every specification profile. -/
theorem attests_of_refuted {m : Module} (hm : (instance? m).isSome = true)
    (himp : (instOf m).imports = [unitFn]) (h : (check m (.neverCall 0)).verdict = .refuted)
    (nd : Bool) : Attests (Profile.spec nd {}) (leafOf m) := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  rw [← leafOf_inst himp] at hI
  exact check_refuted_sound_spec (i := attest) hI h nd

/-- **"The buggy lock opens for some PIN"** may attest (the play `try_pin(0)`). -/
theorem leafDoorOpens_attests (nd : Bool) :
    Attests (Profile.spec nd {}) (leafOf leafDoorOpens) :=
  attests_of_refuted (by decide +kernel) (by decide +kernel) (by decide +kernel) nd

/-- **"`checked_add(a, i32::MAX)` overflows for some `a`"** may attest (the play `probe(1)`). -/
theorem leafOverflow_attests (nd : Bool) :
    Attests (Profile.spec nd {}) (leafOf leafOverflow) :=
  attests_of_refuted (by decide +kernel) (by decide +kernel) (by decide +kernel) nd

/-- **The conjunction of the two Rust propositions**, linked through the gate, may attest. -/
theorem rust_and (nd : Bool) :
    MayCall (andM (coreKit (Profile.spec nd {}))
      ((leafOf leafDoorOpens).toAMod (Profile.spec nd {}))
      ((leafOf leafOverflow).toAMod (Profile.spec nd {}))).σ :=
  (mayAttest_and _ _ _).2 ⟨leafDoorOpens_attests nd, leafOverflow_attests nd⟩

/-- **A Rust proposition and `false`** never attest together, every profile. -/
theorem rust_and_ff (P : Profile) :
    ¬ MayCall (andM (coreKit P) ((leafOf leafDoorOpens).toAMod P) ((leafOf ffMod).toAMod P)).σ :=
  fun h => ((mayAttest_and P _ _).1 h).2 (ff_neverCall P)

/-- **`false` or a Rust proposition** may attest. -/
theorem rust_or_ff (nd : Bool) :
    MayCall (orM ((leafOf ffMod).toAMod (Profile.spec nd {}))
      ((leafOf leafOverflow).toAMod (Profile.spec nd {}))).σ :=
  (mayAttest_or _ _ _).2 (.inr (leafOverflow_attests nd))

end Silmaril.Wasm.Examples.RustInst
