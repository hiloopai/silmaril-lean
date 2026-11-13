module

public import Silmaril.Wasm.Verify.Litmus.Defs
public import Silmaril.Wasm.Verify.Check.Thms

@[expose] public section

/-!
# Litmus tests for the verifier

On the real Core 3.0 modules of `Silmaril.Wasm.Verify.Litmus.Defs`. Every verdict is computed by
kernel evaluation (`decide +kernel`) of `check`, i.e. of silmaril-lean's `validate?`,
`instantiateOnce?` (or `prepare?`), the analyses and, for refutations, silmaril-lean's verified
interpreter; no compiled evaluation.

`neverCall 0`:

* `modDead_verdict`: `proved`, reachable set `[1]`; `modDead_neverCall` (`wasm_check`, every
  profile; non-vacuous: `modDead_instance`).
* `modOne_verdict`, `modIndirect_verdict`: **`refuted`**, counterexample `run()` calling
  `assert(1)`, resp. `assert(0)` through the table; `modZero_not_neverCall` (`wasm_refute`, every
  specification profile).
* `modStart_verdict`: `unknown`, the start function calls `assert`.
* `modStartOk_verdict`: **`proved` with the instantiation phase**; `modStartOk_neverCall`: no play
  of the strategy with the specification's instantiation phase asks `assert`, every profile
  (non-vacuous: `modStartOk_spec` computes the spec instance).

`assertNeverFalse 0`:

* guarded calls: `modOne_assert`, `modNested_assert`, `modDead_assert`: `proved` (`guarded`);
  `modOne_assertNeverFalse`, `modNested_assertNeverFalse` (`wasm_check`, every profile).
* the flow analysis: `modGuardParam_assert` (`if x then assert(x)`), `modSetLocal_assert`
  (`x := 1; assert(x)`), `modLoopLocal_assert` (facts through a loop, a block and an `if`):
  `proved` (`flowGuarded`); the semantic theorems `…_assertNeverFalse` (every profile).
* refutations: `modZero_assert`, `modParam_assert` (`check(0)`), `modIndirect_assert`,
  `modBranch_verdict` (`run(1)`; the candidate `0` does not reach the call), `modSetZero_assert`
  (`x := 0; assert(x)`): `refuted`; `…_not_assertNeverFalse` (`wasm_refute`, every specification
  profile).
* `modStart_assert_verdict`: `unknown`, start function.

`neverCallFrom (0, e)`, per export (`checkFrom`):

* `modTwo` (export `a` calls `assert(1)` and a helper, export `b` calls only the helper):
  `modTwo_from_b`: **`proved`** (callable set `[2, 3]`, no escaping function);
  `modTwo_neverCallFrom_b` (`wasm_check`, every profile). `modTwo_from_a`: **`refuted`**
  (`a()` calls `assert(1)`); `modTwo_not_neverCallFrom_a` (`wasm_refute`, every specification
  profile). The whole-module analysis cannot prove the first: `modTwo_verdict` (`neverCall 0`
  is refuted).
* `modEscape` (function 3 calls `assert(1)` and escapes through the table): `modEscape_from_b`
  (`b` calls it through `call_indirect`): **`refuted`**; `modEscape_not_neverCallFrom_b`.
  `modEscape_from_c` (`c` only takes its reference) and `modEscape_from_a` (`a` does nothing):
  `unknown`, `reaches [3, 0]`: every export may call every escaping function.
-/

namespace Silmaril.Wasm.Verify.Litmus

open Silmaril.Games Silmaril.Wasm.Verify Silmaril.Wasm.Spec Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem modDead_verdict :
    check modDead (.neverCall 0) = ⟨.proved, .unreachable [1]⟩ := by decide +kernel

theorem modDead_instance : (instance? modDead).isSome = true := by decide +kernel

/-- `modDead` has one import. -/
theorem modDead_imports : 0 < (ifaceOf (instOf modDead)).imports.length := by decide +kernel

/-- **`modDead` never calls `assert`**, every profile. -/
theorem modDead_neverCall (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modDead)
      ⟨0, modDead_imports⟩ := by
  wasm_check

theorem modOne_verdict :
    check modOne (.neverCall 0) = ⟨.refuted, .counterexample ⟨0, [], [Val.i32 1]⟩⟩ := by
  decide +kernel

theorem modIndirect_verdict :
    check modIndirect (.neverCall 0) = ⟨.refuted, .counterexample ⟨0, [], [Val.i32 0]⟩⟩ := by
  decide +kernel

theorem modStart_verdict : check modStart (.neverCall 0) = ⟨.unknown, .startFunction true⟩ := by
  decide +kernel

/-! ## Assertions -/

theorem modOne_assert : check modOne (.assertNeverFalse 0) = ⟨.proved, .guarded [1]⟩ := by
  decide +kernel

theorem modOne_instance : (instance? modOne).isSome = true := by decide +kernel

theorem modOne_imports : 0 < (ifaceOf (instOf modOne)).imports.length := by decide +kernel

/-- **`modOne` never calls `assert` with `false`**, every profile. -/
theorem modOne_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf modOne)
      ⟨0, modOne_imports⟩ := by
  wasm_check

theorem modNested_assert : check modNested (.assertNeverFalse 0) = ⟨.proved, .guarded [1]⟩ := by
  decide +kernel

theorem modNested_imports : 0 < (ifaceOf (instOf modNested)).imports.length := by decide +kernel

/-- **`modNested` never calls `assert` with `false`**, every profile. -/
theorem modNested_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf modNested)
      ⟨0, modNested_imports⟩ := by
  wasm_check

theorem modDead_assert : check modDead (.assertNeverFalse 0) = ⟨.proved, .guarded [1]⟩ := by
  decide +kernel

theorem modZero_assert :
    check modZero (.assertNeverFalse 0) = ⟨.refuted, .counterexample ⟨0, [], [Val.i32 0]⟩⟩ := by
  decide +kernel

theorem modParam_assert :
    check modParam (.assertNeverFalse 0) =
      ⟨.refuted, .counterexample ⟨0, [Val.i32 0], [Val.i32 0]⟩⟩ := by
  decide +kernel

theorem modIndirect_assert :
    check modIndirect (.assertNeverFalse 0) =
      ⟨.refuted, .counterexample ⟨0, [], [Val.i32 0]⟩⟩ := by
  decide +kernel

theorem modStart_assert :
    check modStart (.assertNeverFalse 0) = ⟨.unknown, .startFunction true⟩ := by
  decide +kernel

/-! ## Refutations -/

theorem modZero_imports : 0 < (ifaceOf (instOf modZero)).imports.length := by decide +kernel

/-- **`modZero` calls `assert`** (counterexample: `run()`), every specification profile. -/
theorem modZero_not_neverCall (nd : Bool) :
    ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modZero) ⟨0, modZero_imports⟩ := by
  wasm_refute

/-- **`modZero` calls `assert` with `false`**, every specification profile. -/
theorem modZero_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modZero) ⟨0, modZero_imports⟩ := by
  wasm_refute

theorem modParam_imports : 0 < (ifaceOf (instOf modParam)).imports.length := by decide +kernel

/-- **`modParam` calls `assert` with `false`** (counterexample: `check(0)`), every specification
profile. -/
theorem modParam_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modParam) ⟨0, modParam_imports⟩ := by
  wasm_refute

theorem modIndirect_imports : 0 < (ifaceOf (instOf modIndirect)).imports.length := by
  decide +kernel

/-- **`modIndirect` calls `assert` with `false`** through its table, every specification
profile. -/
theorem modIndirect_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modIndirect) ⟨0, modIndirect_imports⟩ := by
  wasm_refute

theorem modBranch_verdict :
    check modBranch (.assertNeverFalse 0) =
      ⟨.refuted, .counterexample ⟨0, [Val.i32 1], [Val.i32 0]⟩⟩ := by
  decide +kernel

theorem modBranch_imports : 0 < (ifaceOf (instOf modBranch)).imports.length := by decide +kernel

/-- **`modBranch` calls `assert(0)` when its argument is nonzero** (counterexample: `run(1)`; the
candidate `0` does not reach the call), every specification profile. -/
theorem modBranch_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modBranch) ⟨0, modBranch_imports⟩ := by
  wasm_refute

/-! ## Start functions -/

theorem modStartOk_verdict :
    check modStartOk (.neverCall 0) = ⟨.proved, .unreachable [2, 1]⟩ := by
  decide +kernel

theorem modStartOk_spec : (specInstance? modStartOk).isSome = true := by decide +kernel

/-- **`modStartOk` never calls `assert`, instantiation included**: no play of its strategy with
the specification's instantiation phase (segment initialisation, then the start function), at
any profile, asks import `0`. -/
theorem modStartOk_neverCall (P : Profile)
    {p : List (Move (specInstOf modStartOk modStartOk_spec).2.1.E
      ((specInstOf modStartOk modStartOk_spec).2.1.F.withInst (Behaviour Val)))}
    (hp : p ∈ ((specInstOf modStartOk modStartOk_spec).2.1.specStrategy P
      (specInstOf modStartOk modStartOk_spec).2.2).toStrategy) :
    ∀ e, (.inl (.ask e) : Move (specInstOf modStartOk modStartOk_spec).2.1.E
      ((specInstOf modStartOk modStartOk_spec).2.1.F.withInst (Behaviour Val))) ∈ p →
      e.1.val ≠ 0 :=
  check_start_module modStartOk_spec (by decide +kernel) (by decide +kernel) P hp

theorem modStart_assert_verdict :
    check modStart (.assertNeverFalse 0) = ⟨.unknown, .startFunction true⟩ := by
  decide +kernel

/-! ## Arguments through locals (the flow analysis) -/

theorem modGuardParam_assert :
    check modGuardParam (.assertNeverFalse 0) = ⟨.proved, .flowGuarded [1]⟩ := by
  decide +kernel

theorem modGuardParam_imports : 0 < (ifaceOf (instOf modGuardParam)).imports.length := by
  decide +kernel

/-- **`check(x)` asserts its parameter only after testing it**: never `false`, every profile. -/
theorem modGuardParam_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf modGuardParam)
      ⟨0, modGuardParam_imports⟩ := by
  wasm_check

theorem modSetLocal_assert :
    check modSetLocal (.assertNeverFalse 0) = ⟨.proved, .flowGuarded [1]⟩ := by
  decide +kernel

theorem modSetLocal_imports : 0 < (ifaceOf (instOf modSetLocal)).imports.length := by
  decide +kernel

/-- **`x := 1; assert(x)`**: never `false`, every profile. -/
theorem modSetLocal_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf modSetLocal)
      ⟨0, modSetLocal_imports⟩ := by
  wasm_check

theorem modLoopLocal_assert :
    check modLoopLocal (.assertNeverFalse 0) = ⟨.proved, .flowGuarded [1]⟩ := by
  decide +kernel

theorem modLoopLocal_imports : 0 < (ifaceOf (instOf modLoopLocal)).imports.length := by
  decide +kernel

/-- **Facts through loops, blocks and branches**: never `false`, every profile. -/
theorem modLoopLocal_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf modLoopLocal)
      ⟨0, modLoopLocal_imports⟩ := by
  wasm_check

theorem modSetZero_assert :
    check modSetZero (.assertNeverFalse 0) = ⟨.refuted, .counterexample ⟨0, [], [Val.i32 0]⟩⟩ := by
  decide +kernel

theorem modSetZero_imports : 0 < (ifaceOf (instOf modSetZero)).imports.length := by
  decide +kernel

/-- **`x := 0; assert(x)` calls `assert` with `false`**, every specification profile. -/
theorem modSetZero_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modSetZero) ⟨0, modSetZero_imports⟩ := by
  wasm_refute

/-! ## Per export -/

theorem modTwo_verdict :
    check modTwo (.neverCall 0) = ⟨.refuted, .counterexample ⟨0, [], [Val.i32 1]⟩⟩ := by
  decide +kernel

theorem modTwo_from_b : checkFrom modTwo 0 1 = ⟨.proved, .unreachableFrom [2, 3] []⟩ := by
  decide +kernel

theorem modTwo_from_a :
    checkFrom modTwo 0 0 = ⟨.refuted, .counterexample ⟨0, [], [Val.i32 1]⟩⟩ := by
  decide +kernel

theorem modTwo_instance : (instance? modTwo).isSome = true := by decide +kernel

theorem modTwo_imports : 0 < (ifaceOf (instOf modTwo)).imports.length := by decide +kernel

theorem modTwo_exports : 1 < (ifaceOf (instOf modTwo)).exports.length := by decide +kernel

/-- **`modTwo` never calls `assert` while `b` is active**, every profile (although `a` does). -/
theorem modTwo_neverCallFrom_b (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf modTwo)
      (⟨0, modTwo_imports⟩, ⟨1, modTwo_exports⟩) := by
  wasm_check

/-- **`modTwo` calls `assert` while `a` is active** (counterexample: `a()`), every specification
profile. -/
theorem modTwo_not_neverCallFrom_a (nd : Bool) :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modTwo) (⟨0, modTwo_imports⟩, ⟨0, by decide +kernel⟩) := by
  wasm_refute

theorem modEscape_from_a : checkFrom modEscape 0 0 = ⟨.unknown, .reaches [3, 0]⟩ := by
  decide +kernel

theorem modEscape_from_b :
    checkFrom modEscape 0 1 = ⟨.refuted, .counterexample ⟨1, [], [Val.i32 1]⟩⟩ := by
  decide +kernel

theorem modEscape_from_c : checkFrom modEscape 0 2 = ⟨.unknown, .reaches [3, 0]⟩ := by
  decide +kernel

theorem modEscape_imports : 0 < (ifaceOf (instOf modEscape)).imports.length := by decide +kernel

/-- **`modEscape` calls `assert` while `b` is active**, through the escaping reference
(counterexample: `b()`), every specification profile. -/
theorem modEscape_not_neverCallFrom_b (nd : Bool) :
    ¬ Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf modEscape) (⟨0, modEscape_imports⟩, ⟨1, by decide +kernel⟩) := by
  wasm_refute

end Silmaril.Wasm.Verify.Litmus
