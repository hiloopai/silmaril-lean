module

public import Silmaril.Proofs.Wasm.FX.Examples.EveryRun.Switch
public import Silmaril.Proofs.Wasm.FX.Examples.EveryRun.CancelRun
public import Silmaril.Proofs.Wasm.FX.Examples.EveryRun.SwitchRun

/-!
# WasmFX examples by the every-run logic: exact behaviour sets

Each program is proved **totally safe** in the every-run logic `Silmaril.Wasm.FX.Logic.EveryRun`
(every run that finishes satisfies the postcondition, and no run is infinite), at **every
profile**, without host calls; one run reaching the result comes from the existential calculus
`Silmaril.Wasm.FX.Logic` or from `Silmaril.Wasm.FX.Examples` (`gen_mem`, `take_mem`). The adequacy
theorem `TSafe.behaviours_eq` then gives the exact `StepFX'` behaviour set.

* **`gen_beh`**: sum of a generator, exactly `{returns [6]}` (the earlier
  `Silmaril.Wasm.FX.Examples.gen_beh` holds at the deterministic profile only);
* **`take_beh`**: take two from a generator, then drop it, exactly `{returns [3]}`;
* **`cancel_beh`**: cancelling the generator with `resume_throw` at its first yield, exactly
  `{throws 0}`;
* **`switch_beh`**: switching between two coroutines with `switch`, exactly `{returns [42]}`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

/-- **Sum of a generator**, by the every-run logic: at every profile, exactly one behaviour,
returning `1 + 2 + 3 = 6`. -/
theorem gen_beh (P : Profile) :
    behavioursFX' P noHost (kitFx 6 genWY) (genProg P noHost) = {.returns [Val.i32 6]} :=
  Silmaril.Proofs.Wasm.FX.Examples.EveryRun.gen_beh P

/-- **Take two from a generator, then drop it**, by the every-run logic: exactly one behaviour,
returning `1 + 2 = 3`. -/
theorem take_beh (P : Profile) :
    behavioursFX' P noHost (kitFx 4 takeWY) (takeProg P noHost) = {.returns [Val.i32 3]} :=
  Silmaril.Proofs.Wasm.FX.Examples.EveryRun.take_beh P

/-- **Cancelling a generator with `resume_throw`**: exactly one behaviour, the exception at
address `0`. -/
theorem cancel_beh (P : Profile) :
    behavioursFX' P noHost (kitFx 2 cancelWY) (cancelProg P noHost) = {.throws 0} :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_behaviours_eq_result (r₀ := .throw 0)
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.cancel_tsafe (fun _ _ _ _ h => h)
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.cancel_mem

/-- **Switching between two coroutines**: exactly one behaviour, returning `42`. -/
theorem switch_beh (P : Profile) :
    behavioursFX' P noHost swFx switchProg = {.returns [Val.i32 42]} :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_behaviours_eq
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.switch_tsafe (fun _ _ _ _ h => h)
    Silmaril.Proofs.Wasm.FX.Examples.EveryRun.switch_mem

/-- info: 'Silmaril.Wasm.FX.Examples.EveryRun.gen_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gen_beh

/-- info: 'Silmaril.Wasm.FX.Examples.EveryRun.take_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms take_beh

/-- info: 'Silmaril.Wasm.FX.Examples.EveryRun.cancel_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cancel_beh

/-- info: 'Silmaril.Wasm.FX.Examples.EveryRun.switch_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms switch_beh

end Silmaril.Wasm.FX.Examples.EveryRun
