module

public import Silmaril.Proofs.Wasm.FX.Examples.Gen

/-!
# WasmFX explainer examples: behaviour theorems

The examples of `Silmaril.Wasm.FX.Examples.Defs`, run under `StepFX'`
(`Silmaril.Wasm.Models.FXV`). Exact behaviour sets are stated for the deterministic profile with no
host calls (the hypotheses of `FXAsyncSus.beh_eq_tight`); membership holds at every profile and
host.

* **`gen_beh`**: sum of a generator yielding `1`, `2`, `3`: the only behaviour returns `[6]`;
* **`take_beh`**: take two values from the generator, then drop its continuation: the only
  behaviour returns `[3]`;
* `gen_mem`, `take_mem`: the same results as members of the behaviours at every profile and
  host.

The status of every explainer example is in `docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- **Sum of a generator**: exactly one `StepFX'` behaviour, returning `1 + 2 + 3 = 6`. -/
theorem gen_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx 6 genWY)
      (genProg (Profile.deterministic o) noHost) = {.returns [Val.i32 6]} :=
  Silmaril.Proofs.Wasm.FX.Examples.gen_beh o

/-- The sum is a `StepFX'` behaviour at every profile and host. -/
theorem gen_mem (P : Profile) (host : HostSemantics Nat) :
    Behaviour.returns [Val.i32 6] ∈ behavioursFX' P host (kitFx 6 genWY) (genProg P host) :=
  Silmaril.Proofs.Wasm.FX.Examples.gen_mem P host

/-- **Take two from a generator, then drop it**: exactly one behaviour, returning `3`. -/
theorem take_beh (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx 4 takeWY)
      (takeProg (Profile.deterministic o) noHost) = {.returns [Val.i32 3]} :=
  Silmaril.Proofs.Wasm.FX.Examples.take_beh o

/-- The result is a `StepFX'` behaviour at every profile and host. -/
theorem take_mem (P : Profile) (host : HostSemantics Nat) :
    Behaviour.returns [Val.i32 3] ∈ behavioursFX' P host (kitFx 4 takeWY) (takeProg P host) :=
  Silmaril.Proofs.Wasm.FX.Examples.take_mem P host

/-- info: 'Silmaril.Wasm.FX.Examples.gen_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gen_beh

/-- info: 'Silmaril.Wasm.FX.Examples.take_beh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms take_beh

end Silmaril.Wasm.FX.Examples
