module

public import Silmaril.Proofs.Wasm.FX.Examples.Asyncify

/-!
# The sum-of-a-generator example through the asyncify lowering

The explainer-style generator `genW` (`Silmaril.Wasm.FX.Examples`: a generator yielding `1`, `2`,
`3`, summed by main) is a program of the one-shot handler kernel `sstep`
(`Silmaril.Wasm.Models.FXAsync`), and its encoding `genWY` is a WasmFX program of `StepFX'`
(`genProg`). This module links the two to the asyncify lowerings of the kernel:

* **`gen_asyncify`**: the asyncify-compiled program `compP genW` (frames, a heap of saved stacks
  and an unwind/rewind mode instead of continuations and handler frames) called on main returns
  `[6]` and nothing else;
* **`gen_asyncify_pc`**: so does the first-order asyncify machine `fstep` on the annotated
  program `annP (compP genW)` (resume indices, a numeric mode register and frame records,
  `Silmaril.Wasm.Models.FXAsyncPC`);
* **`gen_fx_asyncify`**: the `StepFX'` behaviours of the WasmFX program (deterministic profile, no
  host calls) are exactly the images under `obsB` of the asyncify target's behaviours: the
  WasmFX program and its lowering agree on the result `6`.

The target results follow from the kernel's closed run (60 steps) by the lowering theorems
`FXAsync.lower_correct_init` and `FXAsyncPC.kernel_pc_correct`; no target run is evaluated.
What is not linked: `FXLower`'s instruction-level lowering (`ref.func; cont.new; resume` to a
plain `call_ref`) does not apply, since the generator's continuation does suspend; the asyncify
machines are abstract machines, not Core 3.0 modules (see `Silmaril.Wasm.Models.FXAsyncPC`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (beh Obs tstep compP tInit)
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies rootCode fInit)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

/-- **The asyncify lowering of the generator returns `[6]`, and nothing else.** -/
theorem gen_asyncify :
    beh (tstep (compP genW) i32Test) (tInit 1 []) = {.done [.val (Val.i32 6)]} :=
  Silmaril.Proofs.Wasm.FX.Examples.Asyncify.gen_tgt

/-- **The first-order asyncify machine on the generator returns `[6]`, and nothing else.** -/
theorem gen_asyncify_pc :
    beh (fstep (annP (compP genW)) (bodies (compP genW) (rootCode 1)) i32Test) (fInit 1 []) =
      {.done [.val (Val.i32 6)]} :=
  Silmaril.Proofs.Wasm.FX.Examples.Asyncify.gen_pc

/-- **The WasmFX generator and its asyncify lowering have the same behaviours** (through
`obsB`). -/
theorem gen_fx_asyncify (o : GrowKind → Nat → Nat → Nat → Bool) :
    behavioursFX' (Profile.deterministic o) noHost (kitFx 6 genWY)
        (genProg (Profile.deterministic o) noHost) =
      obsB '' beh (tstep (compP genW) i32Test) (tInit 1 []) :=
  Silmaril.Proofs.Wasm.FX.Examples.Asyncify.gen_fx_eq_tgt o

/-- info: 'Silmaril.Wasm.FX.Examples.gen_fx_asyncify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gen_fx_asyncify

/-- info: 'Silmaril.Wasm.FX.Examples.gen_asyncify_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gen_asyncify_pc

end Silmaril.Wasm.FX.Examples
