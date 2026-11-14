module

public import Silmaril.Proofs.Wasm.FX.Logic.Iris.Adequacy

/-!
# An iris-lean `Language` for WasmFX: adequacy

`IExprFX P fx` (`Silmaril.Wasm.FX.Logic.Iris.Defs`) is an iris-lean `Language` for `StepFX'`
without host calls. **`hwp_of_adequate`**: iris-lean's `adequate` (either stuckness) for
`run code` gives the every-run weakest precondition `HWP` of `Silmaril.Wasm.FX.Logic.EveryRun`, so
results proved through Iris's `wp_adequacy` for this language are every-run results of
`StepFX'` (proofs in `Silmaril.Proofs.Wasm.FX.Logic.Iris.Adequacy`).

Open: a state interpretation with one-shot ownership of continuation slots, and
weakest-precondition rules for `cont.new`, `resume`, `suspend` and handlers in Iris.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.IrisFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (HWP)
open Silmaril.Wasm.Numerics (Profile)
open _root_.Iris.ProgramLogic

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- **Iris adequacy for WasmFX gives the every-run weakest precondition.** -/
theorem hwp_of_adequate {st : _root_.Iris.Stuckness} {s : Store H} {K : Conts} {f : Frame}
    {code : List AdminFX} {Q : PostFX H}
    (had : adequate st (IExprFX.run code : IExprFX P fx) ((s, K, f) : IStateFX H)
      (fun r _ => Q r.store r.conts r.frame r.out)) : HWP P fx s K f code Q :=
  Silmaril.Proofs.Wasm.FX.Logic.IrisFX.hwp_of_adequate had

/-- info: 'Silmaril.Wasm.FX.Logic.IrisFX.hwp_of_adequate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hwp_of_adequate

end Silmaril.Wasm.FX.Logic.IrisFX
