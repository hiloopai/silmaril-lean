module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Typ

/-!
# The 1.0 forward step at non-empty export names, from leg 3

The 1.0 form of `Sim20.Utf8Strip.fwdU20_of_legs`. Take a V1 step `c → c'` from a configuration
typed in `utf8Env10T` (export names may be non-empty), with round 4's other invariants. Then

1. `stripConfig10 c` is typed in `simEnv10T` (`typed10_strip`, leg 2), plain, aligned and
   `GSetOk` (`Utf8Strip10Inv`), and its store has no host function;
2. `stripConfig10 c → stripConfig10 c'` is a V1 step (`step_strip10`);
3. round 4's `Whole.wholeStepFwd10T_one` makes it a step of `simEnv10T` between the images, and
   `Utf8Fix.sstepB_utf8_10T` a step of `utf8Env10T`;
4. leg 3, `Task.unstripStep10`, puts the exports back.

* **`stepFwd10U_strip`**: steps 1 to 3, unconditionally: the stripped step is a step of
  `utf8Env10T` between the stripped images;
* **`stepFwd10U_of_unstrip`**: with leg 3, the step itself is.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 NoHost10 fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T sstepB_utf8_10T bytesB10_utf8)

variable {H : Type} {hn : H → String}

/-- **The store of a configuration typed in `utf8Env10T B` has no host function.** -/
theorem noHost10_of_typedU {B : Builtins} (hB : ∀ ws, B.call "utf8" ws = none) {c : Config H}
    (hc : Typed10 (utf8Env10T B) hn c) : NoHost10 c.store :=
  noHost10_of_strip (Whole.noHost10_of_typedT (Whole.typedV_state_of_typed10T (typed10_strip hB hc)))

/-- **Steps 1 to 3, unconditionally**: a V1 step from a configuration typed in `utf8Env10T`
strips to a step of `utf8Env10T` between the stripped images, and the stripped successor is
typed in `simEnv10T`. -/
theorem stepFwd10U_strip {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (stripConfig10 c') ∧
      SStepB (utf8Env10T (fwdB10 nd r)) (configV hn (stripConfig10 c))
        (configV hn (stripConfig10 c')) := by
  have hB' : ∀ ws, (fwdB10 nd r).call "utf8" ws = none := bytesB10_utf8 _
  have hs := typed10_strip hB' hc
  have hstep := step_strip10 h (noHost10_of_typedU hB' hc)
  obtain ⟨ht', hf⟩ := Whole.wholeStepFwd10T_one hs (plain10_strip hpl) (gSetOk_strip10 hg)
    (memsAligned10_strip hal) hstep
  exact ⟨ht', sstepB_utf8_10T hB' hf⟩

/-- **The 1.0 forward step at non-empty export names, from leg 3.** -/
theorem stepFwd10U_of_unstrip (h₃ : Task.unstripStep10) {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c)
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') :
    SStepB (utf8Env10T (fwdB10 nd r)) (configV hn c) (configV hn c') :=
  h₃ H hn nd r host c c' hc h (stepFwd10U_strip hc hpl hg hal h).2

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
