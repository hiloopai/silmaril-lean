module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Unstrip

/-!
# The 1.0 forward run at non-empty export names, from leg 3

* **`stepFwd10U_typed`**: unconditionally, the successor of a V1 step from a configuration typed
  in `utf8Env10T` (with round 4's other invariants) is typed in `utf8Env10T`;
* **`wholeRunFwd10U_of_unstrip`**: round 4's `Whole.wholeRunFwd10T` with typing read in the
  fixed script `fixedU10` (`utf8Env10T`), so export names may be non-empty, given leg 3
  (`Task.unstripStep10`): every V1 run is a run of `utf8Env10T` between the images, and its
  last configuration is typed there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps)
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim10.Whole (Plain10 MemsAligned10 fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T bytesB10_utf8)

variable {H : Type} {hn : H → String}

/-- **Typing in `utf8Env10T` is kept by a V1 step**, under round 4's other invariants. -/
theorem stepFwd10U_typed {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    Typed10 (utf8Env10T (fwdB10 nd r)) hn c' :=
  typed10U_succ (bytesB10_utf8 _) hc h (stepFwd10U_strip hc hpl hg hal h).1

/-- **The 1.0 forward run in the fixed script `fixedU10`, from leg 3**: export names may be
non-empty. -/
theorem wholeRunFwd10U_of_unstrip (h₃ : Task.unstripStep10) {host : HostSemantics H}
    {nd : Bool} {r : RelaxedChoice} {c c' : Config H}
    (hc : Typed10 (utf8Env10T (fwdB10 nd r)) hn c) (hpl : Plain10 c.code)
    (hal : MemsAligned10 c.store) (hg : ∀ d, Steps host c d → GSetOk d.store d.frame d.code)
    (h : Steps host c c') :
    Typed10 (utf8Env10T (fwdB10 nd r)) hn c' ∧
      Relation.ReflTransGen (SStepB (utf8Env10T (fwdB10 nd r))) (configV hn c)
        (configV hn c') := by
  induction h with
  | refl => exact ⟨hc, .refl⟩
  | @tail b d hcb hbd ih =>
    have hnh := noHost10_of_typedU (bytesB10_utf8 _) hc
    have hal' : MemsAligned10 b.store := (Whole.memsAligned10_steps hcb hnh hal).2
    have hpl' : Plain10 b.code := Whole.plain10_steps hcb hpl
    exact ⟨stepFwd10U_typed ih.1 hpl' (hg b hcb) hal' hbd,
      ih.2.tail (stepFwd10U_of_unstrip h₃ ih.1 hpl' (hg b hcb) hal' hbd)⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
