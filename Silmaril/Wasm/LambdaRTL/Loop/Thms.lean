module

public import Silmaril.Wasm.LambdaRTL.Loop.Defs
public import Silmaril.Wasm.LambdaRTL.Thms
public import Silmaril.Semantics.Elgot.Thms
import Silmaril.Proofs.Wasm.LambdaRTL.Loop.Run

/-!
# The whole Wasm fragment in λRTL with loops: checked results

Every function `f` of the structured numeric fragment (`loop` included) is translated
(`trBodyL f`, a region of λRTL with loops). For arguments of the parameter types and any λRTL
store `σ` holding the initial locals (`InitStore f args σ`, e.g. `initStore f args`), in the
model `modelL` (monad `LM = ExceptT WErr Part`):

* `trBodyL_run_iff`: `f.Run args o ↔ ((trBodyL f).evalObs modelL σ).run = Part.some (obsOfL o)`
  for every call outcome `o` (a return with its value, or a trap);
* `trBodyL_noRun_iff`: the fragment has no derivation for the call exactly when the λRTL run is
  stuck (`Part.some (.error .stuck)`) **or diverges** (`Part.none`). The fragment's big-step
  `Run` has no divergence derivation, so it cannot tell a stuck call from a divergent one; the
  λRTL side can, but no statement here relates the two λRTL cases to separate fragment notions;
* `trBodyL_evalObs_of_eval`: a result of the fragment's computable interpreter is the λRTL
  observation (the bridge used by the examples, since `Part` is not computable);
* `trBodyL_agrees_trFunc`: on loop-free functions the loop-free translation
  (`Silmaril.Wasm.LambdaRTL.trFunc`, model `model`) and this one agree on returns and traps, and
  the former is stuck exactly when this one is stuck or divergent.

Examples: `exampleSum` (a `loop` summing `10 + … + 1`) observes `55` in λRTL;
`exampleSpin` (`loop { br 0 }`) diverges in λRTL, hence has no fragment run.

The proofs (`Silmaril.Proofs.Wasm.LambdaRTL.Loop.*`) are a forward simulation of interpreter
results (`fwd`, by induction on fuel; a branch to the loop's label re-enters the λRTL loop) and a
backward simulation of terminating non-stuck λRTL results (`bwd`, by induction on expressions,
with an induction on the finite run of `Part`'s iteration for `loop`). The iteration of `LM`
routes errors out of the loop; no Elgot law of `LM` is used or claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut exampleSum)

/-- **Exact simulation of runs and traps, with loops.** -/
theorem trBodyL_run_iff {f : FragFunc} {args : List WVal} (hargs : args.map WVal.type = f.params)
    {σ : Store} (hσ : InitStore f args σ) (o : FOut) :
    f.Run args o ↔ ((trBodyL f).evalObs modelL σ).run = Part.some (obsOfL o) :=
  Silmaril.Proofs.Wasm.LambdaRTL.trBodyL_run_iff hargs hσ o

/-- **No fragment derivation = λRTL stuck or divergent.** -/
theorem trBodyL_noRun_iff {f : FragFunc} {args : List WVal}
    (hargs : args.map WVal.type = f.params) {σ : Store} (hσ : InitStore f args σ) :
    (¬ ∃ o, f.Run args o) ↔
      (((trBodyL f).evalObs modelL σ).run = Part.some (.error .stuck) ∨
        ((trBodyL f).evalObs modelL σ).run = Part.none) :=
  Silmaril.Proofs.Wasm.LambdaRTL.trBodyL_noRun_iff hargs hσ

/-- An interpreter result is the λRTL observation. -/
theorem trBodyL_evalObs_of_eval {f : FragFunc} {args : List WVal} {n : Nat} {o : FOut}
    (h : f.eval n args = some o) :
    ((trBodyL f).evalObs modelL (initStore f args)).run = Part.some (obsOfL o) :=
  Silmaril.Proofs.Wasm.LambdaRTL.trBodyL_evalObs_of_eval h

/-- **Agreement with the loop-free translation** (by transitivity through `FragFunc.Run`): on a
function without `loop` (`trFunc f = some R`), the loop-free λRTL translation returns or traps
exactly when this one does, and it is stuck exactly when this one is stuck or divergent. (That
this translation does not diverge on loop-free code is not stated here.) -/
theorem trBodyL_agrees_trFunc {f : FragFunc} {R : WRegion} (hf : trFunc f = some R)
    {args : List WVal} (hargs : args.map WVal.type = f.params) {σ : Store}
    (hσ : InitStore f args σ) :
    (∀ o, R.evalObs model σ = obsOf o ↔
      ((trBodyL f).evalObs modelL σ).run = Part.some (obsOfL o)) ∧
    (R.evalObs model σ = .error .stuck ↔
      (((trBodyL f).evalObs modelL σ).run = Part.some (.error .stuck) ∨
        ((trBodyL f).evalObs modelL σ).run = Part.none)) :=
  ⟨fun o => (trFunc_run_iff hf hargs hσ o).symm.trans (trBodyL_run_iff hargs hσ o),
    (trFunc_stuck_iff hf hargs hσ).symm.trans (trBodyL_noRun_iff hargs hσ)⟩

/-! ## Examples -/

/-- `exampleSum` (a `loop` with `br_if` exit and `br 0` back edge) returns `55` on `10`, in λRTL. -/
example : ((trBodyL exampleSum).evalObs modelL (initStore exampleSum [.i32 10])).run =
    Part.some (.ok (.ret, .val (.i32 55))) :=
  trBodyL_evalObs_of_eval (f := exampleSum) (args := [.i32 10]) (n := 100)
    (o := .ret (some (.i32 55))) (by decide)

/-- `loop { br 0 }`. -/
def exampleSpin : FragFunc where
  params := []
  locals := []
  result := none
  body := [.loop none [.br 0 []]]

/-- `exampleSpin` diverges in λRTL. -/
theorem exampleSpin_diverges :
    ((trBodyL exampleSpin).evalObs modelL (initStore exampleSpin [])).run = Part.none :=
  Silmaril.Proofs.Wasm.LambdaRTL.spin_diverges _

/-- Hence `exampleSpin` has no terminating fragment run. -/
theorem exampleSpin_noRun : ¬ ∃ o, exampleSpin.Run [] o :=
  (trBodyL_noRun_iff (f := exampleSpin) (args := []) rfl (initStore_spec _ _)).2
    (Or.inr exampleSpin_diverges)

end Silmaril.Wasm.LambdaRTL
