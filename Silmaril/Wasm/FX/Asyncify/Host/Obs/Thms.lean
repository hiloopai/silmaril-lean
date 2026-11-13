module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Host.Obs.Sim

/-!
# Asyncify with a host: results with the host state observed

The header of `Defs` (`observe`, `HOut`, `hSrcObs`, `hTgtObs`).

* **`host_correct_obs`**: for every optimization `o`, on the fragment of a sound analysis,
  under every host and from every host state, a call has the same behaviours in the host-closed
  kernel and on `compPO o P` under the host protocol, **with the final host state observed**:
  equal results with equal host states, traps with equal host states, divergence. So a host
  that records its calls (or a trace) sees the same calls in both. Proof: `simRel_hostO`, the
  relation of `host_correct` with the trap and result runs restated for the observing machines.
* `host_whole_obs`, `host_analyze_obs`: whole-program and computed analysis, no hypothesis.
* `host_comorphism_obs`: the comorphism of behaviour charts whose sentences are observed
  behaviours (direction `equal`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.Atlas

variable {V σ : Type}

/-- **The host instance, host states observed, is correct for every optimization on its
fragment.** -/
theorem host_correct_obs (o : Opt) (P : Prog (Ins V)) (hP : o.Dom P) (test : V → Bool)
    (H : KHost V σ) (s : σ) (f : Nat) (args : List (SV V)) :
    hTgtObs (compPO o P) test H s f args = hSrcObs P test H s f args :=
  (Silmaril.Proofs.Wasm.FX.Asyncify.Host.beh_hostO o P test H f args hP s).symm

/-- Whole-program instrumentation, host states observed: no hypothesis. -/
theorem host_whole_obs (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ) (s : σ) (f : Nat)
    (args : List (SV V)) :
    hTgtObs (compPO .whole P) test H s f args = hSrcObs P test H s f args :=
  host_correct_obs .whole P (whole_dom P) test H s f args

/-- The computed analysis, host states observed: no hypothesis. -/
theorem host_analyze_obs (P : Prog (Ins V)) (n : Nat) (test : V → Bool) (H : KHost V σ)
    (s : σ) (f : Nat) (args : List (SV V)) :
    hTgtObs (compPO (Selective.analyzed P n) P) test H s f args = hSrcObs P test H s f args :=
  host_correct_obs (Selective.analyzed P n) P (Selective.analyze_sound P n) test H s f args

/-- The host-closed kernel chart with host states observed. -/
def hSrcObsChart (dom : Prog (Ins V) → Prop) : Chart :=
  BChart (Prog (Ins V) × (V → Bool) × KHost V σ × σ) (Nat × List (SV V)) (Obs (HOut V σ))
    (fun p => dom p.1) (fun p c => hSrcObs p.1 p.2.1 p.2.2.1 p.2.2.2 c.1 c.2)

/-- The host-closed target chart with host states observed. -/
def hTgtObsChart : Chart :=
  BChart (Prog (TIns V) × (V → Bool) × KHost V σ × σ) (Nat × List (SV V)) (Obs (HOut V σ))
    (fun _ => True) (fun q c => hTgtObs q.1 q.2.1 q.2.2.1 q.2.2.2 c.1 c.2)

/-- **The host instance, host states observed, as a comorphism** (equal on every sentence). -/
def host_comorphism_obs (o : Opt) :
    Transition (hSrcObsChart (V := V) (σ := σ) o.Dom) (hTgtObsChart (V := V) (σ := σ)) :=
  BTrans.ofEq (fun p => (compPO o p.1, p.2)) id (fun _ _ => trivial)
    (fun p hp c => host_correct_obs o p.1 hp p.2.1 p.2.2.1 p.2.2.2 c.1 c.2)

theorem blocking_src_obs : runN (observe (hsstep blockP blockTest countHost)) 20 (sInit 0 [], 0) =
    .stop (.done [.val (.done [.val 214, .val 5] 1)]) := rfl

theorem blocking_whole_obs :
    runN (observe (htstep (compPO .whole blockP) blockTest countHost)) 40 (tInit 0 [], 0) =
      .stop (.done [.val (.done [.val 214, .val 5] 1)]) := rfl

/-- The example `blockP` under the counting host: one result, and the host saw one call, in the
source and in the whole-program target. -/
theorem blocking_example_obs :
    hSrcObs blockP blockTest countHost 0 0 [] = {.done [.val (.done [.val 214, .val 5] 1)]} ∧
    hTgtObs (compPO .whole blockP) blockTest countHost 0 0 [] =
      {.done [.val (.done [.val 214, .val 5] 1)]} :=
  ⟨Silmaril.Wasm.FX.Asyncify.RelSim.beh_of_stop blocking_src_obs,
    Silmaril.Wasm.FX.Asyncify.RelSim.beh_of_stop blocking_whole_obs⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.Host.host_correct_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms host_correct_obs

end Silmaril.Wasm.FX.Asyncify.Host
