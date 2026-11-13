module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Target.Basic

/-!
# The target half of the tool as an instance: results

The header of `Defs`; proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Target.Basic`.

* **`not_tool_tgt_sim`**: the frozen open target `Task.tool_tgt_sim` is **false**. A positive-step
  simulation (`SimRel`) makes the target run at least as long as the source (`simRel_next`), but
  on `calmP` (no imports; `local.get 0`) the family's whole-program target takes 7 steps to its
  stop and the tool's target 6 (the prologue's four instructions, the instruction, the return):
  after 6 steps the first is still running and the second has stopped (`calm_fam`,
  `calm_tool`). With suspensions it is the other way round: on `sleep-add` the family's target stops within 18
  steps and the tool's is still running (`not_simRel_tool_fam`), so neither target simulates
  the other with positive steps.
* **`tool_tgt_stutter`** (the restatement, proved): for a well-formed program and a call within
  `DepthBound`, the family's whole-program host target on `trP P.env` (`famStep`) and the
  asyncified program under the tool's protocol are related by a **stuttering** simulation
  (`Tool.IsSim`: a source step is matched by target steps, or by none with a smaller measure),
  relating the initial configurations. Its proof goes through the tool's own correctness
  (`asyncify_square`, so `asyncify_beh`) and `isSim_of_beh_eq`: for deterministic systems,
  equal behaviours and a stuttering simulation are the same thing.
* `asyncify_beh_of_stutter`: conversely, any such stuttering simulation gives `asyncify_beh`
  from the family's `host_correct_obs` (through `tool_whole`). With `tool_tgt_stutter` this is
  not a second proof of `asyncify_beh`: a simulation built directly, without it, is not done.
* `beh_famStep`: `famStep`'s behaviours are the family's host-observed target behaviours.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Bridge

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Target

variable {σ : Type}

/-- **`Task.tool_tgt_sim` is false**: on `calmP` the family's target outlasts the tool's. -/
theorem not_tool_tgt_sim : ¬ Task.tool_tgt_sim := by
  intro h
  obtain ⟨R, hR, hi⟩ := h Unit calmP calm_wf unitHost 0 calmFn [5] () rfl rfl calm_depth
  obtain ⟨y, hy⟩ := calm_fam
  obtain ⟨y', hy'⟩ := simRel_next hR 6 hi hy
  rw [calm_tool] at hy'
  cases hy'

/-- **Nor the other way round**: no positive-step simulation of the tool's target by the
family's relates the initial configurations of `sleep-add`. -/
theorem not_simRel_tool_fam :
    ¬ ∃ R, SimRel (asRes (Tool.tgtStep (Tool.asyncifyProg saP) exH))
      (mapObs toolOut (observe (htstep (compPO .whole (trP saP.env)) kTest (kHost saP.env exH))))
      R ∧ R (Tool.tgtSt saP 1 saFn [5] 0) (tInit 1 (kArgs [5]), 0) := by
  rintro ⟨R, hR, hi⟩
  obtain ⟨y, hy⟩ := sa_tool
  obtain ⟨y', hy'⟩ := simRel_next hR 18 hi hy
  obtain ⟨o, ho⟩ := sa_fam
  rw [ho] at hy'
  cases hy'

/-- The behaviours of the family's target read as a tool system. -/
theorem famStep_beh (Q : Prog (TIns KV)) (test : KV → Bool) (K : KHost KV σ) (s : σ) (f : Nat)
    (args : List (SV KV)) :
    Tool.beh (famStep Q test K) (tInit f args, s) = obsOut '' hTgtObs Q test K s f args :=
  beh_famStep Q test K _

/-- **The target half, restated with stuttering, proved** (via `asyncify_square`). -/
theorem tool_tgt_stutter (P : Tool.Prog) (hP : P.WF) (H : Tool.Host σ) {e : Nat}
    {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W)
    (hargs : args.length = fn.nparams) (s : σ)
    (hbound : Tool.DepthBound P H (Tool.srcCfg e fn args, s)) :
    ∃ (R : TCfg KV × σ → Tool.TSt σ → Prop) (μ : TCfg KV × σ → Nat),
      Tool.IsSim (famStep (compPO .whole (trP P.env)) kTest (kHost P.env H))
        (Tool.tgtStep (Tool.asyncifyProg P) H) R μ ∧
      R (tInit e (kArgs args), s) (Tool.tgtSt P e fn args s) := by
  have heq : Tool.beh (famStep (compPO .whole (trP P.env)) kTest (kHost P.env H))
      (tInit e (kArgs args), s) =
      Tool.beh (Tool.tgtStep (Tool.asyncifyProg P) H) (Tool.tgtSt P e fn args s) := by
    rw [famStep_beh, asyncify_square P hP H hfn args hargs s hbound]
  exact ⟨_, _, isSim_of_beh_eq (noDivStop_famStep _ _ _) (noDivStop_tgtStep _ _), heq⟩

/-- **`asyncify_beh` from any stuttering simulation of the family's target by the tool's.** -/
theorem asyncify_beh_of_stutter (P : Tool.Prog) (hP : P.WF) (H : Tool.Host σ) {e : Nat}
    {fn : Tool.FnSrc} (hfn : P.fnAt e = some fn) (args : List Tool.W) (s : σ)
    {R : TCfg KV × σ → Tool.TSt σ → Prop} {μ : TCfg KV × σ → Nat}
    (hS : Tool.IsSim (famStep (compPO .whole (trP P.env)) kTest (kHost P.env H))
      (Tool.tgtStep (Tool.asyncifyProg P) H) R μ)
    (hR : R (tInit e (kArgs args), s) (Tool.tgtSt P e fn args s)) :
    Tool.beh (Tool.srcStep P.env H) (Tool.srcCfg e fn args, s) =
      Tool.beh (Tool.tgtStep (Tool.asyncifyProg P) H) (Tool.tgtSt P e fn args s) := by
  rw [tool_whole P hP H hfn args s, ← famStep_beh]
  exact Tool.beh_eq_of_sim hS hR

/-- info: 'Silmaril.Wasm.FX.Asyncify.Bridge.not_tool_tgt_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_tool_tgt_sim

/-- info: 'Silmaril.Wasm.FX.Asyncify.Bridge.tool_tgt_stutter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tool_tgt_stutter

end Silmaril.Wasm.FX.Asyncify.Bridge
