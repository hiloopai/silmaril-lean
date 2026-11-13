module

public import Silmaril.Wasm.Component.Streams.Alg.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Thms
public import Silmaril.Games.Pair.Thms

/-!
# Stream stages in the component algebra: the strategy of a stage

Under the batch semantics, a stage component is the handler `stageH a.run`: a call of its export
pulls the input with one call of its import and answers `a.run` of it; any other call traps.
All the wiring of the component IR (masks, the environment's split, the core instance's import
and export adapters) collapses into handlers (`Strategy.ofHandler_comp`, `ofHandler_id`,
`ofHandler_pair_ofHandler`), and the handler is computed.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Alg

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Alg

/-- The handler of a stage computing `f`. -/
def stageH (f : List Val → List Val) : Handler sigU sigU := fun q =>
  if q.1 = 0 then .call (0, .vals []) (fun r => .pure (pullAns f r)) else .pure none

/-- The core handler of the batch semantics. -/
def coreH (f : List Val → List Val) : Handler (sigN 1) (sigN 1) := fun _ =>
  .call ((⟨0, by decide⟩ : Fin 1), Payload.vals []) fun r => .pure (pullAns f r)

theorem denU_stage (a : TCode) : (stage a).denU batchSem = Strategy.ofHandler (stageH a.run) := by
  simp only [stage, Comp.denU, denNodes, Node.den, coreNode, ext]
  show ((Strategy.ofHandler (maskH 1)).comp
      ((((Strategy.id sigU).pair ((Strategy.ofHandler (implsN 1 [Impl.fwd 0] 1)).comp
        ((Strategy.ofHandler (coreH a.run)).comp (Strategy.ofHandler (widenH 1))))).comp
          (Strategy.ofHandler (splitH 1))))).comp
      (Strategy.ofHandler (exportsH 2 [⟨"src", ftS, Impl.fwd 1⟩])) = _
  rw [← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp, ← Strategy.ofHandler_id,
    Strategy.ofHandler_pair_ofHandler, ← Strategy.ofHandler_comp, ← Strategy.ofHandler_comp,
    ← Strategy.ofHandler_comp]
  congr 1
  funext q
  obtain ⟨n, p⟩ := q
  cases n with
  | zero =>
    simp [Handler.comp, Prog.interp, Prog.bind, exportsH, implsH, Impl.prog, runChain, Target.prog,
      splitH, Handler.copair, implsN, widenH, maskH, stageH, coreH]
  | succ n =>
    simp [Handler.comp, exportsH, implsH, stageH]

theorem pullAns_comp (f g : List Val → List Val) (r : Option Payload) :
    pullAns g (pullAns f r) = pullAns (fun xs => g (f xs)) r := by
  rcases r with _ | ⟨_ | xs⟩ <;> rfl

/-- **Stage fusion**: two plugged stages are the stage of the composite code. -/
theorem stage_fusion (a b : TCode) :
    CompEquiv batchSem (seq (stage a) (stage b)) (stage (.comp a b)) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · rw [(sizes_seq _ _).2]
    rfl
  · rw [denU_seq, denU_stage, denU_stage, denU_stage, ← Strategy.ofHandler_comp]
    congr 1
    funext q
    obtain ⟨n, p⟩ := q
    cases n with
    | zero => simp [Handler.comp, stageH, Prog.interp, Prog.bind, pullAns_comp, TCode.run]
    | succ n => simp [Handler.comp, stageH]

end Silmaril.Proofs.Wasm.Component.Streams.Alg
