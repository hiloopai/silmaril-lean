module

public import Silmaril.Cerberus.Core.ArenaLift.Defs

/-! # Scheduled procedure entry inside an operand arena

The sole remaining task enters the callee under its own procedure-return frame.
The enclosing arena's continuation and completed siblings remain intact.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.ArenaCall

open Dynamics Interleave ArenaLift

variable (file : Program) (labels : Labels)

/-- A scheduled sole-task request is a transition of the canonical Core LTS. -/
theorem scheduled_reaches (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat)
    (c c' : Control) (fr fr' k : List Frame)
    (hunf : Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr false = .scheduled [(c', fr')])
    (hp : Plain c') :
    CoreReaches file labels ⟨.interleave done [(i, c, fr)], k, m⟩
      ⟨.interleave done [(i, c', fr')], k, m⟩ := by
  refine .single ⟨.tau, Step.respond (fun _ h => nomatch h) ?_⟩
  change Respond m (request file labels ⟨.interleave done [(i, c, fr)], k, m⟩) .tau _
  rw [request_of_requestAux file labels
    (requestAux_sole_scheduled file labels m done i c c' fr fr' k hunf hr hp)
    (fun _ _ _ _ h => nomatch h)]
  exact Respond.scheduled (by simp)

/-- Enter a known ordinary procedure without moving the caller's arena outside
its operand task. This handles the scheduling point in `ccall`. -/
theorem procedure_enter (m : Mem.Concrete.State)
    (done : List (Nat × (Val × List Access))) (i : Nat)
    (s : Sym) (args : List Val) (env : Env) (body : EE) (bindings : Bindings)
    (fr k : List Frame) (ordinary : libraryCall file s = none)
    (resolved : procedureBody file s args = .ok (body, bindings)) :
    CoreReaches file labels
      ⟨.interleave done [(i, .apply (.procedure env)
        (.loaded (.specified (.pointer (.function s))) :: args), fr)], k, m⟩
      ⟨.interleave done [(i, .effectExpr body (extendEnv bindings env),
        .procedureReturn (Map.ofList (saves body).reverse) :: fr)], k, m⟩ := by
  apply scheduled_reaches file labels
  · intro v h
    cases h
  · rw [requestAux.eq_def]
    simp [awaitsScheduling, ordinary, resolved, scheduledRequest]
  · exact ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

end Silmaril.Cerberus.Core.ArenaCall
