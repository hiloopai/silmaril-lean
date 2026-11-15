module

public import Silmaril.Proofs.Wasm.Cfg.Bridge

@[expose] public section

/-!
# The backward bridge (work in progress: open goals in `Task`)

Region runs of lowered, checked, typed trees are native `EvalOX` runs with the same oracle, at
the deterministic profile. Open goals, in order:

1. `Task.flat_complete`: a checked, typed flat instruction's region run is its `evalFlat` result
   (`evalFlat_progressH` gives a result; `flat_run` runs it; head determinism at
   `SingleThreaded.profile o`, up to trap/throw bubbling (`Det.DStep`/`Join`), identifies the
   two ends).
2. `Task.bwd`: the converse of `Proofs.Bridge.fwd`, by induction on the tree list (sizeOf),
   inverting `RunC` on `expression (lowerList es)` with `run_split` at each tree, and the
   label/handler/call rules at each node; `TypedT` is re-established on children by Interp's
   `TypedT` lemmas.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Bridge.Task

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp

variable {H : Type} {C : Abstract.CallRel H}

theorem flat_complete {o : SingleThreaded.GrowOracle} {s s' : Store H} {f f' : Frame}
    {stk : List Val} {i : Instr} {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat}
    {labels : List Nat} {oc : Option Nat} {rest : List Admin} {out : Region.Out}
    (hi : ∀ x, i ≠ .call x) (hc : flatChk F mi f.locals.length ret labels stk.length i = some oc)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩)
    (h : RunC (SingleThreaded.profile o) noHostX C s f stk.reverse [.plain i] s' f' out) :
    ∃ fl, evalFlat s f stk i = some (s', f', fl) ∧ FlowRel fl out := by
  sorry

theorem bwd {o : SingleThreaded.GrowOracle} {s s' : Store H} {f f' : Frame} {stk : List Val}
    {es : List BExpr} {out : Region.Out}
    (ht : TypedT s f stk es)
    (h : RunC (SingleThreaded.profile o) noHostX C s f stk.reverse (expression (BExpr.lowerList es))
      s' f' out) :
    ∃ r, Abstract.CallX.EvalOX C s f stk es r ∧ ResOut C s' f' out r := by
  sorry

end Silmaril.Wasm.Cfg.Proofs.Bridge.Task
