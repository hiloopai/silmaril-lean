module

public import Silmaril.Wasm.Abstract.HostClosing.Defs
import Silmaril.Proofs.Wasm.Abstract.HostClosing.Pending

/-!
# Wasm functions with host calls as an open module: theorems

**The replay links.** The logged closed semantics `wasmEvFun` (host calls as events, internal
calls closed) and the relational native semantics `hostCall host` have the same outcomes,
once the host answers in the log are those the host allows (`HostRel.Consistent` for
`coreHostRel host`):

* `wasmEvFun_hostCall`: a finished behaviour with a consistent log is a `hostCall` outcome,
  through the exit flow;
* `hostCall_wasmEv`: every `hostCall` outcome is a finished behaviour with a consistent log.

Internal Wasm calls never appear in the log; host calls appear in execution order.

**The pending links.** `wasmEvPend_iff`: a host call is pending after a consistent log exactly
when it is the invocation of a host function itself, or a host call reached by
`PendO (hostCall host)` from the invocation (`Silmaril.Wasm.Abstract.HostEval`).

**The reach link.** `reachL_of_reachO`: a reach of `hostCall host` is a logged reach
(`ReachL`) whose completed calls, resolved by the closure, make host calls the host allows.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type} {host : HostSemantics H}

/-- **Finished replay**: a logged behaviour whose host answers are allowed is a `hostCall`
outcome. -/
theorem wasmEvFun_hostCall {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} {e : End (Store H) (List Val ⊕ Nat)}
    (h : (cs, e) ∈ wasmEvFun s (a, vs)) (hc : (coreHostRel host).Consistent cs) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (bfl fl : Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      hostCall host s a vs (s₂, bfl) ∧ exitFlow rs.length bfl = some fl ∧ e = endOfFlow fl s₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosing.close_le_toClosedH a s vs h hc

/-- **Finished replay, converse**: every `hostCall` outcome is a logged behaviour with allowed
host answers. -/
theorem hostCall_wasmEv {s s₂ : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {bfl fl : Flow} (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (h : hostCall host s a vs (s₂, bfl)) (hx : exitFlow rs.length bfl = some fl) :
    ∃ cs, (coreHostRel host).Consistent cs ∧ (cs, endOfFlow fl s₂) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosing.hostCall_le_ofClosedH s a vs _ h fi ps rs fl hfi hty hx

/-- **Pending replay**: a pending host call after a consistent log is the invocation of a host
function itself or a `PendO (hostCall host)` host call, and conversely. -/
theorem wasmEvPend_iff {s : Store H} {a : Nat} {vs : List Val} {m : (wasmHostSig H).Op} :
    (∃ cs, (cs, m) ∈ wasmEvPend s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
        (y = ⟨a, (vs, s)⟩ ∨ PendO (hostCall host) ⟨a, (vs, s)⟩ y) ∧
          y.2.2.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧ m = (hh, y.2.2, y.2.1) := by
  constructor
  · rintro ⟨cs, h, hc⟩
    exact Silmaril.Proofs.Wasm.Abstract.HostClosing.pendO_of_pendL h hc
  · rintro ⟨y, fi, hh, hy | hy, hfi, hcode, rfl⟩
    · subst hy
      exact ⟨[], .self hfi hcode, fun _ h => nomatch h⟩
    · exact Silmaril.Proofs.Wasm.Abstract.HostClosing.pendL_of_pendO hy hfi hcode

/-- **A reach of `hostCall host` is a logged reach** whose completed calls, resolved by the
closure, make host calls the host allows. -/
theorem reachL_of_reachO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachO (hostCall host) s f stk es y) :
    ∃ l q, ReachL s f stk es l y ∧ Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q ∧
      (coreHostRel host).Consistent q := by
  obtain ⟨l, q, hr, ha, hc⟩ := Silmaril.Proofs.Wasm.Abstract.HostClosing.reachL_of_reachO h
  exact ⟨l, q, hr, Silmaril.Proofs.Wasm.Abstract.HostClosing.substPre_lift_iff.mpr ha, hc⟩

end Silmaril.Wasm.Abstract
