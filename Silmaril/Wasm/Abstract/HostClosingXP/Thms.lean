module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Interp.HostEvalP.Thms
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Basic
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Direct
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapClose
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Cut
import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackWhole

/-!
# The canonical relation with host calls as an open module: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingXP`.

* `evalLXPh_of_evalL`: every native logged run `EvalL` is a canonical logged run `EvalLXPh`,
  ending in the same flow; so `wasmHOpen_le_wasmHOpenXP` and `wasmEvFun_le_wasmEvFunXP` (every
  store).
* `wasmEvFunXP_ret_len`: a function returns at most its result arity; so a cut call is never
  resolved by a return.
* **Coincidence on direct stores** (`Interp.StoreDirect`: Wasm bodies without the extended call
  forms and the exception forms):
  * `wasmHOpenXP_direct`: a canonical open behaviour is a native one, or **cut**: it ends in a
    trap, its log ends in a cut call (an answer of more values than the callee's result arity),
    and answering that call by an exception instead (`inr 0`, ending the function in
    `ret (inr 0)`) is a native open behaviour. Cut behaviours are not native ones, so the open
    modules differ exactly by them;
  * `wasmEvFunXP_direct`: the closures agree, on behaviours whose host answers leave direct
    stores (the host answers are arbitrary in a closure: an answer adding a function with a
    `try_table` leaves the direct fragment, where the native module has no behaviour);
  * `wasmEvFunXP_direct_consistent`: so on behaviours whose log a host keeping direct stores
    (`Interp.HostKeepsDirect`) allows.

**Finished behaviours are Core runs with exactly their log** (H2, forward, every profile; a host
in the native host slice whose answers keep the exception checker's store check and the tag
invariants, `Interp.HostSliceE tags`; a store with the tag invariants `Interp.TagsOk tags` and the
exception checker's store check `Interp.StoreChkE (Interp.ehExt tags)`; a typed invocation):

* `wasmEvFunXP_vals_evRun`: a returning behaviour `(cs, ret (inl ws) s₂)` with a log the host
  allows is a Core run of the invocation whose host events are **exactly** `cs`, to the values
  `ws` at `s₂`;
* `wasmEvFunXP_throw_evRun`: an uncaught exception `(cs, ret (inr t) s₂)` is such a run to the
  thrown exception `throwing t` (`REF.EXN_ADDR t; THROW_REF`) at `s₂`, in the empty frame;
* `wasmEvFunXP_trap_evRun`: a trap `(cs, trap)` is such a run to `[trap]`, in some store (a trap
  carries none).

Proof (`Log`, `Struct`, `Cases`, `Calls`, `Fwd`, `Frame`, `Closure`, `TrapCases`, `TrapFwd`,
`TrapClose`): the cases of `Interp.PendSim.evalOXP_goodP` with logs, by induction on
`EvalLXPh`, each inner logged run lifted through its context (sequence, label, handler, frame;
the glue host-free), the arity facts from `Interp.HostEvalP.evalOXP_host_good` on the
`EvalOXP (hostCallXP host)` run that a logged run, its calls answered consistently, is; and
least-fixpoint induction on the closure. Caught exceptions are the handler's `Catches` steps;
`call_indirect`/`call_ref` reach `call_ref` and run the callee in any `call_ref` form; a frame-level
tail call is the body's run to Core's pending tail call (which passes every label and handler),
`return_call_ref-frame-addr`, then the tail callee in the caller's frame, so a host tail callee is
its one event there. A trapping behaviour resolved by `Shape.Subst.intTrap` is the logged run up
to that call, then the callee's trap leaving every context.

**Core runs are finished behaviours at exactly their log** (H2, backward, deterministic profile
`SingleThreaded.profile o`; a host with typed answers, `HostTyped`, in the native host slice with
`Interp.HostSliceE tags`; a typed store `StoreOk` with the exception checker's store check and the
tag invariants; a typed invocation):

* `evRun_wasmEvFunXP_vals`: a Core run of the invocation with the host events `cs` to the values
  `ws` at `s₂`, in any frame, is the returning behaviour `(cs, ret (inl ws) s₂)`;
* `evRun_wasmEvFunXP_throw`: to the thrown exception `throwing t`, it is `(cs, ret (inr t) s₂)`;
* `evRun_wasmEvFunXP_trap`: to a trap, it is `(cs, trap)`;
* `wasmEvFunXP_vals_iff`, `wasmEvFunXP_throw_iff`, `wasmEvFunXP_trap_iff`: with the forward
  lemmas, both ways (the final frame is the empty frame of the invocation; a trap carries no
  store).

Proof (`BackDet`, `BackSplit`, `BackGoal`, `BackCall`, `BackTy`, `BackSeq`, `BackOps`, `BackCtl`,
`BackBlock`, `BackIf`, `BackWhole`): by strong induction on the length of the labelled run
(`EvRunN`) and on the size of the trees, a run of a typed problem (`Interp.TypedP tags`) whose
end has no host-free step and is not at a host call is read back as a logged canonical run whose
calls resolve to exactly the run's log (or a resolved prefix, then a callee trapping in the
closure, read as a cut call). The run is split at each context (sequence, label, handler and
label, callee frame), the sub-runs read back by induction, the glue host-free (`evRunN_through`
with the forward lemmas of `Interp.Control`, `Interp.EHSim`, `Interp.PendSim`). Where the logged
run ends is read off the forward simulation (`evalLXPh_fwd`, `evalLXPh_trap`) by determinism of
labelled runs with the same log (`evRun_det_end_pre`). A callee is a host event, or its frame
entered (its only step), its body read back and its frame left with values or an exception, a
trap, or a pending tail call made in the caller's frame by `return_call_ref-frame-addr` (the
tail callee read back on the strictly shorter rest of the run, a host tail callee its one event
there). Callee types come from typing: progress at a `call_ref` form, a successful cast for
`return_call_indirect`, the operand's subtyping chain for `return_call_ref`.

**Cut calls**:

* `wasmHOpenXP_ne_div`, `wasmEvFunXP_ne_div`: no open behaviour and no closed behaviour ends in
  `div`; a log is a finite list, so no divergence and no productive stream arises from a cut;
* `wasmEvFunXP_cut`: in a resolution against the closure, a cut call (an answer of more values
  than the callee's result arity) is resolved only by `Shape.Subst.intTrap`, at it or at an
  earlier call, never by a return: the resolved behaviour traps, with the resolved prefix's log
  and the trapping callee's log. At the open level a cut answer alone does not force a trap: the
  returning rules (`callRet`, `indRet`, `refRet`) also accept answers of any length and go on, so
  the same log may end in a flow; such behaviours are never resolved past the cut call either.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (StoreDirect)

variable {H : Type}

/-- Every native logged run is a canonical logged run, ending in the same flow. -/
theorem evalLXPh_of_evalL {s s' : Store H} {f f' : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {fl : Flow} (h : EvalL s f stk es l (s', f', fl)) :
    EvalLXPh s f stk es l (s', f', .flow fl) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evalLXPh_of_evalL h

/-- The native open module is included in the canonical one, at every store. -/
theorem wasmHOpen_le_wasmHOpenXP : wasmHOpen (H := H) ≤ wasmHOpenXP :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpen_le

/-- The native closure is included in the canonical one, at every store. -/
theorem wasmEvFun_le_wasmEvFunXP : wasmEvFun (H := H) ≤ wasmEvFunXP :=
  fun s p => Shape.close_mono wasmHOpen_le_wasmHOpenXP p.1 s p.2

/-- **A function returns at most its result arity.** -/
theorem wasmEvFunXP_ret_len {s s' : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s') ∈ wasmEvFunXP s (a, vs)) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ws.length ≤ rs.length :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_ret_len h

/-- **On a direct store, a canonical open behaviour is native, or cut.** -/
theorem wasmHOpenXP_direct {a : Nat} {s : Store H} {vs : List Val} (hs : StoreDirect s)
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) :
    x ∈ wasmHOpen a s vs ∨
      (x.2 = .trap ∧ ∃ (pre : List (OCall H)) (a' : Nat) (args : List Val) (s₁ s₂ : Store H)
        (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
        x.1 = (pre ++ [OCall.mk a' args s₁ (.inl ws) s₂]).map OCall.lift ∧
        s₁.funcs[a']? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        rs.length < ws.length ∧
        ((pre ++ [OCall.mk a' args s₁ (.inr 0) s₂]).map OCall.lift, .ret (.inr 0) s₂) ∈
          wasmHOpen a s vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpenXP_direct hs hx

/-- **On direct stores the closures agree**, on behaviours whose host answers leave direct
stores. -/
theorem wasmEvFunXP_direct {s : Store H} {a : Nat} {vs : List Val} (hs : StoreDirect s)
    {cs : List (Call (wasmHostSig H))} (hd : ∀ c ∈ cs, StoreDirect c.2.1)
    {e : End (Store H) (List Val ⊕ Nat)} :
    (cs, e) ∈ wasmEvFunXP s (a, vs) ↔ (cs, e) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_direct hs hd

/-- **On direct stores the closures agree on behaviours a host keeping direct stores allows.** -/
theorem wasmEvFunXP_direct_consistent {host : HostSemantics H}
    (hD : Interp.HostKeepsDirect host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreDirect s) {cs : List (Call (wasmHostSig H))}
    (hc : (coreHostRel host).Consistent cs) {e : End (Store H) (List Val ⊕ Nat)} :
    (cs, e) ∈ wasmEvFunXP s (a, vs) ↔ (cs, e) ∈ wasmEvFun s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_direct_consistent hD hs hc

/-! ## Finished behaviours are Core runs with exactly their log -/

section Fwd

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}

/-- **Returning behaviours are Core runs with exactly their log** (every profile): a returning
behaviour of `wasmEvFunXP` with a log the host allows is a Core run of the invocation whose host
events are exactly that log, to its values. -/
theorem wasmEvFunXP_vals_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs ws : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvFunXP_ret_evRun hH hE hts hS hok h hc

/-- **Uncaught exceptions are Core runs with exactly their log** (every profile): a behaviour of
`wasmEvFunXP` ending in an uncaught exception, with a log the host allows, is a Core run of the
invocation whose host events are exactly that log, to the thrown exception. -/
theorem wasmEvFunXP_throw_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvFunXP_ret_evRun hH hE hts hS hok h hc

/-- **Traps are Core runs with exactly their log** (every profile): a trapping behaviour of
`wasmEvFunXP` with a log the host allows is a Core run of the invocation whose host events are
exactly that log, to a trap, in some store. -/
theorem wasmEvFunXP_trap_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .trap) ∈ wasmEvFunXP s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmEvFunXP_trap_evRun hH hE hts hS hok h hc

end Fwd

/-! ## Core runs are finished behaviours at exactly their log -/

section Back

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **Values, with exactly the run's log** (deterministic profile): a Core run of a typed
invocation with the host events `cs` to the values `ws` at `s₂`, in any frame, is the returning
behaviour `(cs, ret (inl ws) s₂)` of `wasmEvFunXP`. -/
theorem evRun_wasmEvFunXP_vals (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs ws : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, vals ws⟩) :
    (cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_wasmEvFunXP_vals hT hH hE hs hS hts hok hrun

/-- **An uncaught exception, with exactly the run's log** (deterministic profile): a Core run of
a typed invocation with the host events `cs` to the thrown exception `throwing t` at `s₂`, in
any frame, is the behaviour `(cs, ret (inr t) s₂)` of `wasmEvFunXP`. -/
theorem evRun_wasmEvFunXP_throw (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, throwing t⟩) :
    (cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_wasmEvFunXP_throw hT hH hE hs hS hts hok hrun

/-- **A trap, with exactly the run's log** (deterministic profile): a Core run of a typed
invocation with the host events `cs` to a trap is the trapping behaviour `(cs, trap)` of
`wasmEvFunXP`. -/
theorem evRun_wasmEvFunXP_trap (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {f₂ : Frame}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, [.trap]⟩) :
    (cs, .trap) ∈ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.evRun_wasmEvFunXP_trap hT hH hE hs hS hts hok hrun

/-- **Returning behaviours at exactly their log, both directions** (deterministic profile):
`(cs, ret (inl ws) s₂)` is a behaviour of `wasmEvFunXP` with a log the host allows exactly when
the invocation has a Core run with the host events `cs` to the values `ws` at `s₂`, in the empty
frame. -/
theorem wasmEvFunXP_vals_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  ⟨fun h => wasmEvFunXP_vals_evRun hH hE hts hS hok h.1 h.2,
    fun h => ⟨evRun_wasmEvFunXP_vals hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

/-- **Uncaught exceptions at exactly their log, both directions** (deterministic profile):
`(cs, ret (inr t) s₂)` is a behaviour of `wasmEvFunXP` with a log the host allows exactly when
the invocation has a Core run with the host events `cs` to `throwing t` at `s₂`, in the empty
frame. -/
theorem wasmEvFunXP_throw_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ :=
  ⟨fun h => wasmEvFunXP_throw_evRun hH hE hts hS hok h.1 h.2,
    fun h => ⟨evRun_wasmEvFunXP_throw hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

/-- **Traps at exactly their log, both directions** (deterministic profile): `(cs, trap)` is a
behaviour of `wasmEvFunXP` with a log the host allows exactly when the invocation has a Core run
with the host events `cs` to a trap, in some store (a trap carries none). -/
theorem wasmEvFunXP_trap_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .trap) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ s₂, EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  ⟨fun h => wasmEvFunXP_trap_evRun hH hE hts hS hok h.1 h.2,
    fun ⟨_, h⟩ => ⟨evRun_wasmEvFunXP_trap hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

end Back

/-! ## Cut calls -/

/-- **No open behaviour diverges.** -/
theorem wasmHOpenXP_ne_div {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) : x.2 ≠ .div :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.wasmHOpenXP_ne_div hx

/-- **No closed behaviour diverges.** -/
theorem wasmEvFunXP_ne_div {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} : (cs, .div) ∉ wasmEvFunXP s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_ne_div

/-- **In the closure a cut call is resolved only by a trapping callee**: in a resolution against
the closure of a log `u ++ z :: w` whose call `z` is answered by more values than its callee's
result arity, the resolution stops by `Shape.Subst.intTrap` at the `k`-th call, `k ≤ u.length`
(at `z` or before it): the resolved behaviour traps, its log the resolved prefix's log `q` and the
trapping callee's log `c₁`. -/
theorem wasmEvFunXP_cut {g : Nat} {args : List Val} {s₁ s₂ : Store H} {ws : List Val}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s₁.funcs[g]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hws : rs.length < ws.length)
    {e : End (Store H) (List Val ⊕ Nat)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    {u w : List (HCall H)}
    (h : Shape.Subst (Shape.close wasmHOpenXP)
      (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w) e y) :
    y.2 = .trap ∧ ∃ (k : Nat) (q c₁ : List (Call (wasmHostSig H))) (g' : Nat) (a' : List Val)
        (s' : Store H) (ans : (List Val ⊕ Nat) × Store H),
        k ≤ u.length ∧
        (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop k =
          ⟨.inr ⟨g', (a', s')⟩, ans⟩ ::
            (u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).drop (k + 1) ∧
        Shape.SubstPre (Shape.close wasmHOpenXP)
          ((u ++ ⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩ :: w).take k) q ∧
        (c₁, .trap) ∈ Shape.close wasmHOpenXP g' s' a' ∧ y.1 = q ++ c₁ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingXP.close_cut hfi hty hws h

end Silmaril.Wasm.Abstract
