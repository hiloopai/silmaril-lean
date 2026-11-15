module

public import Silmaril.Wasm.Abstract.HostClosingInf.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
public import Silmaril.Games.Abstract.ModuleDLog.Thms
public import Silmaril.Wasm.Abstract.Decomp.Defs
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Basic
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Quiet

/-!
# Productive runs of invocations: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingInf`. Every profile and host:

* `wasmEvInf_hostObsInf` (**adequacy**): the productive observations against a host,
  `hostObsInf (coreHostRel host) (wasmEvInf P)`, are exactly the productive Core runs with that
  host (`CoreInf`);
* `wasmEvInf_prefix` (**prefix agreement**): the first `n` events of such a run are the actual
  event log of a finite run of the invocation (`EvRun`), continued productively.

**A finite log, then host-free divergence** (`wasmEvFunD := Shape.closeDLog wasmHOpen LDLw`):

* `wasmEvFunD_of_ne_div`: off `div`, `wasmEvFunD` is `wasmEvFun`;
* `quietCall_closedCall`, `closedCall_quietCall`: the host-free oracle `quietCall` agrees with
  the closure `closedCall` on the ends of the answers it gives, and gives every closed answer a
  run can consume; so `localDivO_closed_quiet : LocalDivO closedCall ≤ LocalDivO quietCall` and
  `ldlw_of_wasmLocalDiv : wasmLocalDiv z → LDLw z []`;
* `wasmEvFunD_of_diverges_closed`: a host-free divergent typed invocation (deterministic
  profile) has the behaviour `([], div)`;
* `wasmEvFunD_of_evRun_nil`: **adequacy for the empty log**: a Core run of a typed invocation
  with no host event, then host-free divergence, is `([], div)` in `wasmEvFunD`.

Not yet: adequacy for a **nonempty** event log (`EvRun … cs c'` with `cs ≠ []`, then host-free
divergence, gives `(cs, div) ∈ wasmEvFunD`). It needs a backward simulation of divergence that
keeps the actual host-event log, a logged form of `HostEval.div_whole`. Also not yet: agreement
of the productive prefixes with the logged pending prefixes of `wasmEvPend` with the same log.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **The productive observations against a host are its productive Core runs.** -/
theorem wasmEvInf_hostObsInf {s : Store H} {a : Nat} {vs : List Val}
    {ω : Nat → Call (wasmHostSig H)} :
    ω ∈ hostObsInf (coreHostRel host) (wasmEvInf P) s (a, vs) ↔
      CoreInf P host (invoke s a vs) ω :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInf_hostObsInf

/-- **Prefix agreement**: the first `n` events of a productive run of an invocation are the
actual event log of a finite run of it, continued productively. -/
theorem wasmEvInf_prefix {s : Store H} {a : Nat} {vs : List Val} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host (invoke s a vs) ω) (n : Nat) :
    ∃ c', EvRun P host (invoke s a vs) (streamTake ω n) c' ∧
      CoreInf P host c' (fun k => ω (n + k)) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInf_prefix h n

/-! ## A finite log, then host-free divergence -/

/-- **Off `div`, `wasmEvFunD` is `wasmEvFun`.** -/
theorem wasmEvFunD_of_ne_div {s : Store H} {a : Nat} {vs : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (hy : y.2 ≠ .div) :
    y ∈ wasmEvFunD s (a, vs) ↔ y ∈ wasmEvFun s (a, vs) :=
  Shape.mem_closeDLog_of_ne_div hy

open Silmaril.Wasm.Binaryen in
/-- **The host-free oracle gives closed answers**, up to the end they hand back. -/
theorem quietCall_closedCall {s s₂ : Store H} {a : Nat} {us : List Val} {bfl : Flow}
    (h : quietCall s a us (s₂, bfl)) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (fl fl' bfl' : Flow) (s₂' : Store H),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      exitFlow rs.length bfl = some fl ∧ closedCall s a us (s₂', bfl') ∧
      exitFlow rs.length bfl' = some fl' ∧ endOfFlow fl' s₂' = endOfFlow fl s₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.quietCall_closedCall h

/-- **Every closed answer a run can consume** (values, a trap or an exception) **is a host-free
answer.** -/
theorem closedCall_quietCall {s : Store H} {a : Nat} {us : List Val}
    {out : Store H × Binaryen.Flow} (h : closedCall s a us out)
    (hc : (∃ vs, out.2.retVals = some vs) ∨ out.2 = .trap ∨ ∃ t, out.2 = .throw t) :
    quietCall s a us out :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.closedCall_quietCall h hc

/-- Host-free local divergence is local divergence with host-free callees. -/
theorem localDivO_closed_quiet : LocalDivO (closedCall : CallRel H) ≤ LocalDivO quietCall :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.localDivO_closed_quiet

/-- **Local divergence is logged local divergence with an empty log.** -/
theorem ldlw_of_wasmLocalDiv {z : (wasmOShape H).self.Op} (h : wasmLocalDiv z) : LDLw z [] :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.ldlw_of_wasmLocalDiv h

/-- **A host-free divergent typed invocation diverges in `wasmEvFunD` with an empty log**
(deterministic profile `profile o`). -/
theorem wasmEvFunD_of_diverges_closed {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hd : Diverges (SingleThreaded.profile o) Binaryen.closedHost (invoke s a vs)) :
    ([], .div) ∈ wasmEvFunD s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.invoke_div_closed hs hS hok hd

/-- **Adequacy, empty log** (deterministic profile `profile o`, any host): a Core run of a typed
invocation with no host event, quiescent from there by host-free divergence, is the behaviour
`([], div)` of `wasmEvFunD`, whose log the host allows. -/
theorem wasmEvFunD_of_evRun_nil {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {c' : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (SingleThreaded.profile o) host (invoke s a vs) [] c')
    (hd : Diverges (SingleThreaded.profile o) (fun _ _ _ _ => False) c') :
    ([], .div) ∈ wasmEvFunD s (a, vs) ∧ (coreHostRel host).Consistent [] :=
  ⟨Silmaril.Proofs.Wasm.Abstract.HostClosingInf.evRun_nil_div hs hS hok hrun hd,
    evRun_consistent hrun⟩

end Silmaril.Wasm.Abstract
