module

public import Silmaril.Wasm.Abstract.HostClosingInf.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Games.Abstract.HostRunInf.Thms
public import Silmaril.Games.Abstract.ModuleDLog.Thms
public import Silmaril.Wasm.Abstract.Decomp.Defs
public import Silmaril.Games.Abstract.ModuleInf.Thms
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Basic
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Pend
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Quiet
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Log
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Inf
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Conv
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Div
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.FwdTrap
import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.PendFwd

/-!
# Productive runs of invocations: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostClosingInf`. Every profile and host:

* `wasmEvInf_hostObsInf` (**adequacy**): the productive observations against a host,
  `hostObsInf (coreHostRel host) (wasmEvInf P)`, are exactly the productive Core runs with that
  host (`CoreInf`);
* `wasmEvInf_prefix` (**prefix agreement**): the first `n` events of such a run are the actual
  event log of a finite run of the invocation (`EvRun`), continued productively;
* `coreInf_pend` (deterministic profile, typed checked invocations): every finite prefix of a
  productive run is a logged pending prefix of `wasmEvPend` at the run's next host call, with
  **exactly** that log (from `evRun_pend`).

**A finite log, then host-free divergence** (`wasmEvFunD := Shape.closeDLog wasmHOpen LDLw`):

* `wasmEvFunD_of_ne_div`: off `div`, `wasmEvFunD` is `wasmEvFun`;
* `quietCall_closedCall`, `closedCall_quietCall`: the host-free oracle `quietCall` agrees with
  the closure `closedCall` on the ends of the answers it gives, and gives every closed answer a
  run can consume; so `localDivO_closed_quiet : LocalDivO closedCall ≤ LocalDivO quietCall` and
  `ldlw_of_wasmLocalDiv : wasmLocalDiv z → LDLw z []`;
* `wasmEvFunD_of_diverges_closed`: a host-free divergent typed invocation (deterministic
  profile) has the behaviour `([], div)`;
* `wasmEvFunD_of_evRun_nil`: **adequacy for the empty log**: a Core run of a typed invocation
  with no host event, then host-free divergence, is `([], div)` in `wasmEvFunD`;
* `wasmEvFunD_of_evRun` (deterministic profile, typed checked invocations, a host with typed
  answers in the native host slice): **adequacy for any log**: a Core run of a typed invocation
  with its exact host-event log `cs`, then host-free divergence, is `(cs, div)` in
  `wasmEvFunD`, with exactly that log. From `HostEval.evRun_divL` (a logged form of
  `HostEval.div_whole`, on the run cut at its last event) at
  `Q y q := (q, div) ∈ wasmEvFunD y`: host-free native divergence is local (`LogDiv.div`) or
  reaches a host-free divergent call; a body diverging after a resolved log is `LDLw`, and a
  body reaching a call after a resolved prefix is a descent with that prefix's import calls.

**Productive runs, natively** (`wasmEvInfN := Shape.closeInfL wasmHOpen InfLw`):

* `infL_nil`, `infL_loop_silent`, `infL_loop_op` (**productivity**): empty trees, a loop alone
  whose iterations log no call and whose body has no productive run, and in particular
  `loop { br 0 }`, claim no stream;
* `wasmEvInfN_of_infL`, `wasmEvInfN_of_reachL`, `closeInf_le_wasmEvInfN`: a resolved productive
  run of a Wasm body, a logged reach in front, and the productive runs through unbounded
  recursion are productive runs of the invocation;
* `coreInf_wasmEvInfN` (**the bridge**, deterministic profile, typed checked invocations, a
  host with typed answers in the native host slice): every productive Core run of an invocation
  is in `wasmEvInfN`, with exactly its host events. From `HostEval.coreInf_invokeL` at
  `Q y ω := ω ∈ wasmEvInfN y`: a body's productive run within its function is `InfLw`, a
  reach is a descent (`descends_of_reachL`), and an infinite chain of reaches is a
  `Shape.InfChain`;
* `hostObsInf_wasmEvInf_le`: so against such a host, the productive observations of the Core
  witness `wasmEvInf (profile o)` are productive observations of `wasmEvInfN`.

**The converse, natively to Core** (every profile, checked stores, typed invocations, a host in
the native host slice; no determinism and no `HostTyped` needed):

* `wasmEvFun_evRun` (**logged forward simulation of finite runs**): a returning behaviour
  `(cs, ret ws)` of `wasmEvFun` with a log the host allows is a Core run of the invocation
  whose host events are **exactly** `cs` (`EvRun`), ending at the values `ws`. Unlike
  `wasmEv_core_done` (a run with *some* events), the log is kept: each import call resolved by
  the closure is the one Core event of the answered host call, a Wasm callee contributes the
  events of its body inside its frame, and all other Core glue is host-free. Proof (`Fwd`,
  `FwdEval`): the cases of `Interp.wp_of_eval` with logs, by induction on `EvalL`, the arity
  facts from `Interp.evalH_good`, and least-fixpoint induction on the closure;
* `wasmEvFun_trap_evRun` (**the same for traps**): a trapping behaviour `(cs, trap)` of
  `wasmEvFun` with a log the host allows is a Core run of the invocation whose host events are
  exactly `cs`, ending at `[trap]` in the empty frame and some store (a trap carries none).
  Proof (`FwdTrap`): least-fixpoint induction on the closure; a body trapping itself is
  `evalL_fwd` in its frame, the trap leaving its label and frame; a body meeting a trapping
  callee (`Shape.Subst.intTrap`) is a descent (`descends_unwrap`), a logged reach that is a
  Core run into the call (`reachL_trap`), the callee's trap then bubbling out of every context;
  a host callee answering a trap is its one event;
* `wasmEvInfN_coreInf` (**the converse bridge**): every productive run `ω ∈ wasmEvInfN` whose
  answers the host allows is a productive Core run of the invocation with exactly the events
  `ω` (`CoreInf`). Proof (`Seg`, `FwdInf`, `Conv`): a productive run within a function
  (`InfL`) is, by induction, logged finite Core runs lifted through their contexts, ending in a
  loop iterating forever, a chain of iterations (`coreInf_of_segments`, the stream regrouped
  by iteration); a descent is a logged Core run from the call into the reached call, inside the
  callee frame; a descent path then a productive body, or an infinite chain of descents nested
  ever deeper, is a productive Core run;
* `wasmEvFunD_div_evRun` (**the converse of quiescent adequacy**): every divergent behaviour
  `(cs, div) ∈ wasmEvFunD` whose log the host allows is a Core run of the invocation with
  exactly the host events `cs` (`EvRun`), then host-free divergence. Proof (`Div`): `close` has
  no `div`; an infinite descent chain with finitely many import calls is the logged Core run of
  the descents carrying them, then infinitely many host-free descents nested ever deeper, each
  entering its callee in one step; a descent path to logged local divergence (`LDLw`) is the
  logged Core run of the path and of the `EvalL` prefix (`reachL_fwd`, `prefix_glue`, …), then
  host-free local divergence (`LocalDivO quietCall`), which is Core host-free divergence of the
  checked trees: a non-trapping terminating run with host-free callees is a logged run with no
  import call, and every unfolding takes a Core step or continues with strictly smaller trees
  (`InfiniteTrace.coinduct`). The simulation runs against `host` without its divergent outcomes,
  so the contexts it builds also lift host-free steps;
* `wasmEvFunD_div_iff` (deterministic profile, a host with typed answers in the native host
  slice, typed invocations): with `wasmEvFunD_of_evRun`, **divergence after a log is exactly
  quiescent Core divergence after a run with that log**;
* `hostObsInf_wasmEvInfN_le` (every profile): so the productive observations of `wasmEvInfN`
  against such a host are productive observations of the Core witness `wasmEvInf P`;
* `hostObsInf_wasmEvInf_eq` (deterministic profile, a host with typed answers in the native
  host slice, typed invocations): **the productive observations are equal**,
  `hostObsInf (coreHostRel host) (wasmEvInf (profile o)) = hostObsInf (coreHostRel host)
  wasmEvInfN`. The inclusion `⊆` is `hostObsInf_wasmEvInf_le` (deterministic profile only).

**Finished behaviours at exactly their log, both directions** (deterministic profile, typed
checked invocations, a host with typed answers in the native host slice), with
`HostEval.evRun_wasmEvFun_vals` and `HostEval.evRun_wasmEvFun_trap`:

* `wasmEvFun_vals_iff`: `(cs, ret (inl ws) s₂) ∈ wasmEvFun` with a log the host allows exactly
  when the invocation has a Core run with the host events `cs` to the values `ws` at `s₂`, in
  the empty frame (a run to values ends in no other frame, `HostEval.evRun_vals_frame`);
* `wasmEvFun_trap_iff`: `(cs, trap) ∈ wasmEvFun` with a log the host allows exactly when the
  invocation has a Core run with the host events `cs` to a trap, in some store.

**Pending calls at exactly their log, both directions**:

* `wasmEvPend_evRun` (every profile, checked stores, typed invocations, a host in the native
  host slice): a pending call `(cs, m)` of `wasmEvPend` with a log the host allows is a Core run
  of the invocation with exactly the host events `cs` to a configuration at the host call `m`
  (`decompose?`), in the store of `m`. Proof (`PendFwd`): by induction on `PendL`, each descent
  a logged reach (`reachL_fwd`) inside the callee frame; a host function invoked directly is the
  empty run. The call may have no host outcome, so the run is built against `host` also
  answering `m` (`answerAt`), whose step at `m` shows the call under the context built;
* `wasmEvPend_evRun_iff` (deterministic profile, typed checked invocations, a host with typed
  answers in the native host slice): with `evRun_pend`, the pending calls with a log the host
  allows are exactly the Core runs with that log to a configuration at that host call.

Exceptions `ret (inr t)` are not covered: the native host slice (`noThrow`) and the checker
exclude them from the Core side, and no statement here relates them.

Not yet: the exact-log finished agreement (`wasmEvFun_vals_iff`, `wasmEvFun_trap_iff`), the
inclusion `hostObsInf_wasmEvInf_le` (so the equality of productive observations), and adequacy
for divergence after a log (`wasmEvFunD_of_evRun`, so the equivalence `wasmEvFunD_div_iff`), and
the pending agreement `wasmEvPend_evRun_iff`, at profiles other than the deterministic one; the
forward directions (`wasmEvFun_evRun`, `wasmEvFun_trap_evRun`, `wasmEvInfN_coreInf`,
`wasmEvFunD_div_evRun`, `wasmEvPend_evRun`) hold at every profile.
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

/-- **Adequacy** (deterministic profile `profile o`, typed checked invocations, a host with
typed answers in the native host slice): a Core run of a typed invocation with its exact
host-event log `cs`, quiescent from there by host-free divergence, is the behaviour
`(cs, div)` of `wasmEvFunD`, whose log the host allows. -/
theorem wasmEvFunD_of_evRun {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val} {c' : Config H}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs)
    (hrun : EvRun (SingleThreaded.profile o) host (invoke s a vs) cs c')
    (hd : Diverges (SingleThreaded.profile o) (fun _ _ _ _ => False) c') :
    (cs, .div) ∈ wasmEvFunD s (a, vs) ∧ (coreHostRel host).Consistent cs :=
  ⟨Silmaril.Proofs.Wasm.Abstract.HostClosingInf.evRun_div hT hH hs hS hok hrun hd,
    evRun_consistent hrun⟩

/-- **Productive prefixes are logged pending calls, at the same log** (deterministic profile,
typed checked invocations). -/
theorem coreInf_pend {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf (SingleThreaded.profile o) host (invoke s a vs) ω) (n : Nat) :
    (streamTake ω n, (ω n).1) ∈ wasmEvPend s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.coreInf_pend hT hH hs hS hok h n

/-! ## Productive runs inside one function, natively -/

/-- **Empty trees have no productive run.** -/
theorem infL_nil {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfL s f stk [] ω := nofun

open Silmaril.Wasm.Binaryen in
/-- **A silent loop claims no stream**: a loop alone, whose iterations log no call and whose
body has no productive run of its own, has no productive run. -/
theorem infL_loop_silent {bt : BlockType} {body : List BExpr}
    (hsil : ∀ (s : Store H) f stk l r, EvalL s f stk body l r → l = [])
    (hno : ∀ (s : Store H) f stk (ω : Nat → OCall H), ¬ InfL s f stk body ω)
    {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfL s f stk [.loop bt body] ω :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.infL_loop_silent hsil hno

open Silmaril.Wasm.Binaryen in
/-- **`loop { i }` has no productive run** for a flat non-call instruction `i` with no operand
trees, such as `br 0`: the loop that a greatest fixpoint with an empty back edge would let
claim every stream. -/
theorem infL_loop_op {bt : BlockType} {i : Silmaril.Wasm.Instr} (hi : ∀ x, i ≠ .call x)
    {s : Store H} {f : Frame} {stk : List Val} {ω : Nat → OCall H} :
    ¬ InfL s f stk [.loop bt [.op i []]] ω :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.infL_loop_op hi

open Silmaril.Wasm.Binaryen in
/-- **A resolved productive run of a Wasm body** is a productive run of the invocation. -/
theorem wasmEvInfN_of_infL {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {fn : Func} {ω : Nat → OCall H} {ω' : Nat → Call (wasmHostSig H)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (h : InfL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ω)
    (hs : Shape.SubstInf (Shape.close wasmHOpen) (fun i => (ω i).lift) ω') :
    ω' ∈ wasmEvInfN s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInfN_of_infL hf hcode h hs

open Silmaril.Wasm.Binaryen in
/-- **A logged reach in a Wasm body**, its completed calls resolved to `q`, puts `q` in front
of the productive runs of the reached call. -/
theorem wasmEvInfN_of_reachL {y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {l : List (OCall H)} {z : (wasmOShape H).self.Op}
    {q : List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hr : ReachL y.2.2 (Frame.forCall fi.module y.2.1 fn.locals) [] (liftInstrs fn.body) l z)
    (hq : Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q)
    (h : ω ∈ wasmEvInfN z.2.2 (z.1, z.2.1)) : Shape.streamAppend q ω ∈ wasmEvInfN y.2.2 (y.1, y.2.1) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInfN_of_reachL hf hcode hty hr hq h

/-- The productive runs through unbounded recursion are productive runs of the invocation. -/
theorem closeInf_le_wasmEvInfN {s : Store H} {a : Nat} {vs : List Val} :
    Shape.closeInf wasmHOpen a s vs ⊆ wasmEvInfN s (a, vs) :=
  Shape.closeInf_subset_closeInfL _ _ _ _ _

/-- **The bridge** (deterministic profile `profile o`, typed checked invocations, a host with
typed answers in the native host slice): every productive Core run of an invocation is a
productive run of the logged native semantics `wasmEvInfN`, with exactly its host events. -/
theorem coreInf_wasmEvInfN {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf (SingleThreaded.profile o) host (invoke s a vs) ω) :
    ω ∈ wasmEvInfN s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.coreInf_wasmEvInfN hT hH hs hS hok h

/-- **The productive observations of the Core witness are native** (deterministic profile,
typed checked invocations): against a host, `wasmEvInf` observes no productive run that
`wasmEvInfN` does not. -/
theorem hostObsInf_wasmEvInf_le {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) :
    hostObsInf (coreHostRel host) (wasmEvInf (SingleThreaded.profile o)) s (a, vs) ⊆
      hostObsInf (coreHostRel host) wasmEvInfN s (a, vs) := by
  intro ω hω
  have h := wasmEvInf_hostObsInf.mp hω
  exact ⟨coreInf_wasmEvInfN hT hH hs hS hok h, fun n => coreInf_consistent h n⟩

/-! ## The converse, natively to Core -/

/-- **Logged forward simulation of finite runs** (every profile, checked stores, typed
invocations, a host in the native host slice): a returning behaviour of `wasmEvFun` with a log
the host allows is a Core run of the invocation whose host events are exactly that log. -/
theorem wasmEvFun_evRun (hH : Interp.NativeHostSlice host) {s s₂ : Store H} {a : Nat}
    {vs ws : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl ws) s₂) ∈ wasmEvFun s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvFun_evRun hH hS hok h hc

/-- **Logged forward simulation of trapping runs** (every profile, checked stores, typed
invocations, a host in the native host slice): a trapping behaviour of `wasmEvFun` with a log the
host allows is a Core run of the invocation to a trap whose host events are exactly that log. -/
theorem wasmEvFun_trap_evRun (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .trap) ∈ wasmEvFun s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvFun_trap_evRun hH hS hok h hc

/-- **Returning behaviours at exactly their log, both directions** (deterministic profile
`profile o`, typed checked invocations, a host with typed answers in the native host slice):
`(cs, ret (inl ws) s₂)` is a behaviour of `wasmEvFun` with a log the host allows exactly when the
invocation has a Core run with the host events `cs` to the values `ws` at `s₂`, in the empty
frame. -/
theorem wasmEvFun_vals_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s s₂ : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) :
    ((cs, .ret (.inl ws) s₂) ∈ wasmEvFun s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      EvRun (SingleThreaded.profile o) host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  ⟨fun h => wasmEvFun_evRun hH hS hok h.1 h.2,
    fun h => ⟨evRun_wasmEvFun_vals hT hH hs hS hok h, evRun_consistent h⟩⟩

/-- **Traps at exactly their log, both directions** (deterministic profile `profile o`, typed
checked invocations, a host with typed answers in the native host slice): `(cs, trap)` is a
behaviour of `wasmEvFun` with a log the host allows exactly when the invocation has a Core run
with the host events `cs` to a trap, in some store. -/
theorem wasmEvFun_trap_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) :
    ((cs, .trap) ∈ wasmEvFun s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ s₂, EvRun (SingleThreaded.profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  ⟨fun h => wasmEvFun_trap_evRun hH hS hok h.1 h.2,
    fun ⟨_, h⟩ => ⟨evRun_wasmEvFun_trap hT hH hs hS hok h, evRun_consistent h⟩⟩

/-- **Pending calls, natively to Core, at exactly their log** (every profile, checked stores,
typed invocations, a host in the native host slice): a pending call `(cs, m)` of `wasmEvPend`
with a log the host allows is a Core run of the invocation with exactly the host events `cs`,
to a configuration at the host call `m`, in the store of `m`. -/
theorem wasmEvPend_evRun (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : (cs, m) ∈ wasmEvPend s (a, vs)) (hc : (coreHostRel host).Consistent cs) :
    ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat), EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', m.1, m.2.2) ∧ c.store = m.2.1 :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvPend_evRun hH hS hok h hc

/-- **Pending calls at exactly their log, both directions** (deterministic profile `profile o`,
typed checked invocations, a host with typed answers in the native host slice):
`(cs, (hh, s', us))` is a pending call of `wasmEvPend` with a log the host allows exactly when
the invocation has a Core run with the host events `cs` to a configuration at the host call
`(hh, us)`, in the store `s'`. -/
theorem wasmEvPend_evRun_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s s' : Store H} {a : Nat} {vs us : List Val} {hh : H}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) :
    ((cs, (hh, s', us)) ∈ wasmEvPend s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat),
        EvRun (SingleThreaded.profile o) host (invoke s a vs) cs c ∧
        SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧ c.store = s' := by
  constructor
  · exact fun h => wasmEvPend_evRun hH hS hok h.1 h.2
  · rintro ⟨c, E, a', hrun, hd, rfl⟩
    exact ⟨evRun_pend hT hH hs hS hok hrun hd, evRun_consistent hrun⟩

/-- **The converse bridge** (every profile, checked stores, typed invocations, a host in the
native host slice): every productive run of the logged native semantics `wasmEvInfN` whose
answers the host allows is a productive Core run of the invocation with exactly its events. -/
theorem wasmEvInfN_coreInf (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)} (h : ω ∈ wasmEvInfN s (a, vs))
    (hc : ∀ n, coreHostRel host (ω n).1 (.answer (ω n).2)) :
    CoreInf P host (invoke s a vs) ω :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvInfN_coreInf hH hS hok h hc

/-- **The converse of quiescent adequacy** (every profile, checked stores, typed invocations, a
host in the native host slice): a divergent behaviour `(cs, div)` of `wasmEvFunD` whose log the
host allows is a Core run of the invocation with exactly the host events `cs`, then host-free
divergence. -/
theorem wasmEvFunD_div_evRun (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .div) ∈ wasmEvFunD s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    ∃ c', EvRun P host (invoke s a vs) cs c' ∧ Diverges P (fun _ _ _ _ => False) c' :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingInf.wasmEvFunD_div_evRun hH hS hok h hc

/-- **Divergence after a log, both directions** (deterministic profile `profile o`, typed checked
invocations, a host with typed answers in the native host slice): `(cs, div)` is a behaviour of
`wasmEvFunD` with a log the host allows exactly when the invocation has a Core run with the host
events `cs`, then host-free divergence. -/
theorem wasmEvFunD_div_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) :
    ((cs, .div) ∈ wasmEvFunD s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      ∃ c', EvRun (SingleThreaded.profile o) host (invoke s a vs) cs c' ∧
        Diverges (SingleThreaded.profile o) (fun _ _ _ _ => False) c' :=
  ⟨fun h => wasmEvFunD_div_evRun hH hS hok h.1 h.2,
    fun ⟨_, hrun, hd⟩ => wasmEvFunD_of_evRun hT hH hs hS hok hrun hd⟩

/-- **The productive observations of `wasmEvInfN` are Core observations** (every profile): against
a host in the native host slice, `wasmEvInfN` observes no productive run that the Core witness
`wasmEvInf P` does not. -/
theorem hostObsInf_wasmEvInfN_le (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat}
    {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) :
    hostObsInf (coreHostRel host) wasmEvInfN s (a, vs) ⊆
      hostObsInf (coreHostRel host) (wasmEvInf P) s (a, vs) :=
  fun _ hω => wasmEvInf_hostObsInf.mpr (wasmEvInfN_coreInf hH hS hok hω.1 hω.2)

/-- **The productive observations are equal** (deterministic profile `profile o`, typed checked
invocations, a host with typed answers in the native host slice): the Core witness and the
logged native semantics have the same productive observations against the host. -/
theorem hostObsInf_wasmEvInf_eq {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) :
    hostObsInf (coreHostRel host) (wasmEvInf (SingleThreaded.profile o)) s (a, vs) =
      hostObsInf (coreHostRel host) wasmEvInfN s (a, vs) :=
  Set.Subset.antisymm (hostObsInf_wasmEvInf_le hT hH hs hS hok) (hostObsInf_wasmEvInfN_le hH hS hok)

end Silmaril.Wasm.Abstract
