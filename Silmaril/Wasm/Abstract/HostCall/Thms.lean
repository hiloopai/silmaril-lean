module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Execution.Core.InversionHost.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Games.Abstract.ModuleInf.Defs
import Silmaril.Proofs.Wasm.Abstract.HostCall.Basic
import Silmaril.Proofs.Wasm.Abstract.HostCall.Backward
import Silmaril.Proofs.Wasm.Abstract.HostCall.Split
import Silmaril.Proofs.Wasm.Abstract.HostCall.Runs
import Silmaril.Proofs.Wasm.Abstract.HostCall.Through
import Silmaril.Proofs.Wasm.Abstract.HostCall.Typed
import Silmaril.Proofs.Wasm.Abstract.HostCall.Ctx
import Silmaril.Proofs.Wasm.Abstract.HostCall.Div
import Silmaril.Proofs.Wasm.Abstract.HostCall.Events
import Silmaril.Proofs.Wasm.Abstract.HostCall.Logged
import Silmaril.Proofs.Wasm.Abstract.HostCall.LoggedDiv
import Silmaril.Proofs.Wasm.Abstract.HostCall.Chain

/-!
# Core 3.0 host calls as a relational host: theorems (stage H2, first step)

The single Core step of a host call, read through `coreHostRel`. For any
caller frame, every profile and every host:

* `coreHost_answer_step`: an allowed answer `(s', r)` is the Core step
  `Step.callRefHost` from `vals us ++ [ref.func a, call_ref]` to `r`, with the
  store `s'` the host left;
* `coreHost_diverge`: allowed host divergence makes that configuration diverge
  in Core (`Step.callRefHostDiv` stutters forever);
* `coreHost_functional_iff`: the relational host is functional exactly when
  the Core host semantics is deterministic. Only then does `hostObs_unique`
  apply.

* `coreHost_blocked_stuck`: a call the host has **no** outcome for (`blocked`)
  has no Core step at all (by `Step.callRef_host_stuck`). It is stuck: not
  divergence, not a trap.

In context, for a direct `call` (the shape the native relation will produce):

* `coreHost_call_answer`: `vals ws ++ vals us ++ call x :: rest` runs in two
  steps to `vals ws ++ r.toAdmin ++ rest` in the host's store `s'`;
* `coreHost_call_diverge`: it diverges when the host may diverge.

**Backward, first step** (`coreHost_call_run`): a Core run from a host call,
on exactly its arguments, to a configuration with no step is either **blocked**
(it never left the call, and the host has no outcome) or **answered**: the
host returned `(s', r)` and the run continues from `vals ws ++ r.toAdmin` in
`s'`. Divergence of the host only stutters, so it never ends a run. The answer
is read off the run; nothing is assumed about the host.

**Splitting runs of sequences** (for the whole-run backward simulation):

* `steps_trap_head`, `steps_throw_head`: a trap, or the canonical thrown form
  `throwing x = [ref.exn x, throw_ref]`, at the head of the code only bubbles;
  every run to a stuck configuration ends at `[trap]` (resp. `throwing x`) in
  the same store and frame;
* `steps_seq_split`: a run of `es ++ rest` to a stuck configuration first runs
  `es` alone to a stuck `c₁`; then `c₁` is values and the run continues from
  them followed by `rest`, or `c₁` is `[trap]`/`throwing x` and is the end of
  the run, or `c₁` is stuck on another head and the run ends at
  `c₁.code ++ rest`.

**Counted runs** (`StepsN`, the measure of the whole-run backward simulation):
`StepsN.steps`, `stepsN_of_steps`; `stepsN_seq_split` (the sequence split, with
`es` taking `n₁ ≤ n` steps and the continuation after values the remaining
`n - n₁`); `stepsN_label_split` (a label's body runs inside until the label is
stuck, or exits by `LabelExit` with `n - n₁ - 1` steps left).

**Runs pass through host-free steps** (deterministic profile `profile o`):
`stepsN_through`, `stepsN_through_steps`. A Core run with any host from `K` to a
stuck end also reaches that end, in no more steps, from any host-free successor
of `K` (or the end of any host-free run from `K`): host-free steps join within
one step, and a configuration with a host-free step is not at a host call.

**Typing with a relational host** (`HostTyped`: the typed-answers half of Core's
`HostOk`, without asking every call to have an outcome): `Step.host_mono` (steps
are monotone in the host, every profile), `hostOk_totalize` (the host that also
diverges where it has no outcome is lawful), `Step.preservation_typed`,
`ContextTyped.steps_typed`.

**Runs in a label or a call frame**: `labelExit_stuck` (every label exit form is
stuck, any host), `frameExit_label`, `stepsN_label_seq_split`,
`stepsN_frame_seq_split` (the body runs alone, counted, to a stuck end; then the
context around it goes on).

`coreHost_call_run_seq` is the same **under a continuation** `rest` after the
call. It uses the sequence-context inversion `Step.callRef_host_inv_seq`, built
on the existing head decomposition `Sim.Step.split_head`.

**Divergent runs** (any profile and host): `trap_not_diverges`, `throw_not_diverges` (an
abrupt head only bubbles), `diverges_seq_split` (a divergent run of `es ++ rest` diverges in
`es`, or `es` runs to values and the continuation diverges), `diverges_label_split`,
`diverges_frame_split` (a divergent label or frame diverges inside, or its body runs to an
exit form and what it exits to diverges), `diverges_host_call` (at a host call the host
may diverge, or it answers and the continuation diverges), `diverges_wasm_call` (a Wasm call
enters the callee's frame, which diverges), `diverges_label_seq_split`,
`diverges_frame_seq_split` (the same for a label or a call frame in place, under values and
before a continuation: the body diverges, or it runs to a stuck end and the context around
that end diverges). The divergent counterparts of the splits above, for the decomposition of
Core divergence.

**Divergent runs pass through host-free steps** (deterministic profile, any host, typed
configurations): `diverges_through`, `diverges_through_steps`. Host-free steps join within
one step, and every successor other than the interpreter's (`stepI`) is a bubbling step that
shrinks the code (`Interp.step?_lag_at`), so a divergent trace can be redirected through any
host-free successor.

**Host events of Core runs** (any profile and host). `HEvStep`: a Core step labelled by
its host event (`some e`: every answered host call, whatever its result and context; `none`:
a host-free step or a stutter at a host call the host diverges on). `Quiet` is divergence
without answered host calls, which includes stuttering at a diverging host call: it is not
claimed to be pure Wasm divergence.
`hEvStep_step`, `step_hEvStep`: labelled steps are exactly the Core steps; `hEvStep_unique`:
the label is determined by the step, so no host event is dropped or invented.
**`diverges_events`**: a Core run diverges iff it is quiescent after a finite run with host
events `cs` (`EvRun`, `Quiet`), or productive with an infinite stream `ω` of host events
(`CoreInf`, one coherent run cut at its events). No determinism is assumed.
`evRun_consistent`, `coreInf_consistent`: every recorded event is an answer the host allows.
`coreInf_prefix` (**prefix agreement**): the first `n` events of a productive run are the
events of a finite labelled run of that same run, which continues productively with the
remaining events.
`quiet_iff`: quiescent divergence is exactly host-free divergence (pure Wasm), or a host-free
run to a host call the host diverges on (stuttering there: the `hostDiv` case).

**Labelled runs, split with their logs** (`EvRunN`, the counted `EvRun`; proofs in `Logged`).
The end of a run is only asked to have no *host-free* step, so it may sit at a host call the
host could answer. `evRunN_of_evRun`, `evRunN_evRun`, `evRunN_steps`; `evRunN_seq_split`,
`evRunN_label_seq_split`, `evRunN_frame_seq_split`: the splits of `stepsN_seq_split` and the
label and frame splits, the log split as a concatenation; when the inner part ends at a host
call (`decompose?`), the outer run ends there too, with no events left. `evRunN_through`,
`evRunN_through_steps` (deterministic profile): a labelled run passes through host-free steps
with the same log. `evRunN_unique`, `evRunN_host_call`: a unique host-free step, and a host call,
which ends the run or is answered by its next event. `evRunN_trap_head`: a head trap only
bubbles, with no events. `hEvStep_ctx`: labelled steps lift through contexts with the same label.

**A logged prefix, then host-free divergence** (`EvDiv`, cut at the last event; proofs in
`LoggedDiv`). `evDiv_of_evRun`: a labelled run followed by host-free divergence is `EvDiv`.
`evDiv_seq_split`, `evDiv_label_seq_split`, `evDiv_frame_seq_split`: the inner part diverges
with the whole log, or runs to a stuck end (not at a host call) with a prefix of it, and the
continuation goes on with the rest. `evDiv_through_steps` (deterministic profile, typed start),
`evDiv_unique` (a unique host-free step, a smaller measure when there are events),
`evDiv_host_call` (the next event answers the host call), `evDiv_stuck`, `evDiv_trap`,
`evDiv_nil`, `evDiv_mono`.

**Building labelled and productive runs** (proofs in `Chain`), for the forward simulation of
logged native runs: `evRun_of_free` (a host-free run is silent); `hEvStep_label`,
`hEvStep_frame` (labelled steps lift through a label and a call frame), `evRun_wrap`,
`coreInf_wrap` (a context lifting labelled steps lifts labelled and productive runs), and its
instances `evRun_ctx`, `evRun_label`, `evRun_frame`, `coreInf_ctx`, `coreInf_label`,
`coreInf_frame` (a sequence context, a label and a call frame); `hEvStep_host_call` (an answered host call is one event);
`coreInf_prepend` (a labelled run in front of a productive run); **`coreInf_of_segments`**: a
chain of labelled runs `K n ⟶ K (n + 1)` whose logs concatenate to an unbounded stream `ω`
(`Shape.StreamConcat`) is a productive run with the events `ω`.

The backward simulation of whole native runs is in `Silmaril.Wasm.Abstract.HostEval`.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **An allowed host answer is one Core step**, any frame. -/
theorem coreHost_answer_step {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val} {r : Result}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hans : coreHostRel host ⟨h, s, us⟩ (.answer (s', r))) :
    Step P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ⟨s', f, r.toAdmin⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.answer_step hf he hn hcode hans

/-- **Allowed host divergence is Core divergence**, any frame. -/
theorem coreHost_diverge {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hdiv : coreHostRel host ⟨h, s, us⟩ .diverge) :
    Diverges P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverge_diverges hf he hn hcode hdiv

/-- The relational host is functional exactly when the host semantics is deterministic. -/
theorem coreHost_functional_iff :
    (coreHostRel host).Functional ↔
      ∀ h s vs (o o' : HostOutcome H), host h s vs o → host h s vs o' → o = o' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.functional_iff

/-- **A blocked host call is stuck in Core**, any frame. -/
theorem coreHost_blocked_stuck {s : Store H} {f : Frame} {c : Config H} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hno : ∀ ans, ¬ coreHostRel host ⟨h, s, us⟩ ans) :
    ¬ Step P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ c := by
  refine Step.callRef_host_stuck trivial hf hcode he hn fun o ho => ?_
  rcases o with ⟨s', r⟩ | _
  · exact hno (.answer (s', r)) ho
  · exact hno .diverge ho

/-- **A direct call of a host function, answered**, under values and before a continuation. -/
theorem coreHost_call_answer {s s' : Store H} {f : Frame} {x : Silmaril.Wasm.FuncIdx} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {us ws : List Val} {r : Result}
    {rest : List Admin} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length) (hcode : fi.code = .host h)
    (hans : coreHostRel host ⟨h, s, us⟩ (.answer (s', r))) :
    Steps P host ⟨s, f, vals ws ++ vals us ++ .plain (.call x) :: rest⟩
      ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.steps_call_answer hx hf he hn hcode hans

/-- **A direct call of a host function that may diverge diverges.** -/
theorem coreHost_call_diverge {s : Store H} {f : Frame} {x : Silmaril.Wasm.FuncIdx} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {us ws : List Val} {rest : List Admin}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length) (hcode : fi.code = .host h)
    (hdiv : coreHostRel host ⟨h, s, us⟩ .diverge) :
    Diverges P host ⟨s, f, vals ws ++ vals us ++ .plain (.call x) :: rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_call hx hf he hn hcode hdiv

/-- **The host answer of a Core host call, read off a run to a stuck
configuration**: blocked, or answered and continuing from the host's result. -/
theorem coreHost_call_run {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} {ws us : List Val} {c : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (hrun : Steps P host ⟨s, f, vals ws ++ vals us ++ [.ref (.func a), .callRefType fi.type]⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    (c = ⟨s, f, vals ws ++ vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ∧
        ∀ ans, ¬ coreHostRel host ⟨hh, s, us⟩ ans) ∨
      ∃ s' r, coreHostRel host ⟨hh, s, us⟩ (.answer (s', r)) ∧
        Steps P host ⟨s', f, vals ws ++ r.toAdmin⟩ c := by
  rcases Silmaril.Proofs.Wasm.Abstract.HostCall.host_call_run hf hcode he hn hrun hend with
    ⟨hc, hno⟩ | ⟨s', r, hh', hst⟩
  · refine .inl ⟨hc, fun ans hans => ?_⟩
    rcases ans with ⟨s', r⟩ | _
    · exact hno _ hans
    · exact hno _ hans
  · exact .inr ⟨s', r, hh', hst⟩

/-- **A Core host call under a continuation, read off a run to a stuck
configuration**: blocked at the call, or answered and continuing from the host's
result followed by the continuation. -/
theorem coreHost_call_run_seq {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin} {c : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (hrun : Steps P host
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ∧
        ∀ ans, ¬ coreHostRel host ⟨hh, s, us⟩ ans) ∨
      ∃ s' r, coreHostRel host ⟨hh, s, us⟩ (.answer (s', r)) ∧
        Steps P host ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ c := by
  rcases Silmaril.Proofs.Wasm.Abstract.HostCall.host_call_run_seq hf hcode he hn hrun hend with
    ⟨hc, hno⟩ | ⟨s', r, hh', hst⟩
  · refine .inl ⟨hc, fun ans hans => ?_⟩
    rcases ans with ⟨s', r⟩ | _
    · exact hno _ hans
    · exact hno _ hans
  · exact .inr ⟨s', r, hh', hst⟩

/-- `[trap]` does not step, in any profile, host, store and frame. -/
theorem trap_stuck {s : Store H} {f : Frame} {c : Config H} : ¬ Step P host ⟨s, f, [.trap]⟩ c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.trap_stuck

/-- **A head trap only bubbles** to `[trap]`, in the same store and frame. -/
theorem steps_trap_head {s : Store H} {f : Frame} {ws : List Val} {r : List Admin} {c : Config H}
    (hrun : Steps P host ⟨s, f, vals ws ++ .trap :: r⟩ c) (hend : ∀ c', ¬ Step P host c c') :
    c = ⟨s, f, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.steps_trap_head hrun hend

/-- **A head exception only bubbles** to `throwing x`, in the same store and frame. -/
theorem steps_throw_head {s : Store H} {f : Frame} {ws : List Val} {x : Nat} {r : List Admin}
    {c : Config H} (hrun : Steps P host ⟨s, f, vals ws ++ throwing x ++ r⟩ c)
    (hend : ∀ c', ¬ Step P host c c') : c = ⟨s, f, throwing x⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.steps_throw_head hrun hend

/-- **Splitting a run of a sequence** `es ++ rest` at the end of `es`. -/
theorem steps_seq_split {s : Store H} {f : Frame} {es rest : List Admin} {c : Config H}
    (hrun : Steps P host ⟨s, f, es ++ rest⟩ c) (hend : ∀ c', ¬ Step P host c c') :
    ∃ c₁ : Config H, Steps P host ⟨s, f, es⟩ c₁ ∧ (∀ c', ¬ Step P host c₁ c') ∧
      ((∃ ws, c₁.code = vals ws ∧ Steps P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ c) ∨
        (c₁.code = [.trap] ∧ c = c₁) ∨ (∃ x, c₁.code = throwing x ∧ c = c₁) ∨
        c = ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.steps_seq_split hrun hend

theorem stepsN_steps {n : Nat} {c c' : Config H} (h : StepsN P host n c c') : Steps P host c c' :=
  h.steps

theorem stepsN_of_steps {c c' : Config H} (h : Steps P host c c') : ∃ n, StepsN P host n c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_of_steps h

/-- **Splitting a counted run of a sequence** `es ++ rest` at the end of `es`. -/
theorem stepsN_seq_split {n : Nat} {s : Store H} {f : Frame} {es rest : List Admin}
    {c : Config H} (hrun : StepsN P host n ⟨s, f, es ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    ∃ (c₁ : Config H) (n₁ : Nat), StepsN P host n₁ ⟨s, f, es⟩ c₁ ∧ n₁ ≤ n ∧
      (∀ c', ¬ Step P host c₁ c') ∧
      ((∃ ws, c₁.code = vals ws ∧
          StepsN P host (n - n₁) ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ c) ∨
        (c₁.code = [.trap] ∧ c = c₁) ∨ (∃ x, c₁.code = throwing x ∧ c = c₁) ∨
        c = ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_seq_split hrun hend

/-- **Splitting a counted run of a label**: its body runs inside until the label
is stuck, or exits. -/
theorem stepsN_label_split {n : Nat} {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {is : List Admin} {c : Config H} (hrun : StepsN P host n ⟨s, f, [.label k cont is]⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    ∃ (c₁ : Config H) (n₁ : Nat), StepsN P host n₁ ⟨s, f, is⟩ c₁ ∧ n₁ ≤ n ∧
      ((c = ⟨c₁.store, c₁.frame, [.label k cont c₁.code]⟩ ∧ ∀ c', ¬ Step P host c₁ c') ∨
        ∃ out, n₁ < n ∧ LabelExit k cont c₁.code out ∧
          StepsN P host (n - n₁ - 1) ⟨c₁.store, c₁.frame, out⟩ c) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_label_split hrun hend

/-- **A run to a stuck end passes through every host-free step.** -/
theorem stepsN_through {o : SingleThreaded.GrowOracle} {n : Nat} {K c d : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n K c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (hd : SingleThreaded.Det.DStep o K d) :
    ∃ m ≤ n, StepsN (SingleThreaded.profile o) host m d c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_through hrun hend hd

/-- **A run to a stuck end passes through every host-free run.** -/
theorem stepsN_through_steps {o : SingleThreaded.GrowOracle} {n : Nat} {K T c : Config H}
    (hpred : Relation.ReflTransGen (SingleThreaded.Det.DStep o) K T)
    (hrun : StepsN (SingleThreaded.profile o) host n K c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    ∃ m ≤ n, StepsN (SingleThreaded.profile o) host m T c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_through_steps hpred hrun hend

/-- **Core steps are monotone in the host.** -/
theorem Step.host_mono {host' : HostSemantics H} (hle : ∀ h s vs o, host h s vs o → host' h s vs o)
    {c c' : Config H} (hst : Step P host c c') : Step P host' c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.Step.host_mono hle hst

/-- **A host with typed answers, totalized, is lawful.** -/
theorem hostOk_totalize (ht : HostTyped host) : HostOk (totalize host) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hostOk_totalize ht

/-- **Preservation for a host with typed answers** (no outcome needs to exist). -/
theorem Step.preservation_typed (ht : HostTyped host) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (h : Step P host c c') : ConfigOk c' ts ∧ Extend c.store c'.store :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.Step.preservation_typed ht hc h

/-- Typing in an evaluation context is preserved along runs of a host with typed answers. -/
theorem ContextTyped.steps_typed (ht : HostTyped host) {c c' : Config H} (h : Sim.ContextTyped c)
    (hs : Steps P host c c') : Sim.ContextTyped c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.ContextTyped.steps_typed ht h hs

/-- **A host call under a continuation, on counted runs**: blocked, or answered with
the continuation taking fewer steps than the whole run. -/
theorem host_call_runN_seq {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin} {c : Config H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length)
    (hrun : StepsN P host n
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ∧
        ∀ o, ¬ host hh s us o) ∨
      ∃ s' r m, m < n ∧ host hh s us (.returned s' r) ∧
        StepsN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.host_call_runN_seq hf hcode he hn hrun hend

/-- **Every label exit form is stuck**, whatever the host. -/
theorem labelExit_stuck {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {b out : List Admin}
    (h : LabelExit n cont b out) (c : Config H) : ¬ Step P host ⟨s, f, b⟩ c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.labelExit_stuck h c

/-- A frame around a single label does not exit. -/
theorem frameExit_label {s : Store H} {fi : Frame} {n k : Nat} {cont : List Instr}
    {b code out : List Admin} (h : FrameExit s fi n code out) (hc : code = [.label k cont b]) :
    False :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.frameExit_label h hc

/-- **A run in a label**: the body runs alone to a stuck end, then the label goes on. -/
theorem stepsN_label_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {c : Config H}
    (hrun : StepsN P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    ∃ (cb : Config H) (N₁ : Nat), N₁ ≤ N ∧ StepsN P host N₁ ⟨s, f, b⟩ cb ∧
      (∀ c', ¬ Step P host cb c') ∧
      StepsN P host (N - N₁) ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_label_seq_split hrun hend

/-- **A run in a call frame**: the callee body runs alone, in its frame, to a stuck
end; then the frame and label go on. -/
theorem stepsN_frame_seq_split {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {c : Config H}
    (hrun : StepsN P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ c)
    (hend : ∀ c', ¬ Step P host c c') :
    ∃ (cb : Config H) (N₁ : Nat), N₁ ≤ N ∧ StepsN P host N₁ ⟨s, F, b⟩ cb ∧
      (∀ c', ¬ Step P host cb c') ∧
      StepsN P host (N - N₁)
        ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.stepsN_frame_seq_split hrun hend

/-! ## Splitting divergent runs -/

/-- A head trap does not diverge. -/
theorem trap_not_diverges {s : Store H} {f : Frame} {ws : List Val} {r : List Admin} :
    ¬ Diverges P host ⟨s, f, vals ws ++ .trap :: r⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.trap_not_diverges

/-- A head exception does not diverge. -/
theorem throw_not_diverges {s : Store H} {f : Frame} {ws : List Val} {x : Nat}
    {r : List Admin} : ¬ Diverges P host ⟨s, f, vals ws ++ throwing x ++ r⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.throw_not_diverges

/-- **Splitting a divergent run of a sequence** `es ++ rest`: it diverges in `es`, or `es`
runs to values `ws` and the run of `vals ws ++ rest` diverges. -/
theorem diverges_seq_split {s : Store H} {f : Frame} {es rest : List Admin}
    (h : Diverges P host ⟨s, f, es ++ rest⟩) :
    Diverges P host ⟨s, f, es⟩ ∨
      ∃ (c₁ : Config H) (ws : List Val), Steps P host ⟨s, f, es⟩ c₁ ∧ c₁.code = vals ws ∧
        Diverges P host ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_seq_split h

/-- **Splitting a divergent run of a label**: it diverges inside, or its body runs to an
exit form and what it exits to diverges. -/
theorem diverges_label_split {s : Store H} {f : Frame} {k : Nat} {cont : List Instr}
    {is : List Admin} (h : Diverges P host ⟨s, f, [.label k cont is]⟩) :
    Diverges P host ⟨s, f, is⟩ ∨
      ∃ (c₁ : Config H) (out : List Admin), Steps P host ⟨s, f, is⟩ c₁ ∧
        LabelExit k cont c₁.code out ∧ Diverges P host ⟨c₁.store, c₁.frame, out⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_label_split h

/-- **Splitting a divergent run of a frame**: it diverges inside (in the frame's own frame),
or its body runs to an exit form and what it exits to diverges in the outer frame. -/
theorem diverges_frame_split {s : Store H} {f F : Frame} {n : Nat} {is : List Admin}
    (h : Diverges P host ⟨s, f, [.frame n F is]⟩) :
    Diverges P host ⟨s, F, is⟩ ∨
      ∃ (c₁ : Config H) (out : List Admin), Steps P host ⟨s, F, is⟩ c₁ ∧
        FrameExit c₁.store c₁.frame n c₁.code out ∧ Diverges P host ⟨c₁.store, f, out⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_frame_split h

/-- **A divergent run at a host call**: the host may diverge on the call, or it answers and
the run of the continuation diverges. -/
theorem diverges_host_call {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {r : Admin}
    {fi : FuncInst H} {hh : H} {rest : List Admin} (hr : r.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (h : Diverges P host ⟨s, f, vals vs ++ .ref (.func a) :: r :: rest⟩) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Validation.Expand fi.type (.func ps rs) ∧
      vs₂.length = ps.length ∧
      (host hh s vs₂ .diverged ∨
        ∃ s' res, host hh s vs₂ (.returned s' res) ∧
          Diverges P host ⟨s', f, vals vs₁ ++ res.toAdmin ++ rest⟩) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_host_call hr hf hcode h

/-- **A divergent run at a Wasm call** enters the callee's frame, and the run from there
diverges. -/
theorem diverges_wasm_call {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {r : Admin}
    {fi : FuncInst H} {code : Func} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (h : Diverges P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Validation.Expand fi.type (.func ps rs) ∧
      vs₂.length = ps.length ∧
      Diverges P host ⟨s, f, vals vs₁ ++ [.frame rs.length (Frame.forCall fi.module vs₂ code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_wasm_call hr hf hcode h

/-- **Splitting a divergent run of a label in place**, under values and before a
continuation: the body diverges, or it runs to a stuck end and the label around that end
diverges. -/
theorem diverges_label_seq_split {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin}
    (h : Diverges P host ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩) :
    Diverges P host ⟨s, f, b⟩ ∨
      ∃ cb : Config H, Steps P host ⟨s, f, b⟩ cb ∧ (∀ c', ¬ Step P host cb c') ∧
        Diverges P host ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_label_seq_split h

/-- **Splitting a divergent run of a call frame in place**: the callee body diverges in its
frame, or it runs to a stuck end and the frame and label around that end diverge. -/
theorem diverges_frame_seq_split {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin}
    (h : Diverges P host ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩) :
    Diverges P host ⟨s, F, b⟩ ∨
      ∃ cb : Config H, Steps P host ⟨s, F, b⟩ cb ∧ (∀ c', ¬ Step P host cb c') ∧
        Diverges P host
          ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_frame_seq_split h

/-- **A divergent run passes through every host-free step** of a typed configuration
(deterministic profile, any host). -/
theorem diverges_through {o : SingleThreaded.GrowOracle} {K d : Config H}
    (ht : Sim.ContextTyped K) (hK : Diverges (SingleThreaded.profile o) host K)
    (hd : SingleThreaded.Det.DStep o K d) : Diverges (SingleThreaded.profile o) host d :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_through ht hK hd

/-- **A divergent run passes through every host-free run** of a typed configuration
(deterministic profile, any host). -/
theorem diverges_through_steps {o : SingleThreaded.GrowOracle} {K T : Config H}
    (hpred : Relation.ReflTransGen (SingleThreaded.Det.DStep o) K T) (ht : Sim.ContextTyped K)
    (hK : Diverges (SingleThreaded.profile o) host K) : Diverges (SingleThreaded.profile o) host T :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_through_steps hpred ht hK

/-! ## Host events of Core runs -/

/-- A labelled step is a Core step. -/
theorem hEvStep_step {c c' : Config H} {e : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c e c') : Step P host c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hEvStep_step h

/-- Every Core step is labelled. -/
theorem step_hEvStep {c c' : Config H} (h : Step P host c c') : ∃ e, HEvStep P host c e c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.step_hEvStep h

/-- **The label of a step is determined**: no host event is dropped or invented. -/
theorem hEvStep_unique {c c' : Config H} {e e' : Option (Call (wasmHostSig H))}
    (h : HEvStep P host c e c') (h' : HEvStep P host c e' c') : e = e' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hEvStep_unique h h'

/-- A finite labelled run is a Core run. -/
theorem evRun_steps {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : Steps P host c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_steps h

/-- A productive run is Core divergence. -/
theorem coreInf_diverges {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) : Diverges P host c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_diverges h

/-- **Divergence by host events**: a Core run diverges iff it is quiescent after a finite run
with host events `cs`, or productive with an infinite stream `ω` of host events. -/
theorem diverges_events {c : Config H} :
    Diverges P host c ↔
      (∃ cs c', EvRun P host c cs c' ∧ Quiet P host c') ∨ ∃ ω, CoreInf P host c ω :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverges_events

/-- Finite labelled runs compose. -/
theorem evRun_trans {c₁ c₂ c₃ : Config H} {cs cs' : List (Call (wasmHostSig H))}
    (h : EvRun P host c₁ cs c₂) (h' : EvRun P host c₂ cs' c₃) : EvRun P host c₁ (cs ++ cs') c₃ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_trans h h'

/-- **The events of a finite labelled run are allowed by the host.** -/
theorem evRun_consistent {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : (coreHostRel host).Consistent cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_consistent h

/-- **The events of a productive run are allowed by the host.** -/
theorem coreInf_consistent {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) (n : Nat) : coreHostRel host (ω n).1 (.answer (ω n).2) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_consistent h n

/-- **Prefix agreement**: the first `n` events of a productive run are the events of a finite
labelled run of that run, which continues productively with the remaining events. -/
theorem coreInf_prefix {c : Config H} {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf P host c ω) (n : Nat) :
    ∃ c', EvRun P host c (List.ofFn fun i : Fin n => ω i) c' ∧
      CoreInf P host c' (fun k => ω (n + k)) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_prefix h n

/-- **Quiescent divergence, split**: host-free divergence, or a host-free run to a host call
the host diverges on. -/
theorem quiet_iff {c : Config H} :
    Quiet P host c ↔ (Diverges P (fun _ _ _ _ => False) c ∨
      ∃ d : Config H, Steps P (fun _ _ _ _ => False) c d ∧
        ∃ E a hh us, SingleThreaded.decompose? d.store d.code = some (E, a, hh, us) ∧
          host hh d.store us .diverged) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.quiet_iff

/-! ## Labelled runs, split with their logs -/

theorem evRunN_evRun {n : Nat} {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRunN P host n c cs c') : EvRun P host c cs c' :=
  h.evRun

theorem evRunN_of_evRun {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') : ∃ n, EvRunN P host n c cs c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_of_evRun h

theorem evRunN_steps {n : Nat} {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRunN P host n c cs c') : Steps P host c c' :=
  h.steps

theorem evRunN_zero_eq {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRunN P host 0 c cs c') : c' = c :=
  h.zero_eq

/-- A labelled run from a configuration with no step at all is empty. -/
theorem evRunN_of_stuck {m : Nat} {X c : Config H} {cs : List (Call (wasmHostSig H))}
    (hX : ∀ c', ¬ Step P host X c') (h : EvRunN P host m X cs c) : c = X ∧ cs = [] :=
  h.of_stuck hX

/-- At a host call there is no host-free step. -/
theorem noFree_of_decompose {c c' : Config H} {x : SingleThreaded.Ctx × Nat × H × List Val}
    (hd : SingleThreaded.decompose? c.store c.code = some x) :
    ¬ Step P SingleThreaded.Det.noHost c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.noFree_of_decompose hd

theorem decompose?_label_some {s : Store H} {n : Nat} {cont : List Instr} {b : List Admin}
    {E : SingleThreaded.Ctx} {a : Nat} {hh : H} {us : List Val}
    (hd : SingleThreaded.decompose? s b = some (E, a, hh, us)) :
    SingleThreaded.decompose? s [.label n cont b] = some (.label [] n cont E [], a, hh, us) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.decompose?_label_some hd

theorem decompose?_frame_some {s : Store H} {n : Nat} {F : Frame} {b : List Admin}
    {E : SingleThreaded.Ctx} {a : Nat} {hh : H} {us : List Val}
    (hd : SingleThreaded.decompose? s b = some (E, a, hh, us)) :
    SingleThreaded.decompose? s [.frame n F b] = some (.frame [] n F E [], a, hh, us) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.decompose?_frame_some hd

/-- A label exit form is not at a host call. -/
theorem decompose?_labelExit {s : Store H} {n : Nat} {cont : List Instr} {b out : List Admin}
    (h : LabelExit n cont b out) : SingleThreaded.decompose? s b = none :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.decompose?_labelExit h

/-- **A labelled step lifts through a sequence context**, with the same label. -/
theorem hEvStep_ctx {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {l : Option (Call (wasmHostSig H))} (ws : List Val) (rest : List Admin)
    (h : HEvStep P host ⟨s, f, es⟩ l ⟨s', f', es'⟩) :
    HEvStep P host ⟨s, f, vals ws ++ es ++ rest⟩ l ⟨s', f', vals ws ++ es' ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hEvStep_ctx ws rest h

/-- **A head trap only bubbles**, with no host event. -/
theorem evRunN_trap_head {m : Nat} {s : Store H} {f : Frame} {ws : List Val} {r : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host m ⟨s, f, vals ws ++ .trap :: r⟩ cs c)
    (hend : ∀ c', ¬ Step P SingleThreaded.Det.noHost c c') : c = ⟨s, f, [.trap]⟩ ∧ cs = [] :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_trap_head hrun hend

/-- **Splitting a labelled run of a sequence** `es ++ rest` at the end of `es`, the log split
as a concatenation. -/
theorem evRunN_seq_split {n : Nat} {s : Store H} {f : Frame} {es rest : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host n ⟨s, f, es ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P SingleThreaded.Det.noHost c c') :
    ∃ (c₁ : Config H) (n₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
      EvRunN P host n₁ ⟨s, f, es⟩ cs₁ c₁ ∧ n₁ ≤ n ∧
      (∀ c', ¬ Step P SingleThreaded.Det.noHost c₁ c') ∧
      ((∃ ws, c₁.code = vals ws ∧
          EvRunN P host (n - n₁) ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ cs₂ c) ∨
        (c₁.code = [.trap] ∧ c = c₁ ∧ cs₂ = []) ∨
        (∃ x, c₁.code = throwing x ∧ c = c₁ ∧ cs₂ = []) ∨
        (c = ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩ ∧ cs₂ = [])) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_seq_split hrun hend

/-- **A labelled run in a label**: the body runs alone; then the label around it goes on. If
the body ends at a host call, so does the whole run. -/
theorem evRunN_label_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P SingleThreaded.Det.noHost c c') :
    ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
      N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
      (∀ c', ¬ Step P SingleThreaded.Det.noHost cb c') ∧
      EvRunN P host (N - N₁) ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩
        cs₂ c ∧
      ((SingleThreaded.decompose? cb.store cb.code).isSome →
        cs₂ = [] ∧ c = ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_label_seq_split hrun hend

/-- **A labelled run in a call frame**: the callee body runs alone, in its frame; then the
frame and label around it go on. If the body ends at a host call, so does the whole run. -/
theorem evRunN_frame_seq_split {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hrun : EvRunN P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ cs c)
    (hend : ∀ c', ¬ Step P SingleThreaded.Det.noHost c c') :
    ∃ (cb : Config H) (N₁ : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))), cs = cs₁ ++ cs₂ ∧
      N₁ ≤ N ∧ EvRunN P host N₁ ⟨s, F, b⟩ cs₁ cb ∧
      (∀ c', ¬ Step P SingleThreaded.Det.noHost cb c') ∧
      EvRunN P host (N - N₁)
        ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ cs₂ c ∧
      ((SingleThreaded.decompose? cb.store cb.code).isSome → cs₂ = [] ∧
        c = ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_frame_seq_split hrun hend

/-- **A labelled run passes through every host-free step**, with the same log. -/
theorem evRunN_through {o : SingleThreaded.GrowOracle} {n : Nat} {K c : Config H}
    {cs : List (Call (wasmHostSig H))} (hrun : EvRunN (SingleThreaded.profile o) host n K cs c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) SingleThreaded.Det.noHost c c')
    {d : Config H} (hd : SingleThreaded.Det.DStep o K d) :
    ∃ m ≤ n, EvRunN (SingleThreaded.profile o) host m d cs c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_through hrun hend hd

/-- **A labelled run passes through every host-free run**, with the same log. -/
theorem evRunN_through_steps {o : SingleThreaded.GrowOracle} {n : Nat} {K T c : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hpred : Relation.ReflTransGen (SingleThreaded.Det.DStep o) K T)
    (hrun : EvRunN (SingleThreaded.profile o) host n K cs c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) SingleThreaded.Det.noHost c c') :
    ∃ m ≤ n, EvRunN (SingleThreaded.profile o) host m T cs c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_through_steps hpred hrun hend

/-- A labelled run from a configuration whose only step is a host-free step to `d` goes
through `d`, one step shorter, with the same log. -/
theorem evRunN_unique {n : Nat} {K d c : Config H} {cs : List (Call (wasmHostSig H))}
    (huniq : ∀ c₁, Step P host K c₁ → c₁ = d) (hK : Step P SingleThreaded.Det.noHost K d)
    (hrun : EvRunN P host n K cs c) (hend : ∀ c', ¬ Step P SingleThreaded.Det.noHost c c') :
    ∃ m, n = m + 1 ∧ EvRunN P host m d cs c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_unique huniq hK hrun hend

/-- **A labelled run at a host call**: it ends there with no event, or its next event answers
the call. -/
theorem evRunN_host_call {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin}
    {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hrun : EvRunN P host n
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ cs c) :
    (c = ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ ∧
        cs = []) ∨
      ∃ s' r m cs', m < n ∧ cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧
        host hh s us (.returned s' r) ∧
        EvRunN P host m ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRunN_host_call hf hcode he hn hrun

/-! ## A logged prefix, then host-free divergence -/

/-- **A labelled run followed by host-free divergence** is `EvDiv`. -/
theorem evDiv_of_evRun {c c' : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c') (hd : Diverges P (fun _ _ _ _ => False) c') :
    ∃ n, EvDiv P host n c cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_of_evRun h hd

theorem evDiv_mono {n n' : Nat} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hn : n ≤ n') (h : EvDiv P host n c cs) : EvDiv P host n' c cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_mono hn h

/-- With no event, `EvDiv` is host-free divergence. -/
theorem evDiv_nil {n : Nat} {c : Config H} (h : EvDiv P host n c []) :
    Diverges P (fun _ _ _ _ => False) c :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_nil h

/-- A configuration with no step does not diverge, with or without events. -/
theorem evDiv_stuck {n : Nat} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hX : ∀ c', ¬ Step P host c c') : ¬ EvDiv P host n c cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_stuck hX

/-- A head trap does not diverge, with or without events. -/
theorem evDiv_trap {n : Nat} {s : Store H} {f : Frame} {ws : List Val} {r : List Admin}
    {cs : List (Call (wasmHostSig H))} : ¬ EvDiv P host n ⟨s, f, vals ws ++ .trap :: r⟩ cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_trap

/-- **Splitting a sequence**: `es` diverges with the whole log, or runs to values with a
prefix of the log and the continuation goes on with the rest. -/
theorem evDiv_seq_split {n : Nat} {s : Store H} {f : Frame} {es rest : List Admin}
    {cs : List (Call (wasmHostSig H))} (h : EvDiv P host n ⟨s, f, es ++ rest⟩ cs) :
    EvDiv P host n ⟨s, f, es⟩ cs ∨
      ∃ (c₁ : Config H) (n₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))) (ws : List Val),
        cs = cs₁ ++ cs₂ ∧ m ≤ n ∧ EvRunN P host n₁ ⟨s, f, es⟩ cs₁ c₁ ∧ c₁.code = vals ws ∧
        EvDiv P host m ⟨c₁.store, c₁.frame, vals ws ++ rest⟩ cs₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_seq_split h

/-- **Splitting a label in place**: the body diverges with the whole log, or runs to a stuck
end that is not at a host call with a prefix of the log, and the label around that end goes
on with the rest. -/
theorem evDiv_label_seq_split {N : Nat} {s : Store H} {f : Frame} {ws : List Val} {n : Nat}
    {cont : List Instr} {b rest : List Admin} {cs : List (Call (wasmHostSig H))}
    (h : EvDiv P host N ⟨s, f, vals ws ++ [.label n cont b] ++ rest⟩ cs) :
    EvDiv P host N ⟨s, f, b⟩ cs ∨
      ∃ (cb : Config H) (N₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))),
        cs = cs₁ ++ cs₂ ∧ m ≤ N ∧ EvRunN P host N₁ ⟨s, f, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P SingleThreaded.Det.noHost cb c') ∧
        SingleThreaded.decompose? cb.store cb.code = none ∧
        EvDiv P host m ⟨cb.store, cb.frame, vals ws ++ [.label n cont cb.code] ++ rest⟩ cs₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_label_seq_split h

/-- **Splitting a call frame in place**: the callee body diverges with the whole log, or runs
to a stuck end that is not at a host call with a prefix of the log, and the frame and label
around that end go on with the rest. -/
theorem evDiv_frame_seq_split {N : Nat} {s : Store H} {f F : Frame} {ws : List Val} {n : Nat}
    {b rest : List Admin} {cs : List (Call (wasmHostSig H))}
    (h : EvDiv P host N ⟨s, f, vals ws ++ [.frame n F [.label n [] b]] ++ rest⟩ cs) :
    EvDiv P host N ⟨s, F, b⟩ cs ∨
      ∃ (cb : Config H) (N₁ m : Nat) (cs₁ cs₂ : List (Call (wasmHostSig H))),
        cs = cs₁ ++ cs₂ ∧ m ≤ N ∧ EvRunN P host N₁ ⟨s, F, b⟩ cs₁ cb ∧
        (∀ c', ¬ Step P SingleThreaded.Det.noHost cb c') ∧
        SingleThreaded.decompose? cb.store cb.code = none ∧
        EvDiv P host m
          ⟨cb.store, f, vals ws ++ [.frame n cb.frame [.label n [] cb.code]] ++ rest⟩ cs₂ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_frame_seq_split h

/-- **Through host-free steps**, with the same log (deterministic profile, typed start). -/
theorem evDiv_through_steps {o : SingleThreaded.GrowOracle} {n : Nat} {K T : Config H}
    {cs : List (Call (wasmHostSig H))}
    (hpred : Relation.ReflTransGen (SingleThreaded.Det.DStep o) K T) (ht : Sim.ContextTyped K)
    (h : EvDiv (SingleThreaded.profile o) host n K cs) :
    EvDiv (SingleThreaded.profile o) host n T cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_through_steps hpred ht h

/-- **Through a unique host-free step**, with a smaller measure, when there are events. -/
theorem evDiv_unique {n : Nat} {K d : Config H} {cs : List (Call (wasmHostSig H))}
    (huniq : ∀ c₁, Step P host K c₁ → c₁ = d) (hK : Step P SingleThreaded.Det.noHost K d)
    (hcs : cs ≠ []) (h : EvDiv P host n K cs) : ∃ m < n, EvDiv P host m d cs :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_unique huniq hK hcs h

/-- **At a host call** the next event answers it, and the run goes on from the answer. -/
theorem evDiv_host_call {n : Nat} {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {hh : H} {ps rs : Ty (.list .val)} {ws us : List Val} {rest : List Admin}
    {cs : List (Call (wasmHostSig H))}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : EvDiv P host n
      ⟨s, f, vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ cs) :
    ∃ s' r cs', cs = ⟨(hh, s, us), (s', r)⟩ :: cs' ∧ host hh s us (.returned s' r) ∧
      EvDiv P host n ⟨s', f, vals ws ++ r.toAdmin ++ rest⟩ cs' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evDiv_host_call hf hcode he hn h

/-! ## Building labelled and productive runs -/

/-- **A host-free run is silent.** -/
theorem evRun_of_free {c c' : Config H} (h : Steps P (fun _ _ _ _ => False) c c') :
    EvRun P host c [] c' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_of_free h

/-- **A labelled step lifts through a label**, with the same label. -/
theorem hEvStep_label {s s' : Store H} {f f' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat) (cont : List Instr)
    (h : HEvStep P host ⟨s, f, b⟩ l ⟨s', f', b'⟩) :
    HEvStep P host ⟨s, f, [.label n cont b]⟩ l ⟨s', f', [.label n cont b']⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hEvStep_label n cont h

/-- **A labelled step lifts through a call frame**, with the same label. -/
theorem hEvStep_frame {s s' : Store H} {f F F' : Frame} {b b' : List Admin}
    {l : Option (Call (wasmHostSig H))} (n : Nat)
    (h : HEvStep P host ⟨s, F, b⟩ l ⟨s', F', b'⟩) :
    HEvStep P host ⟨s, f, [.frame n F b]⟩ l ⟨s', f, [.frame n F' b']⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hEvStep_frame n h

/-- A context lifting every labelled step lifts labelled runs. -/
theorem evRun_wrap (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c'))
    {c c' : Config H} {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') :
    EvRun P host (W c) cs (W c') :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_wrap W hW h

/-- A context lifting every labelled step lifts productive runs. -/
theorem coreInf_wrap (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c'))
    {c : Config H} {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host c ω) :
    CoreInf P host (W c) ω :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_wrap W hW h

/-- A labelled run under values and before a continuation. -/
theorem evRun_ctx {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {cs : List (Call (wasmHostSig H))} (ws : List Val) (rest : List Admin)
    (h : EvRun P host ⟨s, f, es⟩ cs ⟨s', f', es'⟩) :
    EvRun P host ⟨s, f, vals ws ++ es ++ rest⟩ cs ⟨s', f', vals ws ++ es' ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_ctx ws rest h

/-- A labelled run inside a label. -/
theorem evRun_label {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {cs : List (Call (wasmHostSig H))} (n : Nat) (cont : List Instr)
    (h : EvRun P host ⟨s, f, es⟩ cs ⟨s', f', es'⟩) :
    EvRun P host ⟨s, f, [.label n cont es]⟩ cs ⟨s', f', [.label n cont es']⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_label n cont h

/-- A labelled run inside a call frame; the outer frame is untouched. -/
theorem evRun_frame {s s' : Store H} {f F F' : Frame} {es es' : List Admin}
    {cs : List (Call (wasmHostSig H))} (n : Nat)
    (h : EvRun P host ⟨s, F, es⟩ cs ⟨s', F', es'⟩) :
    EvRun P host ⟨s, f, [.frame n F es]⟩ cs ⟨s', f, [.frame n F' es']⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.evRun_frame n h

/-- A productive run under values and before a continuation. -/
theorem coreInf_ctx {s : Store H} {f : Frame} {es : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (ws : List Val) (rest : List Admin) (h : CoreInf P host ⟨s, f, es⟩ ω) :
    CoreInf P host ⟨s, f, vals ws ++ es ++ rest⟩ ω :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_ctx ws rest h

/-- A productive run inside a label. -/
theorem coreInf_label {s : Store H} {f : Frame} {es : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (n : Nat) (cont : List Instr) (h : CoreInf P host ⟨s, f, es⟩ ω) :
    CoreInf P host ⟨s, f, [.label n cont es]⟩ ω :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_label n cont h

/-- A productive run inside a call frame. -/
theorem coreInf_frame {s : Store H} {f F : Frame} {es : List Admin}
    {ω : Nat → Call (wasmHostSig H)} (n : Nat) (h : CoreInf P host ⟨s, F, es⟩ ω) :
    CoreInf P host ⟨s, f, [.frame n F es]⟩ ω :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_frame n h

/-- **An answered host call is its one event**, any frame. -/
theorem hEvStep_host_call {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Ty (.list .val)} {us : List Val} {r : Result}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : us.length = ps.length) (hcode : fi.code = .host hh)
    (hans : host hh s us (.returned s' r)) :
    HEvStep P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
      (some ⟨(hh, s, us), (s', r)⟩) ⟨s', f, r.toAdmin⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.hEvStep_host_call hf he hn hcode hans

/-- **A finite labelled run in front of a productive run.** -/
theorem coreInf_prepend {x y : Config H} {cs : List (Call (wasmHostSig H))}
    {ω : Nat → Call (wasmHostSig H)} (hr : EvRun P host x cs y) (h : CoreInf P host y ω) :
    CoreInf P host x (Silmaril.Games.Abstract.Shape.streamAppend cs ω) :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_prepend hr h

/-- **A chain of labelled runs is a productive run**: segments `K n ⟶ K (n + 1)` with logs
`q n` whose concatenation is the unbounded stream `ω`. -/
theorem coreInf_of_segments (K : Nat → Config H) (q : Nat → List (Call (wasmHostSig H)))
    (h : ∀ n, EvRun P host (K n) (q n) (K (n + 1))) {ω : Nat → Call (wasmHostSig H)}
    (hq : Silmaril.Games.Abstract.Shape.StreamConcat q ω) : CoreInf P host (K 0) ω :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.coreInf_of_segments K q h hq

end Silmaril.Wasm.Abstract
