module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Execution.Core.InversionHost.Thms
import Silmaril.Proofs.Wasm.Abstract.HostCall.Basic
import Silmaril.Proofs.Wasm.Abstract.HostCall.Backward
import Silmaril.Proofs.Wasm.Abstract.HostCall.Split
import Silmaril.Proofs.Wasm.Abstract.HostCall.Runs
import Silmaril.Proofs.Wasm.Abstract.HostCall.Through
import Silmaril.Proofs.Wasm.Abstract.HostCall.Typed

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

`coreHost_call_run_seq` is the same **under a continuation** `rest` after the
call. It uses the sequence-context inversion `Step.callRef_host_inv_seq`, built
on the existing head decomposition `Sim.Step.split_head`.

**Not yet proved.** The backward simulation of whole native runs.
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

end Silmaril.Wasm.Abstract
