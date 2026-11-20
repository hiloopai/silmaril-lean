module

public import Silmaril.Wasm.Component.Reference.LegalBoundaryRuns.Defs
public import Silmaril.Wasm.Component.Reference.LegalBoundary.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.Twin
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.Throw

/-!
# Exceptions become traps for every reference observation (theorems)

**Scope.** The reference machine `Machine.Step` over any engine, profile, host readiness and
dispatcher, for the generic part; the Core 3.0 engine `core3P P` at any profile `P`, for the
boundary of a canon call. The session relations are those from which every reference observation
set is defined: `SessCalls`, `SessDiv` and `SessExec`/`SessProd` (the finished outcomes, quiet
divergences and productive runs of `Linked2`, `LinkedSessionDiv`/`LinkedSessionObs`, and of
`LinkedG`, `LinkedGDiv`/`LinkedGInf`), `LinkedSession.SessRun` with `CallQuietDiverges`,
`SessExec` and `CallHostProd` (those of `HLinked2`, `HLinkedSessionDiv`/`HLinkedSessionInf`), and
`Machine.Diverges` (`LinkedGDiv`'s R7, `CallDiverges`).

**Hypotheses.** For the generic part, `StepTwin x y` (the same steps, both stores and host state, a
running activation each). For the boundary, none beyond the shapes stated: `X_throw` is
`coreCfg m th (.active f (throwing a)) k segs rest` (a core activation, any thread, continuation,
pending segments and resumers, whose code is an exception that escaped every handler), and
`X_trap` the same configuration with `[.trap]`. For the session corollaries, a run of the current
call (number `n`, started from `m₀` by the host's invocation) reaching `X_throw` whose host events
are those `Calls` allows and which has no `internal` fault.

**Proved.**

1. **Twins have the same observations from there on** (any engine): the same nonempty runs
   (`StepTwin.steps_cons`), divergences (`StepTwin.diverges`), infinite runs with host events
   (`StepTwin.divergesWithHost`), quiet divergences (`StepTwin.quietDiverges`,
   `StepTwin.quietRest`), host chatter (`StepTwin.hostProdRest`), and the same rest of the
   session call: answer and continuing configuration (`StepTwin.sessRest`).
2. **The rests are exactly what the observations see of a call**: `Calls` and `SessStep` are the
   invocation followed by `CallRest`/`SessRest` (`calls_iff`, `sessStep_iff`), `CallQuietDiverges`
   and `CallHostProd` the invocation followed by `QuietRest`/`HostProdRest`
   (`callQuietDiverges_iff`, `callHostProd_iff`); a rest from a configuration reached during the
   call composes with that prefix (`calls_of_callRest`, `sessStep_of_sessRest`,
   `callDiverges_of_diverges`, `callQuietDiverges_of_quietRest`, `callHostProd_of_hostProdRest`),
   and a session step with the session before and after it (`sessCalls_cons`, `sessDiv_cons`,
   `sessRun_cons`, `sessRun_sessCalls`, `sessRun_sessDiv`, `sessRun_append`).
3. **A thrown and a trapped core activation are twins** (`stepTwin_throw_trap`). The rest of the
   session call from either is exactly the trap, the session resuming from
   `resumeCfg m₀ (trapCfg m)` (`sessRest_throw_iff`, `sessRest_trap_iff`), so every continuation
   observation `Q` agrees (`sessRest_throw_iff_trap`, `rest_throw_iff_trap`, `rest_throw_iff`).
   Neither has any infinite rest: no divergence, no infinite run with host events, no quiet
   divergence, no host chatter (`not_diverges_trap`, `not_divergesWithHost_throw`, `not_divergesWithHost_trap`,
   `not_quietRest_throw`, `not_quietRest_trap`, `not_hostProdRest_throw`,
   `not_hostProdRest_trap`).
4. **Whole sessions.** After a session prefix (`SessRun`, e.g. from the configuration after
   instantiation), a call reaching `X_throw` contributes to the finished outcomes, the quiet
   divergences and the session runs exactly what the rest from `X_trap` contributes
   (`sessStep_through_trap`, `sessCalls_through_trap`, `sessDiv_through_trap`,
   `sessRun_through_trap`; the converse direction from `X_throw` is `sessRest_throw_iff_trap`).
   A productive execution (`SessExec`) is a stream of `SessStep`s, so `sessStep_through_trap`
   applies at each call. For the infinite observations (`CallDiverges`, `CallQuietDiverges`,
   `CallHostProd`) neither configuration can lie on the infinite run. Hence no reference
   observation set of `Linked2`, `LinkedG` or `HLinked2` distinguishes `throwing a` from
   `[.trap]` at the boundary.
5. **The only difference.** The configurations themselves differ (`coreCfg_throw_ne_trap`): an
   observation reading the configuration at that point (the empty run `Steps x [] x`, or the
   final configuration of a call that was already trapped there, `CallRest x c x .trap`)
   distinguishes them. No observation set above reads it: a finished call that traps is observed
   through `resumeCfg m₀`, which reads only the core store and host state, and these agree.

**Not claimed.**

* The instantiated observation predicates (`Linked2.RefSessQuiet`, `LinkedG.RefSessProd`,
  `HLinked2.RefSessDiv`, …) are not restated one by one: they are existentials over the session
  relations of item 4 from the configuration after instantiation, and the statements here are
  about those relations.
* No relation between different engines (an engine in which Core exceptions cross the boundary)
  is stated; `X_trap` is the hypothetical twin of `X_throw` on the same machine.
-/

public section

namespace Silmaril.Wasm.Component.Reference.LegalBoundaryRuns

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.StepDefs Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.LegalBoundary (coreCfg)
open Silmaril.Wasm.Execution.Core (throwing Frame)

local notation "RVal" => Silmaril.Wasm.Component.Value.Val

/-! ## Twins -/

section Twin

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)} {x y : Config E σ}

namespace StepTwin

theorem symm (t : StepTwin prof hr dispatch x y) : StepTwin prof hr dispatch y x :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_symm t

/-- Twins have the same nonempty runs. -/
theorem steps_cons (t : StepTwin prof hr dispatch x y) {l : Label E σ} {tr : List (Label E σ)}
    {m' : Config E σ} :
    Steps prof hr dispatch x (l :: tr) m' ↔ Steps prof hr dispatch y (l :: tr) m' :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_steps_cons t

/-- Twins diverge together. -/
theorem diverges (t : StepTwin prof hr dispatch x y) :
    Diverges prof hr dispatch x ↔ Diverges prof hr dispatch y :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_diverges t

/-- Twins have infinite runs (host events included) together. -/
theorem divergesWithHost (t : StepTwin prof hr dispatch x y) :
    DivergesWithHost prof hr dispatch x ↔ DivergesWithHost prof hr dispatch y :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_divergesWithHost t

/-- Twins satisfy the same call outcomes (only `trap`, if any: both have a running activation). -/
theorem holds (t : StepTwin prof hr dispatch x y) (c : CallId) (out : CallOutcome) :
    out.Holds hr c x ↔ out.Holds hr c y :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_holds t c out

/-- **Twins have the same rest of the session call**: the same answers and continuing
configurations. -/
theorem sessRest [∀ a b, Decidable (E.ExternSub a b)] {h : Host E σ} {x y : Config E σ}
    (t : StepTwin prof h.hr h.dispatch x y) {m₀ m₁ : Config E σ} {n : Nat}
    {o : Option (List RVal)} : SessRest prof h m₀ x n o m₁ ↔ SessRest prof h m₀ y n o m₁ :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_sessRest t

/-- Twins diverge quietly together, in every host state. -/
theorem quietDiverges (t : StepTwin prof hr dispatch x y) (st : σ) :
    QuietDiverges prof hr dispatch st x ↔ QuietDiverges prof hr dispatch st y :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_quietDiverges t st

/-- **Twins have the same quiet divergences of the rest of the call.** -/
theorem quietRest (t : StepTwin prof hr dispatch x y) (st : σ) :
    QuietRest prof hr dispatch st x ↔ QuietRest prof hr dispatch st y :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_quietRest t st

/-- **Twins have the same host chatter of the rest of the call.** -/
theorem hostProdRest {ε : Type} {hr : HostReady (σ × List ε)}
    {dispatch : Call E → P E (σ × List ε) (Ret E)} {x y : Config E (σ × List ε)}
    (t : StepTwin prof hr dispatch x y) (base : List ε) (ev : ℕ → ε) :
    HostProdRest prof hr dispatch base x ev ↔ HostProdRest prof hr dispatch base y ev :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.twin_hostProdRest t base ev

end StepTwin

end Twin

/-! ## Calls and sessions are prefixes followed by rests -/

section Compose

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-- A top-level call is the host's invocation followed by the rest of the call. -/
theorem calls_iff {m m' : Config E σ} {c : CallId} {f : FuncId} {args : List RVal}
    {out : CallOutcome} :
    Calls prof hr dispatch m c f args m' out ↔
      ∃ x, Step prof hr dispatch m (.host (invokeTop c f args)) x ∧
        CallRest prof hr dispatch x c m' out :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.calls_iff

/-- A prefix of the call to `x` followed by the rest from `x` is the call. -/
theorem calls_of_callRest {m x m' : Config E σ} {c : CallId} {f : FuncId} {args : List RVal}
    {tr : List (Label E σ)} {out : CallOutcome}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent c ev)
    (hint : out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : CallRest prof hr dispatch x c m' out) : Calls prof hr dispatch m c f args m' out :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.calls_of_callRest h hev hint r

/-- A prefix of the call to `x` followed by a divergence from `x` is a divergent call. -/
theorem callDiverges_of_diverges {m x : Config E σ} {c : CallId} {f : FuncId}
    {args : List RVal} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hh : ∀ ev, Label.host ev ∉ tr) (d : Diverges prof hr dispatch x) :
    CallDiverges prof hr dispatch m c f args :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.callDiverges_of_diverges h hh d

/-- A quietly diverging call is the invocation followed by a quiet rest. -/
theorem callQuietDiverges_iff {m : Config E σ} {c : CallId} {f : FuncId} {args : List RVal}
    {st : σ} :
    CallQuietDiverges prof hr dispatch m c f args st ↔
      ∃ x, Step prof hr dispatch m (.host (invokeTop c f args)) x ∧
        QuietRest prof hr dispatch st x :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.callQuietDiverges_iff

/-- A host-free prefix of the call to `x` followed by a quiet rest from `x`. -/
theorem callQuietDiverges_of_quietRest {m x : Config E σ} {c : CallId} {f : FuncId}
    {args : List RVal} {tr : List (Label E σ)} {st : σ}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hh : ∀ ev, Label.host ev ∉ tr) (r : QuietRest prof hr dispatch st x) :
    CallQuietDiverges prof hr dispatch m c f args st :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.callQuietDiverges_of_quietRest
    h hh r

section Chatter

variable {ε : Type} {hr : HostReady (σ × List ε)} {dispatch : Call E → P E (σ × List ε) (Ret E)}

/-- A chattering call is the invocation followed by a host-chatter rest, from the log at the
invocation. -/
theorem callHostProd_iff {m : Config E (σ × List ε)} {c : CallId} {f : FuncId}
    {args : List RVal} {ev : ℕ → ε} :
    CallHostProd prof hr dispatch m c f args ev ↔
      ∃ x, Step prof hr dispatch m (.host (invokeTop c f args)) x ∧
        HostProdRest prof hr dispatch m.host.2 x ev :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.callHostProd_iff

/-- A host-free prefix of the call to `x` followed by a host-chatter rest from `x`. -/
theorem callHostProd_of_hostProdRest {m x : Config E (σ × List ε)} {c : CallId} {f : FuncId}
    {args : List RVal} {tr : List (Label E (σ × List ε))} {ev : ℕ → ε}
    (h : Steps prof hr dispatch m (.host (invokeTop c f args) :: tr) x)
    (hh : ∀ e, Label.host e ∉ tr) (r : HostProdRest prof hr dispatch m.host.2 x ev) :
    CallHostProd prof hr dispatch m c f args ev :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.callHostProd_of_hostProdRest
    h hh r

end Chatter

section Sess

variable [∀ a b, Decidable (E.ExternSub a b)] {h : Host E σ}

/-- A session call is the host's invocation followed by the rest of the session call. -/
theorem sessStep_iff {m₀ m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)} :
    SessStep prof h m₀ n f args o m₁ ↔
      ∃ x, Step prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ f args)) x ∧
        SessRest prof h m₀ x n o m₁ :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessStep_iff

/-- A prefix of the session call to `x` followed by the rest from `x` is the session call. -/
theorem sessStep_of_sessRest {m₀ x m₁ : Config E σ} {n : Nat} {f : FuncId}
    {args : List RVal} {tr : List (Label E σ)} {o : Option (List RVal)}
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ f args) :: tr) x)
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : o = none → ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : SessRest prof h m₀ x n o m₁) : SessStep prof h m₀ n f args o m₁ :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessStep_of_sessRest h₁ hev hint r

theorem sessCalls_cons {m₀ m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)} {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    (s : SessStep prof h m₀ n f args o m₁) (r : SessCalls prof h m₁ (n + 1) cs outs) :
    SessCalls prof h m₀ n ((f, args) :: cs) (o :: outs) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessCalls_cons s r

theorem sessDiv_cons {m₀ m₁ : Config E σ} {n : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)} {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    {g : FuncId} {gargs : List RVal}
    (s : SessStep prof h m₀ n f args o m₁) (r : SessDiv prof h m₁ (n + 1) cs outs g gargs) :
    SessDiv prof h m₀ n ((f, args) :: cs) (o :: outs) g gargs :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessDiv_cons s r

theorem sessRun_cons {m₀ m₁ m' : Config E σ} {n : Nat} {f : FuncId} {args : List RVal}
    {o : Option (List RVal)} {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    (s : SessStep prof h m₀ n f args o m₁)
    (r : LinkedSession.SessRun prof h m₁ (n + 1) cs outs m') :
    LinkedSession.SessRun prof h m₀ n ((f, args) :: cs) (o :: outs) m' :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessRun_cons s r

theorem sessRun_sessCalls {m₀ m' : Config E σ} {n : Nat} {cs cs' : List (FuncId × List RVal)}
    {outs outs' : List (Option (List RVal))}
    (r : LinkedSession.SessRun prof h m₀ n cs outs m')
    (c : SessCalls prof h m' (n + cs.length) cs' outs') :
    SessCalls prof h m₀ n (cs ++ cs') (outs ++ outs') :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessRun_sessCalls r c

theorem sessRun_sessDiv {m₀ m' : Config E σ} {n : Nat} {cs cs' : List (FuncId × List RVal)}
    {outs outs' : List (Option (List RVal))} {g : FuncId} {gargs : List RVal}
    (r : LinkedSession.SessRun prof h m₀ n cs outs m')
    (c : SessDiv prof h m' (n + cs.length) cs' outs' g gargs) :
    SessDiv prof h m₀ n (cs ++ cs') (outs ++ outs') g gargs :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessRun_sessDiv r c

theorem sessRun_append {m₀ m' m'' : Config E σ} {n : Nat}
    {cs cs' : List (FuncId × List RVal)} {outs outs' : List (Option (List RVal))}
    (r : LinkedSession.SessRun prof h m₀ n cs outs m')
    (c : LinkedSession.SessRun prof h m' (n + cs.length) cs' outs' m'') :
    LinkedSession.SessRun prof h m₀ n (cs ++ cs') (outs ++ outs') m'' :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessRun_append r c

end Sess

end Compose

/-! ## A thrown and a trapped core activation -/

section Throw

variable {P : Silmaril.Wasm.Numerics.Profile} {σ : Type} {prof : ProfileKind}
  {th : Option ThreadId} {f : Frame} {a : Nat}

section Machine

variable {hr : HostReady σ} {dispatch : Call (core3P P) → Canon.P (core3P P) σ (Ret (core3P P))}
  {m : Config (core3P P) σ} {k : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
  {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)}

/-- **A core activation that threw and the same activation trapped are twins.** -/
theorem stepTwin_throw_trap :
    StepTwin prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest)
      (coreCfg m th (.active f [.trap]) k segs rest) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.stepTwin_throw_trap

/-- **The only difference**: the two configurations are not equal. -/
theorem coreCfg_throw_ne_trap :
    coreCfg m th (.active f (throwing a)) k segs rest ≠
      coreCfg m th (.active f [.trap]) k segs rest :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.coreCfg_throw_ne_trap

/-- A core activation that trapped does not diverge (as one that threw, `not_diverges_throw`). -/
theorem not_diverges_trap :
    ¬ Diverges prof hr dispatch (coreCfg m th (.active f [.trap]) k segs rest) := fun d =>
  LegalBoundary.not_diverges_throw (a := 0) (stepTwin_throw_trap.diverges.2 d)

/-- A core activation that threw has no infinite run, even with host events. -/
theorem not_divergesWithHost_throw :
    ¬ DivergesWithHost prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.not_divergesWithHost_throw

/-- A core activation that trapped has no infinite run, even with host events. -/
theorem not_divergesWithHost_trap :
    ¬ DivergesWithHost prof hr dispatch (coreCfg m th (.active f [.trap]) k segs rest) := fun d =>
  not_divergesWithHost_throw (a := 0) (stepTwin_throw_trap.divergesWithHost.2 d)

/-- No quiet divergence from a core activation that threw. -/
theorem not_quietRest_throw {st : σ} :
    ¬ QuietRest prof hr dispatch st (coreCfg m th (.active f (throwing a)) k segs rest) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.not_quietRest_throw

/-- No quiet divergence from a core activation that trapped. -/
theorem not_quietRest_trap {st : σ} :
    ¬ QuietRest prof hr dispatch st (coreCfg m th (.active f [.trap]) k segs rest) := fun d =>
  not_quietRest_throw (a := 0) ((stepTwin_throw_trap.quietRest st).2 d)

end Machine

section Chatter

variable {ε : Type} {hr : HostReady (σ × List ε)}
  {dispatch : Call (core3P P) → Canon.P (core3P P) (σ × List ε) (Ret (core3P P))}
  {m : Config (core3P P) (σ × List ε)}
  {k : List FlatValue → Canon.P (core3P P) (σ × List ε) (Ret (core3P P))}
  {segs : List (Seg (core3P P) (σ × List ε))} {rest : List (Activation (core3P P) (σ × List ε))}
  {base : List ε} {ev : ℕ → ε}

/-- No host chatter from a core activation that threw. -/
theorem not_hostProdRest_throw :
    ¬ HostProdRest prof hr dispatch base (coreCfg m th (.active f (throwing a)) k segs rest) ev :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.not_hostProdRest_throw

/-- No host chatter from a core activation that trapped. -/
theorem not_hostProdRest_trap :
    ¬ HostProdRest prof hr dispatch base (coreCfg m th (.active f [.trap]) k segs rest) ev :=
  fun d => not_hostProdRest_throw (a := 0) ((stepTwin_throw_trap.hostProdRest base ev).2 d)

end Chatter

section Sess

variable {h : Host (core3P P) σ} {m m₀ m₁ : Config (core3P P) σ}
  {k : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
  {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)} {n : Nat}
  {o : Option (List RVal)}

/-- **The rest of the session call from a core activation that threw**: exactly the trap, the
session resuming from `resumeCfg m₀ (trapCfg m)`. -/
theorem sessRest_throw_iff :
    SessRest prof h m₀ (coreCfg m th (.active f (throwing a)) k segs rest) n o m₁ ↔
      o = none ∧ m₁ = resumeCfg m₀ (trapCfg m) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundaryRuns.sessRest_throw_iff

/-- **The same rest of the session call from one that trapped.** -/
theorem sessRest_trap_iff :
    SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁ ↔
      o = none ∧ m₁ = resumeCfg m₀ (trapCfg m) :=
  (stepTwin_throw_trap (a := 0)).sessRest.symm.trans sessRest_throw_iff

/-- **Thrown and trapped have the same rest of the session call.** -/
theorem sessRest_throw_iff_trap :
    SessRest prof h m₀ (coreCfg m th (.active f (throwing a)) k segs rest) n o m₁ ↔
      SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁ :=
  stepTwin_throw_trap.sessRest

/-- **Every continuation observation agrees**: for any observation `Q` of the answer and the
configuration the session continues from (`SessCalls`, `SessDiv`, `SessRun`, the tail of a
`SessExec`, …), continuing from a thrown or a trapped activation gives the same (namely `Q` of
the trap and `resumeCfg m₀ (trapCfg m)`, `rest_throw_iff`). -/
theorem rest_throw_iff_trap (Q : Option (List RVal) → Config (core3P P) σ → Prop) :
    (∃ o m₁, SessRest prof h m₀ (coreCfg m th (.active f (throwing a)) k segs rest) n o m₁ ∧
        Q o m₁) ↔
      (∃ o m₁, SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁ ∧
        Q o m₁) := by
  simp only [sessRest_throw_iff, sessRest_trap_iff]

/-- The continuation observations from a thrown activation are those of the trap, resuming from
`resumeCfg m₀ (trapCfg m)`. -/
theorem rest_throw_iff (Q : Option (List RVal) → Config (core3P P) σ → Prop) :
    (∃ o m₁, SessRest prof h m₀ (coreCfg m th (.active f (throwing a)) k segs rest) n o m₁ ∧
        Q o m₁) ↔ Q none (resumeCfg m₀ (trapCfg m)) := by
  simp only [sessRest_throw_iff]
  exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, hq⟩ => hq, fun hq => ⟨_, _, ⟨rfl, rfl⟩, hq⟩⟩

section Through

variable {g : FuncId} {args : List RVal} {tr : List (Label (core3P P) σ)}

/-- **The session call through a thrown activation, continued from the trapped one.** -/
theorem sessStep_through_trap
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁) :
    SessStep prof h m₀ n g args o m₁ :=
  sessStep_of_sessRest h₁ hev (fun _ => hint) (sessRest_throw_iff_trap.2 r)

variable {m₀' : Config (core3P P) σ} {j : Nat} {pre : List (FuncId × List RVal)}
  {pouts : List (Option (List RVal))}

/-- **Finished session outcomes**: after a session prefix, a call through a thrown activation
continued from the trapped one, then a session continuing, is a finished session. -/
theorem sessCalls_through_trap {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    (hpre : LinkedSession.SessRun prof h m₀' j pre pouts m₀) (hn : n = j + pre.length)
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁)
    (c : SessCalls prof h m₁ (n + 1) cs outs) :
    SessCalls prof h m₀' j (pre ++ (g, args) :: cs) (pouts ++ o :: outs) := by
  subst hn
  exact sessRun_sessCalls hpre (sessCalls_cons (sessStep_through_trap h₁ hev hint r) c)

/-- **Quiet divergences**: after a session prefix, a call through a thrown activation continued
from the trapped one, then a session ending in a divergent call, is a diverging session. -/
theorem sessDiv_through_trap {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    {g' : FuncId} {args' : List RVal}
    (hpre : LinkedSession.SessRun prof h m₀' j pre pouts m₀) (hn : n = j + pre.length)
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁)
    (c : SessDiv prof h m₁ (n + 1) cs outs g' args') :
    SessDiv prof h m₀' j (pre ++ (g, args) :: cs) (pouts ++ o :: outs) g' args' := by
  subst hn
  exact sessRun_sessDiv hpre (sessDiv_cons (sessStep_through_trap h₁ hev hint r) c)

/-- **Session runs** (the prefixes of `HLinked2`'s quiet divergences and host chatter): after a
session prefix, a call through a thrown activation continued from the trapped one, then a
session run. -/
theorem sessRun_through_trap {cs : List (FuncId × List RVal)} {outs : List (Option (List RVal))}
    {m' : Config (core3P P) σ}
    (hpre : LinkedSession.SessRun prof h m₀' j pre pouts m₀) (hn : n = j + pre.length)
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (r : SessRest prof h m₀ (coreCfg m th (.active f [.trap]) k segs rest) n o m₁)
    (c : LinkedSession.SessRun prof h m₁ (n + 1) cs outs m') :
    LinkedSession.SessRun prof h m₀' j (pre ++ (g, args) :: cs) (pouts ++ o :: outs) m' := by
  subst hn
  exact sessRun_append hpre (sessRun_cons (sessStep_through_trap h₁ hev hint r) c)

end Through

end Sess

end Throw

end Silmaril.Wasm.Component.Reference.LegalBoundaryRuns
