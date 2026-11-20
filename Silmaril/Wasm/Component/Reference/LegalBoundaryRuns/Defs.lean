module

public import Silmaril.Wasm.Component.Reference.LegalBoundary.Defs
public import Silmaril.Wasm.Component.Reference.SessionObs.Defs
public import Silmaril.Wasm.Component.Reference.SessionDiv.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Defs

/-!
# The rest of a reference call from a mid-call configuration (definitions)

**Scope.** The reference machine `Machine.Step` over any engine `E`, any profile, host readiness
and dispatcher, and the resumable reference sessions (`SessStep`, `SessCalls`, `SessExec`,
`SessDiv`, `LinkedSession.SessRun`) with the infinite call observations of `HLinked2`
(`CallQuietDiverges`, `CallHostProd`).

Every reference observation of a session (finished outcomes, quiet divergences, productive runs)
is built from top-level calls, and a top-level call is the host's invocation followed by the
machine's run. This module names what is observed of the **rest** of a top-level call from a
configuration `x` reached during that call, so that two configurations can be compared "from
there on":

* `CallRest prof hr dispatch x c m' out`: the run from `x` ends in `m'` with outcome `out` of
  call `c`, under the side conditions of `Calls` (host events only ticks and cancellations of
  `c`; for a trap, no `internal` fault);
* `SessRest prof h m₀ x n o m₁`: as a session call `n` started from `m₀`, the rest from `x`
  answers `o` (`some rs`, or `none` for a trap) and the session continues from `m₁` (the final
  configuration, or `resumeCfg m₀ m'` after a trap), as in `SessStep`;
* `QuietRest prof hr dispatch st x`: from `x`, a host-free run then quiet divergence in host
  state `st` (the part of `CallQuietDiverges` after the invocation);
* `HostProdRest prof hr dispatch base x ev`: from `x`, an infinite run of internal steps along
  which the host log is, at unboundedly late stages, `base ++ streamTake ev n` for unboundedly
  large `n` (the part of `CallHostProd` after the invocation).

Divergence from `x` is `Machine.Diverges` itself (and `Machine.DivergesWithHost` for infinite
runs with host events).

`StepTwin prof hr dispatch x y`: two mid-call configurations with exactly the same steps (labels
and successors), the same component and core stores and host state, and a running activation each. The
theorems (`LegalBoundaryRuns.Thms`) prove that twins have the same rests for each of the above,
and that a core activation that threw and the same activation trapped (`[.trap]`) are twins.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.LegalBoundaryRuns

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)

variable {E : CoreEngine} {σ : Type}

/-- **Twin mid-call configurations**: the same steps (labels and successors), component and core
stores, and host state, and both have a running activation (the host is not in control). -/
structure StepTwin (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (x y : Config E σ) : Prop where
  step : ∀ l m', Step prof hr dispatch x l m' ↔ Step prof hr dispatch y l m'
  store : x.store = y.store
  core : x.core = y.core
  host : x.host = y.host
  ctl_x : x.ctl ≠ []
  ctl_y : y.ctl ≠ []

/-- **The rest of top-level call `c` from `x`**: the run from `x` ends in `m'` with outcome
`out`, its host events only ticks and cancellations of `c`, and for a trap no `internal`
fault (the side conditions of `Calls` on the part of the trace from `x`). -/
def CallRest (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (x : Config E σ) (c : CallId) (m' : Config E σ) (out : CallOutcome) : Prop :=
  ∃ tr, Steps prof hr dispatch x tr m' ∧ (∀ ev, Label.host ev ∈ tr → CallHostEvent c ev) ∧
    (out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tr) ∧ out.Holds hr c m'

variable [∀ a b, Decidable (E.ExternSub a b)]

/-- **The rest of session call `n` (started from `m₀`) from `x`**: answered `some rs`, the
session continuing from the final configuration, or trapped (`none`), the session resuming
from `resumeCfg m₀ m'` (as `SessStep`). -/
inductive SessRest (prof : ProfileKind) (h : Host E σ) (m₀ x : Config E σ) (n : Nat) :
    Option (List Val) → Config E σ → Prop where
  | ret {m₁ : Config E σ} {rs : List Val} :
      CallRest prof h.hr h.dispatch x ⟨n⟩ m₁ (.resolved (some rs)) →
      SessRest prof h m₀ x n (some rs) m₁
  | trap {m₁ : Config E σ} :
      CallRest prof h.hr h.dispatch x ⟨n⟩ m₁ .trap → SessRest prof h m₀ x n none (resumeCfg m₀ m₁)

omit [∀ a b, Decidable (E.ExternSub a b)]

/-- **Quiet divergence of the rest of a call from `x`** in host state `st`: a host-free run,
then `QuietDiverges` (the part of `CallQuietDiverges` after the invocation). -/
def QuietRest (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (st : σ) (x : Config E σ) : Prop :=
  ∃ tr m₂, Steps prof hr dispatch x tr m₂ ∧ (∀ ev, Label.host ev ∉ tr) ∧
    QuietDiverges prof hr dispatch st m₂

/-- **Host chatter of the rest of a call from `x`**: an infinite run of internal steps from `x`
along which the host log is, at unboundedly late stages, `base` followed by the first `n` events
of `ev`, for unboundedly large `n` (the part of `CallHostProd` after the invocation, `base` the
log at the invocation). -/
def HostProdRest {ε : Type} (prof : ProfileKind) (hr : HostReady (σ × List ε))
    (dispatch : Call E → P E (σ × List ε) (Ret E)) (base : List ε)
    (x : Config E (σ × List ε)) (ev : ℕ → ε) : Prop :=
  ∃ t : ℕ → Config E (σ × List ε), t 0 = x ∧
    (∀ n, InternalStep prof hr dispatch (t n) (t (n + 1))) ∧
    ∀ N, ∃ n p, N ≤ n ∧ (t p).host.2 = base ++ streamTake ev n

end Silmaril.Wasm.Component.Reference.LegalBoundaryRuns
