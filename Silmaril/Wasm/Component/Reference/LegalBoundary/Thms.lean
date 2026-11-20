module

public import Silmaril.Wasm.Component.Reference.LegalBoundary.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
public import Silmaril.Wasm.Component.Reference.SessionObs.Defs
public import Silmaril.Wasm.Cfg.CfgLegalOwner.Thms
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.Status
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.Machine
import Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.Iface

/-!
# The reference boundary of a canon call: exceptions become traps (theorems)

**Scope.** The Core 3.0 engine `core3P P` of the reference machine at an arbitrary profile `P`
(`Silmaril.Wasm.Component.Reference.core3P`), the reference machine `Machine.Step` with any
profile, host readiness and dispatcher, its top-level calls (`Calls`) and resumable sessions
(`SessStep`, `SessCalls`), and, for the legal injections, `Linked2` and `LinkedG` at the
deterministic profiles `profile o`.

**Hypotheses.** None beyond the shapes stated: a configuration whose running activation is a
core activation (`coreCfg`, any thread, continuation, pending segments and resumers). For the
legal injections, those of `CfgLegalOwner.legal_injection_of` (`Linked2.Adequate`) and
`legal_injectionG_of` (`LinkedG.ProfOk o`).

**Proved.**

1. **The exact `core3P` status of a raw Core result** (`core3P_status_result`): for every raw
   Core result `r` (values, trap, uncaught exception `throw a`),
   `(core3P P).status s (.active f r.toAdmin) = flatStatus (.returned (callAndTrapOnThrow r))`.
   In particular an uncaught exception has the status of a trap (`core3P_status_throw`,
   `core3P_status_throw_eq_trap`). Only code that *is* `throwing a`, i.e. an exception that
   escaped every handler of the activation, is a boundary result; inside the activation the
   Core semantics (handlers included) runs unchanged.
2. **Step-level indistinguishability on the reference machine.** For a configuration whose
   running activation is a core activation that threw (`coreCfg m th (.active f (throwing a)) k
   segs rest`):
   * its only step is `coreTrap`, label `.trap .coreTrap` (the trap reason is `coreTrap`, as
     for a Core trap; no rule produces `TrapReason.uncaughtException`), successor `trapCfg m`:
     the core store and host state are `m`'s, `lockdown` is set and the control chain is empty
     (`step_throw_iff`, `trapCfg_coreCfg`);
   * it has exactly the steps, runs (`steps_throw_iff_steps_trap`, nonempty traces) and
     divergences (none: `not_diverges_throw`) of the same configuration whose activation
     trapped (`[.trap]`) instead (`step_throw_iff_step_trap`).
   So raw Core exception versus trap is not an observable at this boundary: every observation
   defined from reference runs (labels, trap reasons, configurations) is the same for both.
   The statements hold for any pending segments, so equally for a top-level export call
   (the export's core activation) and for the exporter's core activation called through a
   cross-instance trampoline, whose segments hold the importer's parked core activation
   (`step_nested_throw_iff`: that activation is discarded and never resumed).
3. **Calls and sessions.** A top-level call whose run reaches such a configuration traps there
   (`calls_throw`); every outcome of a run through it is a trap, with `m`'s core store and host
   state (`calls_outcome_throw`). The session call traps and the session resumes from
   `resumeCfg m₀ (trapCfg …)`, whose core store is `m`'s: every write of the activation before
   the exception escaped persists (`sessStep_throw`, `sessCalls_throw`).
4. **The reference boundary map is the IR's coercion.** On export results: the IR payload of
   the `core3P` status of the Core result of an IR answer `a` is the IR's `answerPayload a`
   (`statusPayload_core3P_answer`), via `answerPayload a = crPayload (callAndTrapOnThrow
   a.toResult)` (`answerPayload_eq`). On import answers: the IR's `payloadAnswer` never
   answers with an exception (`payloadAnswer_ne_throw`), the reference engine resumes a core
   activation only with an engine `CallResult` whose code is never `throwing a`
   (`core3P_resume`, `toCR_toAdmin_ne_throwing`), and on flat values of the right types the two
   plug in the same Core code (`payloadAnswer_toResult_flat`).
5. **The legal injections.** `CfgLegalOwner.OwnerObligations` and `OwnerObligationsG` hold for
   the reference equivalences themselves, `Linked2.RefSessEquivFull (profile o) prof` and
   `LinkedG.RefSessEquivFull (profile o) prof` (`ownerObligations`, `ownerObligationsG`): these
   are defined from reference runs only, on the engine `core3P (profile o)` whose boundary is
   the exception-to-trap erasure of items 1 and 4, so they are already the reference
   equivalences of legal environments. Hence `legal_injection` and `legal_injectionG`:
   the reference equivalence is the IR equivalence at the legal node semantics `impSemLD`.

**Not claimed.**

* The obligations are discharged by `Iff.rfl`: no second "legal" reference relation is
  introduced, since it would add no content. The content is in items 1–4, which justify that
  `RefSessEquivFull` already sits at the exception-free boundary, and in `impSemLD_eq`
  (#995) and `refSessEquivFull_iff_denD`/`compSession_inj_full` (the existing injections) used
  by the legal injections. The proofs of those injections do not go through items 2–3.
* No trap-reason observation is added to the reference equivalences, and no claim is made
  about an equivalence that observes trap reasons. The erasure here is of exceptions into
  traps; the trap reason of an escaped exception is `coreTrap` (not `uncaughtException`, which
  REF names but no machine rule produces).
* An interface in which a raw Core exception crosses a component boundary (an `ssig` with an
  exception answer) is a different interface, not a failure of this one.
* The threading of items 2–3 through the session-level reference observations (finished
  outcomes, quiet divergences and productive runs of `Linked2`, `LinkedG` and `HLinked2`) is not
  here: it is `LegalBoundaryRuns` (`stepTwin_throw_trap`, `rest_throw_iff_trap`,
  `sessCalls_through_trap`, `sessDiv_through_trap`, `sessRun_through_trap`, and no infinite rest
  from either configuration).
-/

public section

namespace Silmaril.Wasm.Component.Reference.LegalBoundary

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.StepDefs Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Result throwing Frame)
open Silmaril.Wasm.Game (Answer FnType)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-! ## The `core3P` status of a raw Core result -/

section Status

variable {P : Silmaril.Wasm.Numerics.Profile} {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H}
  {f : Frame}

/-- REF `call_and_trap_on_throw` identifies an uncaught exception with a trap. -/
theorem callAndTrapOnThrow_throw (a : Nat) :
    callAndTrapOnThrow (.throw a) = callAndTrapOnThrow .trap :=
  rfl

/-- **The status of a raw Core result** under `statusP P`: `callAndTrapOnThrow` of it. -/
theorem statusP_result (r : Result) :
    Silmaril.Wasm.Game.statusP P s (.active f r.toAdmin) = .returned (callAndTrapOnThrow r) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.statusP_result P s f r

/-- **The exact `core3P` status of a raw Core result**: values, trap or uncaught exception,
through `call_and_trap_on_throw`, at the flat boundary. -/
theorem core3P_status_result (r : Result) :
    (core3P P).status s (.active f r.toAdmin) = flatStatus (.returned (callAndTrapOnThrow r)) :=
  congrArg flatStatus (statusP_result r)

/-- **An uncaught exception has the status of a trap** in `core3P P`. -/
theorem core3P_status_throw (a : Nat) :
    (core3P P).status s (.active f (throwing a)) = .returned .trap :=
  core3P_status_result (.throw a)

/-- A trap has the status of a trap in `core3P P`. -/
theorem core3P_status_trap : (core3P P).status s (.active f [.trap]) = .returned .trap :=
  core3P_status_result .trap

/-- **Exception-to-trap erasure at the engine boundary.** -/
theorem core3P_status_throw_eq_trap (a : Nat) :
    (core3P P).status s (.active f (throwing a)) = (core3P P).status s (.active f [.trap]) := by
  rw [core3P_status_throw, core3P_status_trap]

end Status

/-! ## The reference machine at a core activation that threw -/

section Machine

variable {P : Silmaril.Wasm.Numerics.Profile} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call (core3P P) → Canon.P (core3P P) σ (Ret (core3P P))}
  {m m' : Config (core3P P) σ} {l : Label (core3P P) σ} {th : Option ThreadId} {f : Frame}
  {a : Nat} {k : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))}
  {segs : List (Seg (core3P P) σ)} {rest : List (Activation (core3P P) σ)}

/-- A trap discards the running activation: `trapCfg` of `coreCfg m …` is `trapCfg m`. -/
theorem trapCfg_coreCfg {E : CoreEngine} {σ : Type} (m : Config E σ) th ct k segs rest :
    trapCfg (coreCfg m th ct k segs rest) = trapCfg m :=
  rfl

/-- **The only step of a core activation that threw**: `coreTrap`, with the trap reason
`coreTrap`, to `trapCfg` (same core store and host state, `lockdown` set, no activation). -/
theorem step_throw_iff :
    Step prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) l m' ↔
      l = .trap .coreTrap ∧ m' = trapCfg m :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.step_iff_of_status_trap
    rfl (core3P_status_throw a)

/-- **Step-level indistinguishability**: a core activation that threw has exactly the steps of
one that trapped. -/
theorem step_throw_iff_step_trap :
    Step prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) l m' ↔
      Step prof hr dispatch (coreCfg m th (.active f [.trap]) k segs rest) l m' :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.step_iff_step_of_status_trap
    rfl (core3P_status_throw a) rfl core3P_status_trap rfl

/-- The runs of a core activation that threw: none, or the one trap step. -/
theorem steps_throw_iff {tr : List (Label (core3P P) σ)} :
    Steps prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) tr m' ↔
      (tr = [] ∧ m' = coreCfg m th (.active f (throwing a)) k segs rest) ∨
        (tr = [.trap .coreTrap] ∧ m' = trapCfg m) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.steps_iff_of_status_trap
    rfl (core3P_status_throw a)

/-- **Run-level indistinguishability**: the nonempty runs of a core activation that threw are
those of one that trapped. -/
theorem steps_throw_iff_steps_trap {tr : List (Label (core3P P) σ)} :
    Steps prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) (l :: tr) m' ↔
      Steps prof hr dispatch (coreCfg m th (.active f [.trap]) k segs rest) (l :: tr) m' := by
  rw [Steps.cons_iff, Steps.cons_iff]
  exact exists_congr fun _ => and_congr_left' step_throw_iff_step_trap

/-- A core activation that threw does not diverge. -/
theorem not_diverges_throw :
    ¬ Diverges prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.not_diverges_of_status_trap
    rfl (core3P_status_throw a)

/-- **The exporter's activation throwing inside a trampoline**: with the importer's core
activation `ctB` parked in the pending segments, the only step is the trap, and the trap
configuration has no activation (the importer is never resumed, so it never receives the
exception). -/
theorem step_nested_throw_iff {ctB : (core3P P).Thread (CanonHost (core3P P))}
    {kB : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))} :
    Step prof hr dispatch (coreCfg m th (.active f (throwing a)) k (.core ctB kB :: segs) rest)
        l m' ↔ l = .trap .coreTrap ∧ m' = trapCfg m ∧ m'.ctl = [] := by
  rw [step_throw_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, h2 ▸ rfl⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩

/-- **A top-level call that reaches a core activation that threw traps there.** -/
theorem calls_throw {m₀ : Config (core3P P) σ} {c : CallId} {g : FuncId} {args : List Val}
    {tr : List (Label (core3P P) σ)}
    (h₁ : Steps prof hr dispatch m₀ (.host (invokeTop c g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent c ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr) :
    Calls prof hr dispatch m₀ c g args (trapCfg m) .trap :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.calls_trap_of_status_trap
    (m := coreCfg m th (.active f (throwing a)) k segs rest) h₁ hev hint rfl
    (core3P_status_throw a)

/-- **Every outcome of a run through a core activation that threw is a trap**, at `m`'s core
store and host state. -/
theorem calls_outcome_throw {tr : List (Label (core3P P) σ)} {c : CallId} {out : CallOutcome}
    (h : Steps prof hr dispatch (coreCfg m th (.active f (throwing a)) k segs rest) tr m')
    (hout : out.Holds hr c m') :
    out = .trap ∧ m'.core = m.core ∧ m'.host = m.host :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.calls_outcome_of_status_trap
    (m := coreCfg m th (.active f (throwing a)) k segs rest) rfl (core3P_status_throw a) h hout

/-- **The session call traps and the store persists**: the session resumes from
`resumeCfg m₀ (trapCfg m)`, whose core store and host state are `m`'s. -/
theorem sessStep_throw {h : Host (core3P P) σ} {m₀ : Config (core3P P) σ} {n : Nat}
    {g : FuncId} {args : List Val} {tr : List (Label (core3P P) σ)}
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr) :
    SessStep prof h m₀ n g args none (resumeCfg m₀ (trapCfg m)) ∧
      (resumeCfg m₀ (trapCfg m)).core = m.core ∧
      (resumeCfg m₀ (trapCfg m)).host = m.host :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.sessStep_trap_of_status_trap
    (m := coreCfg m th (.active f (throwing a)) k segs rest) h₁ hev hint rfl
    (core3P_status_throw a)

/-- **The resumable session**: the call is answered `none` and the session continues from
`resumeCfg m₀ (trapCfg m)`. -/
theorem sessCalls_throw {h : Host (core3P P) σ} {m₀ : Config (core3P P) σ} {n : Nat}
    {g : FuncId} {args : List Val} {tr : List (Label (core3P P) σ)}
    {cs : List (FuncId × List Val)} {outs : List (Option (List Val))}
    (h₁ : Steps prof h.hr h.dispatch m₀ (.host (invokeTop ⟨n⟩ g args) :: tr)
      (coreCfg m th (.active f (throwing a)) k segs rest))
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨n⟩ ev)
    (hint : ∀ msg, Label.trap (.internal msg) ∉ tr)
    (hrest : SessCalls prof h (resumeCfg m₀ (trapCfg m)) (n + 1) cs outs) :
    SessCalls prof h m₀ n ((g, args) :: cs) (none :: outs) :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.sessCalls_trap_of_status_trap
    (m := coreCfg m th (.active f (throwing a)) k segs rest) h₁ hev hint rfl
    (core3P_status_throw a) hrest

end Machine

/-! ## The reference boundary map against the IR's coercions -/

section Iface

variable {P : Silmaril.Wasm.Numerics.Profile} {H : Type} {s : Silmaril.Wasm.Execution.Core.Store H}
  {f : Frame} {ft : FnType}

/-- **The IR's export coercion is `call_and_trap_on_throw`**: `answerPayload` of an answer is
`crPayload` of its Core result through `callAndTrapOnThrow`. -/
theorem answerPayload_eq (a : Answer ft) :
    answerPayload a = crPayload (callAndTrapOnThrow a.toResult) := by
  cases a <;> rfl

/-- The IR payload of the reference status of a raw Core result. -/
theorem statusPayload_core3P_result (r : Result) :
    statusPayload ((core3P P).status s (.active f r.toAdmin)) =
      crPayload (callAndTrapOnThrow r) := by
  rw [core3P_status_result]
  exact Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.statusPayload_flatStatus _

/-- **The reference boundary matches the IR node's `answerPayload`**: for every IR answer `a`
(values, trap or exception), the IR payload of the `core3P` status of its Core result is
`answerPayload a`. -/
theorem statusPayload_core3P_answer (a : Answer ft) :
    statusPayload ((core3P P).status s (.active f a.toResult.toAdmin)) = answerPayload a := by
  rw [statusPayload_core3P_result, answerPayload_eq]

/-- The IR's import coercion `payloadAnswer` never answers with an exception. -/
theorem payloadAnswer_ne_throw (p : Option Payload) (a : Nat) :
    payloadAnswer ft p ≠ .throw a := by
  unfold payloadAnswer
  split <;> (try split) <;> simp

/-- The reference engine resumes a core activation with an engine `CallResult` (values or a
trap; no exception). -/
theorem core3P_resume (s : (core3P P).Store H) (t : (core3P P).Thread H) (r : CallResult) :
    (core3P P).resume s t r = Silmaril.Wasm.SingleThreaded.resume s t (Core3.toCR r) :=
  rfl

/-- The code plugged into a resumed core activation is never an uncaught exception. -/
theorem toCR_toAdmin_ne_throwing (r : CallResult) (a : Nat) :
    (Core3.toCR r).toAdmin ≠ throwing a := by
  have hn := Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.throwing_ne_vals a
  cases r with
  | values vs => exact fun h => hn ⟨vs.map Silmaril.Wasm.SingleThreaded.ofFlat, h.symm⟩
  | trap => simp [Core3.toCR, Silmaril.Wasm.SingleThreaded.CallResult.toAdmin, throwing]

/-- **Import answers agree**: on flat values `ys` of the result types, the IR's `payloadAnswer`
resumes the importer with the Core code the reference engine plugs in for `ys`. -/
theorem payloadAnswer_toResult_flat {ys : List Silmaril.Wasm.Component.Flat}
    {vs : Silmaril.Wasm.Game.Typed ft.results}
    (h : typed? ft.results (ys.map Silmaril.Wasm.SingleThreaded.ofFlat) = some vs) :
    (payloadAnswer ft (some (.flat ys))).toResult.toAdmin = (Core3.toCR (.values ys)).toAdmin :=
  Silmaril.Proofs.Wasm.Component.Reference.LegalBoundary.payloadAnswer_toResult_flat h

end Iface

/-! ## The legal injections -/

section Injection

open Silmaril.Wasm.Cfg.CfgLegalOwner

variable {o : GrowOracle} {prof : ProfileKind}

/-- **The owner's obligation for `Linked2`** holds for the reference equivalence itself. -/
theorem ownerObligations : OwnerObligations o prof (Linked2.RefSessEquivFull (profile o) prof) :=
  ⟨fun _ _ => Iff.rfl⟩

/-- **The owner's obligation for `LinkedG`** holds for the reference equivalence itself. -/
theorem ownerObligationsG : OwnerObligationsG o prof (LinkedG.RefSessEquivFull (profile o) prof) :=
  ⟨fun _ _ => Iff.rfl⟩

/-- **The legal injection for `Linked2`**: on adequate links, the reference equivalence is the
same export types, the same public plays of the IR at the legal node semantics `impSemLD`, and
the same IR divergences and infinite plays. -/
theorem legal_injection {l l' : Linked2} (hl : l.Adequate) (hl' : l'.Adequate) :
    Linked2.RefSessEquivFull (profile o) prof l l' ↔ Linked2.SameTypes l l' ∧
      pubPlays (l.toComp.denD (impSemLD (profile o))).toStrategy =
        pubPlays (l'.toComp.denD (impSemLD (profile o))).toStrategy ∧
      Linked2.IRDivEq (profile o) l l' ∧ Linked2.IRInfEq (profile o) l l' :=
  legal_injection_of ownerObligations hl hl'

/-- **The legal injection for `LinkedG`**: on `ProfOk` links, the reference equivalence is the
same export types and the same session objects. -/
theorem legal_injectionG {g g' : LinkedG} (hg : g.ProfOk o) (hg' : g'.ProfOk o) :
    LinkedG.RefSessEquivFull (profile o) prof g g' ↔ LinkedG.SameTypes g g' ∧
      LinkedG.compSession (profile o) g = LinkedG.compSession (profile o) g' :=
  legal_injectionG_of ownerObligationsG hg hg'

end Injection

end Silmaril.Wasm.Component.Reference.LegalBoundary
