module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.SingleThreaded.Agreement
public import Silmaril.Wasm.Execution.Core.Soundness.Preservation
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

/-!
# Type preservation with a relational host (proofs)

Core's preservation (`Step.preservation`) assumes `HostOk`, which also asks every
host call to have an outcome. Preservation needs only the other half: that the
answers are typed (`HostTyped`). So the proof goes through the totalized host
`totalize host`, which also diverges where `host` has no outcome:

* `Step.host_mono`: a Core step with a host is a step with any larger host, in
  every profile (a host-free step lifts; a host call is rebuilt at its
  `decompose?` redex);
* `hostOk_totalize`: `HostTyped host` makes `totalize host` lawful;
* `Step.preservation_typed`, `ContextTyped.step_typed`, `ContextTyped.steps_typed`:
  preservation for any host with typed answers. Nothing is assumed about the
  host having outcomes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile}

/-- **Core steps are monotone in the host.** -/
theorem Step.host_mono {host host' : HostSemantics H}
    (hle : ∀ h s vs o, host h s vs o → host' h s vs o) {c c' : Config H}
    (hst : Step P host c c') : Step P host' c c' := by
  rcases Step.split_host hst with h | ⟨E, a, hh, args, hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, heq⟩⟩
  · exact Step.of_noHost host' h
  · obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
    rcases c with ⟨s, f, code⟩
    dsimp only at hcode hr ⊢
    subst hcode
    exact E.step_fill (fun g => Step.callRefHost hyy hf he hn hc (hle _ _ _ _ hr)) f
  · obtain ⟨fi, yy, ps, rs, hf, hc, hyy, he, hn, hcode⟩ := decompose?_sound hd
    rcases c with ⟨s, f, code⟩
    subst heq
    dsimp only at hcode hdiv ⊢
    subst hcode
    exact E.step_fill (fun g => Step.callRefHostDiv hyy hf he hn hc (hle _ _ _ _ hdiv)) f

theorem Steps.host_mono {host host' : HostSemantics H}
    (hle : ∀ h s vs o, host h s vs o → host' h s vs o) {c c' : Config H}
    (hst : Steps P host c c') : Steps P host' c c' := by
  induction hst with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (Step.host_mono hle h)

theorem le_totalize (host : HostSemantics H) :
    ∀ h s vs o, host h s vs o → totalize host h s vs o :=
  fun _ _ _ _ h => .inl h

/-- **A host with typed answers, totalized, is lawful.** -/
theorem hostOk_totalize {host : HostSemantics H} (ht : HostTyped host) : HostOk (totalize host) := by
  intro s fi h vs ps rs hs hfi hcode he hvs
  refine ⟨?_, ?_⟩
  · by_cases hex : ∃ o, host h s vs o
    · obtain ⟨o, ho⟩ := hex
      exact ⟨o, .inl ho⟩
    · exact ⟨.diverged, .inr ⟨rfl, fun o ho => hex ⟨o, ho⟩⟩⟩
  · rintro out (ho | ⟨rfl, -⟩)
    · exact ht s fi h vs ps rs hs hfi hcode he hvs out ho
    · trivial

/-- **Preservation for a host with typed answers** (no outcome needs to exist). -/
theorem Step.preservation_typed {host : HostSemantics H} (ht : HostTyped host) {c c' : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) (h : Step P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store :=
  Step.preservation (hostOk_totalize ht) hc (Step.host_mono (le_totalize host) h)

/-- Typing in an evaluation context is preserved by a step of a host with typed
answers. -/
theorem ContextTyped.step_typed {host : HostSemantics H} (ht : HostTyped host) {c c' : Config H}
    (h : Sim.ContextTyped c) (hs : Step P host c c') : Sim.ContextTyped c' := by
  obtain ⟨E, ts, h⟩ := h
  exact ⟨E, ts, (Step.preservation (P := P) (hostOk_totalize ht) h
    (E.step (Step.host_mono (le_totalize host) hs))).1⟩

theorem ContextTyped.steps_typed {host : HostSemantics H} (ht : HostTyped host) {c c' : Config H}
    (h : Sim.ContextTyped c) (hs : Steps P host c c') : Sim.ContextTyped c' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact ContextTyped.step_typed ht ih hs

end Silmaril.Proofs.Wasm.Abstract.HostCall
