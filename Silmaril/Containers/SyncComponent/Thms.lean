module

public import Silmaril.Containers.SyncComponent.Defs
public import Silmaril.Containers.Executor.Thms
public import Silmaril.Containers.Outcome.Thms
public import Silmaril.Wasi.Host.Thms
import Silmaril.Proofs.Containers.SyncComponent.Basic

public section
namespace Silmaril.Containers.SyncComponent
open Silmaril.Wasi (nsig Reach)

/-- Every operational run simulates a play of the existing component semantics, including
internal computation stuttering. Hence the encoded run has correct turns and pending calls. -/
theorem run_reaches {trap t s} (h : Run trap t s) :
    Reach body (t.map (Event.move trap)) (componentState trap s) :=
  Silmaril.Proofs.Containers.SyncComponent.run_reaches h

theorem run_legal {trap t s} (h : Run trap t s) :
    Silmaril.Games.Legal (t.map (Event.move trap)) := ⟨_, (run_reaches h).path⟩

theorem source_simulates {host trap b} (hb : source host trap b) :
    linked host trap b := Silmaril.Proofs.Containers.SyncComponent.source_simulates hb

theorem loose_admitted : Admitted looseHost :=
  Silmaril.Proofs.Containers.SyncComponent.loose_admitted

/-- Two genuinely distinct host choices are admitted by the same loose host. -/
theorem loose_choice (choice : Bool) : hostPlay choice ∈ looseHost :=
  Silmaril.Proofs.Containers.SyncComponent.hostPlay_loose choice

theorem certificate : executor.Certificate := Silmaril.Proofs.Containers.SyncComponent.certificate

theorem component_sat :
    (Silmaril.Wasi.ag (fun t => TypedAnswers (Silmaril.Wasi.hostView t))
      (fun t => GoodEvents (Silmaril.Wasi.expView t))).holds (Silmaril.Wasi.ofBody body) :=
  Silmaril.Proofs.Containers.SyncComponent.component_sat

/-- Existing `Wasi.link_sat` transfers the export spec over every typed host strategy. -/
theorem linked_good (host : ClosedHost)
    (ha : (Silmaril.Wasi.hostSat TypedAnswers).holds host) :
    ∀ p ∈ Silmaril.Wasi.link host (Silmaril.Wasi.ofBody body),
      GoodEvents (Silmaril.Wasi.xtrace p) :=
  Silmaril.Proofs.Containers.SyncComponent.linked_good host ha

/-- The same interface spec reaches containers via the checked executor certificate. This
quantifies every admitted host and every source execution, not selected test seeds. -/
theorem runtime_returns (host : ClosedHost) (trap : Bool) (ha : Admitted host) :
    (runtime.beh ((), host, trap)).Sat (fun b => Spec.noUB b ∧ Reports trap b) :=
  Silmaril.Proofs.Containers.SyncComponent.runtime_returns host trap ha

theorem runtime_choice (host : ClosedHost) (choice : Bool) (hc : hostPlay choice ∈ host) :
    runtime.beh ((), host, false)
      (.done [.call false, .returned (some (!choice))] (.exited 0)) :=
  Silmaril.Proofs.Containers.SyncComponent.runtime_choice host choice hc

/-- The stronger functional law also relates each result to a choice actually permitted by
the host; neither Boolean branch was dropped by the observation adapter. -/
theorem runtime_complements (host : ClosedHost) :
    (runtime.beh ((), host, false)).Sat (fun b => b = .blocked [.call false] ∨ ∃ choice,
      hostPlay choice ∈ host ∧
      b = .done [.call false, .returned (some (!choice))] (.exited 0)) :=
  Silmaril.Proofs.Containers.SyncComponent.runtime_complements host

/-- Availability of a response in a safety strategy does not prove eventual delivery. -/
theorem runtime_waits (host : ClosedHost) :
    runtime.beh ((), host, false) (.blocked [.call false]) :=
  Silmaril.Proofs.Containers.SyncComponent.runtime_waits host

theorem runtime_trap (host : ClosedHost) :
    runtime.beh ((), host, true) (.done [.call true, .returned none] (.exited 70)) :=
  Silmaril.Proofs.Containers.SyncComponent.runtime_trap host

theorem runtime_nonempty (host : ClosedHost) (trap : Bool) (ha : Admitted host) :
    ∃ b, runtime.beh ((), host, trap) b := certificate.nonempty () host trap trivial ha

theorem two_results :
    runtime.beh ((), looseHost, false) (.done [.call false, .returned (some true)] (.exited 0)) ∧
    runtime.beh ((), looseHost, false) (.done [.call false, .returned (some false)] (.exited 0)) :=
  ⟨runtime_choice _ false (loose_choice false), runtime_choice _ true (loose_choice true)⟩

theorem trapPolicy_reflects : trapPolicy.ReflectsNoUB :=
  Silmaril.Proofs.Containers.SyncComponent.trapPolicy_reflects

/-- A default noUB certificate is insufficient after opting into more UB. The reverse
certificate direction is supplied by `trapPolicy_reflects`. -/
theorem trap_policy_contrast :
    Spec.noUB (Beh.done [Event.call true, .returned none] (.exited 70)) ∧
    ¬ Spec.noUB (trapPolicy.run (.done [.call true, .returned none] (.exited 70))) :=
  ⟨trivial, by simp [trapPolicy, Spec.noUB]⟩

theorem untyped_reply_rejected : ¬ TypedAnswers [.imp chooseName [] (some [.u64 0])] :=
  Silmaril.Proofs.Containers.SyncComponent.untyped_reply_rejected

theorem reply_requires_wait : ¬ Step false .started (some (.chosen true)) (.computing true) := by
  intro h; cases h

theorem guest_trap_defined : (guestOutcome none).NoUB := trivial

theorem guest_trap_moreUB : ¬ ((guestOutcome none).trapAsUB .unmodeled).NoUB := _root_.id

theorem trap_policy_direction (r : Option Bool) :
    ((guestOutcome r).trapAsUB .unmodeled).NoUB → (guestOutcome r).NoUB :=
  Outcome.noUB_of_trapAsUB _ _

/-- WIT parameter/result metadata uses the existing component value checker. -/
theorem choose_result_typed (b : Bool) :
    Silmaril.Wasm.Component.checkVals imports[0]!.2.results [.bool b] = some [.bool b] := rfl

end Silmaril.Containers.SyncComponent
