module

public import Silmaril.Wasm.Game.Machine.Defs
import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Host-free runs of the single-threaded machine: theorems

Everything is stated for an arbitrary silmaril profile `P`, except the one
deterministic fact:

* for the deterministic profiles `profile o`, host-free runs reach at most one
  normal form (`reach_normal_unique`); `InternalP (profile o)` is
  silmaril-lean's `Internal o` (`internalP_profile`). Under a general profile
  the machine is relational and normal forms are not unique;
* finished threads and threads at a callout are normal (every profile);
* agreement with Core reduction (every profile): host-free runs are Core runs for every host
  (`Reach.steps`), a callout answered by the host is one Core step
  (`calloutAt_step`), host-free Core runs to a callout or a result are
  host-free machine runs (`out_iff_core`, `ret_iff_core`), and at a callout
  the only Core step against the one-answer host resumes with that answer
  (`step_answerHost_iff`).

Proofs: `Silmaril.Proofs.Wasm.Game.Machine.Basic`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- For the deterministic profile, `InternalP` is silmaril-lean's `Internal o`. -/
theorem internalP_profile {H : Type} (o : GrowOracle) :
    InternalP (H := H) (profile o) = Internal o :=
  Silmaril.Proofs.Wasm.Game.internalP_profile o

/-- In the deterministic profile `profile o`, host-free runs reach at most one normal form. -/
theorem reach_normal_unique {o : GrowOracle} {x y y' : Store Nat × Thread}
    (h : Reach (profile o) x y) (h' : Reach (profile o) x y')
    (hy : ∀ z, ¬ InternalP (profile o) y z) (hy' : ∀ z, ¬ InternalP (profile o) y' z) :
    y = y' :=
  Silmaril.Proofs.Wasm.Game.reach_normal_unique h h' hy hy'

/-- A finished thread has no internal step. -/
theorem resultAt_no_internal {P : Profile} {s : Store Nat} {t : Thread} {r : Result}
    (h : ResultAt s t r) : ∀ y, ¬ InternalP P (s, t) y :=
  Silmaril.Proofs.Wasm.Game.resultAt_no_internal h

/-- A thread at a callout has no internal step. -/
theorem calloutAt_no_internal {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} (hc : CalloutAt s t h args) : ∀ y, ¬ InternalP P (s, t) y :=
  Silmaril.Proofs.Wasm.Game.calloutAt_no_internal hc

/-- `CalloutAt` is the machine's `status`. -/
theorem calloutAt_iff_status {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} : CalloutAt s t h args ↔ statusP P s t = .callout h args :=
  Silmaril.Proofs.Wasm.Game.calloutAt_iff_status

/-- Host-free runs are Core runs for every host. -/
theorem Reach.steps {P : Profile} {host : HostSemantics Nat} {x y : Store Nat × Thread}
    (h : Reach P x y) : Steps P host (x.2.config x.1) (y.2.config y.1) :=
  Silmaril.Proofs.Wasm.Game.Reach.steps h

/-- A callout answered by the host is one Core step. -/
theorem calloutAt_step {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat}
    {t : Thread} {h : Nat} {args : List Val} {r : Result} (hc : CalloutAt s t h args)
    (hr : host h s args (.returned s' r)) :
    Step P host (t.config s) ((resumeResult s t r).config s') :=
  Silmaril.Proofs.Wasm.Game.calloutAt_step hc hr

/-- A host-free Core run to a host-call redex is a host-free machine run to a callout. -/
theorem out_iff_core {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} :
    (∃ s' t', Reach P (s, t) (s', t') ∧ CalloutAt s' t' h args) ↔
      ∃ d, Steps P (Det.noHost : HostSemantics Nat) (t.config s) d ∧
        ∃ E a, decompose? d.store d.code = some (E, a, h, args) :=
  Silmaril.Proofs.Wasm.Game.out_iff_core

/-- A host-free Core run to a result is a host-free machine run to a result. -/
theorem ret_iff_core {P : Profile} {s : Store Nat} {t : Thread} {r : Result} :
    (∃ s' t', Reach P (s, t) (s', t') ∧ ResultAt s' t' r) ↔
      ∃ d, Steps P (Det.noHost : HostSemantics Nat) (t.config s) d ∧
        d.code = r.toAdmin :=
  Silmaril.Proofs.Wasm.Game.ret_iff_core

/-- At a callout, the only Core step against the one-answer host resumes with the answer. -/
theorem step_answerHost_iff {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} {r : Result} (hc : CalloutAt s t h args) (c' : Config Nat) :
    Step P (answerHost h args r) (t.config s) c' ↔
      c' = (resumeResult s t r).config s :=
  Silmaril.Proofs.Wasm.Game.step_answerHost_iff hc c'

end Silmaril.Wasm.Game
