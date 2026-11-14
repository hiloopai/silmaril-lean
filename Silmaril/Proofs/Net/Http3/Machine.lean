module

public import Silmaril.Net.Http3.Machine.Defs

/-!
# HTTP/3 stream machines: proofs

The finite machines of `Silmaril.Net.Http3.Machine` agree with the stream readers, for
`Silmaril.Net.Http3.Machine.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.Machine

open Silmaril.Net.Http3

theorem requestMachine_step (k : StreamKind) (interim : List UInt8 → Bool) (s : ReqState)
    (f : Frame) :
    (reqStep k interim s f).toOption.map ReqState.phase = phaseStep k s.phase (f.kind k interim) := by
  obtain ⟨phase, parts⟩ := s
  cases f with
  | headers h =>
    by_cases hi : k ≠ .request ∧ interim h = true <;>
      cases phase <;> simp [reqStep, Frame.kind, phaseStep, hi, Except.toOption]
  | data d => cases phase <;> simp [reqStep, Frame.kind, phaseStep, Except.toOption]
  | pushPromise p h =>
    by_cases hk : k = .response <;>
      cases phase <;> simp [reqStep, Frame.kind, phaseStep, hk, Except.toOption]
  | unknown t b => cases phase <;> simp [reqStep, Frame.kind, phaseStep, Except.toOption]
  | settings _ | cancelPush _ | goaway _ | maxPushId _ | h2Reserved _ _ =>
    cases phase <;> simp [reqStep, Frame.kind, phaseStep, Except.toOption]

theorem controlStep_machine {peer : Role} {s s' : ControlState} {f : Frame}
    (h : controlStep peer s f = .ok s') :
    controlPhaseStep peer s.phase f.controlKind = some s'.phase := by
  obtain ⟨settings, g, m⟩ := s
  cases settings with
  | none =>
    cases f <;> simp [controlStep] at h
    subst h; rfl
  | some ps =>
    cases f <;> simp only [controlStep] at h <;> (try cases h)
    all_goals (try rfl)
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; rfl
    · split at h
      · cases h
      · rename_i hp
        split at h
        · cases h
        · cases h
          cases peer
          · rfl
          · exact absurd rfl hp

end Silmaril.Proofs.Net.Http3.Machine
