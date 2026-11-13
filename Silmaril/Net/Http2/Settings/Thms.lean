module

public import Silmaril.Net.Http2.Settings.Defs
import Silmaril.Proofs.Net.Http2.Settings

@[expose] public section

/-!
# HTTP/2 settings and flow control: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http2/Settings.lean`):

* `Settings.initial_valid`, `Settings.applyAll_valid`: the initial settings satisfy the
  constraints of §6.5.2, and every accepted SETTINGS frame preserves them, so the peer's
  `SETTINGS_MAX_FRAME_SIZE` used by `readFrame` is always within `2^14 … 2^24-1`;
* `consume_ok`, `increment_ok`: the window after sending data is non-negative, and after a
  WINDOW_UPDATE at most `2^31 - 1` (§6.9.1);
* `runFlow_eq`: **conservation**: after any accepted sequence of DATA and WINDOW_UPDATE on a
  window `w`, the window is `w + credit - data`, and stays at most `2^31 - 1`;
* `runFlow_dataSent_le`: **a flow-controlled sender never exceeds its credit**: the data
  sent is at most the initial window plus the increments granted (§5.2.1, §6.9).
-/

namespace Silmaril.Net.Http2

theorem Settings.initial_valid : Settings.initial.Valid := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem Settings.applyAll_valid {s s' : Settings} {ps : List (Nat × Nat)} (hs : s.Valid)
    (h : s.applyAll ps = .ok s') : s'.Valid :=
  Silmaril.Proofs.Net.Http2.applyAll_valid hs h

theorem consume_ok {w w' : Int} {n : Nat} (h : consume w n = .ok w') : w' = w - n ∧ 0 ≤ w' :=
  Silmaril.Proofs.Net.Http2.consume_ok h

theorem increment_ok {w w' : Int} {k : Nat} (h : increment w k = .ok w') :
    w' = w + k ∧ w' ≤ maxWindow :=
  Silmaril.Proofs.Net.Http2.increment_ok h

theorem runFlow_eq {w w' : Int} {es : List FlowEvent} (h : runFlow w es = .ok w') :
    w' = w + credit es - dataSent es ∧ (w ≤ maxWindow → w' ≤ maxWindow) :=
  Silmaril.Proofs.Net.Http2.runFlow_eq h

theorem runFlow_dataSent_le {w w' : Int} {es : List FlowEvent} (hw : 0 ≤ w)
    (h : runFlow w es = .ok w') : (dataSent es : Int) ≤ w + credit es := by
  have h1 := (runFlow_eq h).1; have h2 := Silmaril.Proofs.Net.Http2.runFlow_nonneg hw h; omega

/-! Examples, checked by evaluation. -/

/-- `SETTINGS_MAX_FRAME_SIZE = 2^14 - 1` is rejected (§6.5.2). -/
example : (Settings.initial.applyAll [(0x5, 16383)]).toOption = none := by decide
/-- An unknown setting is ignored (§6.5.2). -/
example : Settings.initial.applyAll [(0x99, 7)] = .ok Settings.initial := rfl
/-- A SETTINGS payload of 7 octets is a `FRAME_SIZE_ERROR` (§6.5). -/
example : decodeSettingsPayload [0, 4, 0, 0, 0xff, 0xff, 0] = .error .frameSizeError := rfl
example : decodeSettingsPayload [0, 4, 0, 1, 0, 0] = .ok [(4, 65536)] := rfl
/-- A WINDOW_UPDATE that overflows the window is a `FLOW_CONTROL_ERROR` (§6.9.1). -/
example : increment (maxWindow : Int) 1 = .error .flowControlError := rfl
/-- Sending past the window is refused. -/
example : runFlow 65535 [.data 65535, .data 1] = .error .flowControlError := rfl

end Silmaril.Net.Http2
