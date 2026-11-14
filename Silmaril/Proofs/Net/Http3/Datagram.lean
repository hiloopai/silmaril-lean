module

public import Silmaril.Net.Http3.Datagram.Defs
import Silmaril.Net.Quic.VarInt.Thms

/-!
# HTTP/3 Datagrams: proofs

For `Silmaril.Net.Http3.Datagram.Thms` (RFC 9297 §2.1, §2.1.1).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.Datagram

open Silmaril.Net.Quic Silmaril.Net.Http3

theorem valid_varInt {d : Datagram} (h : d.Valid) : VarInt.Valid d.quarterStreamId := by
  unfold Datagram.Valid Datagram.maxQuarterStreamId at h
  unfold VarInt.Valid VarInt.maxValue; omega

theorem decode_encode {d : Datagram} (h : d.Valid) : Datagram.decode d.encode = .ok d := by
  have h' : ¬ Datagram.maxQuarterStreamId < d.quarterStreamId := by
    unfold Datagram.Valid at h; omega
  simp only [Datagram.decode, Datagram.encode, VarInt.decode_encode (valid_varInt h), h',
    ↓reduceIte]

theorem decode_ok {xs : List UInt8} {d : Datagram} (h : Datagram.decode xs = .ok d) :
    d.Valid ∧ VarInt.decode xs = some (d.quarterStreamId, d.payload) := by
  unfold Datagram.decode at h
  split at h
  · cases h
  · rename_i q p hq
    split at h
    · cases h
    · rename_i hle
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨by simp only [Datagram.Valid]; omega, hq⟩

theorem decode_error {xs : List UInt8} {e : ErrorCode} (h : Datagram.decode xs = .error e) :
    e = .datagramError := by
  unfold Datagram.decode at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

theorem decode_large {q : Nat} (hv : VarInt.Valid q) (hq : Datagram.maxQuarterStreamId < q)
    (payload : List UInt8) :
    Datagram.decode (VarInt.encode q ++ payload) = .error .datagramError := by
  simp only [Datagram.decode, VarInt.decode_encode hv, hq, ↓reduceIte]

theorem streamId_isRequest {d : Datagram} (h : d.Valid) :
    Datagram.isRequestStreamId d.streamId = true := by
  unfold Datagram.Valid Datagram.maxQuarterStreamId at h
  have : 4 * d.quarterStreamId ≤ 2 ^ 62 - 1 := by omega
  simp [Datagram.isRequestStreamId, Datagram.streamId, Datagram.maxStreamId, this]

theorem ofStream_spec {sid : Nat} (h : Datagram.isRequestStreamId sid = true)
    (payload : List UInt8) :
    (Datagram.ofStream sid payload).streamId = sid ∧ (Datagram.ofStream sid payload).Valid := by
  simp only [Datagram.isRequestStreamId, Datagram.maxStreamId, Bool.and_eq_true, beq_iff_eq] at h
  have h2 := of_decide_eq_true h.2
  simp only [Datagram.ofStream, Datagram.streamId, Datagram.Valid, Datagram.maxQuarterStreamId]
  omega

theorem boolSetting_error {v : Nat} {e : ErrorCode} (h : boolSetting v = .error e) :
    e = .settingsError := by
  unfold boolSetting at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem map_error {α β : Type} {f : α → β} {x : Except ErrorCode α} {e : ErrorCode}
    (h : x.map f = .error e) : x = .error e := by
  cases x <;> simp_all [Except.map]

theorem apply_error {s : Settings} {p : Nat × Nat} {e : ErrorCode}
    (h : s.apply p = .error e) : e = .settingsError := by
  obtain ⟨i, w⟩ := p
  unfold Settings.apply at h
  by_cases h1 : i = settingQpackMaxTableCapacity
  · simp only [h1, ↓reduceIte] at h; cases h
  by_cases h2 : i = settingMaxFieldSectionSize
  · simp only [h2, ↓reduceIte] at h; cases h
  by_cases h3 : i = settingQpackBlockedStreams
  · simp only [h3, ↓reduceIte] at h; cases h
  by_cases h4 : i = settingEnableConnectProtocol
  · simp only [h4, ↓reduceIte] at h; exact boolSetting_error (map_error h)
  by_cases h5 : i = settingH3Datagram
  · simp only [h5, ↓reduceIte] at h; exact boolSetting_error (map_error h)
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte] at h; cases h

theorem apply_h3Datagram_bad (s : Settings) {v : Nat} (hv : 1 < v) :
    s.apply (settingH3Datagram, v) = .error .settingsError := by
  simp only [Settings.apply, settingH3Datagram, settingQpackMaxTableCapacity,
    settingMaxFieldSectionSize, settingQpackBlockedStreams, settingEnableConnectProtocol,
    boolSetting, show v ≠ 0 by omega, show v ≠ 1 by omega, ↓reduceIte]
  rfl

theorem foldlM_apply_bad (ps : List (Nat × Nat)) {v : Nat} (hv : 1 < v)
    (hm : (settingH3Datagram, v) ∈ ps) :
    ∀ s : Settings, ps.foldlM Settings.apply s = .error .settingsError := by
  induction ps with
  | nil => simp at hm
  | cons p ps ih =>
    intro s
    rw [List.foldlM_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · rw [apply_h3Datagram_bad s hv]; rfl
    · cases hs : s.apply p with
      | error e => rw [apply_error hs]; rfl
      | ok s' => exact ih hm' s'

theorem ofParams_h3Datagram_bad {ps : List (Nat × Nat)} {v : Nat} (hv : 1 < v)
    (hm : (settingH3Datagram, v) ∈ ps) : Settings.ofParams ps = .error .settingsError :=
  foldlM_apply_bad ps hv hm _

end Silmaril.Proofs.Net.Http3.Datagram
