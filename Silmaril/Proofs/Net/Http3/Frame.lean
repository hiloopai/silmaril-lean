module

public import Silmaril.Net.Http3.Frame.Defs
import Silmaril.Net.Quic.VarInt.Thms

/-!
# HTTP/3 frames: proofs

Round trips of the frame layer (RFC 9114 §7.1) and the typed payloads (§7.2), and the
buffering bound of the reader, for `Silmaril.Net.Http3.Frame.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.Frame

open Silmaril.Net.Quic Silmaril.Net.Http3

theorem readRaw_encodeRaw {f : RawFrame} (hf : f.Valid) {maxPayload : Nat}
    (hmax : f.payload.length ≤ maxPayload) (rest : List UInt8) :
    readRaw maxPayload (encodeRaw f ++ rest) = .ok (f, rest) := by
  obtain ⟨ht, hl⟩ := hf
  unfold encodeRaw readRaw
  rw [List.append_assoc, List.append_assoc, VarInt.decode_encode ht]
  simp only
  rw [VarInt.decode_encode hl]
  simp only [show ¬ maxPayload < f.payload.length by omega, ↓reduceIte, List.length_append,
    show ¬ f.payload.length + rest.length < f.payload.length by omega, List.take_left',
    List.drop_left']

theorem readRaw_ok {maxPayload : Nat} {xs rest : List UInt8} {r : RawFrame}
    (h : readRaw maxPayload xs = .ok (r, rest)) :
    r.payload.length ≤ maxPayload ∧ rest.length < xs.length ∧ rest <:+ xs ∧ r.Valid := by
  unfold readRaw at h
  split at h
  · cases h
  · rename_i ty r1 h1
    split at h
    · cases h
    · rename_i len r2 h2
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hlen hshort
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have l1 := VarInt.decode_length h1
          have l2 := VarInt.decode_length h2
          have s1 := VarInt.decode_suffix h1
          have s2 := VarInt.decode_suffix h2
          refine ⟨?_, ?_, ?_, VarInt.decode_valid h1, ?_⟩
          · simp only [List.length_take]; omega
          · simp only [List.length_drop]; omega
          · exact (List.drop_suffix _ _).trans (s2.trans s1)
          · have hv := VarInt.decode_valid h2
            unfold VarInt.Valid at hv ⊢
            simp only [List.length_take]; omega

theorem readRawAllFuel_flatMap {maxPayload : Nat} (fs : List RawFrame)
    (hv : ∀ f ∈ fs, f.Valid ∧ f.payload.length ≤ maxPayload) :
    ∀ fuel, (fs.flatMap encodeRaw).length ≤ fuel →
      readRawAllFuel maxPayload fuel (fs.flatMap encodeRaw) = .ok fs := by
  induction fs with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons f fs ih =>
    intro fuel hfuel
    obtain ⟨hf, hm⟩ := hv f (by simp)
    have hr := readRaw_encodeRaw hf hm (fs.flatMap encodeRaw)
    obtain ⟨b, tl, hbt⟩ : ∃ b tl, encodeRaw f = b :: tl := by
      cases h : VarInt.encode f.type with
      | nil => exact absurd h (VarInt.encode_ne_nil _)
      | cons b tl => exact ⟨b, tl ++ VarInt.encode f.payload.length ++ f.payload, by
          simp [encodeRaw, h]⟩
    simp only [List.flatMap_cons, List.length_append] at hfuel ⊢
    have hlen : (encodeRaw f).length ≥ 1 := by rw [hbt]; simp
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      rw [hbt, List.cons_append] at hr ⊢
      simp only [readRawAllFuel, hr, ih (fun g hg => hv g (by simp [hg])) fuel (by omega)]

theorem pairUp_flatten (ps : List (Nat × Nat)) : pairUp (flattenParams ps) = some ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => obtain ⟨i, v⟩ := p; simp [flattenParams, pairUp, ih]

theorem flatten_valid {ps : List (Nat × Nat)} (h : ∀ p ∈ ps, VarInt.Valid p.1 ∧ VarInt.Valid p.2) :
    ∀ v ∈ flattenParams ps, VarInt.Valid v := by
  induction ps with
  | nil => simp [flattenParams]
  | cons p ps ih =>
    obtain ⟨i, w⟩ := p
    intro v hv
    simp only [flattenParams, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact (h (v, w) (by simp)).1
    · exact (h (i, v) (by simp)).2
    · exact ih (fun q hq => h q (by simp [hq])) v hv

theorem decodeParams_encodeParams {ps : List (Nat × Nat)}
    (hv : ∀ p ∈ ps, VarInt.Valid p.1 ∧ VarInt.Valid p.2) (hok : paramsOk ps = true) :
    decodeParams (encodeParams ps) = .ok ps := by
  unfold decodeParams encodeParams
  rw [VarInt.decodeAll_flatMap _ (flatten_valid hv)]
  simp [pairUp_flatten, hok]

theorem decodeOneVarInt_encode {v : Nat} (h : VarInt.Valid v) :
    decodeOneVarInt (VarInt.encode v) = .ok v := by
  unfold decodeOneVarInt
  have := VarInt.decode_encode h []
  rw [List.append_nil] at this
  rw [this]

theorem ofRaw_toRaw {f : Frame} (hf : f.Valid) : Frame.ofRaw f.toRaw = .ok f := by
  cases f with
  | data b => rfl
  | headers s => rfl
  | cancelPush p =>
    simp [Frame.toRaw, Frame.ofRaw, typeCancelPush, typeData, typeHeaders,
      decodeOneVarInt_encode (show VarInt.Valid p from hf), Except.map]
  | settings ps =>
    obtain ⟨h1, h2, -⟩ := hf
    simp [Frame.toRaw, Frame.ofRaw, typeSettings, typeData, typeHeaders, typeCancelPush,
      decodeParams_encodeParams h1 h2, Except.map]
  | pushPromise p s =>
    obtain ⟨h1, -⟩ := hf
    simp [Frame.toRaw, Frame.ofRaw, typePushPromise, typeData, typeHeaders, typeCancelPush,
      typeSettings, VarInt.decode_encode h1]
  | goaway i =>
    simp [Frame.toRaw, Frame.ofRaw, typeGoaway, typeData, typeHeaders, typeCancelPush,
      typeSettings, typePushPromise, decodeOneVarInt_encode (show VarInt.Valid i from hf),
      Except.map]
  | maxPushId p =>
    simp [Frame.toRaw, Frame.ofRaw, typeMaxPushId, typeGoaway, typeData, typeHeaders,
      typeCancelPush, typeSettings, typePushPromise,
      decodeOneVarInt_encode (show VarInt.Valid p from hf), Except.map]
  | h2Reserved t b =>
    obtain ⟨ht, -⟩ := hf
    simp only [h2ReservedTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> rfl
  | unknown t b =>
    obtain ⟨ht, -, -⟩ := hf
    simp only [knownTypes, h2ReservedTypes, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at ht
    obtain ⟨h0, h1, h3, h4, h5, h7, h13, h2, h6, h8, h9⟩ := ht
    simp only [typeData, typeHeaders, typeCancelPush, typeSettings, typePushPromise, typeGoaway,
      typeMaxPushId] at h0 h1 h3 h4 h5 h7 h13
    simp [Frame.toRaw, Frame.ofRaw, typeData, typeHeaders, typeCancelPush, typeSettings,
      typePushPromise, typeGoaway, typeMaxPushId, h2ReservedTypes, h0, h1, h3, h4, h5, h7, h13,
      h2, h6, h8, h9]

theorem small_valid {n : Nat} (h : n < 64) : VarInt.Valid n := by
  unfold VarInt.Valid VarInt.maxValue; omega

theorem encode_length_valid (v : Nat) : VarInt.Valid (VarInt.encode v).length := by
  rw [VarInt.encode_length]
  have := VarInt.lenOf_mem v
  simp only [VarInt.lengths, List.mem_cons, List.not_mem_nil, or_false] at this
  exact small_valid (by omega)

theorem toRaw_valid {f : Frame} (hf : f.Valid) : f.toRaw.Valid := by
  cases f with
  | data b => exact ⟨small_valid (n := typeData) (by decide), hf⟩
  | headers s => exact ⟨small_valid (n := typeHeaders) (by decide), hf⟩
  | cancelPush p => exact ⟨small_valid (n := typeCancelPush) (by decide), encode_length_valid p⟩
  | settings ps => exact ⟨small_valid (n := typeSettings) (by decide), hf.2.2⟩
  | pushPromise p s => exact ⟨small_valid (n := typePushPromise) (by decide), hf.2⟩
  | goaway i => exact ⟨small_valid (n := typeGoaway) (by decide), encode_length_valid i⟩
  | maxPushId p => exact ⟨small_valid (n := typeMaxPushId) (by decide), encode_length_valid p⟩
  | h2Reserved t b =>
    obtain ⟨ht, hb⟩ := hf
    refine ⟨?_, hb⟩
    simp only [h2ReservedTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
    exact small_valid (by simp only [Frame.toRaw]; omega)
  | unknown t b => exact ⟨hf.2.1, hf.2.2⟩

theorem decodeFrame_encode {f : Frame} (hf : f.Valid) {maxPayload : Nat}
    (hmax : f.toRaw.payload.length ≤ maxPayload) (rest : List UInt8) :
    decodeFrame maxPayload (f.encode ++ rest) = .ok (f, rest) := by
  unfold decodeFrame Frame.encode
  rw [readRaw_encodeRaw (toRaw_valid hf) hmax]
  simp only [ofRaw_toRaw hf]

theorem apply_unknown (s : Settings) {i : Nat} (v : Nat)
    (hi : i ∉ [settingQpackMaxTableCapacity, settingMaxFieldSectionSize, settingQpackBlockedStreams,
      settingEnableConnectProtocol, settingH3Datagram]) :
    s.apply (i, v) = .ok s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  simp [Settings.apply, h1, h2, h3, h4, h5]

theorem grease_not_known (n : Nat) :
    grease n ∉ [settingQpackMaxTableCapacity, settingMaxFieldSectionSize, settingQpackBlockedStreams,
      settingEnableConnectProtocol, settingH3Datagram] := by
  simp only [grease, settingQpackMaxTableCapacity, settingMaxFieldSectionSize,
    settingQpackBlockedStreams, settingEnableConnectProtocol, settingH3Datagram, List.mem_cons,
    List.not_mem_nil, or_false]
  omega

theorem isGrease_grease (n : Nat) : isGrease (grease n) = true := by
  unfold isGrease grease
  have h1 : (0x1f * n + 0x21 - 0x21) % 0x1f = 0 := by omega
  simp only [h1, beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
  omega

theorem isGrease_iff (m : Nat) : isGrease m = true ↔ ∃ n, m = grease n := by
  constructor
  · intro h
    simp only [isGrease, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨(m - 0x21) / 0x1f, by unfold grease; omega⟩
  · rintro ⟨n, rfl⟩; exact isGrease_grease n

theorem ofParams_cons (s : Settings) (p : Nat × Nat) (ps : List (Nat × Nat)) :
    (p :: ps).foldlM Settings.apply s = (s.apply p >>= fun s' => ps.foldlM Settings.apply s') := by
  simp [List.foldlM]

end Silmaril.Proofs.Net.Http3.Frame
