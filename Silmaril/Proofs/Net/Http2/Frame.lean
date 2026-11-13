module

public import Silmaril.Net.Http2.Frame.Defs

/-!
# HTTP/2 frames: proofs

For `Silmaril.Net.Http2.Frame.Thms` (RFC 9113 §4.1, §4.2).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http2

open Silmaril.Net.Http2

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]

theorem beValue_beBytes3 (x : Nat) (hx : x < 2 ^ 24) : beValue (beBytes 3 x) = x := by
  simp only [beBytes, beValue, List.foldl, toNat_toUInt8, Nat.reducePow] at *
  omega

theorem beValue_beBytes4 (x : Nat) (hx : x < 2 ^ 32) : beValue (beBytes 4 x) = x := by
  simp only [beBytes, beValue, List.foldl, toNat_toUInt8, Nat.reducePow] at *
  omega

theorem length_beBytes (k x : Nat) : (beBytes k x).length = k := by
  induction k <;> simp [beBytes, *]

theorem length_encodeHeader (h : FrameHeader) : (encodeHeader h).length = 9 := by
  simp [encodeHeader, length_beBytes]

theorem decodeHeader_encodeHeader (h : FrameHeader) (hv : h.Valid) (rest : List UInt8) :
    decodeHeader (encodeHeader h ++ rest) = some (h, rest) := by
  obtain ⟨hl, ht, hf, hs⟩ := hv
  have h9 := length_encodeHeader h
  unfold decodeHeader
  simp only [List.length_append, h9, show ¬ (9 + rest.length < 9) by omega, ↓reduceIte]
  have e1 : (encodeHeader h ++ rest).take 3 = beBytes 3 h.length := by
    simp [encodeHeader, beBytes]
  have e2 : (encodeHeader h ++ rest).drop 3 =
      h.type.toUInt8 :: h.flags.toUInt8 :: (beBytes 4 h.streamId ++ rest) := by
    simp [encodeHeader, beBytes]
  have e3 : ((encodeHeader h ++ rest).drop 5).take 4 = beBytes 4 h.streamId := by
    simp [encodeHeader, beBytes]
  have e4 : (encodeHeader h ++ rest).drop 9 = rest := by
    simp [encodeHeader, beBytes]
  have e5 : (encodeHeader h ++ rest).drop 4 =
      h.flags.toUInt8 :: (beBytes 4 h.streamId ++ rest) := by
    simp [encodeHeader, beBytes]
  rw [e1, e2, e3, e4, e5, beValue_beBytes3 _ hl, beValue_beBytes4 _ (by omega)]
  simp only [List.headD_cons, toNat_toUInt8, Option.some.injEq, Prod.mk.injEq, and_true]
  cases h
  simp only [FrameHeader.mk.injEq, true_and] at *
  omega

theorem readFrame_encodeFrame (m : Nat) (f : Frame) (hv : f.Valid) (hm : f.header.length ≤ m)
    (rest : List UInt8) : readFrame m (encodeFrame f ++ rest) = .ok (f, rest) := by
  obtain ⟨hh, hl⟩ := hv
  unfold readFrame encodeFrame
  rw [List.append_assoc, decodeHeader_encodeHeader _ hh]
  simp only [List.length_append, hl,
    show ¬ (f.payload.length + rest.length < f.payload.length) by omega,
    List.take_left', List.drop_left', ↓reduceIte, show ¬ (m < f.payload.length) by omega]

theorem readFrame_sound {m : Nat} {xs : List UInt8} {f : Frame} {rest : List UInt8}
    (h : readFrame m xs = .ok (f, rest)) :
    f.payload.length = f.header.length ∧ f.header.length ≤ m := by
  unfold readFrame at h
  split at h
  · cases h
  · next hd rest' _ =>
    split at h
    · cases h
    · next hm =>
      split at h
      · cases h
      · next hr =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [List.length_take]
        omega

end Silmaril.Proofs.Net.Http2
