module

public import Silmaril.Wasm.Tools.Meta.Frame.Defs

/-!
# Raw proof: a header that reads is the header of its encoding

Case splits on the checks of `readHeader`; restated in
`Silmaril.Wasm.Tools.Meta.Frame.Thms` as `readHeader_sound`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Tools.Meta

open Silmaril.Wasm.Tools.Meta

/-- What a header that reads consists of: the magic number, a version word naming its
encoding, and the rest after eight bytes. -/
theorem readHeader_ok_shape {e : Option Enc} {bs rest : List UInt8} {enc : Enc}
    (h : readHeader e bs = .ok (enc, rest)) :
    bs.take 4 = magic ∧ rest = bs.drop 8 ∧
      ((bs.drop 4).take 4 = [0x01, 0x00, 0x00, 0x00] ∧ enc = .module ∨
        (bs.drop 4).take 4 = [0x0d, 0x00, 0x01, 0x00] ∧ enc = .component) := by
  unfold readHeader at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i h4 hm hv
  have hm' : bs.take 4 = magic := by simpa using hm
  split at h
  · rename_i hv1
    split at h; · cases h
    have he : enc = .module ∧ rest = bs.drop 8 := by simpa [eq_comm] using h
    exact ⟨hm', he.2, .inl ⟨by simpa using hv1, he.1⟩⟩
  · split at h
    · rename_i hv2
      split at h; · cases h
      have he : enc = .component ∧ rest = bs.drop 8 := by simpa [eq_comm] using h
      exact ⟨hm', he.2, .inr ⟨by simpa using hv2, he.1⟩⟩
    · cases h

/-- The first eight bytes and the rest. -/
theorem take_drop_eight (bs : List UInt8) :
    bs.take 4 ++ ((bs.drop 4).take 4 ++ bs.drop 8) = bs := by
  rw [show bs.drop 8 = (bs.drop 4).drop 4 by rw [List.drop_drop], List.take_append_drop,
    List.take_append_drop]

/-- A header that reads is the header of its encoding, followed by the rest. -/
theorem readHeader_sound_raw {e : Option Enc} {bs rest : List UInt8} {enc : Enc}
    (h : readHeader e bs = .ok (enc, rest)) : enc.header ++ rest = bs := by
  obtain ⟨hm, hr, hv⟩ := readHeader_ok_shape h
  have hb : bs.take 4 ++ ((bs.drop 4).take 4 ++ rest) = bs := hr ▸ take_drop_eight bs
  rcases hv with ⟨hv, he⟩ | ⟨hv, he⟩
  · rw [he, ← hb, hm, hv]; simp [Enc.header]
  · rw [he, ← hb, hm, hv]; simp [Enc.header]

end Silmaril.Proofs.Wasm.Tools.Meta

end
