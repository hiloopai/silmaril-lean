module

public import Silmaril.Wasm.Tools.Meta.Frame.Defs
public import Silmaril.Wasm.Tools.Meta.Leb.Thms
import Silmaril.Proofs.Wasm.Tools.Meta.Frame

/-!
# The payload structure: the parse keeps every byte

* `readU32_drop`: `readU32` consumes exactly `lebLen` bytes.
* `readHeader_sound`: a header that reads is the header of its encoding.
* `parseUnit_sound`, `parseBinary_sound`: **a parsed binary is exactly the concatenation of the
  parts it reports**: `enc.header ++ Item.listBytes items = bs`. Every section keeps its size
  field as written, every nested unit its header and items.
* `rawSec_eq_bytes`: re-encoding a section whose size field is minimal gives its bytes back.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

theorem readU32Go_drop : ∀ (acc s : Nat) (bs r : List UInt8) (n : Nat),
    readU32Go acc s bs = .ok (n, r) → r = bs.drop (lebLen bs)
  | _, _, [], _, _, h => by simp [readU32Go] at h
  | acc, s, b :: bs, r, n, h => by
    unfold readU32Go at h
    split at h
    · split at h <;> cases h
    · split at h
      · rename_i hb
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp [lebLen, hb, h.2]
      · rename_i hb
        have := readU32Go_drop _ _ bs r n h
        simp [lebLen, hb, this]

/-- `readU32` consumes exactly `lebLen` bytes. -/
theorem readU32_drop {bs r : List UInt8} {n : Nat} (h : readU32 bs = .ok (n, r)) :
    r = bs.drop (lebLen bs) := by
  cases bs with
  | nil => simp [readU32] at h
  | cons b bs =>
    by_cases hb : b.toNat < 128
    · simp only [readU32, hb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      simp [lebLen, hb, h.2]
    · simp only [readU32, hb, ↓reduceIte] at h
      have := readU32Go_drop _ _ bs r n h
      simp [lebLen, hb, this]

/-- The size field and the rest of a section split its bytes. -/
theorem take_lebLen_append {bs r : List UInt8} {n : Nat} (h : readU32 bs = .ok (n, r)) :
    bs.take (lebLen bs) ++ r = bs := by
  rw [readU32_drop h, List.take_append_drop]

/-- A header that reads is the header of its encoding, followed by the rest. -/
theorem readHeader_sound {e : Option Enc} {bs rest : List UInt8} {enc : Enc}
    (h : readHeader e bs = .ok (enc, rest)) : enc.header ++ rest = bs :=
  Silmaril.Proofs.Wasm.Tools.Meta.readHeader_sound_raw h

theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- The framing of a section splits its bytes. -/
theorem readSec_sound {id : UInt8} {bs size body rest : List UInt8}
    (h : readSec id bs = .ok (size, body, rest)) : size ++ (body ++ rest) = bs := by
  unfold readSec at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i n r hr
  split at h; · cases h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rw [List.take_append_drop, take_lebLen_append hr]

mutual
/-- **The sections of a unit are its bytes.** -/
theorem parseSecs_sound : ∀ (f : Nat) (enc : Enc) (st : PState) (bs : List UInt8)
    (items : List Item), parseSecs f enc st bs = .ok items → Item.listBytes items = bs
  | 0, _, _, _, _, h => by simp [parseSecs] at h
  | f + 1, enc, st, [], items, h => by
    simp only [parseSecs, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | f + 1, enc, st, id :: bs, items, h => by
    simp only [parseSecs, bind_ok_iff] at h
    obtain ⟨⟨size, body, rest⟩, hr, h⟩ := h
    have hsplit := readSec_sound hr
    split at h
    · split at h; · cases h
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨⟨enc', its⟩, hu, is, hs, rfl⟩ := h
      have h1 := parseUnit_sound f _ body enc' its hu
      have h2 := parseSecs_sound f enc st rest is hs
      simp only [Item.listBytes, Item.bytes, List.cons_append, List.append_assoc, h1, h2, hsplit]
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨st', _, is, hs, rfl⟩ := h
      have h2 := parseSecs_sound f enc st' rest is hs
      simp only [Item.listBytes, Item.bytes, Sec.bytes, List.cons_append, List.append_assoc, h2,
        hsplit]
/-- **A unit is its header and the bytes of its items.** -/
theorem parseUnit_sound : ∀ (f : Nat) (e : Option Enc) (bs : List UInt8) (enc : Enc)
    (items : List Item), parseUnit f e bs = .ok (enc, items) →
      enc.header ++ Item.listBytes items = bs
  | 0, _, _, _, _, h => by simp [parseUnit] at h
  | f + 1, e, bs, enc, items, h => by
    simp only [parseUnit, bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨enc', rest⟩, hh, is, hs, rfl, rfl⟩ := h
    rw [parseSecs_sound f _ _ rest is hs]
    exact readHeader_sound hh
end

/-- **A parsed binary is the concatenation of its parts.** -/
theorem parseBinary_sound {bs : List UInt8} {enc : Enc} {items : List Item}
    (h : parseBinary bs = .ok (enc, items)) : enc.header ++ Item.listBytes items = bs :=
  parseUnit_sound _ _ _ _ _ h

/-- A section whose size field is minimal re-encodes (as a `RawSection`) to its bytes. -/
theorem rawSec_eq_bytes (s : Sec) (h : s.size = encU32 s.body.length) :
    rawSec s.id s.body = s.bytes := by
  simp [rawSec, Sec.bytes, h]

end Silmaril.Wasm.Tools.Meta

end
