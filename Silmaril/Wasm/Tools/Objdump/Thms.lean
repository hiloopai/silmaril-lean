module

public import Silmaril.Wasm.Tools.Objdump.Defs
public import Silmaril.Wasm.Tools.Framing.Thms

/-!
# `wasm-tools objdump`: theorems

* `offsets_spec`: the offset `offsets` gives a section is where its contents are in the bytes
  of the section list;
* `frame_drop`: a framed binary is its 8-byte preamble followed by its sections;
* **`objdump_ranges`**: for a binary that frames, every section's printed range
  `[o, o + length)` holds exactly its contents in the input file (custom sections print the
  part after their name, `customName`).

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Objdump

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing

theorem offsets_spec : ∀ (base : Nat) (ss : List RawSec) {s : RawSec} {o : Nat},
    (s, o) ∈ offsets base ss →
      base ≤ o ∧ ((join ss).drop (o - base)).take s.content.length = s.content
  | _, [], _, _, h => by simp [offsets] at h
  | base, t :: ss, s, o, h => by
    simp only [offsets, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · refine ⟨by omega, ?_⟩
      have : base + 1 + s.size.length - base = (s.id :: s.size).length := by simp; omega
      rw [this]
      simp [join, RawSec.bytes]
    · obtain ⟨hle, hc⟩ := offsets_spec (base + (1 + t.size.length + t.content.length)) ss h
      rw [← RawSec.bytes_length] at hle hc
      refine ⟨by omega, ?_⟩
      have : o - base = t.bytes.length + (o - (base + t.bytes.length)) := by omega
      rw [this, join, ← List.drop_drop, List.drop_left]
      exact hc

theorem readHeader_rest {e : Option Enc} {b : Bytes} {e' : Enc} {r : Bytes}
    (h : readHeader e b = .ok (e', r)) : r = b.drop 8 := by
  unfold readHeader at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only at h
      split at h
      · split at h
        · cases h
        · cases h; rfl
      · split at h
        · split at h
          · cases h
          · cases h; rfl
        · cases h

/-- A framed binary is its preamble followed by its sections. -/
theorem frame_drop {e : Option Enc} {b : Bytes} {e' : Enc} {ss : List RawSec}
    (h : frame e b = .ok (e', ss)) : join ss = b.drop 8 := by
  unfold frame at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · rename_i ss' hs
      split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rw [(splitSecs_sound hs).1]
        exact readHeader_rest hp
    · cases h

/-- **The printed ranges are right**: in a binary that frames, a section listed by `offsets 8`
at offset `o` has its contents at `[o, o + length)` of the file. -/
theorem objdump_ranges {b : Bytes} {e : Enc} {ss : List RawSec} (h : frame none b = .ok (e, ss))
    {s : RawSec} {o : Nat} (hs : (s, o) ∈ offsets 8 ss) :
    (b.drop o).take s.content.length = s.content := by
  obtain ⟨hle, hc⟩ := offsets_spec 8 ss hs
  rw [frame_drop h, List.drop_drop] at hc
  have : 8 + (o - 8) = o := by omega
  rwa [this] at hc

end Silmaril.Wasm.Tools.Objdump
