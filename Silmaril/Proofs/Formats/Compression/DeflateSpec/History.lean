module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Complete
public import Silmaril.Formats.Compression.Deflate.WithHistory

/-!
# DEFLATE with a preset history

`Deflate.deflateTakeWithHistory` against `DeflateSpec.StreamWithHistory`, and the
fact that only the last 32 KiB of a history matter (RFC 1951 distances are at
most 32768).
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

/-! ### Outputs only grow -/

theorem copyMatch_prefix (out : List UInt8) (d : Nat) :
    ∀ l, out <+: DeflateSpec.copyMatch out d l
  | 0 => List.prefix_refl _
  | l + 1 => (copyMatch_prefix out d l).trans (List.prefix_append _ _)

theorem length_copyMatch (out : List UInt8) (d : Nat) :
    ∀ l, (DeflateSpec.copyMatch out d l).length = out.length + l
  | 0 => rfl
  | l + 1 => by simp [DeflateSpec.copyMatch, length_copyMatch out d l]; omega

theorem symbols_prefix {lit dist : DeflateSpec.Code} {out bits out' rest}
    (h : DeflateSpec.Symbols lit dist out bits out' rest) : out <+: out' := by
  induction h with
  | endOfBlock => exact List.prefix_refl _
  | literal _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | reference _ _ _ _ _ _ _ _ ih => exact (copyMatch_prefix _ _ _).trans ih

theorem block_prefix {p : DeflateSpec.Policy} {out bits out' rest}
    (h : DeflateSpec.Block p out bits out' rest) : out <+: out' := by
  cases h with
  | stored => exact List.prefix_append _ _
  | fixed _ hs => exact symbols_prefix hs
  | dynamic _ _ hs => exact symbols_prefix hs

theorem blocks_prefix {p : DeflateSpec.Policy} {out bits out' rest}
    (h : DeflateSpec.Blocks p out bits out' rest) : out <+: out' := by
  induction h with
  | last hb => exact block_prefix hb
  | notLast hb _ ih => exact (block_prefix hb).trans ih

/-! ### The decoder with a history -/

theorem deflateTakeWithHistory_sound {history input out rest : List UInt8}
    (h : deflateTakeWithHistory history input = .ok (out, rest)) :
    DeflateSpec.StreamWithHistory .strict history input out rest := by
  unfold deflateTakeWithHistory resultWithHistory at h
  dsimp only at h
  cases hb : decompressBlocks _ _ history with
  | error e => rw [hb] at h; cases h
  | ok p =>
    obtain ⟨out', r'⟩ := p
    rw [hb] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨bits, hbl, hr'⟩ := decompressBlocks_sound _ hb (RR.init input)
    obtain ⟨pad, hpad, rfl⟩ := hr'.pad
    obtain ⟨t, rfl⟩ := blocks_prefix hbl
    refine ⟨pad, hpad, ?_⟩
    rw [inputBits_eq, inputBits_eq, List.drop_left]
    exact hbl

theorem deflateTakeWithHistory_complete {history input out rest : List UInt8}
    (h : DeflateSpec.StreamWithHistory .strict history input out rest) :
    deflateTakeWithHistory history input = .ok (out, rest) := by
  obtain ⟨pad, hpad, hbl⟩ := h
  rw [inputBits_eq, inputBits_eq] at hbl
  obtain ⟨r', h1, hr'⟩ := decompressBlocks_complete hbl (8 * input.length + 1) (RR.init input)
    (by simp; omega)
  have hfuel : ({ buffer := 0, count := 0, input := input, totalRead := 0 } : LSBReader).bitsLeft
      + 1 = 8 * input.length + 1 := by simp [LSBReader.bitsLeft]
  unfold deflateTakeWithHistory resultWithHistory
  dsimp only
  rw [hfuel, h1]
  simp [Except.map, hr'.tail hpad]

/-! ### Only the last 32 KiB of the history matter -/

theorem distTable_bound : ∀ x ∈ DeflateSpec.distTable, x.2 + 2 ^ x.1 ≤ 32769 := by decide

theorem distCode_bound {dsym e b y : Nat} {r r' : List Bool}
    (hd : DeflateSpec.distCode dsym = some (e, b)) (hf : DeflateSpec.Field e r y r') :
    b + y ≤ 32768 := by
  have hmem := List.mem_of_getElem? hd
  have := distTable_bound _ hmem
  have := hf.1
  dsimp only at *
  omega

theorem copyMatch_append (pre out : List UInt8) {d : Nat} (hd : d ≤ out.length) :
    ∀ l, DeflateSpec.copyMatch (pre ++ out) d l = pre ++ DeflateSpec.copyMatch out d l
  | 0 => rfl
  | l + 1 => by
    simp only [DeflateSpec.copyMatch, copyMatch_append pre out hd l]
    have hl := length_copyMatch out d l
    rw [List.append_assoc]
    congr 2
    simp only [List.getD_eq_getElem?_getD, List.length_append]
    rw [show pre.length + (DeflateSpec.copyMatch out d l).length - d =
      pre.length + ((DeflateSpec.copyMatch out d l).length - d) by omega,
      List.getElem?_append_right (by omega)]
    simp

theorem symbols_extend {lit dist : DeflateSpec.Code} (pre : List UInt8) {out bits out' rest}
    (h : DeflateSpec.Symbols lit dist out bits out' rest) :
    DeflateSpec.Symbols lit dist (pre ++ out) bits (pre ++ out') rest := by
  induction h with
  | endOfBlock h => exact .endOfBlock h
  | literal hv hr _ ih => exact .literal hv hr (by simpa using ih)
  | reference h1 h2 h3 h4 h5 h6 h7 _ ih =>
    refine .reference h1 h2 h3 h4 h5 h6 (by simp; omega) ?_
    rwa [copyMatch_append _ _ h7]

theorem symbols_restrict {lit dist : DeflateSpec.Code} (pre : List UInt8) {out bits out' rest}
    (h : DeflateSpec.Symbols lit dist out bits out' rest) :
    ∀ o, out = pre ++ o → 32768 ≤ o.length →
      ∃ o', out' = pre ++ o' ∧ DeflateSpec.Symbols lit dist o bits o' rest := by
  induction h with
  | endOfBlock h => intro o ho _; exact ⟨o, ho, .endOfBlock h⟩
  | @literal _ _ _ _ _ v hv hr _ ih =>
    intro o ho hl
    obtain ⟨o', h1, h2⟩ := ih (o ++ [UInt8.ofNat v]) (by simp [ho]) (by simp; omega)
    exact ⟨o', h1, .literal hv hr h2⟩
  | reference h1 h2 h3 h4 h5 h6 h7 _ ih =>
    intro o ho hl
    have hb := distCode_bound h5 h6
    subst ho
    rw [copyMatch_append _ _ (by omega)] at ih
    obtain ⟨o', e1, e2⟩ := ih _ rfl (by rw [length_copyMatch]; omega)
    exact ⟨o', e1, .reference h1 h2 h3 h4 h5 h6 (by omega) e2⟩

theorem block_extend {p : DeflateSpec.Policy} (pre : List UInt8) {out bits out' rest}
    (h : DeflateSpec.Block p out bits out' rest) :
    DeflateSpec.Block p (pre ++ out) bits (pre ++ out') rest := by
  cases h with
  | stored a b c d e f g i j => rw [← List.append_assoc]; exact .stored a b c d e f g i j
  | fixed a hs => exact .fixed a (symbols_extend pre hs)
  | dynamic a b hs => exact .dynamic a b (symbols_extend pre hs)

theorem block_restrict {p : DeflateSpec.Policy} (pre : List UInt8) {out bits out' rest}
    (h : DeflateSpec.Block p out bits out' rest) (o : List UInt8) (ho : out = pre ++ o)
    (hl : 32768 ≤ o.length) :
    ∃ o', out' = pre ++ o' ∧ DeflateSpec.Block p o bits o' rest := by
  cases h with
  | stored a b c d e f g i j => exact ⟨_, by simp [ho], .stored a b c d e f g i j⟩
  | fixed a hs =>
    obtain ⟨o', e1, e2⟩ := symbols_restrict pre hs o ho hl
    exact ⟨o', e1, .fixed a e2⟩
  | dynamic a b hs =>
    obtain ⟨o', e1, e2⟩ := symbols_restrict pre hs o ho hl
    exact ⟨o', e1, .dynamic a b e2⟩

theorem blocks_extend {p : DeflateSpec.Policy} (pre : List UInt8) {out bits out' rest}
    (h : DeflateSpec.Blocks p out bits out' rest) :
    DeflateSpec.Blocks p (pre ++ out) bits (pre ++ out') rest := by
  induction h with
  | last hb => exact .last (block_extend pre hb)
  | notLast hb _ ih => exact .notLast (block_extend pre hb) ih

theorem blocks_restrict {p : DeflateSpec.Policy} (pre : List UInt8) {out bits out' rest}
    (h : DeflateSpec.Blocks p out bits out' rest) :
    ∀ o, out = pre ++ o → 32768 ≤ o.length →
      ∃ o', out' = pre ++ o' ∧ DeflateSpec.Blocks p o bits o' rest := by
  induction h with
  | last hb =>
    intro o ho hl
    obtain ⟨o', e1, e2⟩ := block_restrict pre hb o ho hl
    exact ⟨o', e1, .last e2⟩
  | notLast hb _ ih =>
    intro o ho hl
    obtain ⟨o1, e1, e2⟩ := block_restrict pre hb o ho hl
    obtain ⟨t, rfl⟩ := block_prefix e2
    obtain ⟨o', e3, e4⟩ := ih _ e1 (by simp; omega)
    exact ⟨o', e3, .notLast e2 e4⟩

/-- Bytes more than 32 KiB back in the history are never referenced. -/
theorem streamWithHistory_append {p : DeflateSpec.Policy} (pre : List UInt8)
    {history input out rest : List UInt8} (hl : 32768 ≤ history.length) :
    DeflateSpec.StreamWithHistory p (pre ++ history) input out rest ↔
      DeflateSpec.StreamWithHistory p history input out rest := by
  constructor
  · rintro ⟨pad, hpad, hb⟩
    obtain ⟨o', e1, e2⟩ := blocks_restrict pre hb history rfl hl
    rw [List.append_assoc, List.append_cancel_left_eq] at e1
    exact ⟨pad, hpad, e1 ▸ e2⟩
  · rintro ⟨pad, hpad, hb⟩
    exact ⟨pad, hpad, by simpa using blocks_extend pre hb⟩

/-- The last 32 KiB of a history: what a 32 KiB window retains. -/
theorem streamWithHistory_window {p : DeflateSpec.Policy} {history input out rest : List UInt8} :
    DeflateSpec.StreamWithHistory p (history.drop (history.length - 32768)) input out rest ↔
      DeflateSpec.StreamWithHistory p history input out rest := by
  by_cases h : history.length ≤ 32768
  · rw [show history.length - 32768 = 0 by omega, List.drop_zero]
  · conv => rhs; rw [← List.take_append_drop (history.length - 32768) history]
    exact (streamWithHistory_append _ (by simp; omega)).symm

theorem stream_eq_withHistory {p : DeflateSpec.Policy} {input out rest : List UInt8} :
    DeflateSpec.Stream p input out rest ↔ DeflateSpec.StreamWithHistory p [] input out rest :=
  Iff.rfl

end Silmaril.Proofs.Formats.Compression.DeflateSpec
