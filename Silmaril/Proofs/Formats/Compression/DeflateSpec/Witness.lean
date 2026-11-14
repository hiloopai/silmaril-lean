module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Profile

/-!
# Strict against RFC-permissive DEFLATE

The RFC-permissive and windowed decoders against the plain relations, the exact
relation between `Policy.strict` and `Policy.rfc`, and one stream for each
difference between them.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

theorem deflateTakeWithHistoryRfc_iff {history input out rest : List UInt8} :
    deflateTakeWithHistoryRfc history input = .ok (out, rest) ↔
      DeflateSpec.StreamWithHistory .rfc history input out rest :=
  deflateTakeWithHistoryProfile_iff.trans streamWithHistoryWithin_none

theorem deflateTakeRfc_iff {input out rest : List UInt8} :
    deflateTakeRfc input = .ok (out, rest) ↔ DeflateSpec.Stream .rfc input out rest :=
  deflateTakeWithHistoryRfc_iff

theorem deflateTakeWithHistoryWindowed_iff {window : Nat} {history input out rest : List UInt8} :
    deflateTakeWithHistoryProfile (.windowed window) history input = .ok (out, rest) ↔
      DeflateSpec.StreamWithHistoryWithin .strict (some window) history input out rest :=
  deflateTakeWithHistoryProfile_iff

theorem stream_rfc_functional {input out out' rest rest' : List UInt8}
    (h : DeflateSpec.Stream .rfc input out rest) (h' : DeflateSpec.Stream .rfc input out' rest') :
    out = out' ∧ rest = rest' := by
  have := (deflateTakeRfc_iff.2 h).symm.trans (deflateTakeRfc_iff.2 h'); simp_all

theorem stream_strict_iff {input out rest : List UInt8} :
    DeflateSpec.Stream .strict input out rest ↔
      DeflateSpec.Stream .rfc input out rest ∧ (deflateTake input).toBool = true := by
  constructor
  · intro h
    exact ⟨stream_strict_rfc h, by rw [deflateTake_complete h]; rfl⟩
  · rintro ⟨h, hb⟩
    cases e : deflateTake input with
    | error _ => rw [e] at hb; cases hb
    | ok p =>
      obtain ⟨o, r⟩ := p
      have hs := deflateTake_sound e
      obtain ⟨rfl, rfl⟩ := stream_rfc_functional h (stream_strict_rfc hs)
      exact hs

/-! ### Large windows change nothing -/

theorem symbolsWithin_of_large {w : Nat} (hw : 32768 ≤ w) {lit dist : DeflateSpec.Code}
    {out bits out' rest} (h : DeflateSpec.Symbols lit dist out bits out' rest) :
    DeflateSpec.SymbolsWithin (some w) lit dist out bits out' rest := by
  induction h with
  | endOfBlock h => exact .endOfBlock h
  | literal a b _ ih => exact .literal a b ih
  | reference a b c d e f g _ ih =>
    have := distCode_bound e f
    exact .reference a b c d e f g (fun w' hw' => by cases hw'; omega) ih

theorem blocksWithin_of_large {p : DeflateSpec.Policy} {w : Nat} (hw : 32768 ≤ w)
    {out bits out' rest} (hb : DeflateSpec.Blocks p out bits out' rest) :
    DeflateSpec.BlocksWithin p (some w) out bits out' rest := by
  have hblock : ∀ {out bits out' rest}, DeflateSpec.Block p out bits out' rest →
      DeflateSpec.BlockWithin p (some w) out bits out' rest := by
    intro out bits out' rest h
    cases h with
    | stored a b c d e f g i j => exact .stored a b c d e f g i j
    | fixed a b => exact .fixed a (symbolsWithin_of_large hw b)
    | dynamic a b c => exact .dynamic a b (symbolsWithin_of_large hw c)
  induction hb with
  | last h => exact .last (hblock h)
  | notLast h _ ih => exact .notLast (hblock h) ih

theorem streamWithHistoryWithin_large {p : DeflateSpec.Policy} {w : Nat} (hw : 32768 ≤ w)
    {history input out rest : List UInt8} :
    DeflateSpec.StreamWithHistoryWithin p (some w) history input out rest ↔
      DeflateSpec.StreamWithHistory p history input out rest :=
  ⟨streamWithHistoryWithin_forget,
   fun ⟨pad, hp, hb⟩ => ⟨pad, hp, blocksWithin_of_large hw hb⟩⟩

/-! ### Witnesses -/

theorem except_toOption_some {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e <;> simp_all [Except.toOption]

/-- A stream that the RFC-permissive decoder accepts and `deflateTake` rejects. -/
theorem rfc_only {input out : List UInt8}
    (h1 : (deflateTakeRfc input).toOption = some (out, []))
    (h2 : (deflateTake input).toOption = none) :
    DeflateSpec.Stream .rfc input out [] ∧ ∀ o r, ¬ DeflateSpec.Stream .strict input o r := by
  refine ⟨deflateTakeRfc_iff.1 (except_toOption_some h1), fun o r h => ?_⟩
  rw [deflateTake_complete h] at h2
  cases h2

set_option maxRecDepth 100000 in
theorem witness_hdist_rfc : (deflateTakeRfc [0x05, 0xde, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x90, 0x56, 0xff, 0x13, 0x94, 0x10]).toOption = some ([0x61], []) := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_hdist_strict : (deflateTake [0x05, 0xde, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x90, 0x56, 0xff, 0x13, 0x94, 0x10]).toOption = none := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_clCode_rfc : (deflateTakeRfc [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x00,
    0xa0, 0xac, 0xf6, 0x2f, 0x21, 0x02]).toOption = some ([0x61], []) := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_clCode_strict : (deflateTake [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x00,
    0xa0, 0xac, 0xf6, 0x2f, 0x21, 0x02]).toOption = none := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_litCode_rfc : (deflateTakeRfc [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x80,
    0xa0, 0xad, 0xfe, 0x3f, 0x11, 0x02]).toOption = some ([0x61], []) := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_litCode_strict : (deflateTake [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x80,
    0xa0, 0xad, 0xfe, 0x3f, 0x11, 0x02]).toOption = none := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_distCode_rfc : (deflateTakeRfc [0x0d, 0xc1, 0x81, 0x00, 0x00, 0x00, 0x00, 0x80,
    0x20, 0xd6, 0xfc, 0x25, 0xfe, 0x4d]).toOption = some ([0x61, 0x61, 0x61, 0x61], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem witness_distCode_strict : (deflateTake [0x0d, 0xc1, 0x81, 0x00, 0x00, 0x00, 0x00, 0x80,
    0x20, 0xd6, 0xfc, 0x25, 0xfe, 0x4d]).toOption = none := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_unassigned_rfc : (deflateTakeRfc [0x05, 0xc0, 0x01, 0x09, 0x00, 0x00, 0x00, 0x80,
    0xa0, 0xad, 0xfe, 0x3f, 0x11, 0x06]).toOption = none := by decide +kernel

theorem none_not_rfc {input : List UInt8} (h : (deflateTakeRfc input).toOption = none) :
    ∀ o r, ¬ DeflateSpec.Stream .rfc input o r := by
  intro o r hs
  rw [deflateTakeRfc_iff.2 hs] at h
  cases h

set_option maxRecDepth 100000 in
theorem witness_window_strict :
    (deflateTake [0x4b, 0x4c, 0x02, 0x42, 0x00]).toOption = some ([0x61, 0x62, 0x61, 0x62, 0x61], [])
    := by decide +kernel

set_option maxRecDepth 100000 in
theorem witness_window_one :
    (deflateTakeProfile (.windowed 1) [0x4b, 0x4c, 0x02, 0x42, 0x00]).toOption = none := by
  decide +kernel

theorem window_witness :
    DeflateSpec.Stream .strict [0x4b, 0x4c, 0x02, 0x42, 0x00] [0x61, 0x62, 0x61, 0x62, 0x61] [] ∧
      ∀ o r, ¬ DeflateSpec.StreamWithin .strict (some 1) [0x4b, 0x4c, 0x02, 0x42, 0x00] o r := by
  refine ⟨deflateTake_sound (except_toOption_some witness_window_strict), fun o r hs => ?_⟩
  have h := witness_window_one
  unfold deflateTakeProfile at h
  rw [deflateTakeWithHistoryWindowed_iff.2 hs] at h
  cases h

end Silmaril.Proofs.Formats.Compression.DeflateSpec
