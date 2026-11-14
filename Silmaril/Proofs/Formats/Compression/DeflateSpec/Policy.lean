module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Complete

/-!
# Acceptance policies

A more permissive policy accepts more streams, with the same meaning; in
particular `Policy.strict` streams are `Policy.rfc` streams.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

section Mono

variable {p q : DeflateSpec.Policy} (hd : p.maxDistCodes ≤ q.maxDistCodes)
  (hcl : ∀ L, p.clCodeOK L → q.clCodeOK L) (hc : ∀ L, p.codeOK L → q.codeOK L)
include hd hcl hc

theorem dynamicHeader_mono {bs rest : List Bool} {lit dist : DeflateSpec.Code}
    (h : DeflateSpec.DynamicHeader p bs lit dist rest) :
    DeflateSpec.DynamicHeader q bs lit dist rest := by
  cases h with
  | mk a b c d e f g i j k l m =>
    exact .mk a b c (Nat.le_trans d hd) e f g (hcl _ i) j k (hc _ l) (hc _ m)

theorem block_mono {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Block p out bs out' rest) : DeflateSpec.Block q out bs out' rest := by
  cases h with
  | stored a b c d e f g i j => exact .stored a b c d e f g i j
  | fixed a b => exact .fixed a b
  | dynamic a b c => exact .dynamic a (dynamicHeader_mono hd hcl hc b) c

theorem blocks_mono {out out' : List UInt8} {bs rest : List Bool}
    (h : DeflateSpec.Blocks p out bs out' rest) : DeflateSpec.Blocks q out bs out' rest := by
  induction h with
  | last hb => exact .last (block_mono hd hcl hc hb)
  | notLast hb _ ih => exact .notLast (block_mono hd hcl hc hb) ih

theorem stream_mono {input out rest : List UInt8} (h : DeflateSpec.Stream p input out rest) :
    DeflateSpec.Stream q input out rest := by
  obtain ⟨pad, hp, hb⟩ := h
  exact ⟨pad, hp, blocks_mono hd hcl hc hb⟩

end Mono

theorem strict_codeOK_rfc {L : List Nat} (h : DeflateSpec.Policy.strict.codeOK L) :
    DeflateSpec.Policy.rfc.codeOK L := by
  rcases h with hc | ⟨hs, h1⟩
  · exact ⟨hc.1, Nat.le_of_eq hc.2⟩
  · refine ⟨fun l hl => by have := hs l hl; omega, ?_⟩
    rw [kraft_of_le_one 15 hs]
    have : L.count 1 * 2 ^ (15 - 1) ≤ 1 * 2 ^ 14 := Nat.mul_le_mul_right _ h1
    simp at this ⊢; omega

theorem stream_strict_rfc {input out rest : List UInt8}
    (h : DeflateSpec.Stream .strict input out rest) : DeflateSpec.Stream .rfc input out rest :=
  stream_mono (p := .strict) (q := .rfc) (by decide)
    (fun _ hc => (⟨hc.1, Nat.le_of_eq hc.2⟩ : DeflateSpec.PrefixLengths 7 _))
    (fun _ h => strict_codeOK_rfc h) h

end Silmaril.Proofs.Formats.Compression.DeflateSpec
