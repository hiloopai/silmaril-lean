module

public import Silmaril.Cerberus.Symbol.Defs
public import Silmaril.Semantics.CPort.Encoding.TaggedCodec.Defs
public import Silmaril.Semantics.CPort.Formats.SExp.Literals.Defs

/-! # Digests as hexadecimal bytes

The syntax codec carries arbitrary byte lists. The document's well-formedness
check restricts them to the empty digest or the pinned exporter's 16-byte MD5.
Uppercase and odd-length spellings are rejected by the codec.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec
open Silmaril.Formats.SExpParser

/-- Two lowercase hexadecimal digits for a byte. -/
def byteHex (b : UInt8) : List Char :=
  let digit := fun n => "0123456789abcdef".toList[n]!
  [digit (b.toNat / 16), digit (b.toNat % 16)]

/-- Lowercase hexadecimal, without a prefix. -/
def digestHex (d : Digest) : String := String.ofList (d.bytes.flatMap byteHex)

private theorem hexPair_append (high low : Char) (rest : List Char) (b : UInt8)
    (h : decodeHexChars [high, low] = some [b]) :
    decodeHexChars ([high, low] ++ rest) =
      (fun tail => b :: tail) <$> decodeHexChars rest := by
  cases hh : hexDigit? high with
  | none => simp [decodeHexChars, hh] at h
  | some hn =>
    cases hl : hexDigit? low with
    | none => simp [decodeHexChars, hh, hl] at h
    | some ln =>
      simp [decodeHexChars, hh, hl] at h
      subst b
      cases ht : decodeHexChars rest <;> simp [decodeHexChars, hh, hl, ht]

private theorem byteHex_complete (b : UInt8) (rest : List Char) :
    decodeHexChars (byteHex b ++ rest) =
      (fun tail => b :: tail) <$> decodeHexChars rest := by
  have h : ∀ n : Fin 256, decodeHexChars (byteHex (UInt8.ofNat n.val)) =
      some [UInt8.ofNat n.val] := by decide +kernel
  have hb : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  have hd : decodeHexChars (byteHex b) = some [b] := by
    simpa only [hb] using h ⟨b.toNat, b.toNat_lt_size⟩
  exact hexPair_append _ _ rest b hd

private theorem digestHex_complete (d : Digest) :
    decodeHexChars (digestHex d).toList = some d.bytes := by
  obtain ⟨bs⟩ := d
  simp only [digestHex, String.toList_ofList]
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, byteHex_complete, ih]

/-- The wire digest, `($str "...")`, decoded into `Digest.bytes`. -/
def digest : Codec Digest where
  enc d := str.enc (digestHex d)
  dec t := do
    let s ← str.dec t
    let bs ← decodeHexChars s.toList
    let d : Digest := ⟨bs⟩
    if digestHex d = s then some d else none
  error _ := ⟨[], "expected a lowercase hexadecimal digest"⟩
  canonical t d h := by
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, bs, hb, h⟩ := h
    split at h
    · cases h
      rename_i heq
      rw [heq]
      exact str.canonical t s hs
    · simp at h
  complete d _ := by
    simp [Codec.complete_of_budget (c := str) rfl, digestHex_complete]

@[simp] theorem digest_budget : digest.budget = none := rfl

end Silmaril.Cerberus.Codec
