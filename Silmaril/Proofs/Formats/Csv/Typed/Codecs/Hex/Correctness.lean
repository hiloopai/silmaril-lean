module

public import Silmaril.Formats.Csv.Typed.Codecs.Hex.Defs
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Codecs.Hex

open Silmaril.Formats.Csv.Typed.Codecs.Hex

private theorem nat_ofByte {n : Nat} (bound : n < 256) : (UInt8.ofNat n).toNat = n :=
  UInt8.toNat_ofNat_of_lt' bound

private theorem value_digit (n : Nat) (bound : n < 16) : digitValue (digit n) = some n := by
  unfold digit
  split
  · rename_i small
    unfold digitValue
    rw [nat_ofByte (by omega), ite_eq_left (by omega)]
    congr 1
    omega
  · rename_i large
    unfold digitValue
    rw [nat_ofByte (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1
    omega

private theorem digit_value {byte : UInt8} {n : Nat} (found : digitValue byte = some n) :
    n < 16 ∧ digit n = byte := by
  simp only [digitValue] at found
  split at found
  · rename_i range
    have eq := Option.some.inj found
    have small : n < 10 := by omega
    refine ⟨by omega, UInt8.toNat_inj.mp ?_⟩
    rw [digit, ite_eq_left small, nat_ofByte (by omega)]
    omega
  · split at found
    · rename_i range
      have eq := Option.some.inj found
      have large : ¬n < 10 := by omega
      refine ⟨by omega, UInt8.toNat_inj.mp ?_⟩
      rw [digit, ite_eq_right large, nat_ofByte (by omega)]
      omega
    · contradiction

private theorem makeByte (byte : UInt8) :
    UInt8.ofNat (16 * (byte.toNat / 16) + byte.toNat % 16) = byte := by
  rw [show 16 * (byte.toNat / 16) + byte.toNat % 16 = byte.toNat by omega]
  simp

private theorem decodeRev_encode (bytes acc : List UInt8) :
    decodeRev (encode bytes) acc = some (acc.reverse ++ bytes) := by
  induction bytes generalizing acc with
  | nil => simp [encode, decodeRev]
  | cons byte rest ih =>
    have high : byte.toNat / 16 < 16 := by have := UInt8.toNat_lt byte; omega
    have low : byte.toNat % 16 < 16 := by omega
    change decodeRev (digit (byte.toNat / 16) :: digit (byte.toNat % 16) :: encode rest) acc = _
    rw [decodeRev, value_digit _ high, value_digit _ low]
    change decodeRev (encode rest) (UInt8.ofNat (16 * (byte.toNat / 16) + byte.toNat % 16) :: acc) = _
    rw [makeByte, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem parseRev_spelling {text acc bytes : List UInt8}
    (parsed : decodeRev text acc = some bytes) :
    encode bytes = encode acc.reverse ++ text := by
  match text with
  | [] =>
    change some acc.reverse = some bytes at parsed
    have same := Option.some.inj parsed
    simp [← same]
  | high :: low :: rest =>
    cases h : digitValue high with
    | none => simp [decodeRev, h, Bind.bind, Option.bind] at parsed
    | some hi =>
      cases l : digitValue low with
      | none => simp [decodeRev, h, l, Bind.bind, Option.bind] at parsed
      | some lo =>
        obtain ⟨hiBound, hiDigit⟩ := digit_value h
        obtain ⟨loBound, loDigit⟩ := digit_value l
        let byte := UInt8.ofNat (16 * hi + lo)
        have exactByte : byte.toNat = 16 * hi + lo := by
          unfold byte
          exact nat_ofByte (by omega)
        have highByte : byte.toNat / 16 = hi := by omega
        have lowByte : byte.toNat % 16 = lo := by omega
        rw [decodeRev, h, l] at parsed
        have next : decodeRev rest (byte :: acc) = some bytes := parsed
        simpa [List.reverse_cons, encode, List.flatMap_append, highByte, lowByte,
          hiDigit, loDigit, List.append_assoc] using parseRev_spelling next
  | [_] => contradiction
termination_by text.length

theorem parsePrint : codec.ParsePrint := by
  intro bytes text printed
  have same : encode bytes = text := Option.some.inj printed
  subst text
  simpa [codec, decode] using decodeRev_encode bytes []

theorem printParse : codec.PrintParse := by
  intro bytes text parsed
  have exactText := parseRev_spelling (acc := []) (show decode text = some bytes from parsed)
  simpa [codec, encode] using exactText

end Silmaril.Proofs.Formats.Csv.Typed.Codecs.Hex
