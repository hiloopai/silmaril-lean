module

public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Formats.Compression.Deflate.WithHistory

/-!
# zlib preset-dictionary member specification

The header parser retains CINFO's window size and optional DICTID. A dictionary
is supplied as actual bytes: its full Adler-32 must match DICTID, while only its
window suffix seeds DEFLATE history. The identifier is a checksum, never an
assumption that a dictionary is unique. The dictionary-enabled decoder below
uses an explicit 32 KiB profile; parsing smaller CINFO values does not imply
support for those dictionary profiles (`Zlib.Windowed` adds them as separately
named decoders). Dictionary-free members retain the
existing zlib specification and ignore any offered dictionary. Trailer checks
cover emitted data only, excluding the initial dictionary history.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.ZlibDictionary

structure Header where
  windowBits : Nat
  dictionaryID : Option Nat
  deriving Repr, DecidableEq

/-- Parse CMF/FLG and, when FDICT is set, the four-byte big-endian DICTID.
All legal CINFO values are retained as metadata, including smaller windows. -/
def checkHeader (input : List UInt8) : Option (Header × List UInt8) :=
  match input with
  | cmf :: flg :: rest =>
    if cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧
        (cmf.toNat * 256 + flg.toNat) % 31 = 0 then
      if flg &&& 0x20 = 0 then some (⟨cmf.toNat / 16 + 8, none⟩, rest)
      else
        match rest with
        | d0 :: d1 :: d2 :: d3 :: body =>
          some (⟨cmf.toNat / 16 + 8, some (be32Val d0 d1 d2 d3)⟩, body)
        | _ => none
    else none
  | _ => none

/-- Current dictionary-enabled raw model has a 32 KiB history bound. Other
parsed window sizes need a separate configured-window refinement. -/
def supportedDictionaryProfile (header : Header) : Prop := header.windowBits = 15

instance (header : Header) : Decidable (supportedDictionaryProfile header) :=
  inferInstanceAs (Decidable (header.windowBits = 15))

/-- The most recent 32 KiB seed history, independent of the full DICTID check. -/
def history (dictionary : List UInt8) : List UInt8 :=
  dictionary.drop (dictionary.length - 32768)

/-- DICTID covers the entire supplied dictionary, before truncation to history. -/
def dictionaryChecksum (dictionary : List UInt8) : Nat :=
  (adler32 ⟨dictionary.toArray⟩).toNat

def finish (raw : Except Deflate.DecompressError (List UInt8 × List UInt8)) :
    Option (List UInt8 × List UInt8) :=
  match raw with
  | .error _ => none
  | .ok (data, afterData) => (zlibCheckTrailer data afterData).map (data, ·)

/-- Decode one member with an actual supplied dictionary. Dictionary-free
headers ignore the offered dictionary. Dictionary-bearing headers require the
explicit 32 KiB profile and a full-dictionary checksum match before decoding. -/
def takeWithDictionary (dictionary input : List UInt8) : Option (List UInt8 × List UInt8) :=
  (checkHeader input).bind fun (header, body) =>
    match header.dictionaryID with
    | none => finish (Deflate.deflateTake body)
    | some expected =>
      if supportedDictionaryProfile header ∧ dictionaryChecksum dictionary = expected then
        finish (Deflate.deflateTakeWithHistory (history dictionary) body)
      else none

end Silmaril.Formats.Compression.ZlibDictionary
