module

public import Silmaril.Formats.Compression.Zlib.Dictionary

/-!
# Dictionary installation with retained history

This extension describes the DICT path when a logical window already exists.
Each accepted dictionary amends the retained history before the most recent
32 KiB are selected. DICTID still validates the full newly supplied dictionary;
earlier retained bytes need not have that checksum. This supports repeated
successful installations without assuming identifiers uniquely name bytes.

The ordinary no-DICT branch delegates to the existing dictionary-free member
specification and ignores retained history. Consequently this is an extension
of the wrapped DICT profile, not a model of every use of `inflateResetKeep`:
the source can retain history even for a subsequent no-DICT stream. Source
execution, allocation failure states and raw-mode dictionary entry points are
separate obligations.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.ZlibDictionaryHistory

open ZlibDictionary

/-- Circular-window logical update: append the newly supplied bytes, then
retain the suffix that fits the supported 32 KiB window. -/
def installedHistory (retained dictionary : List UInt8) : List UInt8 :=
  history (retained ++ dictionary)

/-- A retained-history DICT member; no-DICT headers use the original branch.
The supported dictionary window profile remains explicitly 32 KiB. -/
def takeWithRetainedHistory (retained dictionary input : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  (checkHeader input).bind fun (header, body) =>
    match header.dictionaryID with
    | none => finish (Deflate.deflateTake body)
    | some expected =>
      if supportedDictionaryProfile header ∧ dictionaryChecksum dictionary = expected then
        finish (Deflate.deflateTakeWithHistory (installedHistory retained dictionary) body)
      else none

end Silmaril.Formats.Compression.ZlibDictionaryHistory
