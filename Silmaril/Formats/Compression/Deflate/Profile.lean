module

public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Formats.Compression.Deflate.WithHistory

/-!
# DEFLATE decoding profiles

`deflateTake` implements one acceptance policy, zlib's. RFC 1951 leaves some
acceptance questions open, so this module adds a decoder parameterised by a
`DecodeProfile`, reusing the block readers of `Decompress.lean` and changing only
the checks a profile controls:

* `maxDistCodes`: the largest accepted `HDIST + 1` (30 for zlib, 32 for the
  letter of RFC 1951, §3.2.7 "(1 - 32)");
* `completeCodes`: whether dynamic codes must be complete. When `false`, any
  code-length set satisfying the Kraft inequality is accepted, the canonical
  code is built from it, and decoding fails only when a code word that is not
  assigned to a symbol is actually read;
* `window`: an optional bound on back-reference distances (zlib's `CINFO`
  window, RFC 1950 §2.2), in addition to the bound by the output so far.

`DecodeProfile.strict` is `deflateTake` itself (`deflateTakeProfile_strict` in
`DeflateSpec.Thms`); `deflateTakeRfc` is the RFC-permissive decoder; and
`DecodeProfile.windowed w` is zlib's policy with distances at most `w`.

These decoders are list-based and quadratic like the specification decoder;
they have no `Array` mirror.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

/-- The acceptance choices of a DEFLATE decoder (see the module docstring). -/
structure DecodeProfile where
  /-- The largest accepted number of distance codes, `HDIST + 1`. -/
  maxDistCodes : Nat
  /-- Require complete dynamic codes (except a single one-bit code). -/
  completeCodes : Bool
  /-- The largest accepted back-reference distance, if any. -/
  window : Option Nat

/-- zlib's `inflate` and `deflateTake`. -/
def DecodeProfile.strict : DecodeProfile := ⟨30, true, none⟩

/-- The letter of RFC 1951: up to 32 distance codes, any prefix code. -/
def DecodeProfile.rfc : DecodeProfile := ⟨32, false, none⟩

/-- zlib's policy, with back-references limited to `window` bytes. -/
def DecodeProfile.windowed (window : Nat) : DecodeProfile := ⟨30, true, some window⟩

/-- A distance is allowed by an optional window. -/
def withinWindow (window : Option Nat) (dist : Nat) : Bool :=
  match window with
  | none => true
  | some w => dist ≤ w

/-- `decodeStep` with a distance window. -/
def decodeStepW (window : Option Nat) (litLen : HuffmanTable) (dist : HuffmanTable)
    (r : LSBReader) (output : List UInt8) : Except DecompressError SymbolStep :=
  match litLen.readSymbolLSB r with
  | none => .error .decodeOverrun
  | some (sym, r1) =>
    if sym < 256 then
      .ok (.more (output ++ [UInt8.ofNat sym]) r1)
    else if sym = 256 then
      .ok (.done output r1)
    else if sym ≤ 285 then
      let lengthIdx := sym - 257
      let baseLen := lengthBase.getD lengthIdx 3
      let extraLen := lengthExtraBits.getD lengthIdx 0
      match r1.readBits extraLen with
      | none => .error .decodeOverrun
      | some (extraVal, r2) =>
        let realLen := baseLen + extraVal
        match dist.readSymbolLSB r2 with
        | none => .error .decodeOverrun
        | some (distSym, r3) =>
          if 30 ≤ distSym then .error (.badDistanceCode distSym) else
          let baseDist := distanceBase.getD distSym 1
          let extraDist := distanceExtraBits.getD distSym 0
          match r3.readBits extraDist with
          | none => .error .decodeOverrun
          | some (distVal, r4) =>
            let realDist := baseDist + distVal
            if realDist > output.length then .error .decodeOverrun
            else if !withinWindow window realDist then .error .decodeOverrun
            else .ok (.more (copyBack realDist output realLen) r4)
    else .error .decodeOverrun

/-- `decodeSymbolsFuel` with a distance window. -/
def decodeSymbolsFuelW (window : Option Nat) (litLen : HuffmanTable) (dist : HuffmanTable) :
    Nat → LSBReader → List UInt8 → Except DecompressError (List UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, output =>
    match decodeStepW window litLen dist r output with
    | .error e => .error e
    | .ok (.done out r') => .ok (out, r')
    | .ok (.more out r') => decodeSymbolsFuelW window litLen dist fuel r' out

/-- `readDynamicTables` with the profile's distance-code limit and code checks. -/
def readDynamicTablesP (prof : DecodeProfile) (r : LSBReader) :
    Except DecompressError (HuffmanTable × HuffmanTable × LSBReader) :=
  match r.readBits 5 with
  | none => .error .decodeOverrun
  | some (hlit, r1) =>
    match r1.readBits 5 with
    | none => .error .decodeOverrun
    | some (hdist, r2) =>
      match r2.readBits 4 with
      | none => .error .decodeOverrun
      | some (hclen, r3) =>
        let nlit := hlit + 257
        let ndist := hdist + 1
        let ncl := hclen + 4
        if 286 < nlit ∨ prof.maxDistCodes < ndist then .error .badDynamicHuffman
        else
          match readCLLengths ncl 0 (List.replicate 19 0) r3 with
          | .error e => .error e
          | .ok (clLens, r4) =>
            if prof.completeCodes && !isCompleteCode clLens 7 then .error .badDynamicHuffman
            else
              match HuffmanTable.ofLengths clLens 7 with
              | none => .error .badDynamicHuffman
              | some clTable =>
                match readCodeLengths clTable (nlit + ndist) (nlit + ndist + 1) [] r4 with
                | .error e => .error e
                | .ok (lens, r5) =>
                  let litLens := lens.take nlit
                  let distLens := lens.drop nlit
                  if litLens.getD 256 0 = 0 then .error .badDynamicHuffman
                  else if prof.completeCodes && !validCodeLengths litLens 15 then
                    .error .badDynamicHuffman
                  else if prof.completeCodes && !validCodeLengths distLens 15 then
                    .error .badDynamicHuffman
                  else
                    match HuffmanTable.ofLengths litLens 15,
                        HuffmanTable.ofLengths distLens 15 with
                    | some lt, some dt => .ok (lt, dt, r5)
                    | _, _ => .error .badDynamicHuffman

/-- `decompressBlockBody` under a profile. -/
def decompressBlockBodyP (prof : DecodeProfile) (btype : Nat) (r : LSBReader)
    (out : List UInt8) : Except DecompressError (List UInt8 × LSBReader) :=
  if btype = 0 then
    match decompressStored r with
    | .error e => .error e
    | .ok (bytes, r') => .ok (out ++ bytes, r')
  else if btype = 1 then
    match fixedLitLenTable, fixedDistTable with
    | some litLen, some dist => decodeSymbolsFuelW prof.window litLen dist (r.bitsLeft + 1) r out
    | _, _ => .error .badFixedTable
  else if btype = 2 then
    match readDynamicTablesP prof r with
    | .error e => .error e
    | .ok (litLen, dist, r') => decodeSymbolsFuelW prof.window litLen dist (r'.bitsLeft + 1) r' out
  else .error (.badBlockType btype)

/-- `decompressBlocks` under a profile. -/
def decompressBlocksP (prof : DecodeProfile) : Nat → LSBReader → List UInt8 →
    Except DecompressError (List UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, out =>
    match r.readBit with
    | none => .error .decodeOverrun
    | some (bfinal, r1) =>
      match r1.readBits 2 with
      | none => .error .decodeOverrun
      | some (btype, r2) =>
        match decompressBlockBodyP prof btype r2 out with
        | .error e => .error e
        | .ok (out', r3) =>
          if bfinal then .ok (out', r3) else decompressBlocksP prof fuel r3 out'

/-- Decode one DEFLATE stream after an installed `history` under a profile,
returning the new output and the unread whole bytes (as
`deflateTakeWithHistory`). -/
def deflateTakeWithHistoryProfile (prof : DecodeProfile) (history input : List UInt8) :
    Except DecompressError (List UInt8 × List UInt8) :=
  let reader : LSBReader := ⟨0, 0, input, 0⟩
  resultWithHistory history (decompressBlocksP prof (reader.bitsLeft + 1) reader history)

/-- Decode the DEFLATE stream at the front of `input` under a profile. -/
def deflateTakeProfile (prof : DecodeProfile) (input : List UInt8) :
    Except DecompressError (List UInt8 × List UInt8) :=
  deflateTakeWithHistoryProfile prof [] input

/-- **The RFC-permissive DEFLATE decoder**: `HDIST` up to 31 and incomplete
prefix codes are accepted (`DecodeProfile.rfc`). -/
def deflateTakeRfc (input : List UInt8) : Except DecompressError (List UInt8 × List UInt8) :=
  deflateTakeProfile .rfc input

/-- The RFC-permissive decoder with an installed history. -/
def deflateTakeWithHistoryRfc (history input : List UInt8) :
    Except DecompressError (List UInt8 × List UInt8) :=
  deflateTakeWithHistoryProfile .rfc history input

end Silmaril.Formats.Compression.Deflate
