module

public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Bits.Bitstream

/-!
# Raw DEFLATE decompression (RFC 1951)

`decompress` is taken as the *definition* of the format in this development:
`Compresses data c` means `decompress c = some data`, and `compress_sound`
(`Deflate.RoundTrip`) is proved against it.  All three block types are
implemented — stored (BTYPE 00, §3.2.4), fixed Huffman (01, §3.2.6) and dynamic
Huffman (10, §3.2.7, including the permuted code-length alphabet and the repeat
codes 16/17/18) — and BTYPE 11 is rejected.

Because the decoder is the specification, the theorems about it are only as good
as its fidelity to RFC 1951.  `Deflate.RoundTrip` therefore also carries
known-answer vectors produced by zlib and two rejection theorems.

The last section mirrors the whole decoder with the output in an `Array`, proves
the mirror equal to the specification, and registers it with `@[csimp]`: the
`List` accumulator above is quadratic in the output size.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression

def lengthBase : List Nat :=
  [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258]

def lengthExtraBits : List Nat :=
  [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]

def distanceBase : List Nat :=
  [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577]

def distanceExtraBits : List Nat :=
  [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]

def fixedLitLenLengths : CodeLengths :=
  List.ofFn (λ (i : Fin 288) =>
    if i.val < 144 then 8
    else if i.val < 256 then 9
    else if i.val < 280 then 7
    else 8)

def fixedDistLengths : CodeLengths :=
  List.replicate 32 5

def fixedLitLenTable : Option HuffmanTable :=
  HuffmanTable.ofLengths fixedLitLenLengths 9

def fixedDistTable : Option HuffmanTable :=
  HuffmanTable.ofLengths fixedDistLengths 5

inductive DecompressError where
  /-- BTYPE 11 is reserved (RFC 1951 §3.2.3). -/
  | badBlockType (t : Nat)
  /-- A stored block whose NLEN is not the one's complement of LEN, or that is
  truncated. -/
  | badStoredLen
  /-- A malformed dynamic-block header (RFC 1951 §3.2.7): out-of-range HLIT or
  HDIST, a code-length run that overshoots, or an incomplete code. -/
  | badDynamicHuffman
  /-- Distance symbols 30 and 31 exist in the fixed code but are reserved;
  RFC 1951 §3.2.6 says they never occur and a decoder must reject them. -/
  | badDistanceCode (sym : Nat)
  /-- The hard-coded fixed tables failed to build.  `fixedLitLenTable_spec` and
  `fixedDistTable_spec` prove this cannot happen. -/
  | badFixedTable
  /-- The stream ended in the middle of a code or a field. -/
  | decodeOverrun
deriving Repr, Inhabited

/-- Read `remaining` whole bytes, appending them to `acc`. -/
def readStoredBytes (acc : List UInt8) (r : LSBReader) :
    Nat → Except DecompressError (List UInt8 × LSBReader)
  | 0 => .ok (acc, r)
  | n + 1 =>
    match r.readByte with
    | none => .error .decodeOverrun
    | some (b, r') => readStoredBytes (acc ++ [b]) r' n

/-- Body of a stored block (BTYPE 00): skip to a byte boundary, read `LEN` and
`NLEN`, then `LEN` raw bytes. -/
def decompressStored (r : LSBReader) : Except DecompressError (List UInt8 × LSBReader) :=
  let r' := r.alignToByte
  match r'.readBits 16 with
  | none => .error .badStoredLen
  | some (len, r1) =>
    match r1.readBits 16 with
    | none => .error .badStoredLen
    | some (nlen, r2) =>
      if (len ^^^ nlen) % 65536 ≠ 65535 then .error .badStoredLen
      else readStoredBytes [] r2 len

/-- Append `n` bytes, each copied from `dist` bytes before the end of the output.
The source may overlap the bytes being written (RFC 1951 §3.2.3). -/
def copyBack (dist : Nat) (out : List UInt8) : Nat → List UInt8
  | 0 => out
  | m + 1 => copyBack dist (out ++ [out.getD (out.length - dist) 0]) m

/-- Outcome of decoding one symbol: end of block, or more symbols to come. -/
inductive SymbolStep where
  | done (output : List UInt8) (r : LSBReader)
  | more (output : List UInt8) (r : LSBReader)

/-- Decode one literal/length/distance symbol (with its extra bits and distance)
and apply it to `output`. -/
def decodeStep (litLen : HuffmanTable) (dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) : Except DecompressError SymbolStep :=
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
            else .ok (.more (copyBack realDist output realLen) r4)
    else .error .decodeOverrun

/-- Decode symbols until end-of-block (256), appending to `output`. `fuel` bounds
the number of symbols; every symbol consumes at least one bit, so `decodeSymbol`
supplies one more than the number of unread bits. -/
def decodeSymbolsFuel (litLen : HuffmanTable) (dist : HuffmanTable) :
    Nat → LSBReader → List UInt8 → Except DecompressError (List UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, output =>
    match decodeStep litLen dist r output with
    | .error e => .error e
    | .ok (.done out r') => .ok (out, r')
    | .ok (.more out r') => decodeSymbolsFuel litLen dist fuel r' out

/-- Decode the symbols of one Huffman-coded block, appending to `output`. -/
def decodeSymbol (litLen : HuffmanTable) (dist : HuffmanTable) (r : LSBReader)
    (output : List UInt8) : Except DecompressError (List UInt8 × LSBReader) :=
  decodeSymbolsFuel litLen dist (r.bitsLeft + 1) r output

/-! ### Dynamic Huffman blocks (RFC 1951 §3.2.7) -/

/-- The order in which the 19 lengths of the code-length alphabet appear in a
dynamic block header (RFC 1951 §3.2.7). -/
def codeLengthOrder : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read the `n` code-length-alphabet lengths that are present, three bits each,
scattering them into `acc` through `codeLengthOrder`; the rest stay 0. -/
def readCLLengths : Nat → Nat → List Nat → LSBReader →
    Except DecompressError (List Nat × LSBReader)
  | 0, _, acc, r => .ok (acc, r)
  | n + 1, i, acc, r =>
    match r.readBits 3 with
    | none => .error .decodeOverrun
    | some (v, r') => readCLLengths n (i + 1) (acc.set (codeLengthOrder.getD i 0) v) r'

/-- Decode the `total` literal/length and distance code lengths.  They are
run-length encoded: a symbol below 16 is a literal length, 16 repeats the
previous length 3–6 times (2 extra bits), 17 emits 3–10 zeros (3 extra bits) and
18 emits 11–138 zeros (7 extra bits).  A run that overshoots `total` is rejected,
as is a leading 16.  `fuel` bounds the number of symbols; each appends at least
one length. -/
def readCodeLengths (clTable : HuffmanTable) (total : Nat) :
    Nat → List Nat → LSBReader → Except DecompressError (List Nat × LSBReader)
  | 0, acc, r => if acc.length = total then .ok (acc, r) else .error .badDynamicHuffman
  | fuel + 1, acc, r =>
    if total ≤ acc.length then
      (if acc.length = total then .ok (acc, r) else .error .badDynamicHuffman)
    else
      match clTable.readSymbolLSB r with
      | none => .error .decodeOverrun
      | some (sym, r1) =>
        if sym < 16 then readCodeLengths clTable total fuel (acc ++ [sym]) r1
        else if sym = 16 then
          match acc.getLast? with
          | none => .error .badDynamicHuffman
          | some prev =>
            match r1.readBits 2 with
            | none => .error .decodeOverrun
            | some (e, r2) =>
              readCodeLengths clTable total fuel (acc ++ List.replicate (3 + e) prev) r2
        else if sym = 17 then
          match r1.readBits 3 with
          | none => .error .decodeOverrun
          | some (e, r2) =>
            readCodeLengths clTable total fuel (acc ++ List.replicate (3 + e) 0) r2
        else if sym = 18 then
          match r1.readBits 7 with
          | none => .error .decodeOverrun
          | some (e, r2) =>
            readCodeLengths clTable total fuel (acc ++ List.replicate (11 + e) 0) r2
        else .error .badDynamicHuffman

/-- A decoded length set is acceptable when the code is complete, or is the
degenerate set of at most one code of length 1 — the case RFC 1951 §3.2.7
allows for a single distance code ("If only one distance code is used, it is
encoded using one bit"), and the only incomplete code zlib's `inflate` accepts. -/
def validCodeLengths (lens : List Nat) (maxBits : Nat) : Bool :=
  isCompleteCode lens maxBits || lens.all (λ (len : Nat) => len ≤ 1)

/-- Read a dynamic block header: HLIT, HDIST, HCLEN, the code-length code, and
the run-length-encoded literal/length and distance code lengths.  Returns the
two decoding tables and the reader positioned at the first symbol. -/
def readDynamicTables (r : LSBReader) :
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
        -- RFC 1951 §3.2.7: HLIT ≤ 29 and HDIST ≤ 29, i.e. at most 286 literal/
        -- length codes and 30 distance codes.
        if 286 < nlit ∨ 30 < ndist then .error .badDynamicHuffman
        else
          match readCLLengths ncl 0 (List.replicate 19 0) r3 with
          | .error e => .error e
          | .ok (clLens, r4) =>
            if !isCompleteCode clLens 7 then .error .badDynamicHuffman
            else
              match HuffmanTable.ofLengths clLens 7 with
              | none => .error .badDynamicHuffman
              | some clTable =>
                match readCodeLengths clTable (nlit + ndist) (nlit + ndist + 1) [] r4 with
                | .error e => .error e
                | .ok (lens, r5) =>
                  let litLens := lens.take nlit
                  let distLens := lens.drop nlit
                  -- A complete prefix code need not contain the required
                  -- end-of-block symbol (RFC 1951 §3.2.7).
                  if litLens.getD 256 0 = 0 then .error .badDynamicHuffman
                  else if !validCodeLengths litLens 15 then .error .badDynamicHuffman
                  else if !validCodeLengths distLens 15 then .error .badDynamicHuffman
                  else
                    match HuffmanTable.ofLengths litLens 15,
                        HuffmanTable.ofLengths distLens 15 with
                    | some lt, some dt => .ok (lt, dt, r5)
                    | _, _ => .error .badDynamicHuffman

/-- Decode the body of one block, given its BTYPE and a reader positioned just
after the three header bits. -/
def decompressBlockBody (btype : Nat) (r : LSBReader) (out : List UInt8) :
    Except DecompressError (List UInt8 × LSBReader) :=
  if btype = 0 then
    match decompressStored r with
    | .error e => .error e
    | .ok (bytes, r') => .ok (out ++ bytes, r')
  else if btype = 1 then
    match fixedLitLenTable, fixedDistTable with
    | some litLen, some dist => decodeSymbol litLen dist r out
    | _, _ => .error .badFixedTable
  else if btype = 2 then
    match readDynamicTables r with
    | .error e => .error e
    | .ok (litLen, dist, r') => decodeSymbol litLen dist r' out
  else .error (.badBlockType btype)

/-- Decode blocks, appending to `out`, until one with BFINAL set. Every block
consumes at least its three header bits, which bounds `fuel`. -/
def decompressBlocks : Nat → LSBReader → List UInt8 →
    Except DecompressError (List UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, out =>
    match r.readBit with
    | none => .error .decodeOverrun
    | some (bfinal, r1) =>
      match r1.readBits 2 with
      | none => .error .decodeOverrun
      | some (btype, r2) =>
        match decompressBlockBody btype r2 out with
        | .error e => .error e
        | .ok (out', r3) =>
          if bfinal then .ok (out', r3) else decompressBlocks fuel r3 out'

/-- Decode a raw DEFLATE stream (RFC 1951): stored, fixed-Huffman and
dynamic-Huffman blocks, up to and including the first block with BFINAL set.
BTYPE 11 is reserved and is rejected. -/
def decompressBlock (r : LSBReader) : Except DecompressError (List UInt8) :=
  match decompressBlocks (r.bitsLeft + 1) r [] with
  | .error e => .error e
  | .ok (out, _) => .ok out

/-! ### Executable implementation

The decoder above is the specification, and it accumulates output in a `List`:
`out ++ [b]` and `out.getD (out.length - dist) 0` are both linear in the output
built so far, so decoding is quadratic (200 KB took 103 s).  The definitions
below are the same algorithm with the output in an `Array`, proved equal to the
specification and registered with `@[csimp]`, so compiled code runs the linear
version while every theorem keeps talking about the `List` one.

`decompress` is defined *after* this section on purpose: `@[csimp]` rewrites
only declarations compiled after the attribute is registered. -/

/-- `Array.getD` agrees with `List.getD` on the underlying list. -/
theorem arr_getD (a : Array UInt8) (i : Nat) (d : UInt8) : a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `Array.size` agrees with `List.length` on the underlying list. -/
theorem arr_size (a : Array UInt8) : a.size = a.toList.length := by simp

/-- `copyBack` with the output in an `Array`. -/
def copyBackArr (dist : Nat) (a : Array UInt8) : Nat → Array UInt8
  | 0 => a
  | m + 1 => copyBackArr dist (a.push (a.getD (a.size - dist) 0)) m

theorem copyBackArr_toList (dist : Nat) :
    ∀ (m : Nat) (a : Array UInt8), (copyBackArr dist a m).toList = copyBack dist a.toList m := by
  intro m
  induction m with
  | zero => intro a; rfl
  | succ m ih =>
    intro a
    rw [copyBackArr, copyBack, ih, Array.toList_push, arr_getD, arr_size]

/-- `readStoredBytes` with the output in an `Array`. -/
def readStoredBytesArr (acc : Array UInt8) (r : LSBReader) :
    Nat → Except DecompressError (Array UInt8 × LSBReader)
  | 0 => .ok (acc, r)
  | n + 1 =>
    match r.readByte with
    | none => .error .decodeOverrun
    | some (b, r') => readStoredBytesArr (acc.push b) r' n

/-- Forget the `Array` representation of a decoder result. -/
def toSpecPair (p : Array UInt8 × LSBReader) : List UInt8 × LSBReader := (p.1.toList, p.2)

theorem readStoredBytesArr_eq : ∀ (n : Nat) (acc : Array UInt8) (r : LSBReader),
    (readStoredBytesArr acc r n).map toSpecPair = readStoredBytes acc.toList r n := by
  intro n
  induction n with
  | zero => intro acc r; rfl
  | succ n ih =>
    intro acc r
    rw [readStoredBytesArr, readStoredBytes]
    generalize r.readByte = x
    cases x with
    | none => rfl
    | some p => rw [ih, Array.toList_push]

/-- `decompressStored` with the output in an `Array`. -/
def decompressStoredArr (r : LSBReader) : Except DecompressError (Array UInt8 × LSBReader) :=
  let r' := r.alignToByte
  match r'.readBits 16 with
  | none => .error .badStoredLen
  | some (len, r1) =>
    match r1.readBits 16 with
    | none => .error .badStoredLen
    | some (nlen, r2) =>
      if (len ^^^ nlen) % 65536 ≠ 65535 then .error .badStoredLen
      else readStoredBytesArr #[] r2 len

theorem decompressStoredArr_eq (r : LSBReader) :
    (decompressStoredArr r).map toSpecPair = decompressStored r := by
  simp only [decompressStoredArr, decompressStored]
  generalize r.alignToByte.readBits 16 = x1
  cases x1 with
  | none => rfl
  | some p =>
    obtain ⟨len, r1⟩ := p
    dsimp only
    generalize r1.readBits 16 = x2
    cases x2 with
    | none => rfl
    | some q =>
      obtain ⟨nlen, r2⟩ := q
      by_cases h3 : (len ^^^ nlen) % 65536 = 65535
      · simp only [ne_eq, h3, not_true_eq_false, ↓reduceIte]
        simpa using readStoredBytesArr_eq len #[] r2
      · simp only [ne_eq, h3, not_false_eq_true, ↓reduceIte]
        rfl

/-- `SymbolStep` with the output in an `Array`. -/
inductive SymbolStepArr where
  | done (output : Array UInt8) (r : LSBReader)
  | more (output : Array UInt8) (r : LSBReader)

/-- Forget the `Array` representation of a symbol step. -/
def SymbolStepArr.spec : SymbolStepArr → SymbolStep
  | .done o r => .done o.toList r
  | .more o r => .more o.toList r

/-- `decodeStep` with the output in an `Array`. -/
def decodeStepArr (litLen : HuffmanTable) (dist : HuffmanTable) (r : LSBReader)
    (output : Array UInt8) : Except DecompressError SymbolStepArr :=
  match litLen.readSymbolLSB r with
  | none => .error .decodeOverrun
  | some (sym, r1) =>
    if sym < 256 then
      .ok (.more (output.push (UInt8.ofNat sym)) r1)
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
            if realDist > output.size then .error .decodeOverrun
            else .ok (.more (copyBackArr realDist output realLen) r4)
    else .error .decodeOverrun

theorem decodeStepArr_eq (litLen dist : HuffmanTable) (r : LSBReader) (a : Array UInt8) :
    (decodeStepArr litLen dist r a).map SymbolStepArr.spec = decodeStep litLen dist r a.toList := by
  rw [decodeStepArr, decodeStep]
  generalize litLen.readSymbolLSB r = x0
  cases x0 with
  | none => rfl
  | some p =>
    obtain ⟨sym, r1⟩ := p
    simp only
    by_cases h1 : sym < 256
    · simp [h1, SymbolStepArr.spec, Except.map]
    by_cases h2 : sym = 256
    · simp [h2, SymbolStepArr.spec, Except.map]
    by_cases h3 : sym ≤ 285
    · simp only [h1, h2, h3, ↓reduceIte]
      generalize r1.readBits (lengthExtraBits.getD (sym - 257) 0) = x1
      cases x1 with
      | none => rfl
      | some q =>
        obtain ⟨extraVal, r2⟩ := q
        simp only
        generalize dist.readSymbolLSB r2 = x2
        cases x2 with
        | none => rfl
        | some t =>
          obtain ⟨distSym, r3⟩ := t
          simp only
          by_cases h4 : 30 ≤ distSym
          · simp [h4, Except.map]
          · simp only [h4, ↓reduceIte]
            generalize r3.readBits (distanceExtraBits.getD distSym 0) = x3
            cases x3 with
            | none => rfl
            | some u =>
              obtain ⟨distVal, r4⟩ := u
              simp only [arr_size]
              split
              · rfl
              · simp [SymbolStepArr.spec, Except.map, copyBackArr_toList]
    · simp [h1, h2, h3, Except.map]

/-- `decodeSymbolsFuel` with the output in an `Array`. -/
def decodeSymbolsFuelArr (litLen : HuffmanTable) (dist : HuffmanTable) :
    Nat → LSBReader → Array UInt8 → Except DecompressError (Array UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, output =>
    match decodeStepArr litLen dist r output with
    | .error e => .error e
    | .ok (.done out r') => .ok (out, r')
    | .ok (.more out r') => decodeSymbolsFuelArr litLen dist fuel r' out

theorem decodeSymbolsFuelArr_eq (litLen dist : HuffmanTable) :
    ∀ (fuel : Nat) (r : LSBReader) (a : Array UInt8),
      (decodeSymbolsFuelArr litLen dist fuel r a).map toSpecPair =
        decodeSymbolsFuel litLen dist fuel r a.toList := by
  intro fuel
  induction fuel with
  | zero => intro r a; rfl
  | succ fuel ih =>
    intro r a
    rw [decodeSymbolsFuelArr, decodeSymbolsFuel, ← decodeStepArr_eq]
    generalize decodeStepArr litLen dist r a = x
    cases x with
    | error e => rfl
    | ok st => cases st with
      | done out r' => rfl
      | more out r' => exact ih r' out

/-- `decodeStepArr` with the two Huffman lookups going through prebuilt decode
indices (`HuffmanTable.readSymbolIdx`). -/
def decodeStepIdx (litIdx distIdx : Array Nat) (litLen : HuffmanTable) (dist : HuffmanTable)
    (r : LSBReader) (output : Array UInt8) : Except DecompressError SymbolStepArr :=
  match litLen.readSymbolIdx litIdx r with
  | none => .error .decodeOverrun
  | some (sym, r1) =>
    if sym < 256 then
      .ok (.more (output.push (UInt8.ofNat sym)) r1)
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
        match dist.readSymbolIdx distIdx r2 with
        | none => .error .decodeOverrun
        | some (distSym, r3) =>
          if 30 ≤ distSym then .error (.badDistanceCode distSym) else
          let baseDist := distanceBase.getD distSym 1
          let extraDist := distanceExtraBits.getD distSym 0
          match r3.readBits extraDist with
          | none => .error .decodeOverrun
          | some (distVal, r4) =>
            let realDist := baseDist + distVal
            if realDist > output.size then .error .decodeOverrun
            else .ok (.more (copyBackArr realDist output realLen) r4)
    else .error .decodeOverrun

theorem decodeStepIdx_eq (litLen dist : HuffmanTable) (r : LSBReader) (a : Array UInt8) :
    decodeStepIdx (decTable litLen.entries) (decTable dist.entries) litLen dist r a
      = decodeStepArr litLen dist r a := by
  simp only [decodeStepIdx, decodeStepArr, HuffmanTable.readSymbolIdx_eq]

/-- `decodeSymbolsFuelArr` with prebuilt decode indices. -/
def decodeSymbolsFuelIdx (litIdx distIdx : Array Nat) (litLen : HuffmanTable)
    (dist : HuffmanTable) :
    Nat → LSBReader → Array UInt8 → Except DecompressError (Array UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, output =>
    match decodeStepIdx litIdx distIdx litLen dist r output with
    | .error e => .error e
    | .ok (.done out r') => .ok (out, r')
    | .ok (.more out r') => decodeSymbolsFuelIdx litIdx distIdx litLen dist fuel r' out

theorem decodeSymbolsFuelIdx_eq (litLen dist : HuffmanTable) :
    ∀ (fuel : Nat) (r : LSBReader) (a : Array UInt8),
      decodeSymbolsFuelIdx (decTable litLen.entries) (decTable dist.entries) litLen dist
          fuel r a = decodeSymbolsFuelArr litLen dist fuel r a := by
  intro fuel
  induction fuel with
  | zero => intro r a; rfl
  | succ fuel ih =>
    intro r a
    rw [decodeSymbolsFuelIdx, decodeSymbolsFuelArr, ← decodeStepIdx_eq]
    generalize decodeStepIdx (decTable litLen.entries) (decTable dist.entries) litLen dist r a = x
    cases x with
    | error e => rfl
    | ok st => cases st with
      | done out r' => rfl
      | more out r' => exact ih r' out

/-- `decodeSymbol` with the output in an `Array`, building the two decode
indices once for the whole block. -/
def decodeSymbolArr (litLen : HuffmanTable) (dist : HuffmanTable) (r : LSBReader)
    (output : Array UInt8) : Except DecompressError (Array UInt8 × LSBReader) :=
  decodeSymbolsFuelIdx (decTable litLen.entries) (decTable dist.entries) litLen dist
    (r.bitsLeft + 1) r output

theorem decodeSymbolArr_eq (litLen dist : HuffmanTable) (r : LSBReader) (a : Array UInt8) :
    decodeSymbolArr litLen dist r a = decodeSymbolsFuelArr litLen dist (r.bitsLeft + 1) r a :=
  decodeSymbolsFuelIdx_eq litLen dist (r.bitsLeft + 1) r a

/-- `decompressBlockBody` with the output in an `Array`. -/
def decompressBlockBodyArr (btype : Nat) (r : LSBReader) (out : Array UInt8) :
    Except DecompressError (Array UInt8 × LSBReader) :=
  if btype = 0 then
    match decompressStoredArr r with
    | .error e => .error e
    | .ok (bytes, r') => .ok (out ++ bytes, r')
  else if btype = 1 then
    match fixedLitLenTable, fixedDistTable with
    | some litLen, some dist => decodeSymbolArr litLen dist r out
    | _, _ => .error .badFixedTable
  else if btype = 2 then
    match readDynamicTables r with
    | .error e => .error e
    | .ok (litLen, dist, r') => decodeSymbolArr litLen dist r' out
  else .error (.badBlockType btype)

theorem decompressBlockBodyArr_eq (btype : Nat) (r : LSBReader) (a : Array UInt8) :
    (decompressBlockBodyArr btype r a).map toSpecPair = decompressBlockBody btype r a.toList := by
  rw [decompressBlockBodyArr, decompressBlockBody]
  by_cases h0 : btype = 0
  · simp only [h0, ↓reduceIte, ← decompressStoredArr_eq]
    generalize decompressStoredArr r = x
    cases x with
    | error e => rfl
    | ok pr =>
      obtain ⟨bytes, r'⟩ := pr
      simp [Except.map, toSpecPair]
  · by_cases h1 : btype = 1
    · simp only [h1, ↓reduceIte]
      generalize fixedLitLenTable = t1
      generalize fixedDistTable = t2
      cases t1 with
      | none => rfl
      | some litLen =>
        cases t2 with
        | none => rfl
        | some dist =>
          exact (congrArg (Except.map toSpecPair) (decodeSymbolArr_eq litLen dist r a)).trans
            (decodeSymbolsFuelArr_eq litLen dist (r.bitsLeft + 1) r a)
    · by_cases h2 : btype = 2
      · simp only [h2, ↓reduceIte]
        generalize readDynamicTables r = x
        cases x with
        | error e => rfl
        | ok tr =>
          obtain ⟨litLen, dist, r'⟩ := tr
          exact (congrArg (Except.map toSpecPair) (decodeSymbolArr_eq litLen dist r' a)).trans
            (decodeSymbolsFuelArr_eq litLen dist (r'.bitsLeft + 1) r' a)
      · simp only [h0, h1, h2, ↓reduceIte]
        rfl

/-- `decompressBlocks` with the output in an `Array`. -/
def decompressBlocksArr : Nat → LSBReader → Array UInt8 →
    Except DecompressError (Array UInt8 × LSBReader)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, out =>
    match r.readBit with
    | none => .error .decodeOverrun
    | some (bfinal, r1) =>
      match r1.readBits 2 with
      | none => .error .decodeOverrun
      | some (btype, r2) =>
        match decompressBlockBodyArr btype r2 out with
        | .error e => .error e
        | .ok (out', r3) =>
          if bfinal then .ok (out', r3) else decompressBlocksArr fuel r3 out'

theorem decompressBlocksArr_eq : ∀ (fuel : Nat) (r : LSBReader) (a : Array UInt8),
    (decompressBlocksArr fuel r a).map toSpecPair = decompressBlocks fuel r a.toList := by
  intro fuel
  induction fuel with
  | zero => intro r a; rfl
  | succ fuel ih =>
    intro r a
    rw [decompressBlocksArr, decompressBlocks]
    generalize r.readBit = y0
    cases y0 with
    | none => rfl
    | some p =>
      obtain ⟨bfinal, r1⟩ := p
      simp only
      generalize r1.readBits 2 = y1
      cases y1 with
      | none => rfl
      | some q =>
        obtain ⟨btype, r2⟩ := q
        simp only
        rw [← decompressBlockBodyArr_eq]
        generalize decompressBlockBodyArr btype r2 a = x
        cases x with
        | error e => rfl
        | ok pr =>
          obtain ⟨out', r3⟩ := pr
          cases bfinal with
          | false => simpa [Except.map, toSpecPair] using ih r3 out'
          | true => rfl

/-- `decompressBlock` with the output in an `Array`. -/
def decompressBlockFast (r : LSBReader) : Except DecompressError (List UInt8) :=
  match decompressBlocksArr (r.bitsLeft + 1) r #[] with
  | .error e => .error e
  | .ok (out, _) => .ok out.toList

@[csimp] theorem decompressBlock_eq_decompressBlockFast :
    @decompressBlock = @decompressBlockFast := by
  funext r
  rw [decompressBlock, decompressBlockFast, ← decompressBlocksArr_eq]
  generalize decompressBlocksArr (r.bitsLeft + 1) r #[] = x
  cases x with
  | error e => rfl
  | ok pr => rfl

/-- Raw DEFLATE decompression.  This function is taken as the definition of the
format in this development: `Compresses data c` below means `decompress c = some
data`, and `compress_sound` is proved against it.

It implements all three RFC 1951 block types.  Known deviations from a strict
reading of the standard: trailing bytes after the final block are ignored rather
than reported, and an incomplete literal/length or distance code is accepted
when it has at most one code (matching zlib's `inflate`, which RFC 1951 §3.2.7
licenses only for the distance code). -/
def decompress (data : ByteArray) : Option ByteArray :=
  match decompressBlock (LSBReader.ofByteArray data) with
  | .error _ => none
  | .ok bytes => some ⟨bytes.toArray⟩

/-- `c` is a DEFLATE encoding of `data`. Many encodings decode to the same data;
`compress` picks one of them. -/
def Compresses (data c : ByteArray) : Prop := decompress c = some data

end Silmaril.Formats.Compression.Deflate
