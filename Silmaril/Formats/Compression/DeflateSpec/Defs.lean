module

/-!
# DEFLATE (RFC 1951), declaratively

An independent statement of what an RFC 1951 stream *means*, written to be read
against the RFC section by section. It shares no definitions with the decoder
`Deflate.deflateTake` (`Deflate/Decompress.lean`): there are no readers, tables,
fuel or error values here, only bit lists and inductive relations saying which
bit strings are well-formed streams and what they decode to.
`DeflateSpec.Thms` relates the two.

Conventions. A relation `R … bits … rest` says that a prefix of `bits` is an `R`,
and `rest` is what follows it. Most relations over compressed data also thread
the output produced so far (`out`, needed by back-references, §3.2.3) and the
output after the element (`out'`).

* §3.1.1: `fieldBits` (data elements, least-significant bit first),
  `codeBits` (Huffman codes, most-significant bit first), `inputBits`
  (bytes, each least-significant bit first);
* §3.2.2: `blCount`, `nextCode`, `assignCodes`, `Code.ofLengths` (canonical
  Huffman codes from code lengths, by the RFC's three steps), `kraft`,
  `Complete`, `PrefixLengths`, `SingleCode`;
* §3.2.3: `copyMatch` (LZ77 back-references, overlapping copies byte by byte);
* §3.2.4: `Block.stored`;
* §3.2.5: `lengthTable`, `distTable`, `Symbols` (the compressed data of a block);
* §3.2.6: `fixedLitLenLengths`, `fixedLitLenCode`, `fixedDistCode`;
* §3.2.7: `codeLengthOrder`, `clLengths`, `LengthRuns`, `DynamicHeader`;
* §3.2.3 again: `Block`, `Blocks`, `Stream` (blocks up to the one with `BFINAL`).

## Acceptance policy

RFC 1951 leaves some acceptance questions open, so the dynamic-header relation
is parameterised by a `Policy`:

* `Policy.rfc`, the letter of the RFC: up to 32 distance codes (`HDIST ≤ 31`,
  §3.2.7 "(1 - 32)") and any code-length set that defines a prefix code
  (Kraft sum ≤ 1), complete or not;
* `Policy.strict`, zlib's `inflate` and `Deflate.deflateTake`: at most 30
  distance codes; the code-length code must be complete; the literal/length and
  distance codes must be complete or use at most one code, of length 1 (the case
  §3.2.7 describes for a single distance code).

Choices common to both policies, all agreeing with zlib and `deflateTake`:

* literal/length symbols 286, 287 and distance symbols 30, 31 never occur
  (§3.2.6): `lengthTable` and `distTable` have no entry for them, so no
  derivation uses them, although they take part in the fixed code construction;
* `BTYPE = 11` is reserved (§3.2.3): `Block` has no constructor for it;
* the length is `base + extra` for every value of the extra bits, so code 284
  with extra bits `11111` denotes 258, outside the range 227–257 that the §3.2.5
  table lists for it;
* extra bits are data elements and so are packed least-significant bit first
  (§3.1.1); the §3.2.5 remark about "most-significant bit first" refers to how a
  machine integer is written down, not to the packing order;
* a back-reference may not reach before the start of the stream's output (no
  preset dictionary in raw DEFLATE);
* the stream starts on a byte boundary, and the bits after the final block up to
  the next byte boundary are ignored (`Stream`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.DeflateSpec

/-! ## §3.1.1 Packing into bytes -/

/-- An `n`-bit data element with value `v`, least-significant bit first
(§3.1.1: "Data elements are packed into bytes … starting with the
least-significant bit"). -/
def fieldBits (v : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => decide (v % 2 = 1) :: fieldBits (v / 2) n

/-- A Huffman code `c` of `n` bits, most-significant bit first (§3.1.1: "Huffman
codes are packed starting with the most-significant bit of the code"). -/
def codeBits (c : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => c.testBit n :: codeBits c n

/-- The bits of a byte string: the bytes in order, each least-significant bit
first. -/
def inputBits (bytes : List UInt8) : List Bool :=
  bytes.flatMap fun b => fieldBits b.toNat 8

/-- `bits` starts with an `n`-bit data element of value `v`, followed by `rest`. -/
def Field (n : Nat) (bits : List Bool) (v : Nat) (rest : List Bool) : Prop :=
  v < 2 ^ n ∧ bits = fieldBits v n ++ rest

/-- `bits` starts with the `n`-bit data elements `vs`, in order, then `rest`. -/
def Fields (n : Nat) (bits : List Bool) (vs : List Nat) (rest : List Bool) : Prop :=
  (∀ v ∈ vs, v < 2 ^ n) ∧ bits = (vs.map fun v => fieldBits v n).flatten ++ rest

/-! ## §3.2.2 Canonical Huffman codes

A code maps each symbol it encodes to its codeword (a bit list, in the order the
bits appear in the stream). -/

/-- A prefix code: the codeword of each encoded symbol. -/
abbrev Code := Nat → Option (List Bool)

/-- `bits` starts with the codeword of symbol `s`, followed by `rest`. -/
def Code.Reads (c : Code) (bits : List Bool) (s : Nat) (rest : List Bool) : Prop :=
  ∃ w, c s = some w ∧ bits = w ++ rest

/-- Step 1: `bl_count[len]`, the number of codes of length `len`. -/
def blCount (lengths : List Nat) (len : Nat) : Nat := lengths.count len

/-- Step 2: `next_code[len]`, the smallest code of length `len`.
```
code = 0; bl_count[0] = 0;
for (bits = 1; bits <= MAX_BITS; bits++) {
    code = (code + bl_count[bits-1]) << 1;
    next_code[bits] = code;
}
``` -/
def nextCode (lengths : List Nat) : Nat → Nat
  | 0 => 0
  | bits + 1 => (nextCode lengths bits + if bits = 0 then 0 else blCount lengths bits) * 2

/-- Step 3, the loop over the symbols `n` in order, with the current `next_code`
table `nc`: a symbol with length `len ≠ 0` gets the codeword `nc len` (`len` bits)
and `next_code[len]` is incremented; a symbol with length 0 gets no code.
```
for (n = 0; n <= max_code; n++) {
    len = tree[n].Len;
    if (len != 0) {
        tree[n].Code = next_code[len];
        next_code[len]++;
    }
}
``` -/
def assignCodes (nc : Nat → Nat) : List Nat → List (Option (List Bool))
  | [] => []
  | len :: lengths =>
    if len = 0 then none :: assignCodes nc lengths
    else some (codeBits (nc len) len) ::
      assignCodes (fun l => if l = len then nc l + 1 else nc l) lengths

/-- The canonical Huffman code with the given code lengths (symbol `n` has length
`lengths[n]`). -/
def Code.ofLengths (lengths : List Nat) : Code :=
  fun n => ((assignCodes (nextCode lengths) lengths)[n]?).join

/-- The Kraft sum `Σ 2^-len` over the used lengths, scaled by `2^maxBits`. -/
def kraft (maxBits : Nat) (lengths : List Nat) : Nat :=
  (lengths.map fun len => if len = 0 then 0 else 2 ^ (maxBits - len)).sum

/-- Lengths of at most `maxBits` bits whose canonical code is a prefix code
(Kraft sum at most 1; a larger sum is "over-subscribed" and the codes of
§3.2.2 overflow their lengths). -/
def PrefixLengths (maxBits : Nat) (lengths : List Nat) : Prop :=
  (∀ len ∈ lengths, len ≤ maxBits) ∧ kraft maxBits lengths ≤ 2 ^ maxBits

/-- Lengths of at most `maxBits` bits defining a complete prefix code (Kraft sum
exactly 1: every bit string is a prefix of a codeword or starts with one). -/
def Complete (maxBits : Nat) (lengths : List Nat) : Prop :=
  (∀ len ∈ lengths, len ≤ maxBits) ∧ kraft maxBits lengths = 2 ^ maxBits

/-- At most one symbol is used, with a one-bit code (§3.2.7: "If only one
distance code is used, it is encoded using one bit, not zero bits"; with no
symbol used at all, e.g. "the data is all literals"). -/
def SingleCode (lengths : List Nat) : Prop :=
  (∀ len ∈ lengths, len ≤ 1) ∧ lengths.count 1 ≤ 1

/-! ## §3.2.3 LZ77 back-references -/

/-- Append `len` bytes, each a copy of the byte `dist` positions before the
current end of the output. A copied byte may itself be one appended by the same
reference ("the referenced string may overlap the current position"). -/
def copyMatch (out : List UInt8) (dist : Nat) : Nat → List UInt8
  | 0 => out
  | len + 1 =>
    let o := copyMatch out dist len
    o ++ [o.getD (o.length - dist) 0]

/-! ## §3.2.5 Length and distance codes -/

/-- Literal/length codes 257–285 as `(extra bits, base length)`; the length is
the base plus the value of the extra bits. -/
def lengthTable : List (Nat × Nat) :=
  [ (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),   -- 257–264
    (1, 11), (1, 13), (1, 15), (1, 17),                                -- 265–268
    (2, 19), (2, 23), (2, 27), (2, 31),                                -- 269–272
    (3, 35), (3, 43), (3, 51), (3, 59),                                -- 273–276
    (4, 67), (4, 83), (4, 99), (4, 115),                               -- 277–280
    (5, 131), (5, 163), (5, 195), (5, 227),                            -- 281–284
    (0, 258) ]                                                         -- 285

/-- Distance codes 0–29 as `(extra bits, base distance)`. -/
def distTable : List (Nat × Nat) :=
  [ (0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 7), (2, 9), (2, 13),  -- 0–7
    (3, 17), (3, 25), (4, 33), (4, 49), (5, 65), (5, 97),             -- 8–13
    (6, 129), (6, 193), (7, 257), (7, 385), (8, 513), (8, 769),       -- 14–19
    (9, 1025), (9, 1537), (10, 2049), (10, 3073),                     -- 20–23
    (11, 4097), (11, 6145), (12, 8193), (12, 12289),                  -- 24–27
    (13, 16385), (13, 24577) ]                                        -- 28–29

/-- The `(extra bits, base length)` of a literal/length symbol, if it is a
length code (257–285). -/
def lengthCode (sym : Nat) : Option (Nat × Nat) :=
  if 257 ≤ sym then lengthTable[sym - 257]? else none

/-- The `(extra bits, base distance)` of a distance symbol (0–29). -/
def distCode (sym : Nat) : Option (Nat × Nat) := distTable[sym]?

/-- The compressed data of a Huffman-coded block, up to and including the
end-of-block symbol 256: literals (0–255) and `<length, distance>` pairs, each
pair a length symbol with its extra bits followed by a distance symbol with its
extra bits. `Symbols lit dist out bits out' rest`: starting from output `out`,
the data at the front of `bits` produces `out'` and is followed by `rest`. -/
inductive Symbols (lit dist : Code) : List UInt8 → List Bool → List UInt8 → List Bool → Prop
  /-- End of block (256). -/
  | endOfBlock {out bits rest} :
      lit.Reads bits 256 rest → Symbols lit dist out bits out rest
  /-- A literal byte. -/
  | literal {out bits r out' rest v} :
      v < 256 → lit.Reads bits v r →
      Symbols lit dist (out ++ [UInt8.ofNat v]) r out' rest →
      Symbols lit dist out bits out' rest
  /-- A back-reference: copy `length` bytes from `distance` bytes back. -/
  | reference {out bits out' rest sym r1 lenExtra lenBase x r2 dsym r3 distExtra distBase y r4} :
      lit.Reads bits sym r1 → lengthCode sym = some (lenExtra, lenBase) →
      Field lenExtra r1 x r2 →
      dist.Reads r2 dsym r3 → distCode dsym = some (distExtra, distBase) →
      Field distExtra r3 y r4 →
      distBase + y ≤ out.length →
      Symbols lit dist (copyMatch out (distBase + y) (lenBase + x)) r4 out' rest →
      Symbols lit dist out bits out' rest

/-! ## §3.2.6 Fixed Huffman codes -/

/-- The fixed literal/length code lengths, symbols 0–287. -/
def fixedLitLenLengths : List Nat :=
  List.replicate 144 8 ++    -- 0–143
  List.replicate 112 9 ++    -- 144–255
  List.replicate 24 7 ++     -- 256–279
  List.replicate 8 8         -- 280–287

/-- The fixed literal/length code. -/
def fixedLitLenCode : Code := Code.ofLengths fixedLitLenLengths

/-- The fixed distance code: "Distance codes 0-31 are represented by
(fixed-length) 5-bit codes". -/
def fixedDistCode : Code := fun d => if d < 32 then some (codeBits d 5) else none

/-! ## §3.2.7 Dynamic Huffman codes -/

/-- The order in which the code lengths of the code length alphabet appear. -/
def codeLengthOrder : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- The 19 code lengths of the code length alphabet, from the `HCLEN + 4` values
in the header: starting from all zeros, the `k`-th value is the length of symbol
`codeLengthOrder[k]`. -/
def clLengths (values : List Nat) : List Nat :=
  values.zipIdx.foldl (fun acc (v, k) => acc.set (codeLengthOrder.getD k 0) v)
    (List.replicate 19 0)

/-- The run-length-coded sequence of literal/length and distance code lengths,
read with the code length code `cl`. `LengthRuns cl acc bits lens rest`: with
the lengths `acc` already read, the runs at the front of `bits` extend them to
`lens` and are followed by `rest`. One sequence covers both alphabets, so runs
may cross from the literal/length lengths into the distance lengths. -/
inductive LengthRuns (cl : Code) : List Nat → List Bool → List Nat → List Bool → Prop
  | done {acc bits} : LengthRuns cl acc bits acc bits
  /-- 0–15: a code length. -/
  | length {acc bits r lens rest len} :
      len < 16 → cl.Reads bits len r →
      LengthRuns cl (acc ++ [len]) r lens rest → LengthRuns cl acc bits lens rest
  /-- 16: copy the previous code length 3–6 times (2 extra bits). -/
  | copyPrevious {acc bits r1 e r2 lens rest prev} :
      cl.Reads bits 16 r1 → Field 2 r1 e r2 → acc.getLast? = some prev →
      LengthRuns cl (acc ++ List.replicate (3 + e) prev) r2 lens rest →
      LengthRuns cl acc bits lens rest
  /-- 17: a code length of 0, 3–10 times (3 extra bits). -/
  | zeros {acc bits r1 e r2 lens rest} :
      cl.Reads bits 17 r1 → Field 3 r1 e r2 →
      LengthRuns cl (acc ++ List.replicate (3 + e) 0) r2 lens rest →
      LengthRuns cl acc bits lens rest
  /-- 18: a code length of 0, 11–138 times (7 extra bits). -/
  | longZeros {acc bits r1 e r2 lens rest} :
      cl.Reads bits 18 r1 → Field 7 r1 e r2 →
      LengthRuns cl (acc ++ List.replicate (11 + e) 0) r2 lens rest →
      LengthRuns cl acc bits lens rest

/-- Acceptance conditions the RFC leaves open (see the module docstring). -/
structure Policy where
  /-- The largest accepted number of distance codes, `HDIST + 1`. -/
  maxDistCodes : Nat
  /-- Accepted code length code lengths. -/
  clCodeOK : List Nat → Prop
  /-- Accepted literal/length and distance code lengths. -/
  codeOK : List Nat → Prop

/-- The letter of RFC 1951: `HDIST + 1 ≤ 32`, and every code a prefix code. -/
def Policy.rfc : Policy where
  maxDistCodes := 32
  clCodeOK := PrefixLengths 7
  codeOK := PrefixLengths 15

/-- zlib's `inflate` and `Deflate.deflateTake`: `HDIST + 1 ≤ 30`, a complete code
length code, and complete literal/length and distance codes except for the
single-code case. -/
def Policy.strict : Policy where
  maxDistCodes := 30
  clCodeOK := Complete 7
  codeOK := fun lengths => Complete 15 lengths ∨ SingleCode lengths

/-- The header of a dynamic block, from `HLIT` to the last code length, defining
the literal/length code `lit` and the distance code `dist`. -/
inductive DynamicHeader (p : Policy) : List Bool → Code → Code → List Bool → Prop
  | mk {bits r1 r2 r3 r4 rest : List Bool} {hlit hdist hclen : Nat} {clValues lens : List Nat}
      -- 5 bits: `HLIT`, the number of literal/length codes − 257 (257–286).
      (hlitField : Field 5 bits hlit r1) (hlitRange : hlit + 257 ≤ 286)
      -- 5 bits: `HDIST`, the number of distance codes − 1.
      (hdistField : Field 5 r1 hdist r2) (hdistRange : hdist + 1 ≤ p.maxDistCodes)
      -- 4 bits: `HCLEN`, the number of code length codes − 4 (4–19).
      (hclenField : Field 4 r2 hclen r3)
      -- `(HCLEN + 4) × 3` bits: code lengths for the code length alphabet.
      (clFields : Fields 3 r3 clValues r4) (clCount : clValues.length = hclen + 4)
      (clOK : p.clCodeOK (clLengths clValues))
      -- `HLIT + 257 + HDIST + 1` code lengths, coded with the code length code.
      (runs : LengthRuns (Code.ofLengths (clLengths clValues)) [] r4 lens rest)
      (count : lens.length = hlit + 257 + (hdist + 1))
      (litOK : p.codeOK (lens.take (hlit + 257)))
      (distOK : p.codeOK (lens.drop (hlit + 257))) :
      DynamicHeader p bits (Code.ofLengths (lens.take (hlit + 257)))
        (Code.ofLengths (lens.drop (hlit + 257))) rest

/-! ## Blocks and streams (§3.2.3, §3.2.4) -/

/-- One block after its `BFINAL` bit: the 2-bit `BTYPE`, then the block. -/
inductive Block (p : Policy) : List UInt8 → List Bool → List UInt8 → List Bool → Prop
  /-- `BTYPE = 00` (§3.2.4): skip to the next byte boundary, then `LEN`, `NLEN`
  (the one's complement of `LEN`) and `LEN` bytes of literal data. Being on a
  byte boundary means that a multiple of 8 bits remain: `Stream` starts on a
  byte boundary and consists of whole bytes. -/
  | stored {out bits r1 pad r2 len r3 nlen r4 data rest} :
      Field 2 bits 0 r1 →
      r1 = pad ++ r2 → pad.length < 8 → r2.length % 8 = 0 →
      Field 16 r2 len r3 → Field 16 r3 nlen r4 → nlen = len ^^^ 0xFFFF →
      data.length = len → r4 = inputBits data ++ rest →
      Block p out bits (out ++ data) rest
  /-- `BTYPE = 01` (§3.2.6): compressed with the fixed codes. -/
  | fixed {out bits r out' rest} :
      Field 2 bits 1 r → Symbols fixedLitLenCode fixedDistCode out r out' rest →
      Block p out bits out' rest
  /-- `BTYPE = 10` (§3.2.7): compressed with codes given in the block. -/
  | dynamic {out bits r1 lit dist r2 out' rest} :
      Field 2 bits 2 r1 → DynamicHeader p r1 lit dist r2 → Symbols lit dist out r2 out' rest →
      Block p out bits out' rest

/-- Blocks, each preceded by its `BFINAL` bit, up to the block with `BFINAL = 1`.
Back-references may reach into earlier blocks: the output is threaded through. -/
inductive Blocks (p : Policy) : List UInt8 → List Bool → List UInt8 → List Bool → Prop
  | last {out bits out' rest} :
      Block p out bits out' rest → Blocks p out (true :: bits) out' rest
  | notLast {out bits out1 r out' rest} :
      Block p out bits out1 r → Blocks p out1 r out' rest →
      Blocks p out (false :: bits) out' rest

/-- The DEFLATE stream at the front of `input` decodes to `out`, and `rest` is
the input after it: the stream ends inside the byte holding the end of its final
block, and the remaining bits of that byte (`pad`) are ignored. -/
def Stream (p : Policy) (input out rest : List UInt8) : Prop :=
  ∃ pad : List Bool, pad.length < 8 ∧ Blocks p [] (inputBits input) out (pad ++ inputBits rest)

end Silmaril.Formats.Compression.DeflateSpec
