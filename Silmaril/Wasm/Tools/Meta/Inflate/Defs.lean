module

/-!
# zlib decompression (RFC 1950 and RFC 1951)

`zlibInflate cap src` decompresses a zlib stream as flate2 1.1's `ZlibDecoder` (miniz_oxide
backend) read through `take(cap + 1)` does, the reader of `.dep-v0` sections in wasm-metadata
0.262:

* the zlib header: compression method 8, window size at most 32 KiB, the header check
  (`(CMF * 256 + FLG) % 31 = 0`), no preset dictionary;
* DEFLATE blocks (RFC 1951 §3.2): stored (`LEN` and its complement), fixed Huffman and dynamic
  Huffman blocks, length/distance pairs (distance at most the output so far), until the final
  block; Huffman codes are canonical (§3.2.2) and decoded bit by bit (the decoder of zlib's
  `puff.c`): an over-subscribed code is an error, an incomplete one is allowed only when it has
  a single code;
* then the Adler-32 checksum of the output (big-endian), checked;
* reading stops as soon as more than `cap` bytes are produced (the result is then `none`, and
  the caller reports the limit); bytes after the checksum are ignored.

Errors are flate2's: `"corrupt deflate stream"` for a malformed stream and
`"incomplete deflate stream"` for a truncated one.

Tested (`tools/wasm-tools/tests/depv0-cases.py`: levels 0, 1, 6, 9; truncated, bad checksum,
preset dictionary, oversized). Proved on stored streams (`zlibStored`, the uncompressed encoding
of RFC 1950/1951): `zlibInflate_stored` in `Silmaril.Wasm.Tools.Meta.Inflate.Thms` (Huffman
blocks are tested only).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Inflate

/-- The decoder state: input, position, bit buffer (low bits first), output. -/
structure IS where
  src : ByteArray
  pos : Nat := 0
  bitbuf : Nat := 0
  bitcnt : Nat := 0
  out : ByteArray := ByteArray.empty
  /-- Stop (successfully) once the output is longer than this. -/
  cap : Nat

/-- Why decoding stopped early: a malformed stream, the end of the input, or the output cap. -/
inductive Stop where
  | corrupt
  | eof
  | cap
  deriving DecidableEq, Repr

abbrev IM := StateT IS (Except Stop)

/-- Take bytes into the bit buffer until it holds `need` bits. -/
def fill (need : Nat) : Nat → IM Unit
  | 0 => pure ()
  | f + 1 => do
    let s ← get
    if need ≤ s.bitcnt then return
    if s.src.size ≤ s.pos then throw .eof
    set { s with bitbuf := s.bitbuf + (s.src.get! s.pos).toNat * 2 ^ s.bitcnt,
                 pos := s.pos + 1, bitcnt := s.bitcnt + 8 }
    fill need f

/-- The next `need` bits (`need ≤ 16`), least significant first. -/
def bits (need : Nat) : IM Nat := do
  fill need 3
  let s ← get
  let v := s.bitbuf % 2 ^ need
  set { s with bitbuf := s.bitbuf / 2 ^ need, bitcnt := s.bitcnt - need }
  pure v

/-- Append a byte to the output (stopping at the cap). -/
def emit (b : UInt8) : IM Unit := do
  let s ← get
  let out := s.out.push b
  set { s with out }
  if s.cap < out.size then throw .cap

/-- A canonical Huffman code: the number of codes of each length (0–15) and the symbols
ordered by code. -/
structure Huff where
  count : Array Nat
  symbol : Array Nat
  deriving Inhabited

/-- Build a code from code lengths; with the number of codes left unused (negative: the code is
over-subscribed). -/
def construct (lengths : Array Nat) : Huff × Int := Id.run do
  let mut count := Array.replicate 16 0
  for l in lengths do
    count := count.modify l (· + 1)
  if count[0]! == lengths.size then return (⟨count, #[]⟩, 0)
  let mut left : Int := 1
  for len in [1:16] do
    left := left * 2 - count[len]!
    if left < 0 then return (⟨count, #[]⟩, left)
  let mut offs := Array.replicate 16 0
  for len in [1:15] do
    offs := offs.set! (len + 1) (offs[len]! + count[len]!)
  let mut symbol := Array.replicate lengths.size 0
  for i in [0:lengths.size] do
    let l := lengths[i]!
    if l != 0 then
      symbol := symbol.set! offs[l]! i
      offs := offs.modify l (· + 1)
  return (⟨count, symbol⟩, left)

/-- Decode one symbol (bit by bit, `puff.c`'s `decode`). -/
def decode (h : Huff) : IM Nat := do
  let mut code := 0
  let mut first := 0
  let mut index := 0
  for len in [1:16] do
    code := code + (← bits 1)
    let count := h.count[len]!
    if code < first + count then return h.symbol[index + (code - first)]!
    index := index + count
    first := (first + count) * 2
    code := code * 2
  throw .corrupt

def lbase : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
  67, 83, 99, 115, 131, 163, 195, 227, 258]
def lext : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4,
  5, 5, 5, 5, 0]
def dbase : Array Nat := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385,
  513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
def dext : Array Nat := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
  11, 11, 12, 12, 13, 13]

/-- Copy `len` bytes from `dist` back in the output (they may overlap the bytes written). -/
def copyBack (dist len : Nat) : IM Unit := do
  for _ in [0:len] do
    let s ← get
    emit (s.out.get! (s.out.size - dist))

/-- The symbols of a Huffman block, up to the end-of-block symbol. `fuel` bounds the number of
symbols (each takes at least one bit of input). -/
def codes (lencode distcode : Huff) : Nat → IM Unit
  | 0 => throw .corrupt
  | f + 1 => do
    let sym ← decode lencode
    if sym < 256 then emit sym.toUInt8; codes lencode distcode f
    else if sym == 256 then pure ()
    else
      let sym := sym - 257
      if 29 ≤ sym then throw .corrupt
      let len := lbase[sym]! + (← bits lext[sym]!)
      let ds ← decode distcode
      if 30 ≤ ds then throw .corrupt
      let dist := dbase[ds]! + (← bits dext[ds]!)
      if (← get).out.size < dist then throw .corrupt
      copyBack dist len
      codes lencode distcode f

/-- The fixed codes (RFC 1951 §3.2.6). -/
def fixedLen : Huff :=
  (construct ((Array.replicate 144 8) ++ (Array.replicate 112 9) ++ (Array.replicate 24 7) ++
    (Array.replicate 8 8))).1
def fixedDist : Huff := (construct (Array.replicate 30 5)).1

/-- The fuel of a block: one symbol per bit of input left. -/
def blockFuel : IM Nat := do let s ← get; pure (8 * (s.src.size - s.pos) + s.bitcnt + 1)

/-- A stored block. -/
def stored : IM Unit := do
  modify fun s => { s with bitbuf := 0, bitcnt := 0 }
  let s ← get
  if s.src.size < s.pos + 4 then throw .eof
  let len := (s.src.get! s.pos).toNat + 256 * (s.src.get! (s.pos + 1)).toNat
  let nlen := (s.src.get! (s.pos + 2)).toNat + 256 * (s.src.get! (s.pos + 3)).toNat
  if len + nlen != 65535 then throw .corrupt
  set { s with pos := s.pos + 4 }
  for i in [0:len] do
    let s ← get
    if s.src.size ≤ s.pos then throw .eof
    set { s with pos := s.pos + 1 }
    emit (s.src.get! s.pos)
    let _ := i

/-- The order of the code length code lengths. -/
def clOrder : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- The code lengths of a dynamic block (`nlen + ndist` of them). -/
def readLengths (lencode : Huff) (total : Nat) : Nat → Array Nat → IM (Array Nat)
  | 0, _ => throw .corrupt
  | f + 1, acc => do
    if total ≤ acc.size then return acc
    let sym ← decode lencode
    if sym < 16 then readLengths lencode total f (acc.push sym) else
    let (v, rep) ← if sym == 16 then do
        if acc.isEmpty then throw .corrupt
        pure (acc.back!, 3 + (← bits 2))
      else if sym == 17 then do pure (0, 3 + (← bits 3))
      else do pure (0, 11 + (← bits 7))
    if total < acc.size + rep then throw .corrupt
    readLengths lencode total f (acc ++ Array.replicate rep v)

/-- A dynamic block. -/
def dynamic : IM Unit := do
  let nlen := (← bits 5) + 257
  let ndist := (← bits 5) + 1
  let ncode := (← bits 4) + 4
  if 286 < nlen || 30 < ndist then throw .corrupt
  let mut cl := Array.replicate 19 0
  for i in [0:ncode] do
    cl := cl.set! clOrder[i]! (← bits 3)
  let (lc, err) := construct cl
  if err != 0 then throw .corrupt
  let lengths ← readLengths lc (nlen + ndist) (nlen + ndist + 1) #[]
  if lengths[256]! == 0 then throw .corrupt
  let (lencode, e1) := construct (lengths.extract 0 nlen)
  if e1 < 0 || (0 < e1 && nlen - lencode.count[0]! != 1) then throw .corrupt
  let (distcode, e2) := construct (lengths.extract nlen (nlen + ndist))
  if e2 < 0 || (0 < e2 && ndist - distcode.count[0]! != 1) then throw .corrupt
  codes lencode distcode (← blockFuel)

/-- The blocks, up to the final one. -/
def blocks : Nat → IM Unit
  | 0 => throw .corrupt
  | f + 1 => do
    let last ← bits 1
    let ty ← bits 2
    if ty == 0 then stored
    else if ty == 1 then codes fixedLen fixedDist (← blockFuel)
    else if ty == 2 then dynamic
    else throw .corrupt
    if last == 0 then blocks f

/-- Adler-32 (RFC 1950 §8.2). -/
def adler32 (bs : ByteArray) : Nat := Id.run do
  let mut a := 1
  let mut b := 0
  for x in bs do
    a := (a + x.toNat) % 65521
    b := (b + a) % 65521
  return b * 65536 + a

/-- The zlib stream: header, blocks, checksum. -/
def zlibM : IM Unit := do
  let cmf ← bits 8
  let flg ← bits 8
  if cmf % 16 != 8 || 7 < cmf / 16 || (cmf * 256 + flg) % 31 != 0 || flg / 32 % 2 == 1 then
    throw .corrupt
  blocks ((← get).src.size * 8 + 1)
  modify fun s => { s with bitbuf := 0, bitcnt := 0 }
  let s ← get
  if s.src.size < s.pos + 4 then throw .eof
  let want := (s.src.get! s.pos).toNat * 16777216 + (s.src.get! (s.pos + 1)).toNat * 65536 +
    (s.src.get! (s.pos + 2)).toNat * 256 + (s.src.get! (s.pos + 3)).toNat
  if want != adler32 s.out then throw .corrupt

/-- **Decompress a zlib stream**: the output, or `none` once more than `cap` bytes are
produced. -/
def zlibInflate (cap : Nat) (src : ByteArray) : Except String (Option ByteArray) :=
  match zlibM.run { src, cap } with
  | .ok ((), s) => .ok (some s.out)
  | .error .cap => .ok none
  | .error .corrupt => .error "corrupt deflate stream"
  | .error .eof => .error "incomplete deflate stream"


/-- **A zlib stream holding `d` uncompressed** (RFC 1950 header `78 01`, one final stored
block, RFC 1951 §3.2.4, with `LEN` and `NLEN`, then the Adler-32 checksum, big-endian), for
`d` of at most 65535 bytes: the encoder the inflate theorem is stated against. -/
def zlibStored (d : ByteArray) : ByteArray :=
  let n := d.size
  let c := adler32 d
  ⟨(#[0x78, 0x01, 0x01, (n % 256).toUInt8, (n / 256).toUInt8, ((65535 - n) % 256).toUInt8,
      ((65535 - n) / 256).toUInt8] ++ d.data ++
    #[(c / 16777216 % 256).toUInt8, (c / 65536 % 256).toUInt8, (c / 256 % 256).toUInt8,
      (c % 256).toUInt8])⟩

end Silmaril.Wasm.Tools.Meta.Inflate

end
