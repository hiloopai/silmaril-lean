module

public import Silmaril.Formats.SExp.EncodingWatFullLexer

/-!
# `.wast` reading: positioned S-expressions, checked against the WAT lexical grammar

`wasm-tools json-from-wast` and `wasm-tools wast` need, besides the S-expressions of a
script, the source position of some tokens (the `line` of every JSON command, the text of
each module for the encoder). silmaril-lean's executable WAT lexer and bracketer
(`Wat.sexpWatFullExec?`, sound for the lexical grammar `Wat.sexpWat .core3` by
`Wat.sexpWat_of_fullExec`) produce S-expressions without positions, so this module has a
second, fast lexer over the UTF-8 bytes (`lexBytes`, `bracket`) that keeps byte offsets
(`PNode`), and **checks** at run time that erasing the positions gives exactly the
S-expressions of the verified lexer (`read`). Its result is therefore sound for the
grammar whatever the positioned lexer does (`Silmaril.Wasm.Tools.Wast.read_sound`); the
positions themselves are tested, not proved (they only feed `line` numbers and source
slices).

Lexical conventions (the Core 3.0 profile of `Wat.sexpWat`, which `wast` 1.262.0 shares
on every input of the testsuites): whitespace, `;;` line comments, nested `(; ;)` block
comments and `(@…)` annotations are skipped; tokens are `(`, `)`, string literals (all
escapes), `$"…"` quoted identifiers and `Tidchar` runs (identifiers `$x`, keywords,
numbers). Annotations are whitespace here, as in `Wat.sexpWat`: `(@custom …)` inside a
module is not seen by the script grammar (the module's source slice keeps it).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding

/-- An S-expression with the byte offsets of its tokens. A list records the offsets of
its `(` and of its `)`. -/
inductive PNode where
  | atom (pos : Nat) (a : Atom)
  | list (pos stop : Nat) (xs : List PNode)
  deriving Inhabited, Repr

/-- The byte offset of the first token. -/
def PNode.pos : PNode → Nat
  | .atom p _ => p
  | .list p _ _ => p

mutual
  /-- Forget the positions. -/
  def PNode.erase : PNode → SExp
    | .atom _ a => .atom a
    | .list _ _ xs => PNode.eraseList xs

  /-- `listOf (xs.map erase)`, structurally. -/
  def PNode.eraseList : List PNode → SExp
    | [] => .nil
    | x :: xs => .cons x.erase (PNode.eraseList xs)
end

/-! ## The positioned lexer -/

/-- Positioned tokens. -/
inductive PTok where
  | lp (pos : Nat)
  | rp (pos : Nat)
  | atom (pos : Nat) (a : Atom)
  deriving Inhabited, Repr

/-- `Tidchar` on bytes (ASCII only). -/
def isIdByte (b : UInt8) : Bool :=
  (b ≥ 48 && b ≤ 57) || (b ≥ 65 && b ≤ 90) || (b ≥ 97 && b ≤ 122) ||
    "!#$%&'*+-./:<=>?@\\^_`|~".toList.any (fun c => c.toNat == b.toNat)

def isSpaceByte (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-- Value of a hexadecimal digit byte. -/
def hexVal? (b : UInt8) : Option Nat :=
  if b ≥ 48 && b ≤ 57 then some (b.toNat - 48)
  else if b ≥ 97 && b ≤ 102 then some (b.toNat - 87)
  else if b ≥ 65 && b ≤ 70 then some (b.toNat - 55)
  else none

/-- UTF-8 encoding of a scalar value. -/
def utf8Of (n : Nat) : List UInt8 := (String.singleton (Char.ofNat n)).toUTF8.toList

/-- A lexing error at a byte offset. -/
structure LexError where
  pos : Nat
  msg : String
  deriving Repr

section
variable (s : ByteArray)

/-- The byte at `i` (0 past the end). -/
@[inline] def byteAt (i : Nat) : UInt8 := s.get! i

/-- Skip a nested block comment whose `(;` starts before `i`; `depth` open comments. -/
def blockEnd (start : Nat) : Nat → Nat → Nat → Except LexError Nat
  | 0, _, _ => .error ⟨start, "unterminated block comment"⟩
  | fuel + 1, depth, i =>
    if i ≥ s.size then .error ⟨start, "unterminated block comment"⟩
    else if byteAt s i == 40 && byteAt s (i + 1) == 59 then blockEnd start fuel (depth + 1) (i + 2)
    else if byteAt s i == 59 && byteAt s (i + 1) == 41 then
      if depth == 1 then .ok (i + 2) else blockEnd start fuel (depth - 1) (i + 2)
    else blockEnd start fuel depth (i + 1)

/-- The end of a line comment starting at `i`. -/
def lineEnd : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if i ≥ s.size || byteAt s i == 10 || byteAt s i == 13 then i else lineEnd fuel (i + 1)

/-- A string literal body after the opening quote at `start`: its bytes and the offset after
the closing quote. -/
def strBody (start : Nat) : Nat → Nat → Array UInt8 → Except LexError (Array UInt8 × Nat)
  | 0, _, _ => .error ⟨start, "unterminated string"⟩
  | fuel + 1, i, acc =>
    if i ≥ s.size then .error ⟨start, "unterminated string"⟩
    else
      let b := byteAt s i
      if b == 34 then .ok (acc, i + 1)
      else if b == 92 then
        let e := byteAt s (i + 1)
        if e == 110 then strBody start fuel (i + 2) (acc.push 10)
        else if e == 116 then strBody start fuel (i + 2) (acc.push 9)
        else if e == 114 then strBody start fuel (i + 2) (acc.push 13)
        else if e == 34 then strBody start fuel (i + 2) (acc.push 34)
        else if e == 39 then strBody start fuel (i + 2) (acc.push 39)
        else if e == 92 then strBody start fuel (i + 2) (acc.push 92)
        else if e == 117 then
          -- `\u{h+}`
          if byteAt s (i + 2) != 123 then .error ⟨i, "expected '{' in Unicode escape"⟩
          else
            let rec hexRun : Nat → Nat → Nat → Bool → Option (Nat × Nat)
              | 0, _, _, _ => none
              | f + 1, j, v, any =>
                if byteAt s j == 125 then (if any then some (v, j + 1) else none)
                else if byteAt s j == 95 && any then hexRun f (j + 1) v any
                else match hexVal? (byteAt s j) with
                  | some d => hexRun f (j + 1) (v * 16 + d) true
                  | none => none
            match hexRun (s.size + 1) (i + 3) 0 false with
            | none => .error ⟨i, "malformed Unicode escape"⟩
            | some (v, j) =>
              if v < 0x110000 && !(0xD800 ≤ v && v < 0xE000) then
                strBody start fuel j (acc ++ (utf8Of v).toArray)
              else .error ⟨i, "invalid Unicode scalar value in escape"⟩
        else match hexVal? e, hexVal? (byteAt s (i + 2)) with
          | some hi, some lo => strBody start fuel (i + 3) (acc.push (UInt8.ofNat (16 * hi + lo)))
          | _, _ => .error ⟨i, "invalid string escape"⟩
      else if b < 32 || b == 127 then .error ⟨i, "control character in string"⟩
      else strBody start fuel (i + 1) (acc.push b)

/-- The end of a `Tidchar` run starting at `i`. -/
def idEnd : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if i < s.size && isIdByte (byteAt s i) then idEnd fuel (i + 1) else i

/-- Text of the bytes `[a, b)` (ASCII). -/
def sliceStr (a b : Nat) : String :=
  String.fromUTF8! (s.extract a b)

mutual
  /-- Skip an annotation `(@…)` whose `(` is at `start`; `i` after the `@`. -/
  def annotEnd (start : Nat) : Nat → Nat → Nat → Except LexError Nat
    | 0, _, _ => .error ⟨start, "unterminated annotation"⟩
    | fuel + 1, depth, i =>
      if i ≥ s.size then .error ⟨start, "unterminated annotation"⟩
      else
        let b := byteAt s i
        if b == 59 && byteAt s (i + 1) == 59 then annotEnd start fuel depth (lineEnd s (s.size + 1) i)
        else if b == 40 && byteAt s (i + 1) == 59 then do
          let j ← blockEnd s i (s.size + 1) 1 (i + 2)
          annotEnd start fuel depth j
        else if b == 40 then annotEnd start fuel (depth + 1) (i + 1)
        else if b == 41 then
          if depth == 1 then .ok (i + 1) else annotEnd start fuel (depth - 1) (i + 1)
        else if b == 34 then do
          let (_, j) ← strBody s i (s.size + 1) (i + 1) #[]
          annotEnd start fuel depth j
        else annotEnd start fuel depth (i + 1)
end

/-- Skip whitespace, comments and annotations from `i`. -/
def skipSpace : Nat → Nat → Except LexError Nat
  | 0, i => .ok i
  | fuel + 1, i =>
    if i ≥ s.size then .ok i
    else
      let b := byteAt s i
      if isSpaceByte b then skipSpace fuel (i + 1)
      else if b == 59 && byteAt s (i + 1) == 59 then skipSpace fuel (lineEnd s (s.size + 1) i)
      else if b == 40 && byteAt s (i + 1) == 59 then do
        skipSpace fuel (← blockEnd s i (s.size + 1) 1 (i + 2))
      else if b == 40 && byteAt s (i + 1) == 64 then do
        skipSpace fuel (← annotEnd s i (s.size + 1) 1 (i + 2))
      else .ok i

/-- A token boundary: end of input, whitespace, a parenthesis or a comment. -/
def boundary (i : Nat) : Bool :=
  i ≥ s.size || isSpaceByte (byteAt s i) || byteAt s i == 40 || byteAt s i == 41 ||
    (byteAt s i == 59 && byteAt s (i + 1) == 59)

/-- All tokens from `i`. -/
def lexFrom : Nat → Nat → Array PTok → Except LexError (Array PTok)
  | 0, _, acc => .ok acc
  | fuel + 1, i, acc => do
    let i ← skipSpace s (s.size + 1) i
    if i ≥ s.size then return acc
    let b := byteAt s i
    if b == 40 then lexFrom fuel (i + 1) (acc.push (.lp i))
    else if b == 41 then lexFrom fuel (i + 1) (acc.push (.rp i))
    else if b == 34 then
      let (bytes, j) ← strBody s i (s.size + 1) (i + 1) #[]
      unless boundary s j do throw ⟨i, "reserved token: adjacent tokens need whitespace"⟩
      lexFrom fuel j (acc.push (.atom i (.str bytes.toList)))
    else if b == 36 && byteAt s (i + 1) == 34 then
      let (bytes, j) ← strBody s i (s.size + 1) (i + 2) #[]
      unless boundary s j do throw ⟨i, "reserved token: adjacent tokens need whitespace"⟩
      match String.fromUTF8? (ByteArray.mk bytes) with
      | some n =>
        if n.isEmpty then throw ⟨i, "empty identifier"⟩
        lexFrom fuel j (acc.push (.atom i (.id n)))
      | none => throw ⟨i, "malformed UTF-8 encoding of identifier"⟩
    else if isIdByte b then
      let j := idEnd s (s.size + 1) i
      unless boundary s j do throw ⟨i, "reserved token: adjacent tokens need whitespace"⟩
      let t := sliceStr s i j
      let a : Atom := if b == 36 && j - i ≥ 2 then .id (sliceStr s (i + 1) j) else .sym t
      lexFrom fuel j (acc.push (.atom i a))
    else throw ⟨i, "unexpected character"⟩

end

/-- The positioned tokens of a UTF-8 source. -/
def lexBytes (s : ByteArray) : Except LexError (Array PTok) := lexFrom s (s.size + 1) 0 #[]

/-- Bracket positioned tokens from index `i`: the trees up to the matching `)` (or the end
when `top`), and the index after it. -/
def bracketFrom (ts : Array PTok) : Nat → Nat → List PNode → Except LexError (List PNode × Nat)
  | 0, _, _ => .error ⟨0, "nesting too deep"⟩
  | fuel + 1, i, acc =>
    if h : i < ts.size then
      match ts[i] with
      | .atom p a => bracketFrom ts fuel (i + 1) (.atom p a :: acc)
      | .rp _ => .ok (acc.reverse, i)
      | .lp p => do
        let (xs, j) ← bracketFrom ts fuel (i + 1) []
        match ts[j]? with
        | some (.rp q) => bracketFrom ts fuel (j + 1) (.list p q xs :: acc)
        | _ => throw ⟨p, "unbalanced '('"⟩
    else .ok (acc.reverse, i)

/-- The positioned trees of a token array. -/
def bracket (ts : Array PTok) : Except LexError (List PNode) := do
  let (xs, j) ← bracketFrom ts (2 * ts.size + 2) 0 []
  match ts[j]? with
  | none => return xs
  | some t =>
    let p := match t with | .lp p | .rp p | .atom p _ => p
    throw ⟨p, "unexpected ')'"⟩

/-- The source text of a top-level tree (from its first to its last byte). -/
def PNode.slice (b : ByteArray) : PNode → String
  | .list p q _ => String.fromUTF8! (b.extract p (q + 1))
  | .atom .. => ""

/-- The position of the first top-level list that the executable WAT lexer rejects on its
own (to locate a rejection). -/
def firstRejected (b : ByteArray) (xs : List PNode) : Nat :=
  match xs.find? (fun x => match x with
      | .list .. => (Wat.sexpWatFullExec? .core3 (x.slice b)).isNone
      | .atom .. => false) with
  | some x => x.pos
  | none => 0

/-- Replace the bytes `[i, j)` by spaces, keeping line breaks. -/
def blankRange (out : ByteArray) (i j : Nat) : ByteArray := go (j - i) i out
where
  go : Nat → Nat → ByteArray → ByteArray
    | 0, _, o => o
    | n + 1, k, o =>
      let c := o.get! k
      go n (k + 1) (if c != 10 && c != 13 then o.set! k 32 else o)

/-- Blank every annotation `(@…)` outside strings and comments (scan from `i`). -/
def blankFrom (s : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | fuel + 1, i, out =>
    if i ≥ s.size then out
    else
      let b := byteAt s i
      if b == 59 && byteAt s (i + 1) == 59 then blankFrom s fuel (lineEnd s (s.size + 1) i) out
      else if b == 40 && byteAt s (i + 1) == 59 then
        match blockEnd s i (s.size + 1) 1 (i + 2) with
        | .ok j => blankFrom s fuel j out
        | .error _ => out
      else if b == 40 && byteAt s (i + 1) == 64 then
        match annotEnd s i (s.size + 1) 1 (i + 2) with
        | .ok j => blankFrom s fuel j (blankRange out i j)
        | .error _ => out
      else if b == 34 then
        match strBody s i (s.size + 1) (i + 1) #[] with
        | .ok (_, j) => blankFrom s fuel j out
        | .error _ => out
      else blankFrom s fuel (i + 1) out

/-- The source with its annotations replaced by spaces. -/
def blankAnnots (s : ByteArray) : ByteArray := blankFrom s (s.size + 1) 0 s

/-- The check of positioned trees against the verified lexer: `some true` when it reads
`s` to their erasure, `some false` when it reads the annotation-blanked `s` to it. -/
def readCheck (xs : List PNode) (s : String) : Option Bool :=
  if Wat.sexpWatFullExec? .core3 s = some (PNode.eraseList xs) then some true
  else
    match String.fromUTF8? (blankAnnots s.toUTF8) with
    | some s' => if Wat.sexpWatFullExec? .core3 s' = some (PNode.eraseList xs) then some false
      else none
    | none => none

/-! ## Checking in chunks

The verified lexer is checked on the whole text only as a fallback: the text is cut into
chunks, each ending with a line feed that follows a top-level list (possibly after spaces
and a line comment), and each chunk is checked on its own. The WAT lexical grammar is closed
under concatenation after a line feed (`LexAppend.sexpWat_chunks`), so the chunks' documents
concatenate to the whole text's. This keeps the check linear in the number of chunks where
silmaril-lean's fallback lexer (string escapes) is superlinear in its input. -/

/-- The concatenation of texts. -/
def joinStr (ss : List String) : String := ss.foldr (· ++ ·) ""

/-- The offset after the line feed that ends the line of a top-level list closing at `q`:
spaces, tabs and carriage returns, optionally a line comment, then `\n`. -/
def cutAfter (b : ByteArray) (q : Nat) : Option Nat :=
  go (b.size + 1) (q + 1)
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | f + 1, i =>
      if i ≥ b.size then none
      else
        let c := byteAt b i
        if c == 10 then some (i + 1)
        else if c == 32 || c == 9 || c == 13 then go f (i + 1)
        else if c == 59 && byteAt b (i + 1) == 59 then
          let j := lineEnd b (b.size + 1) i
          if j < b.size && byteAt b j == 10 then some (j + 1) else none
        else none

/-- Group the top-level trees into chunks of at least `minChunk` bytes: (start, stop, trees).
A chunk ends at a `cutAfter` offset; the last one at the end of the text. -/
def chunkRanges (b : ByteArray) (minChunk : Nat) (xs : List PNode) : List (Nat × Nat × List PNode) :=
  go xs 0 []
where
  go : List PNode → Nat → List PNode → List (Nat × Nat × List PNode)
    | [], a, acc => [(a, b.size, acc.reverse)]
    | x :: rest, a, acc =>
      let acc := x :: acc
      match x, rest with
      | .list _ q _, _ :: _ =>
        match cutAfter b q with
        | some z => if z - a ≥ minChunk then (a, z, acc.reverse) :: go rest z [] else go rest a acc
        | none => go rest a acc
      | _, _ => go rest a acc

/-- The chunks as texts with their trees (`none` if a chunk is not UTF-8). -/
def chunks (b : ByteArray) (xs : List PNode) : Option (List (String × List PNode)) :=
  (chunkRanges b 32768 xs).mapM fun (a, z, ns) => (String.fromUTF8? (b.extract a z)).map (·, ns)

/-- The chunk check: the chunks spell the text, all but the last end with a line feed, and
the verified lexer reads each chunk to the erasure of its trees. -/
def chunkCheck (s : String) (gs : List (String × List PNode)) : Bool :=
  decide (joinStr (gs.map (·.1)) = s) &&
    gs.dropLast.all (fun g => decide (g.1.toList.getLast? = some '\n')) &&
    gs.all (fun g => decide (Wat.sexpWatFullExec? .core3 g.1 = some (PNode.eraseList g.2)))

/-- Positioned trees checked chunk by chunk: the concatenation of the chunks' trees. -/
def readChunked (b : ByteArray) (s : String) (xs : List PNode) : Option (List PNode) :=
  match chunks b xs with
  | some gs => if chunkCheck s gs then some (gs.flatMap (·.2)) else none
  | none => none

/-- **Reading a script**: positioned trees whose erasure is the S-expression document the
verified lexer gives, and whether the verified lexer read the input itself (`true`) or
the input with its annotations blanked (`false`: silmaril-lean's executable lexer reads
annotation payloads of atoms and strings only, so `(@custom "n" (after data) "…")` or
`(@producers (language …))` are checked after `blankAnnots`; an annotation is whitespace
in the grammar either way). The check runs chunk by chunk (`readChunked`), and on the whole
text when the chunked check does not succeed. -/
def read (s : String) : Except LexError (List PNode × Bool) :=
  match lexBytes s.toUTF8 >>= bracket with
  | .error e => .error e
  | .ok xs => readFrom s xs
where
  /-- The whole-text check (the fallback). -/
  readWhole (s : String) (xs : List PNode) : Except LexError (List PNode × Bool) :=
    match readCheck xs s with
    | some flag => .ok (xs, flag)
    | none =>
      if (Wat.sexpWatFullExec? .core3 s).isSome then
        .error ⟨0, "internal: positioned lexer disagrees with the WAT lexical grammar"⟩
      else
        .error ⟨firstRejected s.toUTF8 xs,
          "the WAT lexical grammar (executable fragment) rejects this expression"⟩
  /-- The chunked check of the annotation-blanked text, then the fallback. -/
  readBlanked (s : String) (xs : List PNode) : Except LexError (List PNode × Bool) :=
    match (String.fromUTF8? (blankAnnots s.toUTF8)).bind
        (fun s' => readChunked (blankAnnots s.toUTF8) s' xs) with
    | some ps => .ok (ps, false)
    | none => readWhole s xs
  /-- The chunked check of the text, then of the blanked text, then the fallback. -/
  readFrom (s : String) (xs : List PNode) : Except LexError (List PNode × Bool) :=
    match readChunked s.toUTF8 s xs with
    | some ps => .ok (ps, true)
    | none => readBlanked s xs

/-- The positioned trees without the cross-check (for benchmarking the check). -/
def readUnchecked (s : String) : Except LexError (List PNode) := do
  bracket (← lexBytes s.toUTF8)

/-! ## Lines -/

/-- Offsets of the line starts (after each `\n`), ascending, starting with 0. -/
def lineStarts (s : ByteArray) : Array Nat := Id.run do
  let mut out : Array Nat := #[0]
  for i in [0:s.size] do
    if s.get! i == 10 then out := out.push (i + 1)
  return out

/-- The 1-based line of a byte offset: the number of line starts at or before it. -/
def lineOf (starts : Array Nat) (off : Nat) : Nat := Id.run do
  -- binary search for the last start ≤ off
  let mut lo := 0
  let mut hi := starts.size
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if starts[mid]! ≤ off then lo := mid else hi := mid
  return lo + 1

end Silmaril.Wasm.Tools.Wast
