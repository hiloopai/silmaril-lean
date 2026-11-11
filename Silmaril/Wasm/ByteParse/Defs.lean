module

public import Silmaril.Wasm.Binary.Basic
public import Silmaril.Wasm.Binaryen.Exe.EncodeBase

/-!
# Fast, verified binary parsers: the cursor parser

`Parser α` reads a `ByteArray` in place. A parser receives the input, the end of
its *window* `stop` and the current position `pos`, and answers `Res.ok a pos'`
or `Res.err e`. There is no `List UInt8` conversion, no copied suffix, no state
record allocated per byte, and only one allocation per successful step (the
`Res.ok` cell); positions are `Nat`s, which are unboxed scalars at runtime.

The window is how size-prefixed sections are parsed: `sized n p` runs `p` with
`stop := pos + n`, so `p` cannot read past the section, and then requires that
`p` consumed the section exactly.

The *specification* of a parser is a relation `G : List UInt8 → α → Prop`
between the bytes it consumed and its result. Grammars are the pinned
silmaril-lean Wasm grammar where one exists (`UN`, `SN`, `Seq`, `Vec`, `Name`,
`Section` from `Silmaril.Wasm.Binary.Basic`), so soundness statements read like
`Silmaril.Wasm.Binary.Core.Decode.Sound`. The proof principles are in
`Silmaril.Wasm.ByteParse.Thms`:

* `Sound G p`: a successful run consumed a segment of its window that `G`
  relates to the result (position monotonicity and window bounds included);
* `Complete G p`: whenever the window begins with bytes `l` with `G l a`, the
  parser answers `a` after exactly `l`. With an encoder satisfying
  `G (enc a) a` this gives round trips `p (enc a ++ rest) = ok a |enc a|`.

Loops (`many`, `untilEnd`, LEB128) are self tail calls on the `Res` match, so
they compile to loops; vectors accumulate in an `Array`.
-/

@[expose] public section

namespace Silmaril.Wasm.ByteParse

/-- What went wrong. Constant payloads only: building an error allocates
nothing beyond the error itself, and only on failure. -/
inductive Kind where
  /-- The window ended. -/
  | eof
  /-- An unexpected tag byte for the named production. -/
  | tag (what : String) (byte : UInt8)
  /-- A LEB128 number is too long or out of range. -/
  | leb
  /-- A vector count exceeds the bytes left in the window. -/
  | count (n : Nat)
  /-- A name is not UTF-8. -/
  | utf8
  /-- A sub-parser did not consume its sized window exactly. -/
  | size (expected consumed : Nat)
  /-- Bytes remain where the input should end. -/
  | trailing
  /-- A loop body made no progress. -/
  | stuck
  /-- A recursion depth bound was exhausted. -/
  | depth
  /-- Any other message (cold path only). -/
  | other (msg : String)
  deriving Repr, Inhabited, BEq

/-- An error and the position where it was detected. -/
structure Error where
  pos : Nat
  kind : Kind
  deriving Repr, Inhabited, BEq

/-- The result of a parser: a value and the next position, or an error. -/
inductive Res (α : Type) where
  | ok (a : α) (pos : Nat)
  | err (e : Error)
  deriving Repr, Inhabited

/-- A parser: input, window end, position. -/
def Parser (α : Type) : Type := ByteArray → Nat → Nat → Res α

namespace Parser

@[inline] protected def pure {α : Type} (a : α) : Parser α := fun _ _ i => .ok a i

@[inline] protected def bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β :=
  fun bs s i =>
    match p bs s i with
    | .ok a j => f a bs s j
    | .err e => .err e

@[inline] protected def map {α β : Type} (f : α → β) (p : Parser α) : Parser β :=
  fun bs s i =>
    match p bs s i with
    | .ok a j => .ok (f a) j
    | .err e => .err e

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind
  map := Parser.map

end Parser



/-- Fail with `k` at the current position. -/
@[inline] def fail {α : Type} (k : Kind) : Parser α := fun _ _ i => .err ⟨i, k⟩

/-- One byte. -/
@[inline] def byte : Parser UInt8 := fun bs s i =>
  if hs : i < s then
    if h : i < bs.size then .ok bs[i] (i + 1) else .err ⟨i, .eof⟩
  else .err ⟨i, .eof⟩

/-- The next byte, if any, without consuming it. -/
@[inline] def peek : Parser (Option UInt8) := fun bs s i =>
  if i < s then .ok bs[i]? i else .ok none i

/-- Exactly the byte `b`. -/
@[inline] def expect (what : String) (b : UInt8) : Parser Unit := fun bs s i =>
  if hs : i < s then
    if h : i < bs.size then
      if bs[i] = b then .ok () (i + 1) else .err ⟨i, .tag what bs[i]⟩
    else .err ⟨i, .eof⟩
  else .err ⟨i, .eof⟩

/-- Bytes left in the window. -/
@[inline] def remaining : Parser Nat := fun _ s i => .ok (s - i) i

/-- Succeeds at the end of the window only. -/
@[inline] def eoi : Parser Unit := fun _ s i => if i = s then .ok () i else .err ⟨i, .trailing⟩

/-- Skip `n` bytes, returning the half-open span `(start, stop)` (no copy). -/
@[inline] def span (n : Nat) : Parser (Nat × Nat) := fun _ s i =>
  if i + n ≤ s then .ok (i, i + n) (i + n) else .err ⟨i, .eof⟩

/-- `n` bytes, copied once into a fresh array. -/
@[inline] def bytes (n : Nat) : Parser ByteArray := fun bs s i =>
  if i + n ≤ s then .ok (bs.extract i (i + n)) (i + n) else .err ⟨i, .eof⟩

/-- The rest of the window, copied. -/
@[inline] def rest : Parser ByteArray := fun bs s i =>
  if i ≤ s then .ok (bs.extract i s) s else .err ⟨i, .eof⟩

/-- Run `p` in the window of the next `n` bytes, which it must consume exactly.
`p` cannot read past the window. -/
@[inline] def sized {α : Type} (n : Nat) (p : Parser α) : Parser α := fun bs s i =>
  if i + n ≤ s then
    match p bs (i + n) i with
    | .ok a j => if j = i + n then .ok a j else .err ⟨j, .size n (j - i)⟩
    | .err e => .err e
  else .err ⟨i, .eof⟩

/-- `n` repetitions of `p`, accumulated in `acc` (a self tail call). -/
@[specialize] def manyAux {α : Type} (p : Parser α) : Nat → Array α → Parser (Array α)
  | 0, acc => fun _ _ i => .ok acc i
  | n + 1, acc => fun bs s i =>
    match p bs s i with
    | .ok a j => manyAux p n (acc.push a) bs s j
    | .err e => .err e

/-- `n` repetitions of `p`. -/
@[inline] def many {α : Type} (n : Nat) (p : Parser α) : Parser (List α) :=
  Parser.map Array.toList (manyAux p n #[])

/-- Repeat `p` until the window ends; each round must consume a byte. `fuel`
bounds the rounds (`untilEnd` uses the bytes left). -/
@[specialize] def untilEndAux {α : Type} (p : Parser α) : Nat → Array α → Parser (Array α)
  | 0, acc => fun _ s i => if i = s then .ok acc i else .err ⟨i, .stuck⟩
  | fuel + 1, acc => fun bs s i =>
    if i = s then .ok acc i else
    match p bs s i with
    | .ok a j => if i < j then untilEndAux p fuel (acc.push a) bs s j else .err ⟨j, .stuck⟩
    | .err e => .err e

/-- Repeat `p` until the window ends. -/
@[inline] def untilEnd {α : Type} (p : Parser α) : Parser (List α) := fun bs s i =>
  Parser.map Array.toList (untilEndAux p (s - i) #[]) bs s i

/-! ## LEB128 (Wasm `BuN`/`BsN`) -/

/-- Unsigned LEB128 with `budget` bits left, value so far `acc`, next digit
weight `2 ^ shift`. Mirrors `Silmaril.Wasm.Binary.UN`. -/
def uAux (budget shift acc : Nat) : Parser Nat := fun bs s i =>
  if hs : i < s then
    if h : i < bs.size then
      if bs[i].toNat < 128 then
        if bs[i].toNat < 2 ^ budget then .ok (acc + 2 ^ shift * bs[i].toNat) (i + 1)
        else .err ⟨i, .leb⟩
      else if 7 < budget then
        uAux (budget - 7) (shift + 7) (acc + 2 ^ shift * (bs[i].toNat - 128)) bs s (i + 1)
      else .err ⟨i, .leb⟩
    else .err ⟨i, .eof⟩
  else .err ⟨i, .eof⟩
termination_by budget

/-- `BuN(N)`: unsigned LEB128 of at most `N` bits. -/
@[inline] def uN (N : Nat) : Parser Nat := uAux N 0 0

/-- Signed LEB128; mirrors `Silmaril.Wasm.Binary.SN`. -/
def sAux (budget shift : Nat) (acc : Int) : Parser Int := fun bs s i =>
  if hs : i < s then
    if h : i < bs.size then
      if bs[i].toNat < 64 then
        if bs[i].toNat < 2 ^ (budget - 1) then .ok (acc + 2 ^ shift * (bs[i].toNat : Int)) (i + 1)
        else .err ⟨i, .leb⟩
      else if bs[i].toNat < 128 then
        if (2 : Int) ^ 7 - 2 ^ (budget - 1) ≤ bs[i].toNat then
          .ok (acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7)) (i + 1)
        else .err ⟨i, .leb⟩
      else if 7 < budget then
        sAux (budget - 7) (shift + 7) (acc + 2 ^ shift * ((bs[i].toNat : Int) - 2 ^ 7)) bs s (i + 1)
      else .err ⟨i, .leb⟩
    else .err ⟨i, .eof⟩
  else .err ⟨i, .eof⟩
termination_by budget

/-- `BsN(N)`: signed LEB128 of at most `N` bits. -/
@[inline] def sN (N : Nat) : Parser Int := sAux N 0 0

/-- `u32`. -/
@[inline] def u32 : Parser Nat := uN 32

/-! ## Fixed-width little-endian numbers -/

/-- `n` more bytes, little-endian, the first weighted `2 ^ shift`. -/
def leAux : Nat → Nat → Nat → Parser Nat
  | 0, _, acc => fun _ _ i => .ok acc i
  | n + 1, shift, acc => fun bs s i =>
    if hs : i < s then
      if h : i < bs.size then leAux n (shift + 8) (acc + 2 ^ shift * bs[i].toNat) bs s (i + 1)
      else .err ⟨i, .eof⟩
    else .err ⟨i, .eof⟩

/-- `n` bytes as a little-endian natural number. -/
@[inline] def le (n : Nat) : Parser Nat := leAux n 0 0

/-- Fixed-width little-endian 32/64-bit words (e.g. float bit patterns). -/
@[inline] def le32 : Parser (BitVec 32) := Parser.map (BitVec.ofNat 32) (le 4)
@[inline] def le64 : Parser (BitVec 64) := Parser.map (BitVec.ofNat 64) (le 8)

/-- `n` more bytes, big-endian, after the value so far `acc`. -/
def beAux : Nat → Nat → Parser Nat
  | 0, acc => fun _ _ i => .ok acc i
  | n + 1, acc => fun bs s i =>
    if hs : i < s then
      if h : i < bs.size then beAux n (acc * 256 + bs[i].toNat) bs s (i + 1)
      else .err ⟨i, .eof⟩
    else .err ⟨i, .eof⟩

/-- `n` bytes as a big-endian natural number. -/
@[inline] def be (n : Nat) : Parser Nat := beAux n 0

/-! ## Vectors, names, options -/

/-- A `u32` element count, rejected if it exceeds the bytes left (every element
takes at least one byte, so nothing is attempted for absurd counts). -/
@[inline] def count : Parser Nat := fun bs s i =>
  match u32 bs s i with
  | .ok n j => if n ≤ s - j then .ok n j else .err ⟨i, .count n⟩
  | .err e => .err e

/-- `vec(p)`: a count, then that many `p`s. -/
@[inline] def vec {α : Type} (p : Parser α) : Parser (List α) := fun bs s i =>
  match count bs s i with
  | .ok n j => many n p bs s j
  | .err e => .err e

/-- A UTF-8 string of `n` bytes. -/
@[inline] def utf8 (n : Nat) : Parser String := fun bs s i =>
  if i + n ≤ s then
    match String.fromUTF8? (bs.extract i (i + n)) with
    | some str => .ok str (i + n)
    | none => .err ⟨i, .utf8⟩
  else .err ⟨i, .eof⟩

/-- `name`: a byte vector holding UTF-8. -/
@[inline] def name : Parser String := fun bs s i =>
  match count bs s i with
  | .ok n j => utf8 n bs s j
  | .err e => .err e

/-- `p?`: `0x00` (absent) or `0x01 p`. -/
@[inline] def opt {α : Type} (what : String) (p : Parser α) : Parser (Option α) := fun bs s i =>
  match byte bs s i with
  | .ok 0 j => .ok none j
  | .ok 1 j => Parser.map some p bs s j
  | .ok b _ => .err ⟨i, .tag what b⟩
  | .err e => .err e

/-- A tag byte `b`, then the parser `k b` (`none`: an unknown tag). -/
@[inline] def tagged {α : Type} (what : String) (k : UInt8 → Option (Parser α)) : Parser α :=
  fun bs s i =>
    match byte bs s i with
    | .ok b j =>
      match k b with
      | some p => p bs s j
      | none => .err ⟨i, .tag what b⟩
    | .err e => .err e

/-- One byte of lookahead: `p` if the next byte satisfies `pred`, else `q`. -/
@[inline] def choice {α : Type} (pred : UInt8 → Bool) (p q : Parser α) : Parser α :=
  fun bs s i =>
    if hs : i < s then
      if h : i < bs.size then (if pred bs[i] then p bs s i else q bs s i) else .err ⟨i, .eof⟩
    else .err ⟨i, .eof⟩

/-- Keep the results that `f` accepts. -/
@[inline] def filterMap {α β : Type} (what : String) (f : α → Option β) (p : Parser α) :
    Parser β := fun bs s i =>
  match p bs s i with
  | .ok a j =>
    match f a with
    | some b => .ok b j
    | none => .err ⟨i, .other what⟩
  | .err e => .err e

/-! ## Running -/

/-- Run `p` on all of `bs`, which it must consume. -/
@[inline] def runAll {α : Type} (p : Parser α) (bs : ByteArray) : Except Error α :=
  match p bs bs.size 0 with
  | .ok a j => if j = bs.size then .ok a else .error ⟨j, .trailing⟩
  | .err e => .error e

/-! ## Specifications -/

/-- Byte lists, the terminals of grammars (silmaril's `Wasm.Binary.Bytes`). -/
abbrev Bytes := List UInt8

/-- The bytes of `bs` from `i` to `j`. -/
abbrev seg (bs : ByteArray) (i j : Nat) : Bytes := bs.data.toList.extract i j

/-- `p` is sound for the grammar `G`: started inside a window that lies inside
the input, a successful run moves forward, stays in the window, and `G`
relates the consumed bytes to the result. -/
def Sound {α : Type} (G : Bytes → α → Prop) (p : Parser α) : Prop :=
  ∀ ⦃bs : ByteArray⦄ ⦃st i : Nat⦄ ⦃a : α⦄ ⦃j : Nat⦄, i ≤ st → st ≤ bs.size →
    p bs st i = .ok a j → i ≤ j ∧ j ≤ st ∧ G (seg bs i j) a

/-- `p` is complete for `G`: if its window begins with `l` and `G l a`, it
answers `a` after exactly `l`. Implies that `G` is unambiguous on prefixes. -/
def Complete {α : Type} (G : Bytes → α → Prop) (p : Parser α) : Prop :=
  ∀ ⦃l : Bytes⦄ ⦃a : α⦄ ⦃bs : ByteArray⦄ ⦃st i : Nat⦄, G l a →
    i + l.length ≤ st → st ≤ bs.size → seg bs i (i + l.length) = l →
    p bs st i = .ok a (i + l.length)

/-- `G` never relates the empty string (what `vec` and `untilEnd` need). -/
def NonEmpty {α : Type} (G : Bytes → α → Prop) : Prop := ∀ ⦃l a⦄, G l a → l ≠ []

/-! ## Grammar combinators (relations) -/

namespace Spec

/-- Concatenation, with the second part depending on the first value. -/
def bind {α β : Type} (G : Bytes → α → Prop) (H : α → Bytes → β → Prop) : Bytes → β → Prop :=
  fun l b => ∃ l₁ l₂ a, l = l₁ ++ l₂ ∧ G l₁ a ∧ H a l₂ b

/-- The image of a grammar. -/
def map {α β : Type} (f : α → β) (G : Bytes → α → Prop) : Bytes → β → Prop :=
  fun l b => ∃ a, G l a ∧ f a = b

/-- Exactly the empty string. -/
def pure {α : Type} (a : α) : Bytes → α → Prop := fun l b => l = [] ∧ b = a

/-- `n` items. -/
def many {α : Type} (G : Bytes → α → Prop) (n : Nat) : Bytes → List α → Prop :=
  fun l xs => Silmaril.Wasm.Binary.Seq G l xs ∧ xs.length = n

/-- An unsigned/signed LEB-free count prefix, as in `Vec`. -/
abbrev vec {α : Type} (G : Bytes → α → Prop) : Bytes → List α → Prop :=
  Silmaril.Wasm.Binary.Vec G

/-- `G`, with its bytes exactly `n` long. -/
def sized {α : Type} (n : Nat) (G : Bytes → α → Prop) : Bytes → α → Prop :=
  fun l a => l.length = n ∧ G l a

/-- `0x00` or `0x01` followed by `G`. -/
def opt {α : Type} (G : Bytes → α → Prop) : Bytes → Option α → Prop
  | l, none => l = [0x00]
  | l, some a => ∃ l', l = 0x01 :: l' ∧ G l' a

/-- Little-endian bytes of length `n`. -/
def le (n : Nat) : Bytes → Nat → Prop :=
  fun l v => l.length = n ∧ v = Silmaril.Wasm.Binary.littleEndian l

/-- The big-endian value of a byte string. -/
def bigEndian (l : Bytes) : Nat := l.foldl (fun a b => a * 256 + b.toNat) 0

/-- Big-endian bytes of length `n`. -/
def be (n : Nat) : Bytes → Nat → Prop := fun l v => l.length = n ∧ v = bigEndian l

end Spec

/-- One byte: `Silmaril.Wasm.Binary.Byte`. -/
def Spec.byte : Bytes → UInt8 → Prop := fun l b => l = [b]

/-- `n` raw bytes, by span. -/
def Spec.span (n : Nat) : Bytes → Nat × Nat → Prop := fun l _ => l.length = n

/-- The canonical name encoding: a `u32` byte count, then the UTF-8 bytes. -/
def Spec.name : Bytes → String → Prop :=
  fun l s => ∃ nb, l = nb ++ s.toUTF8.data.toList ∧ Silmaril.Wasm.Binary.U32 nb s.toUTF8.size

/-- A tag byte `b`, then bytes in the grammar `K b`. -/
def Spec.tagged {α : Type} (K : UInt8 → Option (Bytes → α → Prop)) : Bytes → α → Prop :=
  fun l a => ∃ b l' G, l = b :: l' ∧ K b = some G ∧ G l' a

/-- A parser that is complete when its window ends exactly after the encoding. -/
def CompleteAtEnd {α : Type} (G : Bytes → α → Prop) (p : Parser α) : Prop :=
  ∀ ⦃l : Bytes⦄ ⦃a : α⦄ ⦃bs : ByteArray⦄ ⦃i : Nat⦄, G l a →
    i + l.length ≤ bs.size → seg bs i (i + l.length) = l → p bs (i + l.length) i = .ok a (i + l.length)

/-- Every encoding starts with a byte satisfying `pred`. -/
def StartsWith {α : Type} (pred : UInt8 → Prop) (G : Bytes → α → Prop) : Prop :=
  ∀ ⦃l a⦄, G l a → ∃ b l', l = b :: l' ∧ pred b

/-! ## Grammars

A `Grammar` pairs a parser with the relation it is meant to implement; the combinators below
build both at once. `Grammar.Lawful g` states that `g.parse` is sound and complete for `g.G`.
Its instances, one per combinator, are proved in `Silmaril/Proofs/Wasm/ByteParse/` and exported by
`Silmaril.Wasm.ByteParse.Thms`, so a grammar built from the combinators is lawful by instance
search (or, through `tagged`, by `Grammar.Lawful.tagged`). Executables import this module only:
they run the parsers and carry no proofs. -/

/-- A parser with the grammar it implements. -/
structure Grammar (α : Type) where
  /-- The relation between consumed bytes and values. -/
  G : Bytes → α → Prop
  /-- The executable parser. -/
  parse : Parser α

/-- The parser of `g` is sound and complete for its grammar. -/
class Grammar.Lawful {α : Type} (g : Grammar α) : Prop where
  sound : Sound g.G g.parse
  complete : Complete g.G g.parse

/-- A parser with its grammar, meant to be complete up to the end of its window. -/
structure GrammarE (α : Type) where
  /-- The relation between consumed bytes and values. -/
  G : Bytes → α → Prop
  /-- The executable parser. -/
  parse : Parser α

/-- The parser of `g` is sound, and complete when its window ends after the encoding. -/
class GrammarE.Lawful {α : Type} (g : GrammarE α) : Prop where
  sound : Sound g.G g.parse
  complete : CompleteAtEnd g.G g.parse

namespace Grammar

variable {α β : Type}

@[inline] def pure (a : α) : Grammar α := ⟨Spec.pure a, Pure.pure a⟩

@[inline] def bind (g : Grammar α) (h : α → Grammar β) : Grammar β :=
  ⟨Spec.bind g.G (fun a => (h a).G), g.parse >>= fun a => (h a).parse⟩

@[inline] def map (f : α → β) (g : Grammar α) : Grammar β :=
  ⟨Spec.map f g.G, Parser.map f g.parse⟩

@[inline] def byte : Grammar UInt8 := ⟨Spec.byte, ByteParse.byte⟩

@[inline] def expect (what : String) (b : UInt8) : Grammar Unit :=
  ⟨fun l (_ : Unit) => l = [b], ByteParse.expect what b⟩

@[inline] def bytes (n : Nat) : Grammar ByteArray :=
  ⟨fun l (b : ByteArray) => l = b.data.toList ∧ l.length = n, ByteParse.bytes n⟩

@[inline] def sized (n : Nat) (g : Grammar α) : Grammar α :=
  ⟨Spec.sized n g.G, ByteParse.sized n g.parse⟩

@[inline] def opt (what : String) (g : Grammar α) : Grammar (Option α) :=
  ⟨Spec.opt g.G, ByteParse.opt what g.parse⟩

/-- Pairs. -/
@[inline] def seq (g : Grammar α) (h : Grammar β) : Grammar (α × β) :=
  g.bind fun a => h.map fun b => (a, b)

/-- Tagged choice between grammars. -/
@[inline] def tagged (what : String) (k : UInt8 → Option (Grammar α)) : Grammar α :=
  ⟨Spec.tagged fun b => (k b).map Grammar.G, ByteParse.tagged what fun b => (k b).map Grammar.parse⟩

/-- `uN N`. -/
@[inline] def uN (N : Nat) : Grammar Nat := ⟨Silmaril.Wasm.Binary.UN N, ByteParse.uN N⟩

/-- `u32`. -/
@[inline] def u32 : Grammar Nat := uN 32

/-- `sN N`. -/
@[inline] def sN (N : Nat) : Grammar Int := ⟨Silmaril.Wasm.Binary.SN N, ByteParse.sN N⟩

/-- `n` little-endian bytes. -/
@[inline] def le (n : Nat) : Grammar Nat := ⟨Spec.le n, ByteParse.le n⟩

/-- `n` big-endian bytes. -/
@[inline] def be (n : Nat) : Grammar Nat := ⟨Spec.be n, ByteParse.be n⟩

/-- `name`. -/
@[inline] def name : Grammar String := ⟨Spec.name, ByteParse.name⟩

/-- `vec(g)` for a grammar that never accepts the empty string (`hne`, which the parser does
not use: it is the condition under which `vec` is complete). -/
@[inline] def vec (g : Grammar α) (_hne : NonEmpty g.G) : Grammar (List α) :=
  ⟨Spec.vec g.G, ByteParse.vec g.parse⟩

/-- `n` repetitions. -/
@[inline] def many (n : Nat) (g : Grammar α) : Grammar (List α) :=
  ⟨Spec.many g.G n, ByteParse.many n g.parse⟩

/-- `size:u32` then `g*` filling exactly `size` bytes (`hne` as for `vec`). -/
@[inline] def sizedItems (g : Grammar α) (_hne : NonEmpty g.G) : Grammar (List α) :=
  u32.bind fun n => ⟨Spec.sized n (Silmaril.Wasm.Binary.Seq g.G), ByteParse.sized n (ByteParse.untilEnd g.parse)⟩

/-- `size:u32` then `g` filling exactly `size` bytes. -/
@[inline] def sizedBy (g : Grammar α) : Grammar α := u32.bind fun n => sized n g

/-- One byte of lookahead between two grammars (`hg`, `hh`: the conditions under which the
choice is complete; the parser does not use them). -/
@[inline] def choice (pred : UInt8 → Bool) (g h : Grammar α)
    (_hg : StartsWith (fun b => pred b = true) g.G) (_hh : StartsWith (fun b => pred b = false) h.G) :
    Grammar α :=
  ⟨fun l a => g.G l a ∨ h.G l a, ByteParse.choice pred g.parse h.parse⟩

/-- Partial post-processing. -/
@[inline] def filterMap (what : String) (f : α → Option β) (g : Grammar α) : Grammar β :=
  ⟨fun l b => ∃ a, g.G l a ∧ f a = some b, ByteParse.filterMap what f g.parse⟩

/-- `g`, then `h`, keeping the result of `h`. -/
@[inline] def then_ (g : Grammar Unit) (h : Grammar α) : Grammar α := g.bind fun _ => h

/-- Exactly the bytes `l`. -/
def lit : List UInt8 → Grammar Unit
  | [] => pure ()
  | b :: bs => (expect "literal" b).then_ (lit bs)

/-- The failing grammar (recursion bottom). -/
@[inline] def fail : Grammar α := ⟨fun _ _ => False, ByteParse.fail .depth⟩

end Grammar

namespace GrammarE

variable {α β : Type}

@[inline] def ofGrammar (g : Grammar α) : GrammarE α := ⟨g.G, g.parse⟩

/-- The rest of the window. -/
@[inline] def rest : GrammarE ByteArray := ⟨fun l (b : ByteArray) => l = b.data.toList, ByteParse.rest⟩

@[inline] def map (f : α → β) (g : GrammarE α) : GrammarE β :=
  ⟨Spec.map f g.G, Parser.map f g.parse⟩

/-- A grammar, then one running to the end. -/
@[inline] def after (g : Grammar α) (h : α → GrammarE β) : GrammarE β :=
  ⟨Spec.bind g.G (fun a => (h a).G), g.parse >>= fun a => (h a).parse⟩

/-- Items up to the end of the window (`hne` as for `Grammar.vec`). -/
@[inline] def items (g : Grammar α) (_hne : NonEmpty g.G) : GrammarE (List α) :=
  ⟨Silmaril.Wasm.Binary.Seq g.G, ByteParse.untilEnd g.parse⟩

/-- Exactly `n` bytes. -/
@[inline] def sized (n : Nat) (g : GrammarE α) : Grammar α :=
  ⟨Spec.sized n g.G, ByteParse.sized n g.parse⟩

/-- `size:u32` then `g` in exactly `size` bytes. -/
@[inline] def sizedBy (g : GrammarE α) : Grammar α := Grammar.u32.bind fun n => sized n g

end GrammarE

/-! ### Non-emptiness

Grammar-level facts (no parser involved) that the arguments of `vec`, `items` and `sizedItems`
need. -/

namespace Grammar

variable {α β : Type}

theorem tagged_nonEmpty (what : String) (k : UInt8 → Option (Grammar α)) :
    NonEmpty (tagged what k).G := by
  rintro l a ⟨b, l', G, rfl, -, -⟩; simp

theorem u32_nonEmpty : NonEmpty u32.G := fun _ _ h e => by subst e; exact Silmaril.Wasm.Binary.UN.ne_nil h

theorem sN_nonEmpty (N : Nat) : NonEmpty (sN N).G := fun _ _ h e => by subst e; cases h

theorem name_nonEmpty : NonEmpty name.G := by
  rintro l s ⟨nb, rfl, hu⟩ e
  simp only [List.append_eq_nil_iff] at e
  exact Silmaril.Wasm.Binary.UN.ne_nil (e.1 ▸ hu)

theorem byte_nonEmpty : NonEmpty byte.G := fun _ _ h e => by subst e; cases h

theorem expect_nonEmpty (what : String) (b : UInt8) : NonEmpty (expect what b).G :=
  fun _ _ h e => by subst e; cases h

theorem vec_nonEmpty {g : Grammar α} {hne : NonEmpty g.G} : NonEmpty (vec g hne).G := by
  rintro l xs ⟨hn, -⟩ e
  simp only [List.append_eq_nil_iff] at e
  exact Silmaril.Wasm.Binary.UN.ne_nil (e.1 ▸ hn)

theorem bind_nonEmpty {g : Grammar α} {h : α → Grammar β} (hg : NonEmpty g.G) :
    NonEmpty (g.bind h).G := by
  rintro l b ⟨l₁, l₂, a, rfl, h1, -⟩ e
  simp only [List.append_eq_nil_iff] at e
  exact hg h1 e.1

theorem seq_nonEmpty {g : Grammar α} {h : Grammar β} (hg : NonEmpty g.G) :
    NonEmpty (g.seq h).G := bind_nonEmpty hg

theorem then_nonEmpty {g : Grammar Unit} {h : Grammar α} (hg : NonEmpty g.G) :
    NonEmpty (g.then_ h).G := bind_nonEmpty hg

theorem map_nonEmpty {f : α → β} {g : Grammar α} (hg : NonEmpty g.G) : NonEmpty (g.map f).G := by
  rintro l b ⟨a, h, -⟩; exact hg h

theorem filterMap_nonEmpty {what : String} {f : α → Option β} {g : Grammar α}
    (hg : NonEmpty g.G) : NonEmpty (g.filterMap what f).G := by
  rintro l b ⟨a, h, -⟩; exact hg h

theorem choice_nonEmpty {pred : UInt8 → Bool} {g h : Grammar α} {hg hh} :
    NonEmpty (choice pred g h hg hh).G := by
  rintro l a (H | H) e <;> subst e
  · obtain ⟨b, l', e, -⟩ := hg H; cases e
  · obtain ⟨b, l', e, -⟩ := hh H; cases e

theorem sized_nonEmpty_of {n : Nat} {g : Grammar α} (hn : 0 < n) : NonEmpty (sized n g).G := by
  rintro l a ⟨hl, -⟩ e; subst e; simp at hl; omega

theorem uN_nonEmpty (N : Nat) : NonEmpty (uN N).G := fun _ _ h e => by
  subst e; exact Silmaril.Wasm.Binary.UN.ne_nil h

theorem sizedBy_nonEmpty {g : Grammar α} : NonEmpty (sizedBy g).G := bind_nonEmpty u32_nonEmpty

theorem GrammarE.sizedBy_nonEmpty {g : GrammarE α} : NonEmpty (GrammarE.sizedBy g).G :=
  bind_nonEmpty u32_nonEmpty

theorem opt_nonEmpty {what : String} {g : Grammar α} : NonEmpty (opt what g).G := by
  rintro l o h e; subst e
  cases o with
  | none => cases h
  | some a => obtain ⟨l', e, -⟩ := h; cases e

end Grammar

/-! ## Encoders

Specification-level encoders into byte lists. They fail (`none`) on values the
format cannot represent (numbers or lengths of `2 ^ 32` or more). Their laws,
`G (enc a) a`, are in `Silmaril.Wasm.ByteParse.Thms` and give round trips. -/

namespace Enc

/-- Minimal unsigned LEB128 of a `u32`. -/
def u32 (n : Nat) : Option Bytes :=
  if n < 2 ^ 32 then some (Silmaril.Wasm.Binaryen.Exe.encU n) else none

/-- Minimal signed LEB128 of an `sN`. -/
def sN (N : Nat) (i : Int) : Option Bytes :=
  if 0 < N ∧ -(2 ^ (N - 1) : Int) ≤ i ∧ i < 2 ^ (N - 1) then
    some (Silmaril.Wasm.Binaryen.Exe.encS i) else none

/-- A name: its UTF-8 byte count, then the bytes. -/
def name (s : String) : Option Bytes := do
  let n ← u32 s.toUTF8.size
  pure (n ++ s.toUTF8.data.toList)

/-- Concatenated encodings. -/
def list {α : Type} (f : α → Option Bytes) : List α → Option Bytes
  | [] => some []
  | x :: xs => do
    let b ← f x
    let bs ← list f xs
    pure (b ++ bs)

/-- `vec`: a count, then the elements. -/
def vec {α : Type} (f : α → Option Bytes) (xs : List α) : Option Bytes := do
  let n ← u32 xs.length
  let b ← list f xs
  pure (n ++ b)

/-- A size prefix. -/
def sized (b : Bytes) : Option Bytes := do
  let n ← u32 b.length
  pure (n ++ b)

/-- `0x00` or `0x01 x`. -/
def opt {α : Type} (f : α → Option Bytes) : Option α → Option Bytes
  | none => some [0x00]
  | some a => (0x01 :: ·) <$> f a

/-- `n` bytes, little-endian. -/
def le : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, v => UInt8.ofNat (v % 256) :: le n (v / 256)

/-- Run an encoder into a `ByteArray`. -/
def toBytes (b : Option Bytes) : Option ByteArray := b.map fun l => ⟨l.toArray⟩

end Enc

end Silmaril.Wasm.ByteParse
