module

public import Std.Data.HashMap

/-! # A linear reader and writer for the tagged S-expression dialect

`docs/projects/cerberus.md` specifies the dialect of the Cerberus documents, and
`Silmaril.TaggedCodec` gives it codecs with round-trip laws. Its trees store children
as functions `Fin n → Tree` built from lists, so a node with `n` children costs
`O(n²)` to build and to print; a Cabs document has nodes with 10⁵ children (the
external declarations of `limits-externdecl.c`) and 2·10⁷ children (the lexemes of
the string literal of `pr46534.c`). This module is the executable path:

* `Sx` is the same tree with `Array` children;
* `read` parses the bytes of a document into an `Sx` in one pass, with an explicit
  stack, so nesting depth costs heap, not native stack;
* `Out` is the output buffer of the emitters of `Silmaril.Cerberus.Cabs.Codec`, which
  append the canonical layout (single spaces, the five string escapes) directly.

The reader accepts any layout of spaces and newlines between items, and it does not
check that integers are canonical. Canonicity is decided by printing again and
comparing bytes (`Codec.parseCabsDocument`).
-/

@[expose] public section

namespace Silmaril.Cerberus.Cabs.Wire

/-- A tagged S-expression: a bare atom (an integer), a quoted atom (the text of
`($str "…")` after unescaping), or a tagged node `(tag c₁ … cₙ)`. -/
inductive Sx where
  | atom (text : String)
  | str (text : String)
  | node (tag : String) (children : Array Sx)
  deriving Inhabited, Repr

/-! ## Reading -/

def isDelimiter (c : UInt8) : Bool :=
  c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '('.toUInt8 || c == ')'.toUInt8 || c == '"'.toUInt8

/-- The end of the bare token that starts at `i`. -/
def scanToken (b : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 => if i < b.size && !isDelimiter b[i]! then scanToken b (i + 1) fuel else i

/-- Unescape the quoted atom whose text starts at `i`, just after the opening quote.
Returns the bytes and the index after the closing quote. -/
def scanQuoted (b : ByteArray) (i : Nat) (acc : ByteArray) : Nat → Except String (ByteArray × Nat)
  | 0 => throw "unterminated string"
  | fuel + 1 =>
    if h : i < b.size then
      let c := b[i]
      if c == '"'.toUInt8 then return (acc, i + 1)
      else if c == '\\'.toUInt8 then
        if i + 1 < b.size then
          let e := b[i + 1]!
          let u := if e == 'n'.toUInt8 then some '\n'.toUInt8
            else if e == 'r'.toUInt8 then some '\r'.toUInt8
            else if e == 't'.toUInt8 then some '\t'.toUInt8
            else if e == '"'.toUInt8 then some '"'.toUInt8
            else if e == '\\'.toUInt8 then some '\\'.toUInt8
            else none
          match u with
          | some u => scanQuoted b (i + 2) (acc.push u) fuel
          | none => throw s!"invalid escape at byte {i}"
        else throw "unterminated string"
      else scanQuoted b (i + 1) (acc.push c) fuel
    else throw "unterminated string"

/-- An open node: its tag and the children read so far. -/
abbrev Frame := String × Array Sx

/-- Tags repeat; each distinct spelling is kept once. -/
abbrev Interner := Std.HashMap String String

def intern (tags : Interner) (s : String) : String × Interner :=
  match tags[s]? with
  | some t => (t, tags)
  | none => (s, tags.insert s s)

def addChild (stack : Array Frame) (x : Sx) : Array Frame :=
  stack.modify (stack.size - 1) fun (tag, cs) => (tag, cs.push x)

def slice (b : ByteArray) (i j : Nat) : Except String String :=
  match String.fromUTF8? (b.extract i j) with
  | some s => return s
  | none => throw s!"invalid UTF-8 at byte {i}"

/-- The rest of the input after the root node: only spaces and newlines. -/
def onlyLayout (b : ByteArray) (i : Nat) : Bool :=
  (b.extract i b.size).toList.all fun c => c == ' '.toUInt8 || c == '\n'.toUInt8

/-- One step per item; every step consumes at least one byte, so `fuel = size + 1` suffices. -/
def readLoop (b : ByteArray) (i : Nat) (stack : Array Frame) (tags : Interner) :
    Nat → Except String Sx
  | 0 => throw "reader out of fuel"
  | fuel + 1 =>
    if h : i < b.size then
      let c := b[i]
      if c == ' '.toUInt8 || c == '\n'.toUInt8 then readLoop b (i + 1) stack tags fuel
      else if c == '('.toUInt8 then do
        let j := scanToken b (i + 1) b.size
        if j == i + 1 then throw s!"missing tag at byte {i}"
        let (tag, tags) := intern tags (← slice b (i + 1) j)
        readLoop b j (stack.push (tag, #[])) tags fuel
      else if c == ')'.toUInt8 then
        match stack.back? with
        | none => throw s!"unbalanced ')' at byte {i}"
        | some (tag, cs) =>
          let rest := stack.pop
          let x := Sx.node tag cs
          if rest.isEmpty then
            if onlyLayout b (i + 1) then return x else throw s!"trailing input at byte {i + 1}"
          else readLoop b (i + 1) (addChild rest x) tags fuel
      else if stack.isEmpty then throw s!"expected '(' at byte {i}"
      else if c == '"'.toUInt8 then do
        let (bytes, j) ← scanQuoted b (i + 1) .empty b.size
        let some s := String.fromUTF8? bytes | throw s!"invalid UTF-8 in the string at byte {i}"
        readLoop b j (addChild stack (.str s)) tags fuel
      else do
        let j := scanToken b i b.size
        readLoop b j (addChild stack (.atom (← slice b i j))) tags fuel
    else throw "unexpected end of input"

/-- Read one document: a single tagged node, then only layout. -/
def read (b : ByteArray) : Except String Sx := readLoop b 0 #[] {} (b.size + 1)

/-! ## Writing -/

/-- The output buffer: canonical text is ASCII outside `$str` payloads, and those are
valid UTF-8, so the buffer is a `String` and appending is amortized linear. -/
abbrev Out := String

/-- Open a node: `(tag`. -/
@[inline] def open_ (tag : String) (o : Out) : Out := o.push '(' ++ tag

/-- One child, after its separating space. -/
@[inline] def arg (child : Out → Out) (o : Out) : Out := child (o.push ' ')

/-- Close a node. -/
@[inline] def close (o : Out) : Out := o.push ')'

/-- A bare integer atom. -/
@[inline] def emitInt (n : Int) (o : Out) : Out := o ++ toString n

@[inline] def emitNat (n : Nat) (o : Out) : Out := o ++ toString n

/-- One character of a `$str` payload: `"`, `\`, newline, carriage return and tab are escaped. -/
@[inline] def escapeChar (o : Out) (c : Char) : Out :=
  if c == '"' then o ++ "\\\""
  else if c == '\\' then o ++ "\\\\"
  else if c == '\n' then o ++ "\\n"
  else if c == '\r' then o ++ "\\r"
  else if c == '\t' then o ++ "\\t"
  else o.push c

/-- A quoted atom. -/
@[inline] def quoted (s : String) (o : Out) : Out := (s.foldl escapeChar (o.push '"')).push '"'

/-- `($str "…")`. -/
@[inline] def emitStr (s : String) (o : Out) : Out := o |> open_ "$str" |> arg (quoted s) |> close

@[inline] def emitBool (b : Bool) (o : Out) : Out := o ++ if b then "($true)" else "($false)"

@[inline] def emitOption {α : Type} (e : α → Out → Out) : Option α → Out → Out
  | none, o => o ++ "($none)"
  | some x, o => o |> open_ "$some" |> arg (e x) |> close

@[inline] def emitList {α : Type} (e : α → Out → Out) (xs : List α) (o : Out) : Out :=
  close (xs.foldl (fun o x => arg (e x) o) (open_ "$list" o))

@[inline] def emitTuple2 {α β : Type} (ea : α → Out → Out) (eb : β → Out → Out) (p : α × β) (o : Out) : Out :=
  o |> open_ "$tuple" |> arg (ea p.1) |> arg (eb p.2) |> close

/-! ## Decoding helpers -/

/-- A short rendering of a node for error messages. -/
def Sx.head : Sx → String
  | .atom s => s
  | .str s => s!"\"{s.take 40}\""
  | .node t cs => s!"({t} …{cs.size})"

def mismatch {α : Type} (expected : String) (t : Sx) : Except String α :=
  throw s!"expected {expected}, found {t.head}"

def decodeInt : Sx → Except String Int
  | .atom s => match s.toInt? with
    | some n => return n
    | none => throw s!"expected an integer, found {s}"
  | t => mismatch "an integer" t

def decodeNat : Sx → Except String Nat
  | .atom s => match s.toNat? with
    | some n => return n
    | none => throw s!"expected a natural number, found {s}"
  | t => mismatch "a natural number" t

def decodeStr : Sx → Except String String
  | .node "$str" #[.str s] => return s
  | t => mismatch "$str" t

def decodeBool : Sx → Except String Bool
  | .node "$true" #[] => return true
  | .node "$false" #[] => return false
  | t => mismatch "a boolean" t

@[inline] def decodeOption {α : Type} (d : Sx → Except String α) : Sx → Except String (Option α)
  | .node "$none" #[] => return none
  | .node "$some" #[x] => some <$> d x
  | t => mismatch "an option" t

@[inline] def decodeList {α : Type} (d : Sx → Except String α) : Sx → Except String (List α)
  | .node "$list" xs => return (← xs.mapM d).toList
  | t => mismatch "a list" t

@[inline] def decodeTuple2 {α β : Type} (da : Sx → Except String α) (db : Sx → Except String β) :
    Sx → Except String (α × β)
  | .node "$tuple" #[a, b] => return (← da a, ← db b)
  | t => mismatch "a pair" t

end Silmaril.Cerberus.Cabs.Wire
