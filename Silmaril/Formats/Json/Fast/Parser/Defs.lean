module

public import Silmaril.Formats.Json.Fast.Defs

/-! A direct reader of the scalar-Unicode RFC 8259 profile. It builds arrays and ordered
members without an intermediate token list or CST. Container width uses a tail-recursive
loop; nested calls consume the explicit depth budget. -/

@[expose] public section
namespace Silmaril.Formats.Json.Fast

inductive ErrorKind where
  | invalidUtf8 | syntax | trailingInput | unpairedSurrogate | depthLimit | numberLimit
  deriving DecidableEq, Repr

structure Error where
  /-- UTF-8 byte offset; invalid UTF-8 reports 0 (no decoded cursor). -/
  offset : Nat
  kind : ErrorKind
  deriving DecidableEq, Repr

structure Limits where
  /-- Maximum number of enclosing arrays/objects, including the root container. -/
  depth : Nat := 128
  /-- Maximum number lexeme length, including sign, point, and exponent. -/
  numberBytes : Nat := 4096

def defaultLimits : Limits := {}

namespace Parser

structure Pos where
  byteIdx : Nat
  rest : List Char

def Pos.get (pos : Pos) : Char := pos.rest.headD (Char.ofNat 0)

def Pos.next (pos : Pos) : Pos :=
  match pos.rest with
  | [] => pos
  | char :: rest => ⟨pos.byteIdx + char.utf8Size, rest⟩

def Pos.atEnd (pos : Pos) : Bool := pos.rest.isEmpty

variable {α : Type}

def fail (pos : Pos) (kind : ErrorKind := .syntax) : Except Error α :=
  .error ⟨pos.byteIdx, kind⟩

def whitespace (offset : Nat) : List Char → Pos
  | [] => ⟨offset, []⟩
  | input@(char :: rest) =>
    if JsonWire.Internal.white .rfc8259 char then whitespace (offset + char.utf8Size) rest
    else ⟨offset, input⟩

def skip (pos : Pos) : Pos := whitespace pos.byteIdx pos.rest

def expect (pos : Pos) (char : Char) : Except Error Pos :=
  if !pos.atEnd && pos.get == char then .ok pos.next else fail pos

def hex : Nat → Pos → Nat → Except Error (Nat × Pos)
  | 0, pos, acc => .ok (acc, pos)
  | count + 1, pos, acc =>
    if pos.atEnd then fail pos else
    match JsonWire.Internal.hex? pos.get with
    | none => fail pos
    | some digit => hex count pos.next (16 * acc + digit)

def unicodeEscape (start : Pos) : Except Error (Char × Pos) := do
  let (unit, pos) ← hex 4 start 0
  if 0xD800 ≤ unit && unit ≤ 0xDBFF then
    if pos.get != '\\' || pos.next.get != 'u' then fail start .unpairedSurrogate
    else
      let (low, stop) ← hex 4 pos.next.next 0
      if 0xDC00 ≤ low && low ≤ 0xDFFF then
        return (Char.ofNat (0x10000 + (unit - 0xD800) * 1024 + low - 0xDC00), stop)
      else fail start .unpairedSurrogate
  else if 0xDC00 ≤ unit && unit ≤ 0xDFFF then fail start .unpairedSurrogate
  else return (Char.ofNat unit, pos)

def escaped (pos : Pos) : Except Error (Char × Pos) :=
  let next := pos.next
  match pos.get with
  | 'u' => unicodeEscape next
  | '"' => .ok ('"', next)
  | '\\' => .ok ('\\', next)
  | '/' => .ok ('/', next)
  | 'b' => .ok (Char.ofNat 8, next)
  | 'f' => .ok (Char.ofNat 12, next)
  | 'n' => .ok ('\n', next)
  | 'r' => .ok ('\r', next)
  | 't' => .ok ('\t', next)
  | _ => fail pos

def stringLoop : Nat → Pos → List Char → Except Error (String × Pos)
  | 0, pos, _ => fail pos
  | fuel + 1, pos, acc =>
    if pos.atEnd then fail pos else
    let char := pos.get
    let next := pos.next
    if char == '"' then .ok (String.ofList acc.reverse, next)
    else if char == '\\' then
      match escaped next with
      | .ok (decoded, stop) => stringLoop fuel stop (decoded :: acc)
      | .error err => .error err
    else if char.toNat < 32 then fail pos
    else stringLoop fuel next (char :: acc)

def quoted (size : Nat) (pos : Pos) : Except Error (String × Pos) := do
  let start ← expect pos '"'
  stringLoop (size - start.byteIdx + 1) start []

def numberChar (char : Char) : Bool :=
  char.isDigit || char == '-' || char == '+' || char == '.' || char == 'e' || char == 'E'

def numberLoop (start : Pos) : Nat → Pos → List Char → Except Error (Value × Pos)
  | fuel, pos, acc =>
    let char := pos.get
    if !numberChar char then
      match JsonWire.Internal.decimal? .rfc8259 acc.reverse with
      | some (.finite decimal) => .ok (.number decimal, pos)
      | _ => fail start
    else match fuel with
      | 0 => fail pos .numberLimit
      | fuel + 1 => numberLoop start fuel pos.next (char :: acc)

def literal : List Char → Pos → Except Error Pos
  | [], pos => .ok pos
  | char :: rest, pos => (expect pos char).bind (literal rest)

@[specialize] def more (close : Char) (item : Pos → Except Error (α × Pos)) :
    Nat → Pos → Array α → Except Error (Array α × Pos)
  | 0, pos, _ => fail pos
  | fuel + 1, pos, items =>
    match item (skip pos) with
    | .error err => .error err
    | .ok (value, stop) =>
      let stop := skip stop
      let char := stop.get
      if char == close then .ok (items.push value, stop.next)
      else if char == ',' then more close item fuel stop.next (items.push value)
      else fail stop

@[specialize] def series (size : Nat) (close : Char) (item : Pos → Except Error (α × Pos))
    (pos : Pos) : Except Error (Array α × Pos) :=
  let start := skip pos
  if start.get == close then .ok (#[], start.next)
  else more close item (size - start.byteIdx + 1) start #[]

def member (size : Nat) (value : Pos → Except Error (Value × Pos)) (pos : Pos) :
    Except Error ((String × Value) × Pos) := do
  let (key, stop) ← quoted size pos
  let start ← expect (skip stop) ':'
  let (child, stop) ← value start
  return ((key, child), stop)

def value (size : Nat) (numberBytes : Nat) : Nat → Pos → Except Error (Value × Pos)
  | depth, pos => do
    let pos := skip pos
    match pos.get with
    | '[' =>
      match depth with
      | 0 => fail pos .depthLimit
      | remaining + 1 =>
        let (items, stop) ← series size ']' (value size numberBytes remaining) pos.next
        return (.ofArray items, stop)
    | '{' =>
      match depth with
      | 0 => fail pos .depthLimit
      | remaining + 1 =>
        let (entries, stop) ← series size '}' (member size (value size numberBytes remaining)) pos.next
        return (.ofObject entries, stop)
    | '"' =>
      let (text, stop) ← quoted size pos
      return (.string text, stop)
    | 'n' => return (.null, ← literal ['n', 'u', 'l', 'l'] pos)
    | 't' => return (.bool true, ← literal ['t', 'r', 'u', 'e'] pos)
    | 'f' => return (.bool false, ← literal ['f', 'a', 'l', 's', 'e'] pos)
    | char =>
      if char == '-' || char.isDigit then numberLoop pos numberBytes pos [] else fail pos

end Parser

/-- Parse one complete scalar-Unicode JSON value; no BOM, comments or trailing commas. -/
def parseText (text : String) (limits : Limits := defaultLimits) : Except Error Value := do
  let (value, stop) ← Parser.value text.utf8ByteSize limits.numberBytes limits.depth ⟨0, text.toList⟩
  let stop := Parser.skip stop
  if stop.atEnd then return value else Parser.fail stop .trailingInput

def parseBytes (bytes : ByteArray) (limits : Limits := defaultLimits) : Except Error Value :=
  match String.fromUTF8? bytes with
  | none => .error ⟨0, .invalidUtf8⟩
  | some text => parseText text limits

def load (path : System.FilePath) (limits : Limits := defaultLimits) : IO (Except Error Value) := do
  return parseBytes (← IO.FS.readBinFile path) limits

/-- A claim about this exact byte sequence, not about the file system or `JsonWire`. -/
def SourceMatches (bytes : ByteArray) (result : Except Error Value) : Prop :=
  parseBytes bytes = result

end Silmaril.Formats.Json.Fast
