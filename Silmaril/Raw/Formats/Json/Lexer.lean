module
public import Silmaril.Formats.Json.Defs
public import Silmaril.Raw.Formats.Json.Unicode
/-! Total JSON/JSON5 lexer. Offsets count UTF-8 bytes, not characters.
The RFC number grammar and escape handling adapt Silmaril's RfcParser;
strings here retain UTF-16 code units instead of discarding lone surrogates. -/
@[expose] public section
namespace Silmaril.Formats.Json.Internal

inductive Token where
  | string (value : Units)
  | identifier (value : Units) (plain : Bool)
  | number (value : Number)
  | null | bool (value : Bool)
  | arrayOpen | arrayClose | objectOpen | objectClose | comma | colon
  deriving Repr

structure Lexed where
  tokens : List Token
  concrete : List (Located TokenKind)

def white (dialect : Dialect) (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' ||
    (dialect == .json5 && (c.toNat == 0xB || c.toNat == 0xC || c.toNat == 0xA0 ||
      c.toNat == 0xFEFF || c.toNat == 0x2028 || c.toNat == 0x2029 ||
      c.toNat == 0x1680 || (0x2000 ≤ c.toNat && c.toNat ≤ 0x200A) ||
      c.toNat == 0x202F || c.toNat == 0x205F || c.toNat == 0x3000))

def lineEnd (c : Char) : Bool :=
  c == '\n' || c == '\r' || c.toNat == 0x2028 || c.toNat == 0x2029

def width (cs : List Char) : Nat := cs.foldl (fun n c => n + c.utf8Size) 0

def hex? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 97 + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 65 + 10)
  else none

def hexes? : Nat → List Char → Option (Nat × List Char)
  | 0, cs => some (0, cs)
  | n + 1, c :: cs => do
      let h ← hex? c
      let (tail, rest) ← hexes? n cs
      pure (h * 16 ^ n + tail, rest)
  | _, [] => none

/-- The closing quote is consumed. JSON5 line continuations denote no units. -/
def quoted? (dialect : Dialect) (quote : Char) : Nat → List Char → Option (Units × List Char)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, c :: cs => do
    if c == quote then return ([], cs)
    if c == '\\' then
      let (head, rest) ← match cs with
        | 'u' :: rest => do
            let (n, rest) ← hexes? 4 rest
            pure ([UInt16.ofNat n], rest)
        | 'x' :: rest =>
            if dialect == .json5 then do
              let (n, rest) ← hexes? 2 rest
              pure ([UInt16.ofNat n], rest)
            else none
        | e :: rest =>
          if dialect == .json5 && lineEnd e then
            some ([], if e == '\r' then match rest with
              | '\n' :: rest => rest | _ => rest else rest)
          else match e with
            | '"' => some ([34], rest) | '\\' => some ([92], rest)
            | '/' => some ([47], rest) | 'b' => some ([8], rest)
            | 'f' => some ([12], rest) | 'n' => some ([10], rest)
            | 'r' => some ([13], rest) | 't' => some ([9], rest)
            | 'v' => if dialect == .json5 then some ([11], rest) else none
            | '0' => if dialect == .json5 && !(rest.head?.any Char.isDigit) then
                some ([0], rest) else none
            | _ => if dialect == .json5 && !e.isDigit then some (charUnits e, rest) else none
        | [] => none
      let (tail, rest) ← quoted? dialect quote fuel rest
      return (head ++ tail, rest)
    -- JSON5 §5.2 explicitly admits raw U+2028 and U+2029 in strings.
    if (dialect != .json5 && c.toNat < 32) ||
        (dialect == .json5 && (c == '\n' || c == '\r')) then
      none
    else
      let (tail, rest) ← quoted? dialect quote fuel cs
      pure (charUnits c ++ tail, rest)

def blockComment? : List Char → Option (List Char)
  | '*' :: '/' :: cs => some cs
  | _ :: cs => blockComment? cs
  | [] => none

def identifier? : Nat → Bool → List Char → Option (Units × List Char)
  | 0, _, _ => none
  | fuel + 1, first, input => do
    let decoded ← match input with
      | '\\' :: 'u' :: cs => do
          let (n, rest) ← hexes? 4 cs
          if 0xD800 ≤ n && n ≤ 0xDFFF then none else some (Char.ofNat n, rest)
      | c :: cs => some (c, cs)
      | [] => none
    let (c, rest) := decoded
    if (if first then identifierStart c else identifierContinue c) then
      let more := match rest with
        | '\\' :: _ => true
        | c :: _ => identifierContinue c
        | [] => false
      if more then
        let (tail, rest) ← identifier? fuel false rest
        pure (charUnits c ++ tail, rest)
      else pure (charUnits c, rest)
    else none

def digitsValue (base : Nat) (cs : List Char) : Nat :=
  cs.foldl (fun n c => base * n + (hex? c).getD 0) 0

def exponent? : List Char → Option Int
  | [] => some 0
  | e :: rest =>
      if e == 'e' || e == 'E' then
        let (neg, ds) := match rest with
          | '-' :: ds => (true, ds) | '+' :: ds => (false, ds) | _ => (false, rest)
        if ds.isEmpty || !(ds.all Char.isDigit) then none
        else
          let n : Int := digitsValue 10 ds
          some (if neg then -n else n)
      else none

def decimal? (dialect : Dialect) (text : List Char) : Option Number := do
  let (negative, cs) := match text with
    | '-' :: cs => (true, cs)
    | '+' :: cs => (false, cs)
    | _ => (false, text)
  if dialect != .json5 && text.head? == some '+' then none else do
  if dialect == .json5 && cs == "Infinity".toList then return .infinity negative
  if dialect == .json5 && cs == "NaN".toList then return .nan
  if dialect == .json5 && (cs.take 2 == ['0', 'x'] || cs.take 2 == ['0', 'X']) then
    let ds := cs.drop 2
    if ds.isEmpty || !(ds.all (hex? · |>.isSome)) then none
    else return .finite ⟨negative, digitsValue 16 ds, 0⟩
  else do
    let (whole, rest) := cs.span Char.isDigit
    if whole.length > 1 && whole.head? == some '0' then none else do
    let (fraction, rest, dot) := match rest with
      | '.' :: rest => let (f, r) := rest.span Char.isDigit; (f, r, true)
      | _ => ([], rest, false)
    if whole.isEmpty && fraction.isEmpty then none else do
    if dialect != .json5 && (whole.isEmpty || (dot && fraction.isEmpty)) then none else do
    let exponent ← exponent? rest
    pure (.finite ⟨negative, digitsValue 10 (whole ++ fraction), exponent - fraction.length⟩)

def delimiter (d : Dialect) (c : Char) : Bool :=
  white d c || c == ',' || c == ']' || c == '}' || c == ':' ||
    c == '[' || c == '{' || (d != .rfc8259 && c == '/')

/-- Tokenization retains trivia. Every successful iteration consumes a character;
fuel is a totality guard bounded by the original character count. -/
def lex (dialect : Dialect) : Nat → Nat → List Char → Option Lexed
  | _, _, [] => some ⟨[], []⟩
  | 0, _, _ => none
  | fuel + 1, offset, input@(c :: cs) => do
    let (token, kind, rest) ←
      if white dialect c then some (none, .whitespace, input.dropWhile (white dialect))
      else if dialect != .rfc8259 && input.take 2 == ['/', '/'] then
        some (none, .comment, cs.drop 1 |>.dropWhile (fun c => !lineEnd c))
      else if dialect != .rfc8259 && input.take 2 == ['/', '*'] then do
        let rest ← blockComment? (input.drop 2)
        pure (none, .comment, rest)
      else if c == '"' || (dialect == .json5 && c == '\'') then do
        let (s, rest) ← quoted? dialect c (input.length + 1) cs
        pure (some (.string s), .string, rest)
      else match c with
        | '[' => some (some .arrayOpen, .arrayOpen, cs)
        | ']' => some (some .arrayClose, .arrayClose, cs)
        | '{' => some (some .objectOpen, .objectOpen, cs)
        | '}' => some (some .objectClose, .objectClose, cs)
        | ',' => some (some .comma, .comma, cs)
        | ':' => some (some .colon, .colon, cs)
        | _ =>
          if c.isDigit || c == '-' || c == '+' || c == '.' then do
            let (word, rest) := input.span (fun c => !delimiter dialect c)
            let n ← decimal? dialect word
            pure (some (.number n), .number, rest)
          else if dialect == .json5 then do
            let (name, rest) ← identifier? (input.length + 1) true input
            let raw := input.take (input.length - rest.length)
            pure (some (.identifier name (raw.all (· != '\\'))), .identifier, rest)
          else
            let (word, rest) := input.span (fun c => !delimiter dialect c)
            if word == "true".toList then some (some (.bool true), .literal, rest)
            else if word == "false".toList then some (some (.bool false), .literal, rest)
            else if word == "null".toList then some (some .null, .literal, rest)
            else none
    let count := input.length - rest.length
    if count == 0 then none else do
    let stop := offset + width (input.take count)
    let tail ← lex dialect fuel stop rest
    pure ⟨token.toList ++ tail.tokens, ⟨kind, ⟨offset, stop⟩⟩ :: tail.concrete⟩

end Silmaril.Formats.Json.Internal
