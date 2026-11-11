module

/-!
# Annotations in WAT text

Under the annotations proposal (part of the Wasm 3.0 text format) an annotation `(@id …)` is
treated as whitespace by the core text grammar. silmaril-lean's lexer accepts `(@name …)` but
not the other annotations wasm-tools reads and writes (`(@custom …)`, `(@producers …)`,
`(@metadata.code.branch_hint …)`).

* `stripTrivia t`: `t` with every annotation and block comment replaced by a space and
  every line comment removed (its newline kept); all of these are whitespace in the text
  grammar. Strings are skipped over, so a `(@` or `;;` inside them is kept. `parse` and the
  `print` check read this text with the certified pipeline. Removing comments is also a
  fast path: silmaril-lean's lexer measures the rest of the input at every block comment.
* `annotations t`: the annotations of `t` at any depth outside strings and comments, in order:
  their identifier and their tokens (strings decoded to bytes, atoms, parenthesised groups of
  atoms).
* `customs t`: the `(@custom "name" (place)? "data"*)` annotations as custom sections, with
  their placement (`wast`'s `CustomPlace`).

Nothing here decides what module a text denotes: annotations only feed custom sections, whose
bytes the certified decoder checks (`Silmaril.Wasm.Tools.Layout`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Annot

/-! ## Removing annotations and comments

Under the annotations proposal (part of the Wasm 3.0 text format), an annotation
`(@id …)` is treated as whitespace by the core text grammar, as comments are. silmaril-lean's
lexer accepts `(@name …)` but not the other annotations wasmprinter writes (`(@custom …)`,
`(@producers …)`, `(@metadata.code.branch_hint …)`), so the check reads the text with every
annotation and comment replaced by whitespace. -/

/-- Lexical state of `stripAnnot`: inside a string, a line comment, `n` nested block
comments, or plain text. -/
inductive Lex where
  | plain | str | line | block (n : Nat)

def keepIf (d : Nat) (acc a : List Char) : List Char := if d = 0 then a else acc

/-- Remove annotations and comments: `d` is the parenthesis depth inside the current
annotation (0 outside); characters are kept only outside annotations and comments. -/
def stripAnnot : List Char → Lex → Nat → List Char → List Char
  | [], _, _, acc => acc.reverse
  | '\\' :: c' :: cs, .str, d, acc => stripAnnot cs .str d (keepIf d acc (c' :: '\\' :: acc))
  | '"' :: cs, .str, d, acc => stripAnnot cs .plain d (keepIf d acc ('"' :: acc))
  | c :: cs, .str, d, acc => stripAnnot cs .str d (keepIf d acc (c :: acc))
  | c :: cs, .line, d, acc =>
    if c = '\n' then stripAnnot cs .plain d (keepIf d acc ('\n' :: acc))
    else stripAnnot cs .line d acc
  | '(' :: ';' :: cs, .block n, d, acc => stripAnnot cs (.block (n + 1)) d acc
  | ';' :: ')' :: cs, .block n, d, acc =>
    stripAnnot cs (if n ≤ 1 then .plain else .block (n - 1)) d acc
  | _ :: cs, .block n, d, acc => stripAnnot cs (.block n) d acc
  | '"' :: cs, .plain, d, acc => stripAnnot cs .str d (keepIf d acc ('"' :: acc))
  | ';' :: ';' :: cs, .plain, d, acc => stripAnnot cs .line d acc
  | '(' :: ';' :: cs, .plain, d, acc => stripAnnot cs (.block 1) d (keepIf d acc (' ' :: acc))
  | '(' :: '@' :: cs, .plain, d, acc => stripAnnot cs .plain (d + 1) (keepIf d acc (' ' :: acc))
  | '(' :: cs, .plain, d, acc =>
    stripAnnot cs .plain (if d = 0 then 0 else d + 1) (keepIf d acc ('(' :: acc))
  | ')' :: cs, .plain, d, acc =>
    if d = 0 then stripAnnot cs .plain 0 (')' :: acc) else stripAnnot cs .plain (d - 1) acc
  | c :: cs, .plain, d, acc => stripAnnot cs .plain d (keepIf d acc (c :: acc))

/-- The text with its annotations and block comments replaced by spaces and its line
comments removed (their newline kept). -/
def stripTrivia (t : String) : String := String.ofList (stripAnnot t.toList .plain 0 [])


/-! ## Reading annotations -/

/-- A token inside an annotation. -/
inductive Tok where
  | str (bytes : List UInt8)
  | atom (s : String)
  | group (ts : List Tok)
  deriving Repr, Inhabited

/-- UTF-8 bytes of a character. -/
def utf8 (c : Char) : List UInt8 := (String.singleton c).toUTF8.data.toList

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode the body of a string literal (after the opening quote) up to the closing quote:
the bytes and the rest after the quote. -/
def strBody : List Char → List UInt8 → Option (List UInt8 × List Char)
  | [], _ => none
  | '"' :: cs, acc => some (acc.reverse, cs)
  | '\\' :: 'n' :: cs, acc => strBody cs (10 :: acc)
  | '\\' :: 't' :: cs, acc => strBody cs (9 :: acc)
  | '\\' :: 'r' :: cs, acc => strBody cs (13 :: acc)
  | '\\' :: '"' :: cs, acc => strBody cs (34 :: acc)
  | '\\' :: '\'' :: cs, acc => strBody cs (39 :: acc)
  | '\\' :: '\\' :: cs, acc => strBody cs (92 :: acc)
  | '\\' :: 'u' :: '{' :: cs, acc =>
    let ds := cs.takeWhile (· != '}')
    let rest := cs.drop (ds.length + 1)
    match ds.filter (· != '_') |>.foldlM (fun n d => (hexVal d).map (n * 16 + ·)) 0 with
    | some v => if v < 0x110000 then strBody rest ((utf8 (Char.ofNat v)).reverse ++ acc) else none
    | none => none
  | '\\' :: h :: l :: cs, acc =>
    match hexVal h, hexVal l with
    | some a, some b => strBody cs (UInt8.ofNat (16 * a + b) :: acc)
    | _, _ => none
  | c :: cs, acc => strBody cs ((utf8 c).reverse ++ acc)
termination_by l => l.length
decreasing_by all_goals simp_wf <;> omega

def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

def isDelim (c : Char) : Bool := isSpace c || c == '(' || c == ')' || c == '"' || c == ';'

/-- The body of a parenthesised group up to its `)` (strings skipped over; no nesting), and
the rest after it. -/
def groupBody : List Char → List Char → Nat → Option (List Char × List Char)
  | _, _, 0 => none
  | [], _, _ => none
  | ')' :: cs, acc, _ => some (acc.reverse, cs)
  | '"' :: cs, acc, fuel + 1 =>
    match strBody cs [] with
    | some (_, rest) =>
      let n := cs.length - rest.length
      groupBody rest ((cs.take n).reverse ++ '"' :: acc) fuel
    | none => none
  | c :: cs, acc, fuel + 1 => groupBody cs (c :: acc) fuel

/-- Tokens of an annotation body (without the leading `(@` and the closing parenthesis). -/
def toks (fuel : Nat) (cs : List Char) (acc : List Tok) : Option (List Tok) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match cs with
    | [] => some acc.reverse
    | c :: rest =>
      if isSpace c then toks fuel rest acc
      else if c == '"' then
        match strBody rest [] with
        | some (bs, rest') => toks fuel rest' (.str bs :: acc)
        | none => none
      else if c == '(' then
        match groupBody rest [] (rest.length + 1) with
        | some (inner, rest') =>
          match toks fuel inner [] with
          | some ts => toks fuel rest' (.group ts :: acc)
          | none => none
        | none => none
      else
        let a := cs.takeWhile (!isDelim ·)
        if a.isEmpty then none
        else toks fuel (cs.drop a.length) (.atom (String.ofList a) :: acc)

/-- Collect the raw bodies of annotations (outside strings and comments, at any depth). -/
def collect : List Char → Lex → Nat → List Char → List (List Char) → List (List Char)
  | [], _, _, _, out => out.reverse
  | '\\' :: c' :: cs, .str, d, cur, out =>
    collect cs .str d (if d = 0 then cur else c' :: '\\' :: cur) out
  | '"' :: cs, .str, d, cur, out => collect cs .plain d (if d = 0 then cur else '"' :: cur) out
  | c :: cs, .str, d, cur, out => collect cs .str d (if d = 0 then cur else c :: cur) out
  | c :: cs, .line, d, cur, out => collect cs (if c = '\n' then .plain else .line) d cur out
  | '(' :: ';' :: cs, .block n, d, cur, out => collect cs (.block (n + 1)) d cur out
  | ';' :: ')' :: cs, .block n, d, cur, out =>
    collect cs (if n ≤ 1 then .plain else .block (n - 1)) d cur out
  | _ :: cs, .block n, d, cur, out => collect cs (.block n) d cur out
  | '"' :: cs, .plain, d, cur, out => collect cs .str d (if d = 0 then cur else '"' :: cur) out
  | ';' :: ';' :: cs, .plain, d, cur, out => collect cs .line d cur out
  | '(' :: ';' :: cs, .plain, d, cur, out => collect cs (.block 1) d cur out
  | '(' :: '@' :: cs, .plain, d, cur, out =>
    if d = 0 then collect cs .plain 1 [] out else collect cs .plain (d + 1) ('@' :: '(' :: cur) out
  | '(' :: cs, .plain, d, cur, out =>
    collect cs .plain (if d = 0 then 0 else d + 1) (if d = 0 then cur else '(' :: cur) out
  | ')' :: cs, .plain, d, cur, out =>
    if d = 0 then collect cs .plain 0 cur out
    else if d = 1 then collect cs .plain 0 [] (cur.reverse :: out)
    else collect cs .plain (d - 1) (')' :: cur) out
  | c :: cs, .plain, d, cur, out => collect cs .plain d (if d = 0 then cur else c :: cur) out

/-- The annotations of a text: identifier and tokens (`none` for an unreadable one). -/
def annotations (t : String) : List (String × Option (List Tok)) :=
  (collect t.toList .plain 0 [] []).map fun body =>
    let id := body.takeWhile (!isDelim ·)
    (String.ofList id, toks (body.length + 1) (body.drop id.length) [])

/-- Where a custom section goes (`wast`'s `CustomPlace`): before the first section, before or
after a section kind (`type`, `import`, `func`, `table`, `memory`, `global`, `export`,
`start`, `elem`, `code`, `data`, `tag`), or after the last. -/
inductive Place where
  | beforeFirst
  | before (anchor : String)
  | after (anchor : String)
  | afterLast
  deriving Repr, Inhabited, BEq

def anchors : List String :=
  ["type", "import", "func", "table", "memory", "global", "export", "start", "elem", "code",
    "data", "tag"]

def place? : List String → Option Place
  | ["before", "first"] => some .beforeFirst
  | ["after", "last"] => some .afterLast
  | ["before", a] => if anchors.contains a then some (.before a) else none
  | ["after", a] => if anchors.contains a then some (.after a) else none
  | _ => none

/-- A custom section from an annotation. -/
structure Custom where
  name : List UInt8
  place : Place
  data : List UInt8
  deriving Repr, Inhabited

def atoms (ts : List Tok) : List String :=
  ts.filterMap fun | .atom a => some a | _ => none

/-- `(@custom "name" (place)? "data"*)`. -/
def custom? : List Tok → Option Custom
  | .str n :: .group g :: rest => do
    let p ← place? (atoms g)
    let ds ← rest.mapM fun | .str b => some b | _ => none
    pure ⟨n, p, ds.flatten⟩
  | .str n :: rest => do
    let ds ← rest.mapM fun | .str b => some b | _ => none
    pure ⟨n, .afterLast, ds.flatten⟩
  | _ => none

/-- Unsigned LEB128. -/
def leb (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: leb (n / 128)
termination_by n
decreasing_by omega

def name (bs : List UInt8) : List UInt8 := leb bs.length ++ bs

/-- `(@producers (language|sdk|processed-by "name" "version")*)`: the `producers` section
as the `wast` crate writes it (fields in the order language, sdk, processed-by). -/
def producers? (ts : List Tok) : Option Custom := do
  let entries ← ts.mapM fun
    | .group [.atom f, .str n, .str v] =>
      if ["language", "sdk", "processed-by"].contains f then some (f, n, v) else none
    | _ => none
  let fields := ["language", "sdk", "processed-by"].filterMap fun f =>
    let vs := entries.filter (·.1 == f)
    if vs.isEmpty then none else some (f, vs.map (·.2))
  let body := leb fields.length ++ fields.flatMap fun (f, vs) =>
    name f.toUTF8.data.toList ++ leb vs.length ++ vs.flatMap fun (n, v) => name n ++ name v
  pure ⟨"producers".toUTF8.data.toList, .afterLast, body⟩

/-- The `@custom` and `@producers` annotations of a text as custom sections, in order, or
`none` if one of them is malformed. -/
def customs (t : String) : Option (List Custom) :=
  (annotations t).filterMap (fun (id, ts) =>
      if id == "custom" then some (ts.bind custom?)
      else if id == "producers" then some (ts.bind producers?)
      else none)
    |>.mapM id

/-! ## Name annotations

`$id (@name "S")`: the item with identifier `id` is called `S` in the `name` section. -/

/-- Skip a block comment body (after `(;`), nested `n` deep. -/
def skipBlock : Nat → List Char → List Char
  | _, [] => []
  | n, '(' :: ';' :: cs => skipBlock (n + 1) cs
  | n, ';' :: ')' :: cs => if n ≤ 1 then cs else skipBlock (n - 1) cs
  | n, _ :: cs => skipBlock n cs

/-- An identifier after `$`: a quoted one (decoded) or identifier characters. -/
def readId (cs : List Char) : Option (String × List Char) :=
  match cs with
  | '"' :: rest => do
    let (bs, rest') ← strBody rest []
    let s ← String.fromUTF8? ⟨bs.toArray⟩
    pure (s, rest')
  | _ =>
    let a := cs.takeWhile (!isDelim ·)
    if a.isEmpty then none else some (String.ofList a, cs.drop a.length)

/-- `(@name "S")` at the start of `cs` (after spaces): `S` and the rest. -/
def nameAnnot? (cs : List Char) : Option String :=
  match cs.dropWhile isSpace with
  | '(' :: '@' :: 'n' :: 'a' :: 'm' :: 'e' :: rest =>
    match rest.dropWhile isSpace with
    | '"' :: r => do
      let (bs, _) ← strBody r []
      String.fromUTF8? ⟨bs.toArray⟩
    | _ => none
  | _ => none

/-- The `$id (@name "S")` pairs of a text, outside strings and comments. -/
def nameAnnotsGo : Nat → List Char → List (String × String) → List (String × String)
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | fuel + 1, '"' :: cs, acc =>
    match strBody cs [] with
    | some (_, rest) => nameAnnotsGo fuel rest acc
    | none => acc.reverse
  | fuel + 1, ';' :: ';' :: cs, acc => nameAnnotsGo fuel (cs.dropWhile (· != '\n')) acc
  | fuel + 1, '(' :: ';' :: cs, acc => nameAnnotsGo fuel (skipBlock 1 cs) acc
  | fuel + 1, '$' :: cs, acc =>
    match readId cs with
    | some (id, rest) =>
      match nameAnnot? rest with
      | some n => nameAnnotsGo fuel rest ((id, n) :: acc)
      | none => nameAnnotsGo fuel rest acc
    | none => nameAnnotsGo fuel cs acc
  | fuel + 1, _ :: cs, acc => nameAnnotsGo fuel cs acc

def nameAnnots (t : String) : List (String × String) :=
  nameAnnotsGo (t.length + 1) t.toList []

/-! ## Branch hints

`(@metadata.code.branch_hint "\00")` / `"\01"` before an instruction (the form wasmprinter
writes): `parse` writes them as the `metadata.code.branch_hint` section. To find which
instruction each one precedes, the text is elaborated once more with every hint replaced by a
marker pair of instructions (`markerText`), which `Layout.hintPositions` then looks for. The
section is custom, so a misplaced hint cannot change the module. -/

def hintOpen : String := "(@metadata.code.branch_hint \"\\0"

/-- The hints of a text, in order: `true` for taken (`"\01"`). -/
def branchHints (t : String) : List Bool :=
  ((t.splitOn hintOpen).drop 1).map fun part => part.startsWith "1"

/-- The marker pair: an `i64.const` with an improbable value, then `drop`. -/
def markerBits : Nat := 0x7a7a7a7a7a7a7a7b

def markerText (t : String) : String :=
  let m := " i64.const 0x7a7a7a7a7a7a7a7b drop "
  (t.replace (hintOpen ++ "0\")") m).replace (hintOpen ++ "1\")") m

end Silmaril.Wasm.Tools.Annot
