module

public import Silmaril.Wasm.Wit.Text.Parse.Defs

/-!
# WIT text: doc comments as `wit-parser` reads them

`Silmaril.Wasm.Wit.Text.lex` reads only `///` lines as documentation, verbatim, as
`WIT.md` says. `wit-parser` 0.263.0 (crate sha256
`874d6ce9db4261cb66980ab14f3da066b24292497b6f46f988c0d1b9b27913f3`) does more: every
comment right before an item is documentation, including `//` lines and block
comments `/* … */` and `/** … */`, and the text is normalised. This module transcribes
that reading as a second front end, `parseWP`, on top of the same parser.

* `ast.rs` `parse_docs`: the comments between two tokens (separated only by
  whitespace) form one group; `parse_docs` is called where an item may start
  (`DeclList::parse_until`, the item lists of interfaces, worlds and resources,
  `parse_list_trailer` for fields, cases, parameters, `use` names, …), and the group
  is dropped where the item has no docs (parameters, `use` and `with` lists) or where
  the list ends instead. `docPos` restates this on tokens: after the start of the
  file, `;`, `{`, `}` or `,`, inside braces that open an item list (not `.{` of `use`,
  not `with {`) and outside `( )` and `< >`, and before a token other than `}`.
* `ast/resolve.rs` `docs` (`normDocs`): each comment loses `/**` and `*/`, or its
  leading slashes (`trim_start_matches('/')`, so a `/* … */` comment keeps its `* `
  and `*/`), then trailing whitespace; the smallest number of leading ASCII
  whitespace characters over the non-empty comments is removed from each comment
  when it starts with that many spaces; an empty comment gives an empty line, the
  lines of the others are kept (`lines`: split at `\n`, a final `\r` dropped);
  trailing newlines are removed.
* `lexWP`: the comments of the text are cut out (`segments`), the code between them
  is lexed by `lex`, and each comment group in a doc position becomes the doc lines
  of its normalised text (`Tok.doc`, one leading space each, which `Parse.docs`
  removes again).

Deviations: `/**/` (which makes `wit-parser` panic on `strip_suffix("*/").unwrap()`)
gives an empty comment; `trim_end` is restricted to `isWs` characters (space, tab,
newline, carriage return) instead of Unicode whitespace.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

/-! ## Normalisation (`ast/resolve.rs`, `docs`) -/

/-- ASCII whitespace (`u8::is_ascii_whitespace`). -/
def isAsciiWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

/-- Remove trailing whitespace. -/
def trimEnd (l : List Char) : List Char := (l.reverse.dropWhile isWs).reverse

/-- The text of one comment: without `/**` and `*/`, or without its leading slashes,
and without trailing whitespace. -/
def commentBody (c : List Char) : List Char :=
  trimEnd (match c with
    | '/' :: '*' :: '*' :: r => r.take (r.length - 2)
    | _ => c.dropWhile (· == '/'))

/-- The number of leading ASCII whitespace characters. -/
def leadWs (l : List Char) : Nat := (l.takeWhile isAsciiWs).length

/-- Remove `m` leading spaces, if there are that many. -/
def stripSpaces (m : Nat) (l : List Char) : List Char :=
  if l.take m = List.replicate m ' ' then l.drop m else l

/-- Split at newlines. -/
def splitNl : List Char → List (List Char)
  | [] => [[]]
  | '\n' :: r => [] :: splitNl r
  | c :: r => match splitNl r with
    | [] => [[c]]
    | l :: ls => (c :: l) :: ls

/-- Rust's `str::lines`: split at newlines, drop a final `\r` of each line, and no
empty last line after a final newline. -/
def rustLines (l : List Char) : List (List Char) :=
  let ls := splitNl l
  let ls := if l.getLast? = some '\n' then ls.dropLast else ls
  ls.map fun x => if x.getLast? = some '\r' then x.dropLast else x

/-- Remove trailing newlines. -/
def dropTrailingNl (l : List Char) : List Char := (l.reverse.dropWhile (· == '\n')).reverse

/-- **The docs of a comment group**, as `wit-parser` normalises them (`none` for no
comment). -/
def normDocs (cs : List (List Char)) : Option (List Char) :=
  match cs with
  | [] => none
  | _ =>
    let docs := cs.map commentBody
    let m := ((docs.filter (· ≠ [])).map leadWs).min?.getD 0
    let docs := if m > 0 then docs.map (stripSpaces m) else docs
    some (dropTrailingNl (docs.flatMap fun d =>
      if d = [] then ['\n'] else (rustLines d).flatMap (· ++ ['\n'])))

/-! ## Cutting out comments -/

/-- A piece of text: code, or a group of comments separated by whitespace only. -/
inductive Seg where
  | code (cs : List Char)
  | comments (raw : List (List Char))
  deriving Repr, DecidableEq, Inhabited

/-- Add a code character. -/
def pushCode (c : Char) : List Seg → List Seg
  | .code cs :: r => .code (c :: cs) :: r
  | r => .code [c] :: r

/-- Add a comment (to the group before it when only whitespace separates them). -/
def pushComment (raw : List Char) : List Seg → List Seg
  | .comments g :: r => .comments (raw :: g) :: r
  | .code cs :: .comments g :: r =>
    if cs.all isWs then .comments (raw :: g) :: r else .comments [raw] :: .code cs :: .comments g :: r
  | r => .comments [raw] :: r

/-- Cut a text into code and comment groups, in reverse order, with reversed contents
(`n` is fuel). -/
def segRev : Nat → List Char → List Seg → Option (List Seg)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc
  | n + 1, '/' :: '/' :: r, acc =>
    segRev n (takeLine r).2 (pushComment ('/' :: '/' :: (takeLine r).1) acc)
  | n + 1, '/' :: '*' :: r, acc =>
    match skipBlock 0 r with
    | none => none
    | some r' => segRev n r' (pushComment ('/' :: '*' :: r.take (r.length - r'.length)) acc)
  | n + 1, c :: r, acc => segRev n r (pushCode c acc)

/-- Put a segment the right way round. -/
def Seg.fix : Seg → Seg
  | .code cs => .code cs.reverse
  | .comments g => .comments g.reverse

/-- The segments of a text. -/
def segments (cs : List Char) : Option (List Seg) :=
  (segRev (cs.length + 1) cs []).map fun acc => (acc.map Seg.fix).reverse

/-! ## Doc positions -/

/-- An open bracket. -/
inductive Ctx where
  | items | braces | paren | angle
  deriving Repr, DecidableEq, Inhabited

/-- The brackets open after a token (`prev`: the token before it). -/
def ctxStep (st : List Ctx) (prev : Option Tok) : Tok → List Ctx
  | .sym '{' =>
    (if prev = some (.sym '.') ∨ prev = some (.kw .«with») then Ctx.braces else Ctx.items) :: st
  | .sym '(' => .paren :: st
  | .sym '<' => .angle :: st
  | .sym '}' | .sym ')' | .sym '>' => st.tail
  | _ => st

/-- Whether a comment group between `prev` and `next` is documentation. -/
def docPos (st : List Ctx) (prev next : Option Tok) : Bool :=
  (match prev with
    | none | some (.sym ';') | some (.sym '{') | some (.sym '}') | some (.sym ',') => true
    | _ => false) &&
  (match st with
    | [] | .items :: _ => true
    | _ => false) &&
  (match next with
    | none | some (.sym '}') => false
    | _ => true)

/-- The doc tokens of a normalised doc text. -/
def docToks (d : List Char) : List Tok := (splitNl d).map fun l => .doc (String.ofList (' ' :: l))

/-- The tokens of the segments (`st`: open brackets, `prev`: the last token). -/
def assemble : List Ctx → Option Tok → List (List Tok ⊕ List (List Char)) → List Tok
  | _, _, [] => []
  | st, prev, .inl ts :: r =>
    let (st', prev') := ts.foldl (fun (p : List Ctx × Option Tok) t => (ctxStep p.1 p.2 t, some t))
      (st, prev)
    ts ++ assemble st' prev' r
  | st, prev, .inr g :: r =>
    let next := match r with
      | .inl (t :: _) :: _ => some t
      | _ => none
    (if docPos st prev next then (normDocs g).elim [] docToks else []) ++ assemble st prev r

/-- Lex the segments. -/
def lexSegs : List Seg → Option (List (List Tok ⊕ List (List Char)))
  | [] => some []
  | .code cs :: r => do
    let ts ← lex cs
    let r' ← lexSegs r
    pure (if ts = [] then r' else .inl ts :: r')
  | .comments g :: r => (lexSegs r).map (.inr g :: ·)

/-- **Lex as `wit-parser` reads doc comments.** -/
def lexWP (cs : List Char) : Option (List Tok) :=
  (segments cs).bind fun segs => (lexSegs segs).map (assemble [] none)

/-- **Parse a WIT document, with `wit-parser`'s doc comments.** -/
def parseWP (s : String) : Option Document := (lexWP s.toList).bind Parse.document

end Silmaril.Wasm.Wit.Text
