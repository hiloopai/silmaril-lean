module

public import Init.Data.String

/-!
# A regular-expression subset for `wasm-tools strip --delete`

`strip --delete REGEX` uses Rust's `regex` crate (`RegexSet::is_match`: the pattern matches
somewhere in the name). This topic gives a documented subset of that syntax, its language
(`Matches`) and a matcher by Brzozowski derivatives (`isMatch`).

* `CharSet`: `.` (any character but `\n`), a literal, a class `[…]`/`[^…]` of characters and
  ranges, the Perl classes `\d`, `\w`, `\s` (ASCII; see the parity document);
* `Re`: `∅`, `ε`, a character set, concatenation, alternation, Kleene star; `Re.Matches r cs`:
  the language, inductively;
* `parse`: literals, escapes of metacharacters, `.`, classes, groups `(…)` and `(?:…)`,
  alternation `|`, `*`, `+`, `?`, `{n}`, `{n,}`, `{n,m}` (greedy and lazy forms match the same
  strings), `^` at the start and `$` at the end; other syntax is an error;
* `Pattern`: a parsed regex with its anchors; `Pattern.search`: `is_match` (somewhere in the
  string, honouring the anchors), by derivatives (`Re.deriv`, `Re.nullable`).

`Thms`: `Re.matchList_iff` (the derivative matcher decides `Matches`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Regex

/-- A set of characters. -/
inductive CharSet where
  | any
  | lit (c : Char)
  | cls (neg : Bool) (ranges : List (Char × Char))
  deriving Repr, DecidableEq

/-- Membership in a character set. -/
def CharSet.mem : CharSet → Char → Bool
  | .any, c => c != '\n'
  | .lit d, c => c == d
  | .cls neg rs, c => neg != rs.any fun (lo, hi) => lo ≤ c && c ≤ hi

/-- Regular expressions. -/
inductive Re where
  | zero
  | eps
  | chr (s : CharSet)
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  deriving Repr, DecidableEq

namespace Re

/-- **The language of a regular expression.** -/
inductive Matches : Re → List Char → Prop where
  | eps : Matches .eps []
  | chr {s : CharSet} {c : Char} (h : s.mem c = true) : Matches (.chr s) [c]
  | seq {a b : Re} {u v : List Char} (ha : Matches a u) (hb : Matches b v) :
      Matches (.seq a b) (u ++ v)
  | altL {a b : Re} {u : List Char} (h : Matches a u) : Matches (.alt a b) u
  | altR {a b : Re} {u : List Char} (h : Matches b u) : Matches (.alt a b) u
  | starNil {a : Re} : Matches (.star a) []
  | starCons {a : Re} {u v : List Char} (ha : Matches a u) (hs : Matches (.star a) v) :
      Matches (.star a) (u ++ v)

/-- Does the language contain the empty string? -/
def nullable : Re → Bool
  | .zero => false
  | .eps => true
  | .chr _ => false
  | .seq a b => a.nullable && b.nullable
  | .alt a b => a.nullable || b.nullable
  | .star _ => true

/-- Smart concatenation (drops `∅` and `ε`). -/
def mkSeq : Re → Re → Re
  | .zero, _ => .zero
  | _, .zero => .zero
  | .eps, b => b
  | a, .eps => a
  | a, b => .seq a b

/-- Smart alternation (drops `∅`, merges equal branches). -/
def mkAlt : Re → Re → Re
  | .zero, b => b
  | a, .zero => a
  | a, b => if a = b then a else .alt a b

/-- **The Brzozowski derivative** by a character. -/
def deriv (c : Char) : Re → Re
  | .zero => .zero
  | .eps => .zero
  | .chr s => if s.mem c then .eps else .zero
  | .seq a b =>
    if a.nullable then mkAlt (mkSeq (a.deriv c) b) (b.deriv c) else mkSeq (a.deriv c) b
  | .alt a b => mkAlt (a.deriv c) (b.deriv c)
  | .star a => mkSeq (a.deriv c) (.star a)

/-- **The matcher**: derive by every character, then ask for `ε`. -/
def matchList (r : Re) : List Char → Bool
  | [] => r.nullable
  | c :: cs => (r.deriv c).matchList cs

/-- `r` repeated `n` times. -/
def rep (r : Re) : Nat → Re
  | 0 => .eps
  | n + 1 => .seq r (r.rep n)

/-- At most `n` copies of `r`. -/
def upTo (r : Re) : Nat → Re
  | 0 => .eps
  | n + 1 => .alt .eps (.seq r (r.upTo n))

end Re

/-! ## The parser -/

/-- A parsed pattern: the expression and its anchors. -/
structure Pattern where
  re : Re
  startAnchor : Bool
  endAnchor : Bool
  deriving Repr

/-- Any string. -/
def anyStar : Re := .star (.chr (.cls true []))

/-- **`is_match`**: the pattern matches a substring (a prefix with `^`, a suffix with `$`). -/
def Pattern.search (p : Pattern) (s : String) : Bool :=
  let r := if p.startAnchor then p.re else Re.seq anyStar p.re
  let r := if p.endAnchor then r else Re.seq r anyStar
  r.matchList s.toList

/-- Metacharacters that a backslash escapes to themselves. -/
def metaChars : List Char := ['\\', '.', '+', '*', '?', '(', ')', '|', '[', ']', '{', '}', '^',
  '$', '#', '&', '-', '~', ' ', '/', ':', '"', '\'', '<', '>', '!', '=', '@', '%', ',', ';', '`',
  '_']

/-- The Perl classes (ASCII). -/
def perlClass : Char → Option (List (Char × Char))
  | 'd' => some [('0', '9')]
  | 'w' => some [('0', '9'), ('A', 'Z'), ('a', 'z'), ('_', '_')]
  | 's' => some [(' ', ' '), ('\t', '\t'), ('\n', '\n'), ('\x0B', '\x0B'), ('\x0C', '\x0C'),
      ('\r', '\r')]
  | _ => none

/-- An escape `\c` outside a class. -/
def escape (c : Char) : Except String CharSet :=
  if c = 'n' then .ok (.lit '\n') else if c = 't' then .ok (.lit '\t')
  else if c = 'r' then .ok (.lit '\r')
  else match perlClass c with
    | some rs => .ok (.cls false rs)
    | none => match perlClass c.toLower with
      | some rs => if c.isUpper then .ok (.cls true rs) else .ok (.cls false rs)
      | none => if metaChars.contains c then .ok (.lit c) else .error s!"unsupported escape \\{c}"

/-- The body of a class, after `[` or `[^`: ranges until `]` (a `]` first is a literal). -/
def parseClass : Nat → List Char → Bool → Except String (List (Char × Char) × List Char)
  | 0, _, _ => .error "class too long"
  | _, [], _ => .error "unclosed character class"
  | fuel + 1, c :: cs, first =>
    if c = ']' && !first then .ok ([], cs)
    else do
      let (lo, cs, perl) ← (match c, cs with
        | '\\', d :: cs' =>
          match perlClass d with
          | some rs => .ok (' ', cs', some rs)
          | none =>
            if d = 'n' then .ok ('\n', cs', none) else if d = 't' then .ok ('\t', cs', none)
            else .ok (d, cs', none)
        | '[', ':' :: _ => .error "unsupported POSIX class"
        | _, _ => .ok (c, cs, none) : Except String (Char × List Char × Option (List (Char × Char))))
      match perl with
      | some rs =>
        let (more, rest) ← parseClass fuel cs false
        return (rs ++ more, rest)
      | none =>
        match cs with
        | '-' :: hi :: cs' =>
          if hi = ']' then
            let (more, rest) ← parseClass fuel ('-' :: hi :: cs') false
            return ((lo, lo) :: more, rest)
          else
            let (hi, cs'') ← (match hi, cs' with
              | '\\', d :: t => .ok (d, t)
              | _, _ => .ok (hi, cs') : Except String (Char × List Char))
            if hi < lo then .error "invalid class range"
            let (more, rest) ← parseClass fuel cs'' false
            return ((lo, hi) :: more, rest)
        | _ =>
          let (more, rest) ← parseClass fuel cs false
          return ((lo, lo) :: more, rest)

/-- Digits of a repetition count. -/
def digits : List Char → Nat × List Char × Bool
  | cs =>
    let ds := cs.takeWhile Char.isDigit
    (ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0, cs.drop ds.length, !ds.isEmpty)

/-- A repetition `{n}`, `{n,}`, `{n,m}` (after `{`). -/
def parseCounted (cs : List Char) : Except String (Nat × Option Nat × List Char) :=
  let (n, cs, ok) := digits cs
  if !ok then .error "invalid repetition" else
  match cs with
  | '}' :: rest => .ok (n, some n, rest)
  | ',' :: '}' :: rest => .ok (n, none, rest)
  | ',' :: cs' =>
    let (m, cs'', ok') := digits cs'
    match cs'' with
    | '}' :: rest => if ok' && n ≤ m then .ok (n, some m, rest) else .error "invalid repetition"
    | _ => .error "invalid repetition"
  | _ => .error "invalid repetition"

/-- Apply a quantifier to an atom. -/
def quantify (a : Re) : Nat × Option Nat → Re
  | (n, none) => .seq (a.rep n) (.star a)
  | (n, some m) => .seq (a.rep n) (a.upTo (m - n))

mutual

/-- Alternatives, until `)` or the end. -/
def parseAlt : Nat → List Char → Except String (Re × List Char)
  | 0, _ => .error "pattern too long"
  | fuel + 1, cs => do
    let (a, cs) ← parseSeq fuel cs
    match cs with
    | '|' :: cs' =>
      let (b, cs'') ← parseAlt fuel cs'
      return (.alt a b, cs'')
    | _ => return (a, cs)

/-- A concatenation of quantified atoms, until `|`, `)` or the end. -/
def parseSeq : Nat → List Char → Except String (Re × List Char)
  | 0, _ => .error "pattern too long"
  | _, [] => .ok (.eps, [])
  | fuel + 1, c :: cs =>
    if c = '|' || c = ')' then .ok (.eps, c :: cs) else do
    let (atom, cs) ← parseAtom fuel (c :: cs)
    let (atom, cs) ← (match cs with
      | '*' :: t => .ok (.star atom, t)
      | '+' :: t => .ok (.seq atom (.star atom), t)
      | '?' :: t => .ok (.alt .eps atom, t)
      | '{' :: t => do
        let (n, m, t) ← parseCounted t
        .ok (quantify atom (n, m), t)
      | _ => .ok (atom, cs) : Except String (Re × List Char))
    -- a lazy marker `?` after a quantifier does not change the set of matched strings
    let cs := match cs with
      | '?' :: t => t
      | _ => cs
    let (rest, cs) ← parseSeq fuel cs
    return (.seq atom rest, cs)

/-- One atom. -/
def parseAtom : Nat → List Char → Except String (Re × List Char)
  | 0, _ => .error "pattern too long"
  | _, [] => .error "unexpected end of pattern"
  | fuel + 1, c :: cs =>
    match c, cs with
    | '(', '?' :: ':' :: t => do
      let (r, t) ← parseAlt fuel t
      match t with
      | ')' :: t' => return (r, t')
      | _ => .error "unclosed group"
    | '(', '?' :: _ => .error "unsupported group flags"
    | '(', t => do
      let (r, t) ← parseAlt fuel t
      match t with
      | ')' :: t' => return (r, t')
      | _ => .error "unclosed group"
    | '[', '^' :: t => do
      let (rs, t) ← parseClass t.length t true
      return (.chr (.cls true rs), t)
    | '[', t => do
      let (rs, t) ← parseClass t.length t true
      return (.chr (.cls false rs), t)
    | '\\', d :: t => do return (.chr (← escape d), t)
    | '\\', [] => .error "trailing backslash"
    | '.', t => .ok (.chr .any, t)
    | '*', _ | '+', _ | '?', _ => .error "repetition operator missing expression"
    | '^', _ | '$', _ => .error "unsupported anchor position"
    | c, t => .ok (.chr (.lit c), t)

end

/-- **Parse a pattern.** -/
def parse (p : String) : Except String Pattern := do
  let cs := p.toList
  let (sa, cs) := match cs with
    | '^' :: t => (true, t)
    | _ => (false, cs)
  let (ea, cs) :=
    if cs.getLast? = some '$' && !(cs.dropLast.getLast? = some '\\') then (true, cs.dropLast)
    else (false, cs)
  let (r, rest) ← parseAlt (3 * cs.length + 3) cs
  if !rest.isEmpty then .error "unopened group"
  return ⟨r, sa, ea⟩

/-- Does `pattern` match somewhere in `s`? (`false` for a pattern outside the subset; the CLI
reports those as errors before matching.) -/
def isMatch (pattern s : String) : Bool :=
  match parse pattern with
  | .ok p => p.search s
  | .error _ => false

end Silmaril.Wasm.Tools.Regex
