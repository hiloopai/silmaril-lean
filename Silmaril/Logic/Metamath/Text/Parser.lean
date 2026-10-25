module

public import Silmaril.Logic.Metamath.Text.Lexer

@[expose] public section

/-!
# Metamath parser

From tokens to statements (Megill and Wheeler, *Metamath*, 2nd ed., §4.1.3
and Appendix B). The parser is a token automaton, so parsing is a left fold
over the token list:

* `$c` and `$v` statements declare one or more math symbols, `$d` statements
  two or more;
* `label $f tc v $.`, `label $e tc s₁ … sₙ $.`, `label $a tc s₁ … sₙ $.` and
  `label $p tc s₁ … sₙ $= proof $.`, where labels are nonempty strings of
  letters, digits, `-`, `_` and `.`;
* a normal proof is a sequence of labels and `?`; a compressed proof is `(`,
  labels, `)`, then tokens made of the letters `A`–`Z` and `?`, which are
  concatenated;
* `${`, `$}`, and the inclusion command `$[ file $]`.

The specification treats comments as white space, so a comment may occur inside
a statement. A top-level comment becomes a `Stmt.comment`; a comment inside a
statement is kept and emitted as a `Stmt.comment` right after that statement,
since the statement syntax has no room for it.

The grammar of the specification requires a nonempty proof. Like
`metamath-exe` and `metamath-knife`, the parser also accepts an empty normal
proof and a compressed proof with an empty letter block; the verifier rejects
them. Scoping, declarations and proofs are checked later, by the verifier.
-/

namespace Silmaril.Logic.Metamath.Text

/-- A proof step of a normal proof: a label or `?`. -/
def isProofStep (s : String) : Bool := s == "?" || isLabel s

/-- A character of a compressed proof's letter block. -/
def isProofLetter (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || c == '?'

/-- A token of a compressed proof's letter block. -/
def isLetterToken (s : String) : Bool := s.toList.all isProofLetter

/-- The statements `$c`, `$v` and `$d`. -/
inductive DeclKind where
  | c | v | d
  deriving DecidableEq, Repr, Inhabited

/-- The statements `$e`, `$a` and `$p`. -/
inductive ExprKind where
  | e | a | p
  deriving DecidableEq, Repr, Inhabited

/-- The state of the parser automaton. Accumulated lists are reversed. -/
inductive ParseMode where
  /-- Between statements. -/
  | top
  /-- Reading the symbols of a `$c`, `$v` or `$d` statement. -/
  | decl (k : DeclKind) (acc : List String)
  /-- After a label, expecting `$f`, `$e`, `$a` or `$p`. -/
  | label (l : String)
  /-- Reading the typecode and variable of a `$f` statement. -/
  | float (l : String) (acc : List String)
  /-- Reading the typecode and body of a `$e`, `$a` or `$p` statement. -/
  | expr (k : ExprKind) (l : String) (acc : List String)
  /-- Just after `$=`. -/
  | proofStart (l tc : String) (body : List String)
  /-- Reading a normal proof. -/
  | normal (l tc : String) (body : List String) (steps : List String)
  /-- Reading the label list of a compressed proof. -/
  | cLabels (l tc : String) (body : List String) (labels : List String)
  /-- Reading the letter block of a compressed proof. -/
  | cLetters (l tc : String) (body labels : List String) (letters : List String)
  /-- Just after `$[`. -/
  | incl
  /-- After `$[ file`. -/
  | inclFile (file : String)
  deriving DecidableEq, Repr, Inhabited

/-- The parser state: statements so far (reversed), the mode, and the comments
met inside the current statement (reversed). -/
structure ParseState where
  stmts : List Stmt
  mode : ParseMode
  pending : List String
  deriving DecidableEq, Repr, Inhabited

/-- A parse error: the number of statements read before it, and a message. -/
structure ParseError where
  stmt : Nat
  msg : String
  deriving DecidableEq, Repr, Inhabited

instance : ToString ParseError := ⟨fun e => s!"after statement {e.stmt}: {e.msg}"⟩

namespace ParseState

/-- The initial parser state. -/
def init : ParseState := ⟨[], .top, []⟩

/-- Finish a statement: record it, then the comments met inside it. -/
def emit (st : ParseState) (s : Stmt) : ParseState :=
  ⟨st.pending.map Stmt.comment ++ s :: st.stmts, .top, []⟩

/-- Move to a new mode inside the current statement. -/
def goto (st : ParseState) (m : ParseMode) : ParseState := { st with mode := m }

/-- Fail at the current position. -/
def fail {α : Type} (st : ParseState) (msg : String) : Except ParseError α :=
  .error ⟨st.stmts.length, msg⟩

/-- A math symbol token. -/
def stepSym (st : ParseState) (s : String) : Except ParseError ParseState :=
  match st.mode with
  | .top => if isLabel s then .ok (st.goto (.label s)) else st.fail s!"invalid label '{s}'"
  | .decl k acc => .ok (st.goto (.decl k (s :: acc)))
  | .label l => st.fail s!"expected $f, $e, $a or $p after label '{l}', found '{s}'"
  | .float l acc => .ok (st.goto (.float l (s :: acc)))
  | .expr k l acc => .ok (st.goto (.expr k l (s :: acc)))
  | .proofStart l tc body =>
    if s = "(" then .ok (st.goto (.cLabels l tc body []))
    else if isProofStep s then .ok (st.goto (.normal l tc body [s]))
    else st.fail s!"invalid proof step '{s}' in '{l}'"
  | .normal l tc body steps =>
    if isProofStep s then .ok (st.goto (.normal l tc body (s :: steps)))
    else st.fail s!"invalid proof step '{s}' in '{l}'"
  | .cLabels l tc body labels =>
    if s = ")" then .ok (st.goto (.cLetters l tc body labels []))
    else if isLabel s then .ok (st.goto (.cLabels l tc body (s :: labels)))
    else st.fail s!"invalid label '{s}' in compressed proof of '{l}'"
  | .cLetters l tc body labels letters =>
    if isLetterToken s then .ok (st.goto (.cLetters l tc body labels (s :: letters)))
    else st.fail s!"invalid compressed proof block '{s}' in '{l}'"
  | .incl => .ok (st.goto (.inclFile s))
  | .inclFile _ => st.fail s!"expected $] after file name, found '{s}'"

/-- A keyword token. -/
def stepKw (st : ParseState) (k : Keyword) : Except ParseError ParseState :=
  match st.mode, k with
  | .top, .c => .ok (st.goto (.decl .c []))
  | .top, .v => .ok (st.goto (.decl .v []))
  | .top, .d => .ok (st.goto (.decl .d []))
  | .top, .openScope => .ok (st.emit .openScope)
  | .top, .closeScope => .ok (st.emit .closeScope)
  | .top, .openInclude => .ok (st.goto .incl)
  | .decl .c acc, .stop =>
    if acc.isEmpty then st.fail "empty $c statement" else .ok (st.emit (.constants acc.reverse))
  | .decl .v acc, .stop =>
    if acc.isEmpty then st.fail "empty $v statement" else .ok (st.emit (.variables acc.reverse))
  | .decl .d acc, .stop =>
    if acc.length < 2 then st.fail "$d statement with fewer than two variables"
    else .ok (st.emit (.disjoint acc.reverse))
  | .label l, .f => .ok (st.goto (.float l []))
  | .label l, .e => .ok (st.goto (.expr .e l []))
  | .label l, .a => .ok (st.goto (.expr .a l []))
  | .label l, .p => .ok (st.goto (.expr .p l []))
  | .float l [v, tc], .stop => .ok (st.emit (.floating l tc v))
  | .expr .e l acc, .stop =>
    match acc.reverse with
    | tc :: body => .ok (st.emit (.essential l tc body))
    | [] => st.fail s!"missing typecode in '{l}'"
  | .expr .a l acc, .stop =>
    match acc.reverse with
    | tc :: body => .ok (st.emit (.axiom l tc body))
    | [] => st.fail s!"missing typecode in '{l}'"
  | .expr .p l acc, .eq =>
    match acc.reverse with
    | tc :: body => .ok (st.goto (.proofStart l tc body))
    | [] => st.fail s!"missing typecode in '{l}'"
  | .proofStart l tc body, .stop => .ok (st.emit (.provable l tc body (.normal [])))
  | .normal l tc body steps, .stop =>
    .ok (st.emit (.provable l tc body (.normal steps.reverse)))
  | .cLetters l tc body labels letters, .stop =>
    .ok (st.emit (.provable l tc body (.compressed labels.reverse (String.join letters.reverse))))
  | .inclFile f, .closeInclude => .ok (st.emit (.include f))
  | _, k => st.fail s!"unexpected keyword {k}"

/-- One step of the parser automaton. -/
def step (st : ParseState) : Token → Except ParseError ParseState
  | .comment text =>
    match st.mode with
    | .top => .ok ⟨.comment text :: st.stmts, .top, []⟩
    | _ => .ok { st with pending := text :: st.pending }
  | .kw k => st.stepKw k
  | .sym s => st.stepSym s

/-- End of input. -/
def finish (st : ParseState) : Except ParseError Source :=
  match st.mode with
  | .top => .ok st.stmts.reverse
  | _ => st.fail "unterminated statement at end of file"

end ParseState

/-- The parser step on a possibly failed state. -/
def parseStep (st : Except ParseError ParseState) (t : Token) : Except ParseError ParseState :=
  st.bind (·.step t)

/-- Parse a token list. -/
def parseTokens (ts : List Token) : Except ParseError Source :=
  (ts.foldl parseStep (.ok .init)).bind ParseState.finish

/-- A lexical or syntax error. -/
inductive Error where
  | lex (e : LexError)
  | parse (e : ParseError)
  deriving DecidableEq, Repr, Inhabited

instance : ToString Error where
  toString
    | .lex e => s!"lexical error: {repr e}"
    | .parse e => s!"syntax error {e}"

/-- Parse a Metamath source text. -/
def parse (s : String) : Except Error Source :=
  match lex s with
  | .error e => .error (.lex e)
  | .ok ts => (parseTokens ts).mapError .parse

/-- Parse a Metamath source given as characters. -/
def parseChars (l : List Char) : Except Error Source :=
  match lexChars l with
  | .error e => .error (.lex e)
  | .ok ts => (parseTokens ts).mapError .parse

theorem parse_eq_parseChars (s : String) : parse s = parseChars s.toList := by
  simp [parse, parseChars, lex_eq_lexChars]

end Silmaril.Logic.Metamath.Text
