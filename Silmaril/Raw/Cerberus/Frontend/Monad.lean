module

public import Silmaril.Cerberus.Cabs.Codec.Defs
public import Silmaril.Cerberus.Frontend.Token.Defs
public import Silmaril.Cerberus.Frontend.TypedefEnv.Defs

/-! # The parser monad and the recursion knot

The parser is a recursive descent over the token array, one function per nonterminal of
`c_parser.mly`. Its state is the position in the token array, the typedef names in scope
(`Lexer_feedback.current`) and the end of the last consumed token, which is Menhir's
`$startpos` of a production that starts with an empty symbol (gotcha 3 of
`docs/projects/cerberus.md`).

The grammar is mutually recursive across files (expressions contain type names,
declarators contain expressions, statement expressions contain declarations). Each file
takes a `Rec`, the record of the nonterminals it calls recursively, and never calls
itself directly; `Frontend.Grammar.knot` ties the record with a depth bound. So every
definition is total and each part of the grammar lives in its own file.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus Cabs

/-- The parser state. -/
structure PState where
  toks : Array Token
  /-- The index of the next token; the last token is `eof`. -/
  index : Nat
  env : TypedefEnv
  /-- `$endpos` of the last consumed token. -/
  prevEnd : Pos

/-- The parser monad: a rejection at the stage `parse`, or a value and a new state. -/
abbrev P := StateT PState (Except Codec.Reject)

/-- How a declarator is parsed: `declarator` (with an identifier), `abstract_declarator`
(without), or either, as in a parameter declaration. -/
inductive DeclMode where
  | concrete
  | abstract
  | either
  deriving DecidableEq

/-- Which specifier list is parsed: `declaration_specifiers` with or without `typedef`
(`_typedef`), or `specifier_qualifier_list`. -/
inductive SpecMode where
  | declaration
  | parameter
  | specQual
  deriving DecidableEq

/-- `Lexer_feedback.decl_sort`: what the outermost part of a declarator is. A function
declarator carries the context saved after its parameters, which a function definition
reinstalls for its body. `pointer_decl` overwrites the sort, so `int *f(int x) {…}` does
not reinstall it. -/
inductive DeclSort where
  | ident
  | fn (ctxt : TypedefEnv)
  | fnIds (ctxt : TypedefEnv) (ids : List Identifier)
  | ptr (p : PointerDeclarator)
  | other

/-- `Lexer_feedback.declarator`: the declared name, the sort and the direct declarator. -/
structure Decl where
  name : String
  sort : DeclSort
  direct : DirectDeclarator

/-- `cabs_of_declarator`: the pointer part is kept only in the sort. -/
def Decl.toCabs (d : Decl) : Declarator :=
  match d.sort with
  | .ptr p => .mk (some p) d.direct
  | _ => .mk none d.direct

/-- A declarator, an abstract declarator, or nothing. -/
inductive AnyDecl where
  | concrete (d : Decl)
  | abstract (a : AbstractDeclarator)
  | none

/-- The nonterminals that the grammar files call across the recursion. -/
structure Rec where
  /-- `expression` (§6.5.17, the comma level). -/
  expression : P Expression
  /-- `assignment_expression` (§6.5.16). -/
  assignmentExpression : P Expression
  /-- `constant_expression`, i.e. `conditional_expression` (§6.6). -/
  constantExpression : P Expression
  /-- `unary_expression` (§6.5.3). -/
  unaryExpression : P Expression
  /-- `cast_expression` and whether it is also unary (§6.5.4). -/
  castExpression : P (Expression × Bool)
  /-- Binary expression at a minimum precedence (§6.5.5–14). -/
  binaryExpression : Nat → P (Expression × Bool)
  /-- `conditional_expression` and whether it is also unary (§6.5.15). -/
  conditionalExpression : P (Expression × Bool)
  /-- `type_name` (§6.7.7). -/
  typeName : P TypeName
  /-- `initializer_` (§6.7.9). -/
  initr : P Initializer
  /-- `compound_statement` (§6.8.2). -/
  compoundStatement : P Statement
  /-- `statement` (§6.8). -/
  statement : P Statement
  /-- `declarator`, `abstract_declarator`, or either (§6.7.6-7). -/
  declarator : DeclMode → P AnyDecl
  /-- `declaration_specifiers` or `specifier_qualifier_list` (§6.7), and whether it
  has `typedef`. -/
  specifiers : SpecMode → P (Specifiers × Bool)

namespace P

/-- The next token without consuming it. -/
@[inline] def peek : P Token := do
  let s ← get
  return s.toks[s.index]?.getD (s.toks.back?.getD default)

/-- The token `k` places ahead (`peekAt 0 = peek`). -/
@[inline] def peekAt (k : Nat) : P Token := do
  let s ← get
  return s.toks[s.index + k]?.getD (s.toks.back?.getD default)

/-- Consume and return the next token. -/
@[inline] def advance : P Token := do
  let s ← get
  let t := s.toks[s.index]?.getD (s.toks.back?.getD default)
  set { s with index := if s.index < s.toks.size then s.index + 1 else s.index, prevEnd := t.stop }
  return t

/-- Reject at the next token, as Menhir reports a syntax error at the region of the
lookahead token. -/
def fail {α : Type} (message : String) : P α := do
  let t ← peek
  throw ⟨"parse", t.start.region t.stop, message⟩

/-- `$startpos` of the next token. -/
@[inline] def startPos : P Pos := return (← peek).start

/-- `$endpos` of the last consumed token. -/
@[inline] def endPos : P Pos := return (← get).prevEnd

@[inline] def isPunct (t : Token) (p : Punct) : Bool :=
  match t.kind with
  | .punct q => q == p
  | _ => false

@[inline] def isKeyword (t : Token) (k : Keyword) : Bool :=
  match t.kind with
  | .keyword k' => k' == k
  | _ => false

/-- Whether the next token is the punctuator `p`. -/
@[inline] def atPunct (p : Punct) : P Bool := return isPunct (← peek) p

/-- Whether the next token is the keyword `k`. -/
@[inline] def atKeyword (k : Keyword) : P Bool := return isKeyword (← peek) k

/-- Consume the punctuator `p` if it is next. -/
def eatPunct (p : Punct) : P Bool := do
  if ← atPunct p then let _ ← advance; return true else return false

/-- Consume the punctuator `p`, or reject. -/
def expectPunct (p : Punct) : P Token := do
  if ← atPunct p then advance else fail s!"expected {repr p}"

/-- Consume the keyword `k`, or reject. -/
def expectKeyword (k : Keyword) : P Token := do
  if ← atKeyword k then advance else fail s!"expected {repr k}"

/-- The typedef names in scope (`save_context`). -/
@[inline] def env : P TypedefEnv := return (← get).env

/-- `restore_context`. -/
@[inline] def setEnv (e : TypedefEnv) : P Unit := modify fun s => { s with env := e }

/-- `declare_varname`. -/
def declareVar (x : String) : P Unit := modify fun s => { s with env := s.env.declareVar x }

/-- `declare_typedefname`. -/
def declareTypedef (x : String) : P Unit :=
  modify fun s => { s with env := s.env.declareTypedef x }

/-- If the token is a name: its text, and whether the lexer hack makes it `TYPE`. -/
def nameOf (t : Token) : P (Option (String × Bool)) := do
  match t.kind with
  | .name x => return some (x, (← env).isTypedef x)
  | _ => return none

/-- Repeat `p` while `cond` holds and collect the results. Every iteration of a grammar
list consumes a token, so the token count bounds the loop. -/
def manyWhile {α : Type} (cond : P Bool) (p : P α) : P (Array α) := do
  let mut acc := #[]
  for _ in [0:(← get).toks.size + 1] do
    if !(← cond) then break
    acc := acc.push (← p)
  return acc

/-- `p` followed by `(sep p)*`. -/
def sepBy1 {α : Type} (sep : Punct) (p : P α) : P (Array α) := do
  let x ← p
  let xs ← manyWhile (atPunct sep) (do let _ ← advance; p)
  return #[x] ++ xs

end P

/-- Every nonterminal of `Rec` rejecting: the knot at depth 0. -/
def Rec.exhausted : Rec :=
  let f {α : Type} : P α := P.fail "nesting too deep"
  ⟨f, f, f, f, f, fun _ => f, f, f, f, f, f, fun _ => f, fun _ => f⟩

end Silmaril.Cerberus.Frontend
