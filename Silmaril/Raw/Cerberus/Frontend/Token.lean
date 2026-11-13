module

public import Silmaril.Cerberus.Cabs.Syntax.Defs

/-! # Tokens of the Cerberus C lexer

The tokens of `parsers/c/tokens.ml` that the C grammar uses, as `c_lexer.mll` produces
them (`docs/projects/cerberus.md`). `LNAME` and `UNAME` are one constructor `name`:
the C grammar treats them alike (`%inline NAME`, `c_parser.mly:436-441`). The
`TYPE`/`VARIABLE` token that the lexer hack emits after a name is not a token here: the
parser asks `TypedefEnv` when it looks at a name, which is when Menhir would read that
token. CN-only tokens are absent, except `CN_CONSTANT`, which the lexer produces even
outside CN (`1u8`), so that the parser can reject it.

A position is what `C_lexer.LineMap.position` makes of a `Lexing.position`: the source
file and line from the linemarkers, and the 1-based byte column in the preprocessed text.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend

open Silmaril.Cerberus

/-- The keywords of the lexicon (`c_lexer.mll:61-125`). Constructor names follow the
Menhir tokens. -/
inductive Keyword where
  | auto | break_ | case_ | char | const | continue_ | default | do_ | double | else_
  | enum | extern_ | float | for_ | goto | if_ | inline | int | long | register
  | restrict | return_ | short | signed | sizeof | static | struct | switch | typedef
  | typeof | union | unsigned | void | volatile | while_
  | alignas | alignof | atomic | bool | complex | generic | noreturn | staticAssert
  | threadLocal
  | assert | offsetof | vaStart | vaCopy | vaArg | vaEnd | printType | bmcAssume
  /-- `asm` and `__asm__`. -/
  | asm
  /-- `__volatile__`. -/
  | asmVolatile
  | builtinTypesCompatibleP | builtinChooseExpr
  deriving DecidableEq, Repr, Inhabited

/-- Punctuators (STD §6.4.6) and the non-standard tokens of `c_lexer.mll:590-656`.
Digraphs are their standard tokens. -/
inductive Punct where
  | lbrack | rbrack | lparen | rparen | lbrace | rbrace | dot | minusGt
  | plusPlus | minusMinus | ampersand | star | plus | minus | tilde | bang
  | slash | percent | ltLt | gtGt | lt | gt | ltEq | gtEq | eqEq | bangEq
  | caret | pipe | ampersandAmpersand | pipePipe | question | colonColon | colon
  | semicolon | ellipsis | eq | starEq | slashEq | percentEq | plusEq | minusEq
  | ltLtEq | gtGtEq | ampersandEq | caretEq | pipeEq | comma
  /-- `[` whitespace* `[` (`c_lexer.mll:442`); `]]` stays two `rbrack`s. -/
  | lbrackLbrack
  /-- The GNU `?:`, only as adjacent characters (`c_lexer.mll:651`). -/
  | questionColon
  /-- cppmem `{-{`, `|||` and `}-}`. -/
  | lbraces | pipes | rbraces
  deriving DecidableEq, Repr, Inhabited

/-- What a token is. -/
inductive TokenKind where
  /-- `LNAME` or `UNAME`: an identifier that is not a keyword. -/
  | name (text : String)
  | keyword (k : Keyword)
  | punct (p : Punct)
  | constant (c : Cabs.Constant)
  /-- `STRING_LITERAL`: the prefix and the s-char lexemes, undecoded. -/
  | string (pfx : Option Cabs.EncodingPrefix) (lexemes : Array Cabs.RawString)
  /-- `CN_CONSTANT` (`1u8`, `2i32`): never part of a C parse. -/
  | cnConstant
  | eof
  deriving Inhabited

/-- A position: source file and line after the linemarkers, and the 1-based byte column
in the preprocessed text (`Cerb_position.column`). -/
structure Pos where
  file : String
  line : Int
  column : Int
  deriving Inhabited, DecidableEq, Repr

/-- A token with its `$startpos` and `$endpos`. -/
structure Token where
  kind : TokenKind
  start : Pos
  stop : Pos
  deriving Inhabited

/-- `Cerb_location.point`. -/
def Pos.point (p : Pos) : Loc := .point p.file p.line p.column

/-- `Cerb_location.region (p, q) _`; the wire format drops the cursor. -/
def Pos.region (p q : Pos) : Loc := .region p.file p.line p.column q.file q.line q.column

end Silmaril.Cerberus.Frontend
