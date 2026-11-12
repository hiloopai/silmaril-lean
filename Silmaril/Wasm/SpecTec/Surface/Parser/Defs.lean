module

public import Silmaril.Wasm.SpecTec.Surface.Syntax.Defs

/-!
# SpecTec surface syntax: the parser

The productions of `specs/spectec/src/spectec/src/frontend/parser.mly` that
the fragment uses, as relations, and a recursive-descent parser for them.

## Grammar relations

Each nonterminal `N` is a relation `N ts x r`: the tokens `ts` start with a
phrase of `N` whose semantic value is `x`, and `r` is what follows. Operator
precedence and associativity (`parser.mly:180-211`) are not modelled: an
expression has at most one binary operator outside parentheses, which is all
the fragment needs. The relations are permissive where the parser
disambiguates (for instance, they do not say where a juxtaposition stops);
`parse?_sound` only claims that what `parse?` returns is a derivation.

## Declarations by span

A script is cut into declarations at the tokens that start one
(`syntax`, `grammar`, `relation`, `rule`, `var`, `def`, `NL_NL_NL`) outside
brackets (`splitSpan`). A span is parsed as a supported declaration only if
the whole span parses (up to trailing `NL_NL`, `parser.mly:1143`); otherwise
it is kept as `Def.unsupported`. So a declaration outside the fragment is
skipped, never read as a prefix of something else. This span rule is ours,
not `parser.mly`'s.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Parser

open Silmaril.Wasm.SpecTec.Surface.Lexer (Token)
open Silmaril.Wasm.SpecTec.Surface.Syntax

/-! ## Token classes -/

/-- `iter` (`parser.mly:478-484`). -/
def iterOf : Token → Option Iter
  | .sym "?" => some .opt
  | .sym "*" => some .list
  | .sym "+" => some .list1
  | _ => none

/-- `cmpop` (`parser.mly:406-412`). -/
def cmpOf : Token → Option CmpOp
  | .sym "=" => some .eq
  | .sym "=/=" => some .ne
  | .sym "<" => some .lt
  | .sym ">" => some .gt
  | .sym "<=" => some .le
  | .sym ">=" => some .ge
  | _ => none

/-- `binop` (`parser.mly:399-404`). -/
def binOf : Token → Option BinOp
  | .sym "+" => some .add
  | .sym "-" => some .sub
  | .sym "*" => some .mul
  | .sym "/" => some .div
  | .sym "\\" => some .mod
  | _ => none

/-- `numtyp` and the other type keywords of `typ_prim_`
(`parser.mly:492-505`). -/
def typKwOf : Token → Option Typ
  | .sym "bool" => some .bool
  | .sym "nat" => some (.num .nat)
  | .sym "int" => some (.num .int)
  | .sym "rat" => some (.num .rat)
  | .sym "real" => some (.num .real)
  | .sym "text" => some .text
  | _ => none

/-- The type keywords read as variables by `exp_var_`
(`parser.mly:679-688`). -/
def typKwNames : List String := ["bool", "nat", "int", "rat", "real", "text"]

/-- One operator: a comparison or an arithmetic operator. -/
inductive Op where
  | cmp (op : CmpOp)
  | bin (op : BinOp)

/-- Apply an operator. -/
def Op.apply : Op → Exp → Exp → Exp
  | .cmp op => .cmp op
  | .bin op => .bin op

/-! ## Grammar relations -/

mutual

/-- `exp_prim_` (`parser.mly:702-729`), the fragment. -/
inductive ExpPrim : List Token → Exp → List Token → Prop where
  /-- `varid` (`parser.mly:680`). -/
  | var {x : List Char} {r : List Token} : ExpPrim (.id x :: r) (.var x []) r
  /-- A type keyword as a variable (`parser.mly:682-687`). -/
  | typKw {k : String} {r : List Token} : k ∈ typKwNames → ExpPrim (.sym k :: r) (.var k.toList []) r
  /-- `varid_lparen comma_list(arg) RPAREN` (`parser.mly:681`). -/
  | app {x : List Char} {r r' : List Token} {as : List Exp} :
      Args r as (.sym ")" :: r') → ExpPrim (.idParen x :: r) (.var x as) r'
  /-- `NATLIT` (`parser.mly:673`). -/
  | nat {s : List Char} {r : List Token} : ExpPrim (.nat s :: r) (.nat s) r
  /-- `DOLLAR defid` (`parser.mly:691`). -/
  | call0 {f : List Char} {r : List Token} : ExpPrim (.sym "$" :: .id f :: r) (.call f []) r
  /-- `DOLLAR defid_lparen comma_list(arg) RPAREN` (`parser.mly:692`). -/
  | call {f : List Char} {r r' : List Token} {as : List Exp} :
      Args r as (.sym ")" :: r') → ExpPrim (.sym "$" :: .idParen f :: r) (.call f as) r'
  /-- `DOLLAR LPAREN arith RPAREN` (`parser.mly:727`): the arithmetic escape
  leaves no node. -/
  | arith {e : Exp} {r r' : List Token} :
      Arith r e (.sym ")" :: r') → ExpPrim (.sym "$" :: .sym "(" :: r) e r'
  /-- `EPS` (`parser.mly:707`). -/
  | eps {r : List Token} : ExpPrim (.sym "eps" :: r) .eps r
  /-- `LPAREN comma_list(exp_rel) RPAREN` with one element (`parser.mly:709-713`). -/
  | paren {e : Exp} {r r' : List Token} :
      ExpE r e (.sym ")" :: r') → ExpPrim (.sym "(" :: r) (.paren e) r'

/-- `exp_post_` (`parser.mly:731-738`): a primary and its iterations
(`exp_atom iter`, `parser.mly:737`). -/
inductive ExpPost : List Token → Exp → List Token → Prop where
  | prim {ts r : List Token} {e : Exp} : ExpPrim ts e r → ExpPost ts e r
  | iter {ts r : List Token} {t : Token} {e : Exp} {it : Iter} :
      ExpPost ts e (t :: r) → iterOf t = some it → ExpPost ts (.iter e it) r

/-- `exp_seq_` (`parser.mly:761-765`): one or more juxtaposed atoms. -/
inductive ExpSeq : List Token → List Exp → List Token → Prop where
  | one {ts r : List Token} {e : Exp} : ExpPost ts e r → ExpSeq ts [e] r
  | cons {ts r r' : List Token} {e : Exp} {es : List Exp} :
      ExpPost ts e r → ExpSeq r es r' → ExpSeq ts (e :: es) r'

/-- `exp` down to `exp_bin_` (`parser.mly:787-795`): a juxtaposition, or two
joined by a comparison (`exp_bin cmpop exp_bin`, `parser.mly:792`). -/
inductive ExpE : List Token → Exp → List Token → Prop where
  | seq {ts r : List Token} {es : List Exp} : ExpSeq ts es r → ExpE ts (.ofSeq es) r
  | cmp {ts r r' : List Token} {t : Token} {es es' : List Exp} {op : CmpOp} :
      ExpSeq ts es (t :: r) → cmpOf t = some op → ExpSeq r es' r' →
      ExpE ts (.cmp op (.ofSeq es) (.ofSeq es')) r'

/-- `arith_prim_` (`parser.mly:826-847`), the fragment. -/
inductive ArithPrim : List Token → Exp → List Token → Prop where
  /-- `exp_lit_`, `exp_var_`, `exp_call_` (`parser.mly:827-829`). -/
  | exp {ts r : List Token} {e : Exp} : ExpPrim ts e r → ArithPrim ts e r

/-- `arith_bin_` (`parser.mly:870-877`): a primary, or two joined by an
arithmetic or comparison operator. -/
inductive Arith : List Token → Exp → List Token → Prop where
  | one {ts r : List Token} {e : Exp} : ArithPrim ts e r → Arith ts e r
  | cmp {ts r r' : List Token} {t : Token} {e e' : Exp} {op : CmpOp} :
      ArithPrim ts e (t :: r) → cmpOf t = some op → ArithPrim r e' r' →
      Arith ts (.cmp op e e') r'
  | bin {ts r r' : List Token} {t : Token} {e e' : Exp} {op : BinOp} :
      ArithPrim ts e (t :: r) → binOf t = some op → ArithPrim r e' r' →
      Arith ts (.bin op e e') r'

/-- `comma_list(arg)` (`parser.mly:232-235`) with `arg_ : exp_bin`
(`parser.mly:1117`). -/
inductive Args : List Token → List Exp → List Token → Prop where
  | nil {ts : List Token} : Args ts [] ts
  | one {ts r : List Token} {e : Exp} : ExpE ts e r → Args ts [e] r
  | cons {ts r r' : List Token} {e : Exp} {es : List Exp} :
      ExpE ts e (.sym "," :: r) → Args r es r' → Args ts (e :: es) r'

end

/-- `typ_prim_` and `typ_post_` (`parser.mly:499-512`), without tuples. -/
inductive TypP : List Token → Typ → List Token → Prop where
  | var {x : List Char} {r : List Token} : TypP (.id x :: r) (.var x []) r
  | app {x : List Char} {r r' : List Token} {as : List Exp} :
      Args r as (.sym ")" :: r') → TypP (.idParen x :: r) (.var x as) r'
  | kw {t : Token} {ty : Typ} {r : List Token} : typKwOf t = some ty → TypP (t :: r) ty r
  | iter {ts r : List Token} {t : Token} {ty : Typ} {it : Iter} :
      TypP ts ty (t :: r) → iterOf t = some it → TypP ts (.iter ty it) r

/-- Tokens that open a bracket. -/
def opens : Token → Bool
  | .sym "(" | .sym "[" | .sym "{" | .sym "hint(" | .idParen _ | .tickIdParen _ => true
  | _ => false

/-- Tokens that close a bracket. -/
def closes : Token → Bool
  | .sym ")" | .sym "]" | .sym "}" => true
  | _ => false

/-- The tokens up to the `)` that closes an already open parenthesis, nested
by depth `d`. Square brackets and braces are not allowed inside. -/
inductive Balanced : Nat → List Token → List Token → List Token → Prop where
  | close {r : List Token} : Balanced 0 (.sym ")" :: r) [] r
  | closeIn {d : Nat} {r b r' : List Token} :
      Balanced d r b r' → Balanced (d + 1) (.sym ")" :: r) (.sym ")" :: b) r'
  | openP {d : Nat} {t : Token} {r b r' : List Token} :
      opens t → t ≠ .sym "[" → t ≠ .sym "{" →
      Balanced (d + 1) r b r' → Balanced d (t :: r) (t :: b) r'
  | other {d : Nat} {t : Token} {r b r' : List Token} :
      opens t = false → closes t = false → Balanced d r b r' → Balanced d (t :: r) (t :: b) r'

/-- `hint*` (`parser.mly:1219-1223`), each hint's expression kept as raw
tokens. -/
inductive Hints : List Token → List Hint → List Token → Prop where
  | nil {ts : List Token} : Hints ts [] ts
  | cons {x : List Char} {r b r' r'' : List Token} {hs : List Hint} :
      Balanced 0 r b r' → Hints r' hs r'' →
      Hints (.sym "hint(" :: .id x :: r) (⟨x, b⟩ :: hs) r''

/-- `nl_dash_list(prem)` (`parser.mly:247-253`) with `prem_ : OTHERWISE | IF exp`
(`parser.mly:903`, `parser.mly:928`), without the `-- --` line breaks. -/
inductive Prems : List Token → List Prem → List Token → Prop where
  | nil {ts : List Token} : Prems ts [] ts
  | otherwise {r r' : List Token} {ps : List Prem} :
      Prems r ps r' → Prems (.sym "--" :: .sym "otherwise" :: r) (.otherwise :: ps) r'
  | ifP {r r' r'' : List Token} {e : Exp} {ps : List Prem} :
      ExpE r e r' → Prems r' ps r'' → Prems (.sym "--" :: .sym "if" :: r) (.ifP e :: ps) r''

/-- Only `NL_NL` tokens: the `def_ NL_NL*` of `parser.mly:1143`. -/
def AllNl (ts : List Token) : Prop := ∀ t ∈ ts, t = .nlNl

/-- A whole supported declaration (`def_`, `parser.mly:1144-1186`), with its
trailing `NL_NL*` (`parser.mly:1143`). -/
inductive DefP : List Token → Def → Prop where
  /-- `SYNTAX varid_bind hint* EQ deftyp` with a plain type
  (`parser.mly:1147`), no rule identifiers. -/
  | syntaxAlias {x : List Char} {r r' r'' : List Token} {hs : List Hint} {t : Typ} :
      Hints r hs (.sym "=" :: r') → TypP r' t r'' → AllNl r'' →
      DefP (.sym "syntax" :: .id x :: r) (.syntaxAlias x hs t)
  /-- `DEF DOLLAR defid_lparen comma_list(arg) RPAREN COLON typ hint*`
  (`parser.mly:1179-1180`). -/
  | decSig {x : List Char} {r r' r'' r''' : List Token} {as : List Exp} {t : Typ}
      {hs : List Hint} :
      Args r as (.sym ")" :: .sym ":" :: r') → TypP r' t r'' → Hints r'' hs r''' → AllNl r''' →
      DefP (.sym "def" :: .sym "$" :: .idParen x :: r) (.decSig x as t hs)
  /-- `DEF DOLLAR defid COLON typ hint*` (`parser.mly:1177-1178`). -/
  | decSig0 {x : List Char} {r' r'' r''' : List Token} {t : Typ} {hs : List Hint} :
      TypP r' t r'' → Hints r'' hs r''' → AllNl r''' →
      DefP (.sym "def" :: .sym "$" :: .id x :: .sym ":" :: r') (.decSig x [] t hs)
  /-- `DEF DOLLAR defid_lparen comma_list(arg) RPAREN EQ exp prem_list`
  (`parser.mly:1183-1184`). -/
  | decClause {x : List Char} {r r' r'' r''' : List Token} {as : List Exp} {e : Exp}
      {ps : List Prem} :
      Args r as (.sym ")" :: .sym "=" :: r') → ExpE r' e r'' → Prems r'' ps r''' → AllNl r''' →
      DefP (.sym "def" :: .sym "$" :: .idParen x :: r) (.decClause x as e ps)
  /-- `DEF DOLLAR defid EQ exp prem_list` (`parser.mly:1181-1182`). -/
  | decClause0 {x : List Char} {r' r'' r''' : List Token} {e : Exp} {ps : List Prem} :
      ExpE r' e r'' → Prems r'' ps r''' → AllNl r''' →
      DefP (.sym "def" :: .sym "$" :: .id x :: .sym "=" :: r') (.decClause x [] e ps)

/-- A grammar whose right-hand side is one symbol `g(args)`: `GRAMMAR
varid_bind COLON typ hint* EQ gram` (`parser.mly:1153`) with a single short
production (`parser.mly:136-139`). -/
inductive GramAliasP : List Token → Def → Prop where
  | mk {x g : List Char} {r1 r2 r3 r4 : List Token} {t : Typ} {hs : List Hint}
      {as : List Exp} :
      TypP r1 t r2 → Hints r2 hs (.sym "=" :: .idParen g :: r3) →
      Args r3 as (.sym ")" :: r4) → AllNl r4 →
      GramAliasP (.sym "grammar" :: .id x :: .sym ":" :: r1) (.gramAlias x t hs g as)

/-- A whole supported declaration: `DefP` or a grammar alias. -/
inductive DeclP : List Token → Def → Prop where
  | defP {ts : List Token} {d : Def} : DefP ts d → DeclP ts d
  | gramAlias {ts : List Token} {d : Def} : GramAliasP ts d → DeclP ts d

/-! ## Declaration spans -/

/-- Tokens that start a declaration (`def_`, `parser.mly:1144-1218`). -/
def startsDecl : Token → Bool
  | .sym "syntax" | .sym "grammar" | .sym "relation" | .sym "rule" | .sym "var" | .sym "def" => true
  | .nlNlNl => true
  | _ => false

/-- The tokens up to the next declaration start outside brackets, and the
rest. -/
def takeSpan : Nat → List Token → List Token × List Token
  | _, [] => ([], [])
  | d, t :: ts =>
    if d = 0 && startsDecl t then ([], t :: ts)
    else
      let d' := if opens t then d + 1 else if closes t then d - 1 else d
      let (a, b) := takeSpan d' ts
      (t :: a, b)

/-- A declaration's span: its first token and everything up to the next
declaration start outside brackets. -/
def splitSpan : List Token → List Token × List Token
  | [] => ([], [])
  | .nlNlNl :: ts => ([.nlNlNl], ts)
  | t :: ts =>
    let (a, b) := takeSpan 0 ts
    (t :: a, b)

/-- A script (`script : NL_NL* def* EOF`, `parser.mly:1228-1229`), cut into
declaration spans. -/
inductive Parses : List Token → List Def → Prop where
  | nil : Parses [] []
  /-- `NL_NL` between declarations (`parser.mly:1143,1229`). -/
  | nl {r : List Token} {ds : List Def} : Parses r ds → Parses (.nlNl :: r) ds
  /-- `NL_NL_NL` is `SepD` (`parser.mly:1185-1186`). -/
  | sep {r : List Token} {ds : List Def} : Parses r ds → Parses (.nlNlNl :: r) (.sep :: ds)
  /-- A supported declaration spanning `sp`. -/
  | decl {ts sp r : List Token} {d : Def} {ds : List Def} :
      splitSpan ts = (sp, r) → DeclP sp d → Parses r ds → Parses ts (d :: ds)
  /-- A declaration outside the fragment, kept as its span. -/
  | skip {ts sp r : List Token} {ds : List Def} :
      splitSpan ts = (sp, r) → sp ≠ [] → Parses r ds → Parses ts (.unsupported sp :: ds)

/-! ## The parser -/

/-- Tokens that can start an `exp_prim_` of the fragment, which is where a
juxtaposition continues. -/
def startsPrim : Token → Bool
  | .id _ | .idParen _ | .nat _ | .sym "$" | .sym "eps" | .sym "(" => true
  | .sym k => typKwNames.contains k
  | _ => false

/-- The iterations after a primary (`exp_atom iter`). -/
def pIters (e : Exp) : List Token → Exp × List Token
  | t :: r =>
    match iterOf t with
    | some it => pIters (.iter e it) r
    | none => (e, t :: r)
  | [] => (e, [])

/-- A phrase followed by `)`, mapped through `f`. -/
def closeP {α β : Type} (f : α → β) : Option (α × List Token) → Option (β × List Token)
  | some (a, .sym ")" :: r) => some (f a, r)
  | _ => none

/-- Parsers for the five expression nonterminals, at some fuel. -/
abbrev PFun (α : Type) := List Token → Option (α × List Token)

/-- `exp_prim_`, given parsers for its sub-phrases. -/
def primStep (args : PFun (List Exp)) (arith exp : PFun Exp) : PFun Exp
  | .id x :: r => some (.var x [], r)
  | .idParen x :: r => closeP (.var x) (args r)
  | .nat s :: r => some (.nat s, r)
  | .sym "$" :: .id f :: r => some (.call f [], r)
  | .sym "$" :: .idParen f :: r => closeP (.call f) (args r)
  | .sym "$" :: .sym "(" :: r => closeP id (arith r)
  | .sym "eps" :: r => some (.eps, r)
  | .sym "(" :: r => closeP .paren (exp r)
  | .sym k :: r => if k ∈ typKwNames then some (.var k.toList [], r) else none
  | _ => none

/-- `exp_seq_`: juxtaposed `exp_post_`s, continued while the next token can
start a primary. -/
def seqStep (prim : PFun Exp) (seq : PFun (List Exp)) (ts : List Token) :
    Option (List Exp × List Token) :=
  match prim ts with
  | none => none
  | some (e, r) =>
    let (e', r') := pIters e r
    if r'.head?.map startsPrim = some true then
      match seq r' with
      | some (es, r'') => some (e' :: es, r'')
      | none => some ([e'], r')
    else some ([e'], r')

/-- `exp`: a juxtaposition, optionally compared with another. -/
def expStep (seq : PFun (List Exp)) (ts : List Token) : Option (Exp × List Token) :=
  match seq ts with
  | none => none
  | some (es, []) => some (.ofSeq es, [])
  | some (es, t :: r) =>
    match cmpOf t with
    | some op => (seq r).map fun (es', r') => (.cmp op (.ofSeq es) (.ofSeq es'), r')
    | none => some (.ofSeq es, t :: r)

/-- `arith`: a primary, optionally combined with another by an operator. -/
def arithStep (prim : PFun Exp) (ts : List Token) : Option (Exp × List Token) :=
  match prim ts with
  | none => none
  | some (e, []) => some (e, [])
  | some (e, t :: r) =>
    match cmpOf t, binOf t with
    | some op, _ => (prim r).map fun (e', r') => (.cmp op e e', r')
    | none, some op => (prim r).map fun (e', r') => (.bin op e e', r')
    | none, none => some (e, t :: r)

/-- `comma_list(arg)`, stopping before `)`. -/
def argsStep (exp : PFun Exp) (args : PFun (List Exp)) : PFun (List Exp)
  | .sym ")" :: r => some ([], .sym ")" :: r)
  | ts =>
    match exp ts with
    | some (e, .sym "," :: r) => (args r).map fun (es, r') => (e :: es, r')
    | some (e, r) => some ([e], r)
    | none => none

mutual

/-- `exp_prim_`. -/
def pPrim : Nat → PFun Exp
  | 0, _ => none
  | n + 1, ts => primStep (pArgs n) (pArith n) (pExp n) ts

/-- `exp_seq_`. -/
def pSeq : Nat → PFun (List Exp)
  | 0, _ => none
  | n + 1, ts => seqStep (pPrim n) (pSeq n) ts

/-- `exp`. -/
def pExp : Nat → PFun Exp
  | 0, _ => none
  | n + 1, ts => expStep (pSeq n) ts

/-- `arith`. -/
def pArith : Nat → PFun Exp
  | 0, _ => none
  | n + 1, ts => arithStep (pPrim n) ts

/-- `comma_list(arg)`. -/
def pArgs : Nat → PFun (List Exp)
  | 0, _ => none
  | n + 1, ts => argsStep (pExp n) (pArgs n) ts

end

/-- The iterations after a type. -/
def pTypIters (ty : Typ) : List Token → Typ × List Token
  | t :: r =>
    match iterOf t with
    | some it => pTypIters (.iter ty it) r
    | none => (ty, t :: r)
  | [] => (ty, [])

/-- `typ`. -/
def pTyp (n : Nat) : List Token → Option (Typ × List Token)
  | .id x :: r => some (pTypIters (.var x []) r)
  | .idParen x :: r => (closeP (.var x) (pArgs n r)).map fun (ty, r') => pTypIters ty r'
  | t :: r =>
    match typKwOf t with
    | some ty => some (pTypIters ty r)
    | none => none
  | [] => none

/-- The tokens of a hint up to its closing `)`. -/
def pBalanced : Nat → List Token → Option (List Token × List Token)
  | 0, .sym ")" :: r => some ([], r)
  | d + 1, .sym ")" :: r => (pBalanced d r).map fun (b, r') => (.sym ")" :: b, r')
  | d, t :: r =>
    if opens t && !(t == .sym "[" || t == .sym "{") then
      (pBalanced (d + 1) r).map fun (b, r') => (t :: b, r')
    else if t == .sym "[" || t == .sym "{" || closes t then none
    else (pBalanced d r).map fun (b, r') => (t :: b, r')
  | _, [] => none

/-- `prem_list`: `-- otherwise` and `-- if exp`. -/
def pPrems : Nat → List Token → Option (List Prem × List Token)
  | n + 1, .sym "--" :: .sym "otherwise" :: r =>
    (pPrems n r).map fun (ps, r') => (.otherwise :: ps, r')
  | n + 1, .sym "--" :: .sym "if" :: r =>
    match pExp n r with
    | some (e, r') => (pPrems n r').map fun (ps, r'') => (.ifP e :: ps, r'')
    | none => none
  | _, ts => some ([], ts)

/-- `hint*`. -/
def pHints : Nat → List Token → List Hint × List Token
  | n + 1, .sym "hint(" :: .id x :: r =>
    match pBalanced 0 r with
    | some (b, r') =>
      let (hs, r'') := pHints n r'
      (⟨x, b⟩ :: hs, r'')
    | none => ([], .sym "hint(" :: .id x :: r)
  | _, ts => ([], ts)

/-- Only `NL_NL` tokens remain. -/
def allNl (ts : List Token) : Bool := ts.all (· == .nlNl)

/-- `typ hint*` and the end of the span, for a `def` signature. -/
def pSigRest (n : Nat) (x : List Char) (as : List Exp) (r : List Token) : Option Def :=
  match pTyp n r with
  | some (t, r') =>
    let (hs, r'') := pHints n r'
    if allNl r'' then some (.decSig x as t hs) else none
  | none => none

/-- `exp prem_list` and the end of the span, for a `def` clause. -/
def pClauseRest (n : Nat) (x : List Char) (as : List Exp) (r : List Token) : Option Def :=
  match pExp n r with
  | some (e, r') =>
    match pPrems n r' with
    | some (ps, r'') => if allNl r'' then some (.decClause x as e ps) else none
    | none => none
  | none => none

/-- `typ hint* = g(args)` and the end of the span, for a grammar alias. -/
def pGramRest (n : Nat) (x : List Char) (r : List Token) : Option Def :=
  match pTyp n r with
  | some (t, r1) =>
    match pHints n r1 with
    | (hs, .sym "=" :: .idParen g :: r2) =>
      match pArgs n r2 with
      | some (as, .sym ")" :: r3) => if allNl r3 then some (.gramAlias x t hs g as) else none
      | _ => none
    | _ => none
  | none => none

/-- A whole declaration span, if it is in the fragment. -/
def pDef (n : Nat) : List Token → Option Def
  | .sym "syntax" :: .id x :: r =>
    match pHints n r with
    | (hs, .sym "=" :: r') =>
      match pTyp n r' with
      | some (t, r'') => if allNl r'' then some (.syntaxAlias x hs t) else none
      | none => none
    | _ => none
  | .sym "def" :: .sym "$" :: .idParen x :: r =>
    match pArgs n r with
    | some (as, .sym ")" :: .sym ":" :: r') => pSigRest n x as r'
    | some (as, .sym ")" :: .sym "=" :: r') => pClauseRest n x as r'
    | _ => none
  | .sym "def" :: .sym "$" :: .id x :: .sym ":" :: r' => pSigRest n x [] r'
  | .sym "def" :: .sym "$" :: .id x :: .sym "=" :: r' => pClauseRest n x [] r'
  | .sym "grammar" :: .id x :: .sym ":" :: r' => pGramRest n x r'
  | _ => none

/-- Declarations until the tokens run out; `n` bounds the number of spans. -/
def parseList : Nat → List Token → Option (List Def)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, .nlNl :: r => parseList n r
  | n + 1, .nlNlNl :: r => (parseList n r).map (.sep :: ·)
  | n + 1, t :: ts =>
    let (sp, r) := splitSpan (t :: ts)
    if sp = [] then none else
    match pDef (sp.length + 1) sp with
    | some d => (parseList n r).map (d :: ·)
    | none => (parseList n r).map (.unsupported sp :: ·)

/-- The parser: a script's tokens to declarations of the fragment, with every
other declaration kept as `Def.unsupported`. -/
def parse? (ts : List Token) : Option (List Def) := parseList (ts.length + 1) ts

end Silmaril.Wasm.SpecTec.Surface.Parser
