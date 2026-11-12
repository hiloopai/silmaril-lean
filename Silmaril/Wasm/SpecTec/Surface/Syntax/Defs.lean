module

public import Silmaril.Wasm.SpecTec.Surface.Lexer.Defs

/-!
# SpecTec surface syntax: the fragment's AST

A subset of SpecTec's external language `El.Ast`, as built by the semantic
actions of `specs/spectec/src/spectec/src/frontend/parser.mly`. Each
constructor cites the production that builds it. Declarations outside the
fragment are kept as `Def.unsupported`, by their token span, and are never
given a meaning.

Identifiers are `List Char` (the lexer's representation); the elaborator turns
them into `String`s.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Syntax

open Silmaril.Wasm.SpecTec.Surface.Lexer (Token)

/-- `iter` (`parser.mly:478-484`), without `^ arith`. -/
inductive Iter where
  /-- `QUEST` gives `Opt`. -/
  | opt
  /-- `STAR` gives `List`. -/
  | list
  /-- `PLUS` gives `List1`. -/
  | list1
  deriving DecidableEq, Repr

/-- Numeric types, `numtyp` (`parser.mly:492-496`). -/
inductive NumTyp where
  | nat
  | int
  | rat
  | real
  deriving DecidableEq, Repr

/-- Comparison operators, `cmpop` (`parser.mly:406-412`). -/
inductive CmpOp where
  | eq
  | ne
  | lt
  | gt
  | le
  | ge
  deriving DecidableEq, Repr

/-- Arithmetic operators, `binop` (`parser.mly:399-404`). -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | mod
  deriving DecidableEq, Repr

/-- Expressions: the fragment of `exp'` (`El.Ast`) built by `exp_prim_`,
`exp_post_`, `exp_seq_`, `exp_bin_` and `arith_bin_`
(`parser.mly:702-879`). -/
inductive Exp where
  /-- `VarE (id, args)` from `exp_var_` (`parser.mly:679-688`); a type keyword
  such as `nat` is the variable of that name. -/
  | var (x : List Char) (args : List Exp)
  /-- `NumE (DecOp, Nat n)` from `NATLIT` (`parser.mly:673`), as written. -/
  | nat (digits : List Char)
  /-- `CallE (id, args)` from `exp_call_` (`parser.mly:690-692`). -/
  | call (f : List Char) (args : List Exp)
  /-- `EpsE` (`parser.mly:707`). -/
  | eps
  /-- `ParenE e` (`parser.mly:709-713`, `parser.mly:831`). -/
  | paren (e : Exp)
  /-- `IterE (e, iter)` (`parser.mly:737`). -/
  | iter (e : Exp) (it : Iter)
  /-- `SeqE es` from juxtaposition (`parser.mly:764`). -/
  | seq (es : List Exp)
  /-- `CmpE (e₁, op, e₂)` (`parser.mly:792`, `parser.mly:873`). -/
  | cmp (op : CmpOp) (e₁ e₂ : Exp)
  /-- `BinE (e₁, op, e₂)` (`parser.mly:872`). -/
  | bin (op : BinOp) (e₁ e₂ : Exp)
  deriving Repr, Inhabited

/-- The expression of a juxtaposition: a single element is itself
(`exp_seq_ : exp_atom_`, `parser.mly:762`). -/
def Exp.ofSeq : List Exp → Exp
  | [e] => e
  | es => .seq es

/-- Types: `typ_prim_` and `typ_post_` (`parser.mly:499-512`), without
tuples. -/
inductive Typ where
  /-- `VarT (id, args)` -/
  | var (x : List Char) (args : List Exp)
  /-- `BoolT` -/
  | bool
  /-- `NumT t` -/
  | num (t : NumTyp)
  /-- `TextT` -/
  | text
  /-- `IterT (t, iter)` -/
  | iter (t : Typ) (it : Iter)
  deriving Repr, Inhabited

/-- A hint `hint(id …)` (`parser.mly:1219-1223`), with its expression kept as
the raw tokens up to the matching `)`: hints are erased by elaboration, so the
fragment does not parse them. -/
structure Hint where
  /-- `hintid` -/
  id : List Char
  /-- The tokens of `hintexp`. -/
  body : List Token
  deriving Repr

/-- Premises: `prem_` (`parser.mly:903`, `parser.mly:923-934`), `otherwise` and `if`. -/
inductive Prem where
  /-- `IfPr e` -/
  | ifP (e : Exp)
  /-- `ElsePr` -/
  | otherwise
  deriving Repr

/-- Declarations: the fragment of `def_` (`parser.mly:1144-1186`). -/
inductive Def where
  /-- `TypD (x, "", [], t, hints)` with a plain type as `deftyp`
  (`parser.mly:1147-1149`). -/
  | syntaxAlias (x : List Char) (hints : List Hint) (t : Typ)
  /-- `DecD (x, params, t, hints)` (`parser.mly:1177-1180`); the parameters
  are still arguments here, as in the parser, which converts them with
  `El.Convert.param_of_arg`. -/
  | decSig (x : List Char) (params : List Exp) (t : Typ) (hints : List Hint)
  /-- `DefD (x, args, e, prems)` (`parser.mly:1181-1184`). -/
  | decClause (x : List Char) (args : List Exp) (e : Exp) (prems : List Prem)
  /-- `GramD (x, "", [], t, gram, hints)` whose grammar is one short
  production `g(args)` (`parser.mly:1153`, short productions
  `parser.mly:136-139`). -/
  | gramAlias (x : List Char) (t : Typ) (hints : List Hint) (g : List Char) (args : List Exp)
  /-- `SepD` from `NL_NL_NL` (`parser.mly:1185-1186`). -/
  | sep
  /-- A declaration outside the fragment, kept as its token span. -/
  | unsupported (toks : List Token)
  deriving Repr

end Silmaril.Wasm.SpecTec.Surface.Syntax
