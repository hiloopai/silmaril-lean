module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.List.Basic

/-!
# SpecTec's internal language

A transcription of `spectec/src/il/ast.ml` at
`608711107b7f1edb13efd57b7d79b49477462d36`, the pin recorded in
`specs/wasm/core-3.0.json`.  Every constructor names its OCaml counterpart.

## What this file keeps, and what it drops

The only machine-readable form of an elaborated SpecTec specification is the
S-expression stream printed by `spectec --ast`
(`spectec/src/backend-ast/print.ml`).  That printer is not injective on
`Il.Ast.def`, and the information it drops can never be recovered from a
`.ast` file.  The transcription below is therefore the *image* of `ast.ml`
under that erasure, so that `IL.Def` and its printed form determine each other
(`Silmaril/SpecTec/IL/Decode.lean`).  The erasures are:

| OCaml | dropped | printer |
| --- | --- | --- |
| `_ phrase` | source regions (`at`) | never printed |
| `(exp', typ) note_phrase` | the type annotation on every `exp` and `path` | never printed |
| `CaseE (_, _, check)`, `StrE (_, check)` | the `check` flag | `print.ml:120,111` |
| `LetPr (quants, _, _)` | the premise's quantifiers | `print.ml:165` |
| `typfield`, `typcase` | the trailing `hint list` | `print.ml:89,92` |
| `HintD` | the entire definition | `print.ml:218-219`, filtered at `print.ml:225` |
| `atom`, `mixop` | the mixfix structure, replaced by its rendering | `print.ml:14` |

Types are recovered by typing an imported script, not by reading them off the
stream; `Silmaril/SpecTec/IL/Hint.lean` keeps `hint` and `hintdef` for
reference.  Atoms and mixfix operators are fully transcribed in
`Silmaril/SpecTec/IL/Atom.lean` and `Silmaril/SpecTec/IL/Mixop.lean`, together
with the normal form that the rendering determines; the AST stores the
rendering itself.

## Narrowings that are not erasures of the printer

* `and check = Unchecked | Checked` (`spectec/src/il/ast.ml:52`) has no Lean
  counterpart at all.  Both of its uses, `CaseE` and `StrE`, drop it above, so
  the type itself becomes unreachable and is simply not transcribed.
* `Script` is `List Def`, which is the image of `Il.Ast.script`
  (`spectec/src/il/ast.ml:177`) under `Backend_ast.Print.script`
  (`print.ml:224-225`), *not* `Il.Ast.script` itself: the OCaml list may still
  contain `HintD`s, and a `--ast` stream records only what survives the
  filter.
* `` `Rat of rat `` (`spectec/src/xl/num.ml:10`), where `rat = Q.t`
  (`spectec/src/xl/num.ml:3`), becomes Lean's `Rat`.  Zarith's `Q.t` admits a
  zero denominator — `1/0`, `-1/0` and `0/0` are its `inf`, `-inf` and
  `undef` — which Lean's `Rat` cannot represent.  `print.ml:19` would render
  `1/0` literally and `Silmaril/SpecTec/IL/Digits.lean` rejects a zero
  denominator, so such a value has no round trip; no pinned specification
  contains one.
* `` `Nat of nat `` (`spectec/src/xl/num.ml:8`), where `nat = Z.t`
  (`spectec/src/xl/num.ml:1`), becomes Lean's `Nat`.  Zarith's `Z.t` is all of
  the integers, so the OCaml type admits a *negative* `` `Nat ``.  This one is
  unreachable rather than merely unused: every numeral-building operation of
  `Xl.Num` keeps a `` `Nat `` non-negative — subtraction is guarded by
  `when n1 >= n2` and falls through to `None` otherwise
  (`spectec/src/xl/num.ml:145`), negation of a nat yields an `` `Int ``
  (`spectec/src/xl/num.ml:130`), and addition, multiplication, exact division,
  remainder and power (`spectec/src/xl/num.ml:140,150,155,160,163`) preserve
  the sign.  Nor would the rendering survive: `print.ml:17` emits
  `Z.to_string n` as a bare atom, and `Digits.parseDecString?` reads back
  digits only, so a negative `` `Nat `` would have no round trip.  Contrast
  `` `Int ``, which `print.ml:18` renders with an explicit sign and which is
  therefore kept as Lean's `Int`.

## One place where the Lean type is *larger* than the OCaml

`` `Real of real `` (`spectec/src/xl/num.ml:11`), where `real = float`
(`spectec/src/xl/num.ml:4`), is `Num.realN (rendering : String)`: a `--ast`
stream contains only the rendering that `Printf.sprintf "%.17g"`
(`spectec/src/xl/num.ml:25`) produces, and that rendering cannot be inverted
in general — every NaN prints `nan` — so storing the string is what keeps
`defS` injective.  But the Lean constructor accepts *any*
string, while `%.17g` can only produce characters drawn from `[-+0-9.eE]`,
or one of `inf`, `-inf` and `nan` — all of them bare tokens of the
`--ast` lexical convention.  `Num.realN` is therefore the one constructor
whose Lean type is strictly larger than the image of `il/ast.ml` under the
printer's erasure, and the only one for which a *hand-built* `IL.Def` can
print something no `spectec` run would write: `numS` emits the payload as a
bare atom (`print.ml:20`), so `Num.realN " "` prints a tree the lexer cannot
read and `Num.realN ""` prints the empty atom, which the renderer erases.
`Silmaril/SpecTec/IL/Printable.lean` makes this precise — printability of a
printed script is *equivalent* to `AllToken (realsScript s)`, the statement
that each such payload is a token — and discharges it for every script read
out of a file.  Nothing else in this file needs a side condition: identifiers,
texts, atoms and mixfix operators are quoted, and the remaining numerals and
tags are fixed bare runs.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

/-- `type text = string` (`spectec/src/il/ast.ml:8`). -/
abbrev Text := String

/-- `type id = string phrase` (`spectec/src/il/ast.ml:9`), with the source
region dropped. -/
abbrev Id := String

/-- A rendered atom: `Atom.to_string` of an `Xl.Atom.atom`
(`spectec/src/xl/atom.ml:111`).  The printer never emits an atom directly; it
wraps it as `mixop (Mixop.Atom at)` (`spectec/src/backend-ast/print.ml:14`,
applied at `print.ml:90,112,131,138`).

The rendering is *not* injective: `Atom "infinity"` and `Infinity` both render
as `infinity` (`atom.ml:114,115`).  So `Silmaril.SpecTec.IL.Atom.ofString` is
a *section* of `Atom.toString` — `Atom.toString_ofString` says
`(ofString s).toString = s`, and there is no retraction law in the other
direction.  What `ofString` picks out is the normal form `Atom.Normal`
describes, and `Atom.toString_injective_on_normal` says the rendering
determines a normal atom uniquely. -/
abbrev AtomS := String

/-- A rendered mixfix operator: `Mixop.to_string` of a `unit Xl.Mixop.mixop`
(`spectec/src/xl/mixop.ml:91`), as printed by
`spectec/src/backend-ast/print.ml:14`.

This rendering is not injective either: `mixop.ml:92` collapses
`Seq (Atom a :: args)` to `Atom.to_string a` whenever every `args` entry is an
`Arg`, and `mixop.ml:93` renders every `Arg` as `%` and joins with the empty
separator, so the bracketing is lost.  `Silmaril.SpecTec.IL.Mixop.ofString` is
therefore a *section* of `Mixop.toString` (`Mixop.toString_ofString`), picking
out the normal form `Mixop.Normal` describes;
`Mixop.toString_injective_on_normal` says the rendering determines a normal
operator uniquely. -/
abbrev MixopS := String

/-! ## Terminals -/

/-- `Xl.Num.typ` (`spectec/src/xl/num.ml:14`). -/
inductive NumTyp where
  /-- `` `NatT `` -/
  | natT
  /-- `` `IntT `` -/
  | intT
  /-- `` `RatT `` -/
  | ratT
  /-- `` `RealT `` -/
  | realT
  deriving DecidableEq, Repr, Inhabited

/-- `optyp = [Bool.typ | Num.typ]` (`spectec/src/il/ast.ml:26`). -/
inductive OpTyp where
  /-- `` `BoolT `` (`spectec/src/xl/bool.ml:1`). -/
  | boolT
  /-- A numeric type (`spectec/src/xl/num.ml:14`). -/
  | numT (t : NumTyp)
  deriving DecidableEq, Repr, Inhabited

/-- `Xl.Num.num` (`spectec/src/xl/num.ml:6`).

`` `Real `` carries the rendering produced by `Printf.sprintf "%.17g"`
(`spectec/src/xl/num.ml:25`) rather than a float: that rendering is all a
`--ast` stream contains.  No pinned specification uses it. -/
inductive Num where
  /-- `` `Nat of nat `` (`spectec/src/xl/num.ml:8`).  OCaml's `nat` is `Z.t`,
  which admits negatives; this is `Nat`.  See the module docstring for why no
  elaborated IL can hold a negative one. -/
  | natN (n : Nat)
  /-- `` `Int of int `` -/
  | intN (i : Int)
  /-- `` `Rat of rat `` (`spectec/src/xl/num.ml:10`).  Zarith's `Q.t` admits a
  zero denominator, which Lean's `Rat` cannot; see the module docstring. -/
  | ratN (q : Rat)
  /-- `` `Real of real ``, as rendered.  The payload is unchecked, so this is
  the one constructor admitting values no `spectec` run can print; see the
  module docstring and `Silmaril/SpecTec/IL/Printable.lean`. -/
  | realN (rendering : String)
  deriving DecidableEq, Repr, Inhabited

/-- `unop = [Bool.unop | Num.unop]` (`spectec/src/il/ast.ml:49`).

`print.ml:29-30` also renders `` `PlusMinusOp `` and `` `MinusPlusOp ``, which
`Xl.Num.unop` (`spectec/src/xl/num.ml:16`) cannot produce at this pin. -/
inductive UnOp where
  /-- `` `NotOp `` -/
  | notOp
  /-- `` `PlusOp `` -/
  | plusOp
  /-- `` `MinusOp `` -/
  | minusOp
  deriving DecidableEq, Repr, Inhabited

/-- `binop = [Bool.binop | Num.binop]` (`spectec/src/il/ast.ml:50`). -/
inductive BinOp where
  /-- `` `AndOp `` -/
  | andOp
  /-- `` `OrOp `` -/
  | orOp
  /-- `` `ImplOp `` -/
  | implOp
  /-- `` `EquivOp `` -/
  | equivOp
  /-- `` `AddOp `` -/
  | addOp
  /-- `` `SubOp `` -/
  | subOp
  /-- `` `MulOp `` -/
  | mulOp
  /-- `` `DivOp `` -/
  | divOp
  /-- `` `ModOp `` -/
  | modOp
  /-- `` `PowOp `` -/
  | powOp
  deriving DecidableEq, Repr, Inhabited

/-- `cmpop = [Bool.cmpop | Num.cmpop]` (`spectec/src/il/ast.ml:51`). -/
inductive CmpOp where
  /-- `` `EqOp `` -/
  | eqOp
  /-- `` `NeOp `` -/
  | neOp
  /-- `` `LtOp `` -/
  | ltOp
  /-- `` `GtOp `` -/
  | gtOp
  /-- `` `LeOp `` -/
  | leOp
  /-- `` `GeOp `` -/
  | geOp
  deriving DecidableEq, Repr, Inhabited

/-! ## Iterations, types, expressions, grammars and definitions

`spectec/src/il/ast.ml:16-172` is one recursive group; so is this one.  The
auxiliary one-constructor types `TypBind`, `TypField`, `TypCase`, `ExpField`,
`IterExp` and `Dom` stand for OCaml tuple types, and are named after the
printer functions that emit them (`print.ml:86,89,92,130,140-141`). -/

mutual

/-- `iter` (`spectec/src/il/ast.ml:16`). -/
inductive Iter where
  /-- `Opt` — `?` -/
  | opt
  /-- `List` — `*` -/
  | list
  /-- `List1` — `+` -/
  | list1
  /-- `ListN of exp * id option` — `^ exp` -/
  | listN (e : Exp) (x : Option Id)

/-- `typ'` (`spectec/src/il/ast.ml:29`). -/
inductive Typ where
  /-- `VarT of id * arg list` — `typid( arg* )` -/
  | varT (x : Id) (args : List Arg)
  /-- `BoolT` -/
  | boolT
  /-- `NumT of numtyp` -/
  | numT (t : NumTyp)
  /-- `TextT` -/
  | textT
  /-- `TupT of (id * typ) list` -/
  | tupT (binds : List TypBind)
  /-- `IterT of typ * iter` -/
  | iterT (t : Typ) (it : Iter)

/-- One entry of `TupT`'s `(id * typ) list` (`spectec/src/il/ast.ml:34`),
printed by `typbind` (`print.ml:86`). -/
inductive TypBind where
  /-- `(id, typ)` -/
  | mk (x : Id) (t : Typ)

/-- `deftyp'` (`spectec/src/il/ast.ml:38`). -/
inductive DefTyp where
  /-- `AliasT of typ` -/
  | aliasT (t : Typ)
  /-- `StructT of typfield list` -/
  | structT (fields : List TypField)
  /-- `VariantT of typcase list` -/
  | variantT (cases : List TypCase)

/-- `typfield = atom * (typ * quant list * prem list) * hint list`
(`spectec/src/il/ast.ml:43`); the hints are dropped (`print.ml:89`). -/
inductive TypField where
  /-- `(atom, (typ, quants, prems), _)` -/
  | mk (atom : AtomS) (t : Typ) (quants : List Param) (prems : List Prem)

/-- `typcase = mixop * (typ * quant list * prem list) * hint list`
(`spectec/src/il/ast.ml:44`); the hints are dropped (`print.ml:92`). -/
inductive TypCase where
  /-- `(mixop, (typ, quants, prems), _)` -/
  | mk (op : MixopS) (t : Typ) (quants : List Param) (prems : List Prem)

/-- `exp'` (`spectec/src/il/ast.ml:55`), with the `typ` note of
`exp = (exp', typ) note_phrase` (`ast.ml:54`) dropped. -/
inductive Exp where
  /-- `VarE of id` — `varid` -/
  | varE (x : Id)
  /-- `BoolE of bool` -/
  | boolE (b : Bool)
  /-- `NumE of num` -/
  | numE (n : Num)
  /-- `TextE of text` -/
  | textE (t : Text)
  /-- `UnE of unop * optyp * exp` -/
  | unE (op : UnOp) (t : OpTyp) (e : Exp)
  /-- `BinE of binop * optyp * exp * exp` -/
  | binE (op : BinOp) (t : OpTyp) (e₁ e₂ : Exp)
  /-- `CmpE of cmpop * optyp * exp * exp` -/
  | cmpE (op : CmpOp) (t : OpTyp) (e₁ e₂ : Exp)
  /-- `TupE of exp list` — `( exp* )` -/
  | tupE (es : List Exp)
  /-- `ProjE of exp * int` — `exp.i`.  Printed with `string_of_int`
  (`print.ml:119`), which is injective on all of `Int`, so unlike `Sym.numG`
  there is nothing to gain from narrowing the index to `Nat`. -/
  | projE (e : Exp) (i : Int)
  /-- `CaseE of mixop * exp * check`; the `check` flag is dropped
  (`print.ml:120`). -/
  | caseE (op : MixopS) (e : Exp)
  /-- `UncaseE of exp * mixop` — `exp!mixop` -/
  | uncaseE (e : Exp) (op : MixopS)
  /-- `OptE of exp option` -/
  | optE (e : Option Exp)
  /-- `TheE of exp` — `exp!`, printed as `unopt` (`print.ml:123`). -/
  | theE (e : Exp)
  /-- `StrE of expfield list * check`; the `check` flag is dropped
  (`print.ml:111`). -/
  | strE (fields : List ExpField)
  /-- `DotE of exp * atom` — `exp.atom` -/
  | dotE (e : Exp) (atom : AtomS)
  /-- `CompE of exp * exp` — `exp @ exp` -/
  | compE (e₁ e₂ : Exp)
  /-- `ListE of exp list` — `[exp … exp]` -/
  | listE (es : List Exp)
  /-- `LiftE of exp` — `exp : _? <: _*` -/
  | liftE (e : Exp)
  /-- `MemE of exp * exp` — ``exp `<-` exp`` -/
  | memE (e₁ e₂ : Exp)
  /-- `LenE of exp` — `|exp|` -/
  | lenE (e : Exp)
  /-- `CatE of exp * exp` — `exp :: exp` -/
  | catE (e₁ e₂ : Exp)
  /-- `IdxE of exp * exp` — `exp[exp]` -/
  | idxE (e₁ e₂ : Exp)
  /-- `SliceE of exp * exp * exp` — `exp[exp : exp]` -/
  | sliceE (e₁ e₂ e₃ : Exp)
  /-- `UpdE of exp * path * exp` — `exp[path = exp]` -/
  | updE (e₁ : Exp) (p : Path) (e₂ : Exp)
  /-- `ExtE of exp * path * exp` — `exp[path =.. exp]` -/
  | extE (e₁ : Exp) (p : Path) (e₂ : Exp)
  /-- `CallE of id * arg list` — `defid( arg* )` -/
  | callE (x : Id) (args : List Arg)
  /-- `IterE of exp * iterexp` -/
  | iterE (e : Exp) (it : IterExp)
  /-- `CvtE of exp * numtyp * numtyp` — `exp : typ1 <:> typ2` -/
  | cvtE (e : Exp) (t₁ t₂ : NumTyp)
  /-- `SubE of exp * typ * typ` — `exp : typ1 <: typ2` -/
  | subE (e : Exp) (t₁ t₂ : Typ)

/-- `expfield = atom * exp` (`spectec/src/il/ast.ml:86`). -/
inductive ExpField where
  /-- `(atom, exp)` -/
  | mk (atom : AtomS) (e : Exp)

/-- `path'` (`spectec/src/il/ast.ml:89`), with the `typ` note of
`path = (path', typ) note_phrase` (`ast.ml:88`) dropped. -/
inductive Path where
  /-- `RootP` -/
  | rootP
  /-- `IdxP of path * exp` — `path[exp]` -/
  | idxP (p : Path) (e : Exp)
  /-- `SliceP of path * exp * exp` — `path[exp : exp]` -/
  | sliceP (p : Path) (e₁ e₂ : Exp)
  /-- `DotP of path * atom` — `path.atom` -/
  | dotP (p : Path) (atom : AtomS)

/-- `iterexp = iter * (id * exp) list` (`spectec/src/il/ast.ml:95`). -/
inductive IterExp where
  /-- `(iter, doms)` -/
  | mk (it : Iter) (doms : List Dom)

/-- One entry of an `iterexp`'s `(id * exp) list`, printed by `print.ml:141`
as a `dom` node. -/
inductive Dom where
  /-- `(id, exp)` -/
  | mk (x : Id) (e : Exp)

/-- `sym'` (`spectec/src/il/ast.ml:101`). -/
inductive Sym where
  /-- `VarG of id * arg list` — `gramid( arg* )` -/
  | varG (x : Id) (args : List Arg)
  /-- `NumG of int` (`spectec/src/il/ast.ml:103`), a grammar terminal, rendered
  with `Printf.sprintf "0x%02X"` (`print.ml:149`): the literal `0x` followed by
  uppercase hexadecimal.

  It is *not* a byte.  `02` is a minimum field width, not a bound, and the
  value is used both for byte terminals of the binary grammar and for Unicode
  scalar bounds in the UTF-8 grammar: `specs/spectec/wasm-3.0.ast` contains
  `(num 0xD7FF)`, `(num 0xE000)` and `(num 0x10FFFF)` beside `(num 0x00)` …
  `(num 0xFF)`.

  The OCaml type is `int` and this is `Nat`.  The narrowing is sound because
  nothing in the elaborated IL produces a negative `NumG` — a terminal is a
  byte value or a scalar bound — and it is forced because the rendering of a
  negative one would be meaningless: OCaml's `%X` formats its argument as an
  unsigned 63-bit word, so `-1` would print as `0x7FFFFFFFFFFFFFFF`, which no
  consumer of a `--ast` stream could read back.  Contrast `Exp.projE`, whose
  index stays `Int`: there the rendering is `string_of_int`, which is
  injective on all of `Int`, so the wider type costs nothing. -/
  | numG (n : Nat)
  /-- `TextG of string` -/
  | textG (t : Text)
  /-- `EpsG` — epsilon -/
  | epsG
  /-- `SeqG of sym list` — `sym sym` -/
  | seqG (gs : List Sym)
  /-- `AltG of sym list` — `sym | sym` -/
  | altG (gs : List Sym)
  /-- `RangeG of sym * sym` — `sym | … | sym` -/
  | rangeG (g₁ g₂ : Sym)
  /-- `IterG of sym * iterexp` -/
  | iterG (g : Sym) (it : IterExp)
  /-- `AttrG of exp * sym` — `exp : sym` -/
  | attrG (e : Exp) (g : Sym)

/-- `arg'` (`spectec/src/il/ast.ml:116`). -/
inductive Arg where
  /-- `ExpA of exp` -/
  | expA (e : Exp)
  /-- `TypA of typ` — `` `syntax` typ `` -/
  | typA (t : Typ)
  /-- `DefA of id` — `` `def` defid `` -/
  | defA (x : Id)
  /-- `GramA of sym` — `` `grammar` sym `` -/
  | gramA (g : Sym)

/-- `param'` (`spectec/src/il/ast.ml:123`), which `quant` abbreviates
(`spectec/src/il/ast.ml:129`). -/
inductive Param where
  /-- `ExpP of id * typ` — `varid : typ` -/
  | expP (x : Id) (t : Typ)
  /-- `TypP of id` — `` `syntax` varid `` -/
  | typP (x : Id)
  /-- `DefP of id * param list * typ` -/
  | defP (x : Id) (ps : List Param) (t : Typ)
  /-- `GramP of id * param list * typ` -/
  | gramP (x : Id) (ps : List Param) (t : Typ)

/-- `prem'` (`spectec/src/il/ast.ml:157`). -/
inductive Prem where
  /-- `RulePr of id * arg list * mixop * exp` -/
  | rulePr (x : Id) (args : List Arg) (op : MixopS) (e : Exp)
  /-- `IfPr of exp` — a side condition -/
  | ifPr (e : Exp)
  /-- `LetPr of quant list * exp * exp`; the quantifiers are dropped
  (`print.ml:165`). -/
  | letPr (e₁ e₂ : Exp)
  /-- `ElsePr` -/
  | elsePr
  /-- `IterPr of prem * iterexp` -/
  | iterPr (pr : Prem) (it : IterExp)

/-- `def'` (`spectec/src/il/ast.ml:132`), without `HintD` (`ast.ml:138`).

`print.ml:218-219` renders a hint definition as `Atom ""` and `print.ml:225`
filters empty atoms out of the script, so no `--ast` stream contains one.  By
itself that is not enough, because the filter is top level only: `RecD`
recurses with `List.map def` (`print.ml:216-217`), so a `HintD` nested inside
one would reach `print.ml:218-219` all the same and print as a stray empty
atom among its siblings.

It cannot be nested.  `Il.Free.bound_def` of a `HintD` is `empty`
(`spectec/src/il/free.ml:212`), so `recursify_defs`
(`spectec/src/frontend/elab.ml:2864-2897`) registers no identifier for it in
the origin maps (`elab.ml:2872-2878`) and the dependency graph therefore gives
it no incoming edge (`elab.ml:2879-2887`); a vertex with no incoming edge is
its own SCC, so the `[d']` branch at `elab.ml:2895` applies, and its guard
`Il.Free.disjoint bounds.(i) frees.(i)` holds vacuously because `bounds.(i)`
is `empty`.  The hint definition is emitted unwrapped rather than as
`RecD [d']`.  The `src/middlend` passes then map `RecD` structurally
(`sideconditions.ml:190`, `totalize.ml:192`, `unthe.ml:223`, `sub.ml:258`) and
pass `HintD` through unchanged (`totalize.ml:223`, `sub.ml:267`), so none of
them can move one inside a group either.

See `Silmaril/SpecTec/IL/Hint.lean`. -/
inductive Def where
  /-- `TypD of id * param list * inst list` — a syntax type or type family -/
  | typD (x : Id) (ps : List Param) (insts : List Inst)
  /-- `RelD of id * param list * mixop * typ * rule list` — a relation -/
  | relD (x : Id) (ps : List Param) (op : MixopS) (t : Typ) (rules : List Rule)
  /-- `DecD of id * param list * typ * clause list` — a definition -/
  | decD (x : Id) (ps : List Param) (t : Typ) (clauses : List Clause)
  /-- `GramD of id * param list * typ * prod list` — a grammar -/
  | gramD (x : Id) (ps : List Param) (t : Typ) (prods : List Prod)
  /-- `RecD of def list` — a recursive group -/
  | recD (ds : List Def)

/-- `inst'` (`spectec/src/il/ast.ml:141`). -/
inductive Inst where
  /-- `InstD of quant list * arg list * deftyp` — a family instance clause -/
  | instD (quants : List Param) (args : List Arg) (dt : DefTyp)

/-- `rule'` (`spectec/src/il/ast.ml:145`). -/
inductive Rule where
  /-- `RuleD of id * quant list * mixop * exp * prem list` -/
  | ruleD (x : Id) (quants : List Param) (op : MixopS) (e : Exp) (prems : List Prem)

/-- `clause'` (`spectec/src/il/ast.ml:149`). -/
inductive Clause where
  /-- `DefD of quant list * arg list * exp * prem list` -/
  | defD (quants : List Param) (args : List Arg) (e : Exp) (prems : List Prem)

/-- `prod'` (`spectec/src/il/ast.ml:153`). -/
inductive Prod where
  /-- `ProdD of quant list * sym * exp * prem list` -/
  | prodD (quants : List Param) (g : Sym) (e : Exp) (prems : List Prem)

end

deriving instance Repr for Iter, Typ, TypBind, DefTyp, TypField, TypCase, Exp, ExpField,
  Path, IterExp, Dom, Sym, Arg, Param, Prem, Def, Inst, Rule, Clause, Prod

deriving instance Inhabited for Iter, Typ, DefTyp, Exp, Path, Sym, Arg, Param, Prem, Def

/-- `type script = def list` (`spectec/src/il/ast.ml:177`), after the printer's
filter.

OCaml's `script` may contain `HintD`s, which `IL.Def` has no constructor for;
`IL.Script` is its image under `Backend_ast.Print.script`
(`spectec/src/backend-ast/print.ml:224-225`), i.e. the list a `--ast` stream
actually records. -/
abbrev Script := List Def

end Silmaril.SpecTec.IL
