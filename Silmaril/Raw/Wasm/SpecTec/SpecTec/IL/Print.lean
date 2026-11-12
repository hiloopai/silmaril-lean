module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Digits
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Printer
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Escape

/-!
# The `--ast` rendering of the internal language

A transcription of `spectec/src/backend-ast/print.ml`, which is what
`spectec … --ast` prints.  Every function here is named after the OCaml
function it transcribes, with an `S` suffix (for "S-expression") where the
OCaml name would clash with a type.

The transcription is exact except that the three constructs
`Silmaril/SpecTec/IL/Ast.lean` does not carry — hints, `check` flags and
`LetPr` quantifiers — cannot be passed in, and `HintD`, whose rendering
`print.ml:218-219` is the empty atom that `print.ml:224-225` then filters out, has no
counterpart in `IL.Def`.  Atoms and mixfix operators arrive already rendered
(`IL.AtomS`, `IL.MixopS`), so `print.ml:13-14`'s `text (Atom.to_string at)`
and `text (Mixop.to_string op)` appear here as `textS`.

`Decode.lean` inverts every function in this file.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

open Silmaril.SpecTec (SExp)

/-! ## Literals (`print.ml:11-20`) -/

/-- `bool b = Atom (Bool.to_string b)` (`print.ml:11`). -/
def boolS (b : Bool) : SExp := .atom (if b then "true" else "false")

/-- `text t = Atom ("\"" ^ String.escaped t ^ "\"")` (`print.ml:12`).  This is
also `id x` (`print.ml:13`) and `mixop op` (`print.ml:14`), both of which go
through `text`. -/
def textS (t : String) : SExp := .atom (Escape.quote t)

/-- `num` (`print.ml:16-20`). -/
def numS : Num → SExp
  | .natN n => .node "nat" [.atom (Digits.decString n)]
  | .intN i => .node "int" [.atom (Digits.signedString i)]
  | .ratN q => .node "rat" [.atom (Digits.ratString q.num q.den)]
  | .realN r => .node "real" [.atom r]

/-! ## Operators (`print.ml:25-52`) -/

/-- `unop` (`print.ml:25`). -/
def unOpS : UnOp → SExp
  | .notOp => .atom "not"
  | .plusOp => .atom "plus"
  | .minusOp => .atom "minus"

/-- `binop` (`print.ml:32`). -/
def binOpS : BinOp → SExp
  | .andOp => .atom "and"
  | .orOp => .atom "or"
  | .implOp => .atom "impl"
  | .equivOp => .atom "equiv"
  | .addOp => .atom "add"
  | .subOp => .atom "sub"
  | .mulOp => .atom "mul"
  | .divOp => .atom "div"
  | .modOp => .atom "mod"
  | .powOp => .atom "pow"

/-- `cmpop` (`print.ml:44`). -/
def cmpOpS : CmpOp → SExp
  | .eqOp => .atom "eq"
  | .neOp => .atom "ne"
  | .ltOp => .atom "lt"
  | .gtOp => .atom "gt"
  | .leOp => .atom "le"
  | .geOp => .atom "ge"

/-- `numtyp t = Atom (Num.string_of_typ t)` (`print.ml:65`,
`spectec/src/xl/num.ml:27`). -/
def numTypS : NumTyp → SExp
  | .natT => .atom "nat"
  | .intT => .atom "int"
  | .ratT => .atom "rat"
  | .realT => .atom "real"

/-- `optyp` (`print.ml:67`); `booltyp` is `Bool.string_of_typ`
(`spectec/src/xl/bool.ml:9`). -/
def opTypS : OpTyp → SExp
  | .boolT => .atom "bool"
  | .numT t => numTypS t

/-! ## The recursive group (`print.ml:55-219`) -/

mutual

/-- `iter` (`print.ml:55`). -/
def iterS : Iter → SExp
  | .opt => .atom "opt"
  | .list => .atom "list"
  | .list1 => .atom "list1"
  | .listN e none => .node "listn" [expS e]
  | .listN e (some x) => .node "listn" [expS e, textS x]

/-- `typ` (`print.ml:71`). -/
def typS : Typ → SExp
  | .varT x args => .node "var" (textS x :: argsS args)
  | .boolT => .atom "bool"
  | .numT t => numTypS t
  | .textT => .atom "text"
  | .tupT binds => .node "tup" (typBindsS binds)
  | .iterT t it => .node "iter" [typS t, iterS it]

/-- `List.map typbind` (`print.ml:77`). -/
def typBindsS : List TypBind → List SExp
  | [] => []
  | b :: bs => typBindS b :: typBindsS bs

/-- `typbind (x, t) = Node ("bind", [id x; typ t])` (`print.ml:86-87`). -/
def typBindS : TypBind → SExp
  | .mk x t => .node "bind" [textS x, typS t]

/-- `deftyp` (`print.ml:80`). -/
def defTypS : DefTyp → SExp
  | .aliasT t => .node "alias" [typS t]
  | .structT fields => .node "struct" (typFieldsS fields)
  | .variantT cases => .node "variant" (typCasesS cases)

/-- `List.map typfield` (`print.ml:83`). -/
def typFieldsS : List TypField → List SExp
  | [] => []
  | f :: fs => typFieldS f :: typFieldsS fs

/-- `typfield (at, (t, qs, prs), _hints)` (`print.ml:89-90`). -/
def typFieldS : TypField → SExp
  | .mk atom t quants prems =>
      .node "field" (textS atom :: typS t :: (paramsS quants ++ premsS prems))

/-- `List.map typcase` (`print.ml:84`). -/
def typCasesS : List TypCase → List SExp
  | [] => []
  | c :: cs => typCaseS c :: typCasesS cs

/-- `typcase (op, (t, qs, prs), _hints)` (`print.ml:92-93`). -/
def typCaseS : TypCase → SExp
  | .mk op t quants prems =>
      .node "case" (textS op :: typS t :: (paramsS quants ++ premsS prems))

/-- `exp` (`print.ml:98`). -/
def expS : Exp → SExp
  | .varE x => .node "var" [textS x]
  | .boolE b => .node "bool" [boolS b]
  | .numE n => .node "num" [numS n]
  | .textE t => .node "text" [textS t]
  | .unE op t e => .node "un" [unOpS op, opTypS t, expS e]
  | .binE op t e₁ e₂ => .node "bin" [binOpS op, opTypS t, expS e₁, expS e₂]
  | .cmpE op t e₁ e₂ => .node "cmp" [cmpOpS op, opTypS t, expS e₁, expS e₂]
  | .idxE e₁ e₂ => .node "idx" [expS e₁, expS e₂]
  | .sliceE e₁ e₂ e₃ => .node "slice" [expS e₁, expS e₂, expS e₃]
  | .updE e₁ p e₂ => .node "upd" [expS e₁, pathS p, expS e₂]
  | .extE e₁ p e₂ => .node "ext" [expS e₁, pathS p, expS e₂]
  | .strE fields => .node "struct" (expFieldsS fields)
  | .dotE e atom => .node "dot" [expS e, textS atom]
  | .compE e₁ e₂ => .node "comp" [expS e₁, expS e₂]
  | .memE e₁ e₂ => .node "mem" [expS e₁, expS e₂]
  | .lenE e => .node "len" [expS e]
  | .tupE es => .node "tup" (expsS es)
  | .callE x args => .node "call" (textS x :: argsS args)
  | .iterE e it => .node "iter" (expS e :: iterExpS it)
  | .projE e i => .node "proj" [expS e, .atom (Digits.intString i)]
  | .caseE op e => .node "case" [textS op, expS e]
  | .uncaseE e op => .node "uncase" [expS e, textS op]
  | .optE none => .node "opt" []
  | .optE (some e) => .node "opt" [expS e]
  | .theE e => .node "unopt" [expS e]
  | .listE es => .node "list" (expsS es)
  | .liftE e => .node "lift" [expS e]
  | .catE e₁ e₂ => .node "cat" [expS e₁, expS e₂]
  | .cvtE e t₁ t₂ => .node "cvt" [numTypS t₁, numTypS t₂, expS e]
  | .subE e t₁ t₂ => .node "sub" [typS t₁, typS t₂, expS e]

/-- `List.map exp` (`print.ml:116,122,124`). -/
def expsS : List Exp → List SExp
  | [] => []
  | e :: es => expS e :: expsS es

/-- `List.map expfield` (`print.ml:111`). -/
def expFieldsS : List ExpField → List SExp
  | [] => []
  | f :: fs => expFieldS f :: expFieldsS fs

/-- `expfield (at, e) = Node ("field", [mixop (Mixop.Atom at); exp e])`
(`print.ml:130-131`). -/
def expFieldS : ExpField → SExp
  | .mk atom e => .node "field" [textS atom, expS e]

/-- `path` (`print.ml:133`). -/
def pathS : Path → SExp
  | .rootP => .atom "root"
  | .idxP p e => .node "idx" [pathS p, expS e]
  | .sliceP p e₁ e₂ => .node "slice" [pathS p, expS e₁, expS e₂]
  | .dotP p atom => .node "dot" [pathS p, textS atom]

/-- `iterexp (it, xes)` (`print.ml:140-141`), which contributes a *list* of
children to its parent node. -/
def iterExpS : IterExp → List SExp
  | .mk it doms => iterS it :: domsS doms

/-- `List.map (fun (x, e) -> Node ("dom", [id x; exp e]))` (`print.ml:141`). -/
def domsS : List Dom → List SExp
  | [] => []
  | d :: ds => domS d :: domsS ds

/-- `Node ("dom", [id x; exp e])` (`print.ml:141`). -/
def domS : Dom → SExp
  | .mk x e => .node "dom" [textS x, expS e]

/-- `sym` (`print.ml:146`). -/
def symS : Sym → SExp
  | .varG x args => .node "var" (textS x :: argsS args)
  | .numG n => .node "num" [.atom (Digits.hexByteString n)]
  | .textG t => .node "text" [textS t]
  | .epsG => .atom "eps"
  | .seqG gs => .node "seq" (symsS gs)
  | .altG gs => .node "alt" (symsS gs)
  | .rangeG g₁ g₂ => .node "range" [symS g₁, symS g₂]
  | .iterG g it => .node "iter" (symS g :: iterExpS it)
  | .attrG e g => .node "attr" [expS e, symS g]

/-- `List.map sym` (`print.ml:152,153`). -/
def symsS : List Sym → List SExp
  | [] => []
  | g :: gs => symS g :: symsS gs

/-- `prem` (`print.ml:161`). -/
def premS : Prem → SExp
  | .rulePr x args op e => .node "rule" (textS x :: (argsS args ++ [textS op, expS e]))
  | .ifPr e => .node "if" [expS e]
  | .letPr e₁ e₂ => .node "let" [expS e₁, expS e₂]
  | .elsePr => .atom "else"
  | .iterPr pr it => .node "iter" (premS pr :: iterExpS it)

/-- `List.map prem` (`print.ml:90,93,…`). -/
def premsS : List Prem → List SExp
  | [] => []
  | p :: ps => premS p :: premsS ps

/-- `arg` (`print.ml:172`). -/
def argS : Arg → SExp
  | .expA e => .node "exp" [expS e]
  | .typA t => .node "typ" [typS t]
  | .defA x => .node "def" [textS x]
  | .gramA g => .node "gram" [symS g]

/-- `List.map arg` (`print.ml:73,117,…`). -/
def argsS : List Arg → List SExp
  | [] => []
  | a :: as => argS a :: argsS as

/-- `param` (`print.ml:179`). -/
def paramS : Param → SExp
  | .expP x t => .node "exp" [textS x, typS t]
  | .typP x => .node "typ" [textS x]
  | .defP x ps t => .node "def" (textS x :: (paramsS ps ++ [typS t]))
  | .gramP x ps t => .node "gram" (textS x :: (paramsS ps ++ [typS t]))

/-- `List.map param` (`print.ml:90,…`). -/
def paramsS : List Param → List SExp
  | [] => []
  | p :: ps => paramS p :: paramsS ps

/-- `inst` (`print.ml:186`). -/
def instS : Inst → SExp
  | .instD quants args dt => .node "inst" (paramsS quants ++ argsS args ++ [defTypS dt])

/-- `List.map inst` (`print.ml:209`). -/
def instsS : List Inst → List SExp
  | [] => []
  | i :: is => instS i :: instsS is

/-- `rule` (`print.ml:191`). -/
def ruleS : Rule → SExp
  | .ruleD x quants op e prems =>
      .node "rule" (textS x :: (paramsS quants ++ [textS op, expS e] ++ premsS prems))

/-- `List.map rule` (`print.ml:211`). -/
def rulesS : List Rule → List SExp
  | [] => []
  | r :: rs => ruleS r :: rulesS rs

/-- `clause` (`print.ml:196`). -/
def clauseS : Clause → SExp
  | .defD quants args e prems =>
      .node "clause" (paramsS quants ++ argsS args ++ [expS e] ++ premsS prems)

/-- `List.map clause` (`print.ml:213`). -/
def clausesS : List Clause → List SExp
  | [] => []
  | c :: cs => clauseS c :: clausesS cs

/-- `prod` (`print.ml:201`). -/
def prodS : Prod → SExp
  | .prodD quants g e prems =>
      .node "prod" (paramsS quants ++ [symS g, expS e] ++ premsS prems)

/-- `List.map prod` (`print.ml:215`). -/
def prodsS : List Prod → List SExp
  | [] => []
  | p :: ps => prodS p :: prodsS ps

/-- `def` (`print.ml:206`). -/
def defS : Def → SExp
  | .typD x ps insts => .node "typ" (textS x :: (paramsS ps ++ instsS insts))
  | .relD x ps op t rules =>
      .node "rel" (textS x :: (paramsS ps ++ [textS op, typS t] ++ rulesS rules))
  | .decD x ps t clauses =>
      .node "def" (textS x :: (paramsS ps ++ [typS t] ++ clausesS clauses))
  | .gramD x ps t prods =>
      .node "gram" (textS x :: (paramsS ps ++ [typS t] ++ prodsS prods))
  | .recD ds => .node "rec" (defsS ds)

/-- `List.map def` (`print.ml:217`). -/
def defsS : List Def → List SExp
  | [] => []
  | d :: ds => defS d :: defsS ds

end

/-- `script ds = List.filter ((<>) (Atom "")) (List.map def ds)`
(`print.ml:225`).  The filter is vacuous here: `IL.Def` has no `HintD`, the
only definition the printer renders as the empty atom. -/
def scriptS (ds : Script) : List SExp := defsS ds

/-- The exact contents of a `spectec … --ast -o FILE` file for a script, at
the default `--ast-width` (`spectec/src/exe-spectec/main.ml:254-258`). -/
def astFile (width : Nat) (ds : Script) : String := SExp.astFile width (scriptS ds)

end Silmaril.SpecTec.IL
