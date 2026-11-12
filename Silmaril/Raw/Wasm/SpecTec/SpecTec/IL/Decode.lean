module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Print

/-!
# Decoding the `--ast` S-expression stream

The inverse of `Silmaril/SpecTec/IL/Print.lean`.  `decodeDef?` is a total
function `SExp → Option IL.Def`; `DecodeSound.lean` proves it inverts `defS`
in both directions, so `defS` is injective and the induced encoding relation
is functional.

## Reading `param` and `arg` sequences

`print.ml` concatenates parameters, arguments and a fixed tail into one child
list with no separators (`inst`, `clause`, `rule`, `prod`, `typ`, `def`,
`gram`, `rel`, `field`, `case`).  The layout is nevertheless unambiguous:

* `param` and `arg` are the only children whose tag is one of `exp`, `typ`,
  `def`, `gram` (`isPATag`), and every tail that can follow them starts with
  something else — a `deftyp` (`alias`/`struct`/`variant`), an `exp`, a `sym`,
  an `inst`/`rule`/`clause`/`prod` node, or a bare atom (a `mixop`, or a `typ`
  that is `bool`/`text`/`nat`/`int`/`rat`/`real`).
* Within that prefix, parameters come first, and the two shapes are disjoint
  (`isParamShaped`): `(exp _ _)` has two children and `(exp _)` has one;
  `(def …)` and `(gram …)` have at least two children as parameters and
  exactly one as arguments; `(typ x)` is a parameter exactly when `x` is a
  quoted identifier, and a `typ` argument is never a quoted atom.

`decodeParamsRest?` reads that prefix in one structural pass.  Every decoder
here recurses structurally on its `SExp` or `List SExp` argument, so the whole
group is accepted by Lean's structural recursion and reduces in the kernel.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

open Silmaril.SpecTec (SExp)

/-! ## Leaves -/

/-- Read an identifier or text atom: the inverse of `textS`. -/
def decodeText? : SExp → Option String
  | .atom s => Escape.unquote? s
  | .node _ _ => none

/-- Read a `bool` atom: the inverse of `boolS` (`print.ml:11`). -/
def decodeBool? : SExp → Option Bool
  | .atom "true" => some true
  | .atom "false" => some false
  | _ => none

/-- Read a `num` node: the inverse of `numS` (`print.ml:16-20`). -/
def decodeNum? : SExp → Option Num
  | .node "nat" [.atom s] => (Digits.parseDecString? s).map .natN
  | .node "int" [.atom s] => (Digits.parseSignedString? s).map .intN
  | .node "rat" [.atom s] => do
      let (n, d) ← Digits.parseRatString? s
      -- `print.ml:19-20` renders `Q.num`/`Q.den`, which zarith keeps reduced;
      -- Lean's `Rat` is reduced by construction, so a stream that spells an
      -- unreduced fraction is not in the image of `numS` and is rejected.
      if h : d ≠ 0 ∧ n.natAbs.Coprime d then some (.ratN ⟨n, d, h.1, h.2⟩) else none
  | .node "real" [.atom s] => some (.realN s)
  | _ => none

/-- The inverse of `unOpS` (`print.ml:25`). -/
def decodeUnOp? : SExp → Option UnOp
  | .atom "not" => some .notOp
  | .atom "plus" => some .plusOp
  | .atom "minus" => some .minusOp
  | _ => none

/-- The inverse of `binOpS` (`print.ml:32`). -/
def decodeBinOp? : SExp → Option BinOp
  | .atom "and" => some .andOp
  | .atom "or" => some .orOp
  | .atom "impl" => some .implOp
  | .atom "equiv" => some .equivOp
  | .atom "add" => some .addOp
  | .atom "sub" => some .subOp
  | .atom "mul" => some .mulOp
  | .atom "div" => some .divOp
  | .atom "mod" => some .modOp
  | .atom "pow" => some .powOp
  | _ => none

/-- The inverse of `cmpOpS` (`print.ml:44`). -/
def decodeCmpOp? : SExp → Option CmpOp
  | .atom "eq" => some .eqOp
  | .atom "ne" => some .neOp
  | .atom "lt" => some .ltOp
  | .atom "gt" => some .gtOp
  | .atom "le" => some .leOp
  | .atom "ge" => some .geOp
  | _ => none

/-- The inverse of `numTypS` (`print.ml:65`). -/
def decodeNumTyp? : SExp → Option NumTyp
  | .atom "nat" => some .natT
  | .atom "int" => some .intT
  | .atom "rat" => some .ratT
  | .atom "real" => some .realT
  | _ => none

/-- The inverse of `opTypS` (`print.ml:67`). -/
def decodeOpTyp? : SExp → Option OpTyp
  | .atom "bool" => some .boolT
  | s => (decodeNumTyp? s).map .numT

/-! ## Shape tests for `param`/`arg` prefixes -/

/-- Whether a child could be a `param` or an `arg` (`print.ml:172,179`). -/
def isPATag : SExp → Bool
  | .node t _ => t == "exp" || t == "typ" || t == "def" || t == "gram"
  | .atom _ => false

/-- Whether a child has the shape of a `param` rather than an `arg`. -/
def isParamShaped : SExp → Bool
  | .node "exp" ks => ks.length == 2
  | .node "typ" [k] => (decodeText? k).isSome
  | .node "def" ks => 2 ≤ ks.length
  | .node "gram" ks => 2 ≤ ks.length
  | _ => false

/-! ## The recursive group -/

mutual

/-- The inverse of `iterS` (`print.ml:55`). -/
def decodeIter? : SExp → Option Iter
  | .atom "opt" => some .opt
  | .atom "list" => some .list
  | .atom "list1" => some .list1
  | .node "listn" [e] => (decodeExp? e).map fun e => .listN e none
  | .node "listn" [e, x] => do
      let e ← decodeExp? e
      let x ← decodeText? x
      pure (.listN e (some x))
  | _ => none

/-- The inverse of `iterExpS` (`print.ml:140-141`): an `iter` followed by `dom`
nodes, read from the tail of a parent node's children. -/
def decodeIterExp? : List SExp → Option IterExp
  | [] => none
  | it :: ds => do
      let it ← decodeIter? it
      let ds ← decodeDoms? ds
      pure (.mk it ds)

/-- The inverse of `domsS` (`print.ml:141`). -/
def decodeDoms? : List SExp → Option (List Dom)
  | [] => some []
  | d :: ds => do
      let d ← decodeDom? d
      let ds ← decodeDoms? ds
      pure (d :: ds)

/-- The inverse of `domS` (`print.ml:141`). -/
def decodeDom? : SExp → Option Dom
  | .node "dom" [x, e] => do
      let x ← decodeText? x
      let e ← decodeExp? e
      pure (.mk x e)
  | _ => none

/-- The inverse of `typS` (`print.ml:71`). -/
def decodeTyp? : SExp → Option Typ
  | .atom "bool" => some .boolT
  | .atom "text" => some .textT
  | .atom "nat" => some (.numT .natT)
  | .atom "int" => some (.numT .intT)
  | .atom "rat" => some (.numT .ratT)
  | .atom "real" => some (.numT .realT)
  | .node "var" (x :: args) => do
      let x ← decodeText? x
      let args ← decodeArgs? args
      pure (.varT x args)
  | .node "tup" binds => (decodeTypBinds? binds).map .tupT
  | .node "iter" [t, it] => do
      let t ← decodeTyp? t
      let it ← decodeIter? it
      pure (.iterT t it)
  | _ => none

/-- The inverse of `typBindsS` (`print.ml:77`). -/
def decodeTypBinds? : List SExp → Option (List TypBind)
  | [] => some []
  | b :: bs => do
      let b ← decodeTypBind? b
      let bs ← decodeTypBinds? bs
      pure (b :: bs)

/-- The inverse of `typBindS` (`print.ml:86-87`). -/
def decodeTypBind? : SExp → Option TypBind
  | .node "bind" [x, t] => do
      let x ← decodeText? x
      let t ← decodeTyp? t
      pure (.mk x t)
  | _ => none

/-- The inverse of `defTypS` (`print.ml:80`). -/
def decodeDefTyp? : SExp → Option DefTyp
  | .node "alias" [t] => (decodeTyp? t).map .aliasT
  | .node "struct" fs => (decodeTypFields? fs).map .structT
  | .node "variant" cs => (decodeTypCases? cs).map .variantT
  | _ => none

/-- The inverse of `typFieldsS` (`print.ml:83`). -/
def decodeTypFields? : List SExp → Option (List TypField)
  | [] => some []
  | f :: fs => do
      let f ← decodeTypField? f
      let fs ← decodeTypFields? fs
      pure (f :: fs)

/-- The inverse of `typFieldS` (`print.ml:89-90`). -/
def decodeTypField? : SExp → Option TypField
  | .node "field" (a :: t :: rest) => do
      let a ← decodeText? a
      let t ← decodeTyp? t
      let (quants, args, tail) ← decodeParamsRest? rest
      if args.isEmpty then
        let prems ← decodePrems? tail
        pure (.mk a t quants prems)
      else none
  | _ => none

/-- The inverse of `typCasesS` (`print.ml:84`). -/
def decodeTypCases? : List SExp → Option (List TypCase)
  | [] => some []
  | c :: cs => do
      let c ← decodeTypCase? c
      let cs ← decodeTypCases? cs
      pure (c :: cs)

/-- The inverse of `typCaseS` (`print.ml:92-93`). -/
def decodeTypCase? : SExp → Option TypCase
  | .node "case" (op :: t :: rest) => do
      let op ← decodeText? op
      let t ← decodeTyp? t
      let (quants, args, tail) ← decodeParamsRest? rest
      if args.isEmpty then
        let prems ← decodePrems? tail
        pure (.mk op t quants prems)
      else none
  | _ => none

/-- The inverse of `expS` (`print.ml:98`). -/
def decodeExp? : SExp → Option Exp
  | .node "var" [x] => (decodeText? x).map .varE
  | .node "bool" [b] => (decodeBool? b).map .boolE
  | .node "num" [n] => (decodeNum? n).map .numE
  | .node "text" [t] => (decodeText? t).map .textE
  | .node "un" [op, t, e] => do
      let op ← decodeUnOp? op
      let t ← decodeOpTyp? t
      let e ← decodeExp? e
      pure (.unE op t e)
  | .node "bin" [op, t, e₁, e₂] => do
      let op ← decodeBinOp? op
      let t ← decodeOpTyp? t
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.binE op t e₁ e₂)
  | .node "cmp" [op, t, e₁, e₂] => do
      let op ← decodeCmpOp? op
      let t ← decodeOpTyp? t
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.cmpE op t e₁ e₂)
  | .node "idx" [e₁, e₂] => do
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.idxE e₁ e₂)
  | .node "slice" [e₁, e₂, e₃] => do
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      let e₃ ← decodeExp? e₃
      pure (.sliceE e₁ e₂ e₃)
  | .node "upd" [e₁, p, e₂] => do
      let e₁ ← decodeExp? e₁
      let p ← decodePath? p
      let e₂ ← decodeExp? e₂
      pure (.updE e₁ p e₂)
  | .node "ext" [e₁, p, e₂] => do
      let e₁ ← decodeExp? e₁
      let p ← decodePath? p
      let e₂ ← decodeExp? e₂
      pure (.extE e₁ p e₂)
  | .node "struct" fs => (decodeExpFields? fs).map .strE
  | .node "dot" [e, a] => do
      let e ← decodeExp? e
      let a ← decodeText? a
      pure (.dotE e a)
  | .node "comp" [e₁, e₂] => do
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.compE e₁ e₂)
  | .node "mem" [e₁, e₂] => do
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.memE e₁ e₂)
  | .node "len" [e] => (decodeExp? e).map .lenE
  | .node "tup" es => (decodeExps? es).map .tupE
  | .node "call" (x :: args) => do
      let x ← decodeText? x
      let args ← decodeArgs? args
      pure (.callE x args)
  | .node "iter" (e :: rest) => do
      let e ← decodeExp? e
      let it ← decodeIterExp? rest
      pure (.iterE e it)
  | .node "proj" [e, .atom i] => do
      let e ← decodeExp? e
      let i ← Digits.parseIntString? i
      pure (.projE e i)
  | .node "case" [op, e] => do
      let op ← decodeText? op
      let e ← decodeExp? e
      pure (.caseE op e)
  | .node "uncase" [e, op] => do
      let e ← decodeExp? e
      let op ← decodeText? op
      pure (.uncaseE e op)
  | .node "opt" [] => some (.optE none)
  | .node "opt" [e] => (decodeExp? e).map fun e => .optE (some e)
  | .node "unopt" [e] => (decodeExp? e).map .theE
  | .node "list" es => (decodeExps? es).map .listE
  | .node "lift" [e] => (decodeExp? e).map .liftE
  | .node "cat" [e₁, e₂] => do
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.catE e₁ e₂)
  | .node "cvt" [t₁, t₂, e] => do
      let t₁ ← decodeNumTyp? t₁
      let t₂ ← decodeNumTyp? t₂
      let e ← decodeExp? e
      pure (.cvtE e t₁ t₂)
  | .node "sub" [t₁, t₂, e] => do
      let t₁ ← decodeTyp? t₁
      let t₂ ← decodeTyp? t₂
      let e ← decodeExp? e
      pure (.subE e t₁ t₂)
  | _ => none

/-- The inverse of `expsS` (`print.ml:116`). -/
def decodeExps? : List SExp → Option (List Exp)
  | [] => some []
  | e :: es => do
      let e ← decodeExp? e
      let es ← decodeExps? es
      pure (e :: es)

/-- The inverse of `expFieldsS` (`print.ml:111`). -/
def decodeExpFields? : List SExp → Option (List ExpField)
  | [] => some []
  | f :: fs => do
      let f ← decodeExpField? f
      let fs ← decodeExpFields? fs
      pure (f :: fs)

/-- The inverse of `expFieldS` (`print.ml:130-131`). -/
def decodeExpField? : SExp → Option ExpField
  | .node "field" [a, e] => do
      let a ← decodeText? a
      let e ← decodeExp? e
      pure (.mk a e)
  | _ => none

/-- The inverse of `pathS` (`print.ml:133`). -/
def decodePath? : SExp → Option Path
  | .atom "root" => some .rootP
  | .node "idx" [p, e] => do
      let p ← decodePath? p
      let e ← decodeExp? e
      pure (.idxP p e)
  | .node "slice" [p, e₁, e₂] => do
      let p ← decodePath? p
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.sliceP p e₁ e₂)
  | .node "dot" [p, a] => do
      let p ← decodePath? p
      let a ← decodeText? a
      pure (.dotP p a)
  | _ => none

/-- The inverse of `symS` (`print.ml:146`). -/
def decodeSym? : SExp → Option Sym
  | .atom "eps" => some .epsG
  | .node "var" (x :: args) => do
      let x ← decodeText? x
      let args ← decodeArgs? args
      pure (.varG x args)
  | .node "num" [.atom n] => (Digits.parseHexByteString? n).map .numG
  | .node "text" [t] => (decodeText? t).map .textG
  | .node "seq" gs => (decodeSyms? gs).map .seqG
  | .node "alt" gs => (decodeSyms? gs).map .altG
  | .node "range" [g₁, g₂] => do
      let g₁ ← decodeSym? g₁
      let g₂ ← decodeSym? g₂
      pure (.rangeG g₁ g₂)
  | .node "iter" (g :: rest) => do
      let g ← decodeSym? g
      let it ← decodeIterExp? rest
      pure (.iterG g it)
  | .node "attr" [e, g] => do
      let e ← decodeExp? e
      let g ← decodeSym? g
      pure (.attrG e g)
  | _ => none

/-- The inverse of `symsS` (`print.ml:152`). -/
def decodeSyms? : List SExp → Option (List Sym)
  | [] => some []
  | g :: gs => do
      let g ← decodeSym? g
      let gs ← decodeSyms? gs
      pure (g :: gs)

/-- The inverse of `premS` (`print.ml:161`). -/
def decodePrem? : SExp → Option Prem
  | .atom "else" => some .elsePr
  | .node "rule" (x :: rest) => do
      let x ← decodeText? x
      let (args, tail) ← decodeArgsRest? rest
      match tail with
      | [op, e] => do
          let op ← decodeText? op
          let e ← decodeExp? e
          pure (.rulePr x args op e)
      | _ => none
  | .node "if" [e] => (decodeExp? e).map .ifPr
  | .node "let" [e₁, e₂] => do
      let e₁ ← decodeExp? e₁
      let e₂ ← decodeExp? e₂
      pure (.letPr e₁ e₂)
  | .node "iter" (p :: rest) => do
      let p ← decodePrem? p
      let it ← decodeIterExp? rest
      pure (.iterPr p it)
  | _ => none

/-- The inverse of `premsS` (`print.ml:90`). -/
def decodePrems? : List SExp → Option (List Prem)
  | [] => some []
  | p :: ps => do
      let p ← decodePrem? p
      let ps ← decodePrems? ps
      pure (p :: ps)

/-- The inverse of `argS` (`print.ml:172`). -/
def decodeArg? : SExp → Option Arg
  | .node "exp" [e] => (decodeExp? e).map .expA
  | .node "typ" [t] => (decodeTyp? t).map .typA
  | .node "def" [x] => (decodeText? x).map .defA
  | .node "gram" [g] => (decodeSym? g).map .gramA
  | _ => none

/-- The inverse of `argsS` (`print.ml:73`), where every remaining child is an
argument. -/
def decodeArgs? : List SExp → Option (List Arg)
  | [] => some []
  | a :: as => do
      let a ← decodeArg? a
      let as ← decodeArgs? as
      pure (a :: as)

/-- Read a maximal prefix of arguments, returning the remaining children. -/
def decodeArgsRest? : List SExp → Option (List Arg × List SExp)
  | [] => some ([], [])
  | k :: ks =>
      if isPATag k then do
        let a ← decodeArg? k
        let (as, rest) ← decodeArgsRest? ks
        pure (a :: as, rest)
      else some ([], k :: ks)

/-- Read a maximal prefix of parameters, then of arguments, returning the
remaining children. -/
def decodeParamsRest? : List SExp → Option (List Param × List Arg × List SExp)
  | [] => some ([], [], [])
  | k :: ks =>
      if isParamShaped k then do
        let p ← decodeParam? k
        let (ps, as, rest) ← decodeParamsRest? ks
        pure (p :: ps, as, rest)
      else if isPATag k then do
        let a ← decodeArg? k
        let (as, rest) ← decodeArgsRest? ks
        pure ([], a :: as, rest)
      else some ([], [], k :: ks)

/-- The inverse of `paramS` (`print.ml:179`). -/
def decodeParam? : SExp → Option Param
  | .node "exp" [x, t] => do
      let x ← decodeText? x
      let t ← decodeTyp? t
      pure (.expP x t)
  | .node "typ" [x] => (decodeText? x).map .typP
  | .node "def" (x :: rest) => do
      let x ← decodeText? x
      let (ps, args, tail) ← decodeParamsRest? rest
      match args, tail with
      | [], [t] => (decodeTyp? t).map fun t => .defP x ps t
      | _, _ => none
  | .node "gram" (x :: rest) => do
      let x ← decodeText? x
      let (ps, args, tail) ← decodeParamsRest? rest
      match args, tail with
      | [], [t] => (decodeTyp? t).map fun t => .gramP x ps t
      | _, _ => none
  | _ => none

/-- The inverse of `paramsS` (`print.ml:90`), where every child is a
parameter. -/
def decodeParams? : List SExp → Option (List Param)
  | [] => some []
  | p :: ps => do
      let p ← decodeParam? p
      let ps ← decodeParams? ps
      pure (p :: ps)

/-- The inverse of `instS` (`print.ml:186`). -/
def decodeInst? : SExp → Option Inst
  | .node "inst" ks => do
      let (quants, args, tail) ← decodeParamsRest? ks
      match tail with
      | [dt] => (decodeDefTyp? dt).map fun dt => .instD quants args dt
      | _ => none
  | _ => none

/-- The inverse of `instsS` (`print.ml:209`). -/
def decodeInsts? : List SExp → Option (List Inst)
  | [] => some []
  | i :: is => do
      let i ← decodeInst? i
      let is ← decodeInsts? is
      pure (i :: is)

/-- The inverse of `ruleS` (`print.ml:191`). -/
def decodeRule? : SExp → Option Rule
  | .node "rule" (x :: ks) => do
      let x ← decodeText? x
      let (quants, args, tail) ← decodeParamsRest? ks
      if args.isEmpty then
        match tail with
        | op :: e :: prems => do
            let op ← decodeText? op
            let e ← decodeExp? e
            let prems ← decodePrems? prems
            pure (.ruleD x quants op e prems)
        | _ => none
      else none
  | _ => none

/-- The inverse of `rulesS` (`print.ml:211`). -/
def decodeRules? : List SExp → Option (List Rule)
  | [] => some []
  | r :: rs => do
      let r ← decodeRule? r
      let rs ← decodeRules? rs
      pure (r :: rs)

/-- The inverse of `clauseS` (`print.ml:196`). -/
def decodeClause? : SExp → Option Clause
  | .node "clause" ks => do
      let (quants, args, tail) ← decodeParamsRest? ks
      match tail with
      | e :: prems => do
          let e ← decodeExp? e
          let prems ← decodePrems? prems
          pure (.defD quants args e prems)
      | _ => none
  | _ => none

/-- The inverse of `clausesS` (`print.ml:213`). -/
def decodeClauses? : List SExp → Option (List Clause)
  | [] => some []
  | c :: cs => do
      let c ← decodeClause? c
      let cs ← decodeClauses? cs
      pure (c :: cs)

/-- The inverse of `prodS` (`print.ml:201`). -/
def decodeProd? : SExp → Option Prod
  | .node "prod" ks => do
      let (quants, args, tail) ← decodeParamsRest? ks
      if args.isEmpty then
        match tail with
        | g :: e :: prems => do
            let g ← decodeSym? g
            let e ← decodeExp? e
            let prems ← decodePrems? prems
            pure (.prodD quants g e prems)
        | _ => none
      else none
  | _ => none

/-- The inverse of `prodsS` (`print.ml:215`). -/
def decodeProds? : List SExp → Option (List Prod)
  | [] => some []
  | p :: ps => do
      let p ← decodeProd? p
      let ps ← decodeProds? ps
      pure (p :: ps)

/-- The inverse of `defS` (`print.ml:206`). -/
def decodeDef? : SExp → Option Def
  | .node "typ" (x :: ks) => do
      let x ← decodeText? x
      let (ps, args, tail) ← decodeParamsRest? ks
      if args.isEmpty then
        let insts ← decodeInsts? tail
        pure (.typD x ps insts)
      else none
  | .node "rel" (x :: ks) => do
      let x ← decodeText? x
      let (ps, args, tail) ← decodeParamsRest? ks
      if args.isEmpty then
        match tail with
        | op :: t :: rules => do
            let op ← decodeText? op
            let t ← decodeTyp? t
            let rules ← decodeRules? rules
            pure (.relD x ps op t rules)
        | _ => none
      else none
  | .node "def" (x :: ks) => do
      let x ← decodeText? x
      let (ps, args, tail) ← decodeParamsRest? ks
      if args.isEmpty then
        match tail with
        | t :: clauses => do
            let t ← decodeTyp? t
            let clauses ← decodeClauses? clauses
            pure (.decD x ps t clauses)
        | _ => none
      else none
  | .node "gram" (x :: ks) => do
      let x ← decodeText? x
      let (ps, args, tail) ← decodeParamsRest? ks
      if args.isEmpty then
        match tail with
        | t :: prods => do
            let t ← decodeTyp? t
            let prods ← decodeProds? prods
            pure (.gramD x ps t prods)
        | _ => none
      else none
  | .node "rec" ds => (decodeDefs? ds).map .recD
  | _ => none

/-- The inverse of `defsS` (`print.ml:217`). -/
def decodeDefs? : List SExp → Option (List Def)
  | [] => some []
  | d :: ds => do
      let d ← decodeDef? d
      let ds ← decodeDefs? ds
      pure (d :: ds)

end

/-- The inverse of `scriptS` (`print.ml:225`). -/
def decodeScript? (ss : List SExp) : Option Script := decodeDefs? ss

end Silmaril.SpecTec.IL
