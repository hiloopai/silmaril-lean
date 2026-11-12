module

public meta import Lean
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.DecodeSound
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Parse

/-!
# Importing an `--ast` stream

```
spectec_import wasm30 from "specs/spectec/wasm-3.0.ast"
```

reads the file at elaboration time, parses it with
`Silmaril/SpecTec/SExp/Parse.lean`, decodes it with `IL.decodeScript?`, and
adds

* `wasm30.defs.0 … wasm30.defs.n` — one `IL.Def` per top-level definition,
* `wasm30 : IL.Script` — the list of those,
* `wasm30.sexps : List SExp` — the printed form, *defined* as
  `IL.scriptS wasm30`,
* `wasm30.decodes : IL.decodeScript? wasm30.sexps = some wasm30`.

## What is established, and by what

`wasm30.decodes` is *not* evidence about the file.  Its proof term is
`IL.decodeScript?_scriptS wasm30`, an instance of a theorem that holds for
every `IL.Script`, and `wasm30.sexps` is by definition `IL.scriptS wasm30`.
It records the shape of the data; it does not certify the import.  What the
import establishes lives in the elaborator, and divides as follows.

**The kernel checks** that each `wasm30.defs.i` is a well-typed closed term of
type `IL.Def`, that `wasm30` is a well-typed `List IL.Def`, and that
`IL.decodeScript?_scriptS wasm30` has the stated type — which it does because
`wasm30.sexps` unfolds to `IL.scriptS wasm30`.  No claim about the bytes
reaches the kernel.

**The elaborator checks**, in compiled code, that

1. the bytes parse: `SExp.parseStream` returns a list of forms;
2. the forms decode: `IL.decodeScript? forms = some script`;
3. the terms emitted for `wasm30.defs.i` denote exactly the definitions that
   were decoded, that `wasm30` is those constants in order, and that
   `wasm30.sexps` is `IL.scriptS wasm30` — see "The round trip through the
   environment" below.

Step 2 is what gives `wasm30.sexps` its meaning.  `IL.scriptS_of_decodeScript?`
(`Silmaril/SpecTec/IL/DecodeComplete.lean`) turns `decodeScript? forms = some
script` into `IL.scriptS script = forms`: "the decoder accepted the parsed
forms" becomes "the parsed forms *are* `IL.scriptS script`".  So given that
the forms are what the file contains, `wasm30.sexps` is literally the parsed
file, and `wasm30` is the unique script that prints to it
(`IL.scriptS_injective`).  Both of those are theorems; what is unverified is
only their application to these particular bytes.

**What remains trusted** is then exactly two things:

* *the reader* — `IO.FS.readFile` and `SExp.parseStream` are ordinary Lean
  functions run outside the kernel, so "the forms are what the file contains"
  is a property of compiled code, not a proof.  The bytes are pinned by
  SHA-256 in `specs/spectec/manifest.json` and re-checked by
  `sil spectec-asts --check`;
* *the agreement of `qDef` with `unqDef`* — a reflection bug now has to be
  present in both, which are written in opposite directions and read their
  constructor names and argument orders off `Silmaril/SpecTec/IL/Ast.lean`
  independently.

`Silmaril/SpecTec/Examples.lean` is where a literal, fully kernel-checked
certificate *is* exhibited.  For small snippets it emits the S-expressions as
terms and proves `IL.defS d = s` by `rfl`, so there the kernel itself sees a
definition and its printed form agree, and `IL.decodeDef?_defS` turns that
into `decodeDef? s = some d` with no further computation.

## The round trip through the environment

`qDef`/`qDefs` below reflect an `IL.Def` *value* into an `Expr`.  That is
unverified meta code, and a transposed argument in, say, `qTypField` would
silently change what `wasm30` denotes while leaving everything above intact.
So after the declarations are added, `elabSpectecImport` reads each constant's
value back out of the environment — the `Expr` the kernel accepted — applies
the inverse traversal `unqDef`, and checks the result against the form it was
decoded from.  The comparison runs through `IL.defS` because `IL.Def` has no
`DecidableEq` instance; it is nevertheless equality of definitions, since
`IL.decodeDef?_defS` and `IL.defS_of_decodeDef?` make `defS d' = s` and
`d' = d` equivalent when `decodeDef? s = some d`.

This costs about 0.95 s for the three pinned specifications (112 ms, 263 ms
and 575 ms, measured): elaborating `Silmaril/SpecTec/Specs.lean` goes from
about 7.6 s to about 8.5 s.

## Why the certificate is not literal

The obvious certificate — emit the parsed S-expressions as literal terms and
prove `IL.decodeScript? literals = some script` by `rfl` — is not affordable.
In Lean v4.35 `String` is UTF-8/`ByteArray` backed, so reducing
`Escape.quote` on one ten-character identifier costs about 18 ms of kernel
time (measured); the wasm-3.0 stream has tens of thousands of quoted atoms, so
that route costs tens of minutes per build.  Hence the arrangement above:
`wasm30.sexps` is defined rather than given, the general theorem
`IL.decodeScript?_scriptS` replaces a per-definition computation, and the
literal route is taken only where it is cheap.

`spectec_sexp%` and `spectec_def%` quote small snippets inline, which is where
`Silmaril/SpecTec/Examples.lean` takes it.
-/

public meta section

namespace Silmaril.SpecTec.IL

open Lean Elab Command Term Meta Silmaril.SpecTec

universe u
variable {α : Type u}

/-- A constant of the IL namespace. -/
def mkIL (n : Name) : Expr := mkConst n

/-- Reflect an `Option α` given a reflection of `α` at type `ty`. -/
def qOption (ty : Expr) (f : α → Expr) : Option α → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) ty
  | some a => mkAppN (mkConst ``Option.some [Level.zero]) #[ty, f a]

/-- Reflect an `IL.NumTyp`. -/
def qNumTyp : NumTyp → Expr
  | .natT => mkIL ``NumTyp.natT
  | .intT => mkIL ``NumTyp.intT
  | .ratT => mkIL ``NumTyp.ratT
  | .realT => mkIL ``NumTyp.realT

/-- Reflect an `IL.OpTyp`. -/
def qOpTyp : OpTyp → Expr
  | .boolT => mkIL ``OpTyp.boolT
  | .numT t => mkApp (mkIL ``OpTyp.numT) (qNumTyp t)

/-- Reflect an `IL.Num`.  A rational is rebuilt with `mkRat`, which normalizes
to the same value; no pinned stream contains one. -/
def qNum : Num → Expr
  | .natN n => mkApp (mkIL ``Num.natN) (mkNatLit n)
  | .intN i => mkApp (mkIL ``Num.intN) (toExpr i)
  | .ratN q => mkApp (mkIL ``Num.ratN) (mkAppN (mkConst ``mkRat) #[toExpr q.num, mkNatLit q.den])
  | .realN s => mkApp (mkIL ``Num.realN) (mkStrLit s)

/-- Reflect an `IL.UnOp`. -/
def qUnOp : UnOp → Expr
  | .notOp => mkIL ``UnOp.notOp
  | .plusOp => mkIL ``UnOp.plusOp
  | .minusOp => mkIL ``UnOp.minusOp

/-- Reflect an `IL.BinOp`. -/
def qBinOp : BinOp → Expr
  | .andOp => mkIL ``BinOp.andOp
  | .orOp => mkIL ``BinOp.orOp
  | .implOp => mkIL ``BinOp.implOp
  | .equivOp => mkIL ``BinOp.equivOp
  | .addOp => mkIL ``BinOp.addOp
  | .subOp => mkIL ``BinOp.subOp
  | .mulOp => mkIL ``BinOp.mulOp
  | .divOp => mkIL ``BinOp.divOp
  | .modOp => mkIL ``BinOp.modOp
  | .powOp => mkIL ``BinOp.powOp

/-- Reflect an `IL.CmpOp`. -/
def qCmpOp : CmpOp → Expr
  | .eqOp => mkIL ``CmpOp.eqOp
  | .neOp => mkIL ``CmpOp.neOp
  | .ltOp => mkIL ``CmpOp.ltOp
  | .gtOp => mkIL ``CmpOp.gtOp
  | .leOp => mkIL ``CmpOp.leOp
  | .geOp => mkIL ``CmpOp.geOp

mutual

/-- Reflect an `IL.Iter` as a term. -/
partial def qIter : Iter → Expr
  | .opt => mkIL ``Iter.opt
  | .list => mkIL ``Iter.list
  | .list1 => mkIL ``Iter.list1
  | .listN a b => mkAppN (mkIL ``Iter.listN) #[qExp a, qOption (mkConst ``String) mkStrLit b]

/-- Reflect a `List IL.Iter` as a term. -/
partial def qIters : List Iter → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Iter)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Iter, qIter x, qIters xs]

/-- Reflect an `IL.Typ` as a term. -/
partial def qTyp : Typ → Expr
  | .varT a b => mkAppN (mkIL ``Typ.varT) #[mkStrLit a, qArgs b]
  | .boolT => mkIL ``Typ.boolT
  | .numT a => mkAppN (mkIL ``Typ.numT) #[qNumTyp a]
  | .textT => mkIL ``Typ.textT
  | .tupT a => mkAppN (mkIL ``Typ.tupT) #[qTypBinds a]
  | .iterT a b => mkAppN (mkIL ``Typ.iterT) #[qTyp a, qIter b]

/-- Reflect a `List IL.Typ` as a term. -/
partial def qTyps : List Typ → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Typ)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Typ, qTyp x, qTyps xs]

/-- Reflect an `IL.TypBind` as a term. -/
partial def qTypBind : TypBind → Expr
  | .mk a b => mkAppN (mkIL ``TypBind.mk) #[mkStrLit a, qTyp b]

/-- Reflect a `List IL.TypBind` as a term. -/
partial def qTypBinds : List TypBind → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``TypBind)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``TypBind, qTypBind x, qTypBinds xs]

/-- Reflect an `IL.DefTyp` as a term. -/
partial def qDefTyp : DefTyp → Expr
  | .aliasT a => mkAppN (mkIL ``DefTyp.aliasT) #[qTyp a]
  | .structT a => mkAppN (mkIL ``DefTyp.structT) #[qTypFields a]
  | .variantT a => mkAppN (mkIL ``DefTyp.variantT) #[qTypCases a]

/-- Reflect a `List IL.DefTyp` as a term. -/
partial def qDefTyps : List DefTyp → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``DefTyp)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``DefTyp, qDefTyp x, qDefTyps xs]

/-- Reflect an `IL.TypField` as a term. -/
partial def qTypField : TypField → Expr
  | .mk a b c d => mkAppN (mkIL ``TypField.mk) #[mkStrLit a, qTyp b, qParams c, qPrems d]

/-- Reflect a `List IL.TypField` as a term. -/
partial def qTypFields : List TypField → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``TypField)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``TypField, qTypField x, qTypFields xs]

/-- Reflect an `IL.TypCase` as a term. -/
partial def qTypCase : TypCase → Expr
  | .mk a b c d => mkAppN (mkIL ``TypCase.mk) #[mkStrLit a, qTyp b, qParams c, qPrems d]

/-- Reflect a `List IL.TypCase` as a term. -/
partial def qTypCases : List TypCase → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``TypCase)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``TypCase, qTypCase x, qTypCases xs]

/-- Reflect an `IL.Exp` as a term. -/
partial def qExp : Exp → Expr
  | .varE a => mkAppN (mkIL ``Exp.varE) #[mkStrLit a]
  | .boolE a => mkAppN (mkIL ``Exp.boolE) #[toExpr a]
  | .numE a => mkAppN (mkIL ``Exp.numE) #[qNum a]
  | .textE a => mkAppN (mkIL ``Exp.textE) #[mkStrLit a]
  | .unE a b c => mkAppN (mkIL ``Exp.unE) #[qUnOp a, qOpTyp b, qExp c]
  | .binE a b c d => mkAppN (mkIL ``Exp.binE) #[qBinOp a, qOpTyp b, qExp c, qExp d]
  | .cmpE a b c d => mkAppN (mkIL ``Exp.cmpE) #[qCmpOp a, qOpTyp b, qExp c, qExp d]
  | .tupE a => mkAppN (mkIL ``Exp.tupE) #[qExps a]
  | .projE a b => mkAppN (mkIL ``Exp.projE) #[qExp a, toExpr b]
  | .caseE a b => mkAppN (mkIL ``Exp.caseE) #[mkStrLit a, qExp b]
  | .uncaseE a b => mkAppN (mkIL ``Exp.uncaseE) #[qExp a, mkStrLit b]
  | .optE a => mkAppN (mkIL ``Exp.optE) #[qOption (mkIL ``Exp) qExp a]
  | .theE a => mkAppN (mkIL ``Exp.theE) #[qExp a]
  | .strE a => mkAppN (mkIL ``Exp.strE) #[qExpFields a]
  | .dotE a b => mkAppN (mkIL ``Exp.dotE) #[qExp a, mkStrLit b]
  | .compE a b => mkAppN (mkIL ``Exp.compE) #[qExp a, qExp b]
  | .listE a => mkAppN (mkIL ``Exp.listE) #[qExps a]
  | .liftE a => mkAppN (mkIL ``Exp.liftE) #[qExp a]
  | .memE a b => mkAppN (mkIL ``Exp.memE) #[qExp a, qExp b]
  | .lenE a => mkAppN (mkIL ``Exp.lenE) #[qExp a]
  | .catE a b => mkAppN (mkIL ``Exp.catE) #[qExp a, qExp b]
  | .idxE a b => mkAppN (mkIL ``Exp.idxE) #[qExp a, qExp b]
  | .sliceE a b c => mkAppN (mkIL ``Exp.sliceE) #[qExp a, qExp b, qExp c]
  | .updE a b c => mkAppN (mkIL ``Exp.updE) #[qExp a, qPath b, qExp c]
  | .extE a b c => mkAppN (mkIL ``Exp.extE) #[qExp a, qPath b, qExp c]
  | .callE a b => mkAppN (mkIL ``Exp.callE) #[mkStrLit a, qArgs b]
  | .iterE a b => mkAppN (mkIL ``Exp.iterE) #[qExp a, qIterExp b]
  | .cvtE a b c => mkAppN (mkIL ``Exp.cvtE) #[qExp a, qNumTyp b, qNumTyp c]
  | .subE a b c => mkAppN (mkIL ``Exp.subE) #[qExp a, qTyp b, qTyp c]

/-- Reflect a `List IL.Exp` as a term. -/
partial def qExps : List Exp → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Exp)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Exp, qExp x, qExps xs]

/-- Reflect an `IL.ExpField` as a term. -/
partial def qExpField : ExpField → Expr
  | .mk a b => mkAppN (mkIL ``ExpField.mk) #[mkStrLit a, qExp b]

/-- Reflect a `List IL.ExpField` as a term. -/
partial def qExpFields : List ExpField → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``ExpField)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``ExpField, qExpField x, qExpFields xs]

/-- Reflect an `IL.Path` as a term. -/
partial def qPath : Path → Expr
  | .rootP => mkIL ``Path.rootP
  | .idxP a b => mkAppN (mkIL ``Path.idxP) #[qPath a, qExp b]
  | .sliceP a b c => mkAppN (mkIL ``Path.sliceP) #[qPath a, qExp b, qExp c]
  | .dotP a b => mkAppN (mkIL ``Path.dotP) #[qPath a, mkStrLit b]

/-- Reflect a `List IL.Path` as a term. -/
partial def qPaths : List Path → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Path)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Path, qPath x, qPaths xs]

/-- Reflect an `IL.IterExp` as a term. -/
partial def qIterExp : IterExp → Expr
  | .mk a b => mkAppN (mkIL ``IterExp.mk) #[qIter a, qDoms b]

/-- Reflect a `List IL.IterExp` as a term. -/
partial def qIterExps : List IterExp → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``IterExp)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``IterExp, qIterExp x, qIterExps xs]

/-- Reflect an `IL.Dom` as a term. -/
partial def qDom : Dom → Expr
  | .mk a b => mkAppN (mkIL ``Dom.mk) #[mkStrLit a, qExp b]

/-- Reflect a `List IL.Dom` as a term. -/
partial def qDoms : List Dom → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Dom)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Dom, qDom x, qDoms xs]

/-- Reflect an `IL.Sym` as a term. -/
partial def qSym : Sym → Expr
  | .varG a b => mkAppN (mkIL ``Sym.varG) #[mkStrLit a, qArgs b]
  | .numG a => mkAppN (mkIL ``Sym.numG) #[mkNatLit a]
  | .textG a => mkAppN (mkIL ``Sym.textG) #[mkStrLit a]
  | .epsG => mkIL ``Sym.epsG
  | .seqG a => mkAppN (mkIL ``Sym.seqG) #[qSyms a]
  | .altG a => mkAppN (mkIL ``Sym.altG) #[qSyms a]
  | .rangeG a b => mkAppN (mkIL ``Sym.rangeG) #[qSym a, qSym b]
  | .iterG a b => mkAppN (mkIL ``Sym.iterG) #[qSym a, qIterExp b]
  | .attrG a b => mkAppN (mkIL ``Sym.attrG) #[qExp a, qSym b]

/-- Reflect a `List IL.Sym` as a term. -/
partial def qSyms : List Sym → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Sym)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Sym, qSym x, qSyms xs]

/-- Reflect an `IL.Arg` as a term. -/
partial def qArg : Arg → Expr
  | .expA a => mkAppN (mkIL ``Arg.expA) #[qExp a]
  | .typA a => mkAppN (mkIL ``Arg.typA) #[qTyp a]
  | .defA a => mkAppN (mkIL ``Arg.defA) #[mkStrLit a]
  | .gramA a => mkAppN (mkIL ``Arg.gramA) #[qSym a]

/-- Reflect a `List IL.Arg` as a term. -/
partial def qArgs : List Arg → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Arg)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Arg, qArg x, qArgs xs]

/-- Reflect an `IL.Param` as a term. -/
partial def qParam : Param → Expr
  | .expP a b => mkAppN (mkIL ``Param.expP) #[mkStrLit a, qTyp b]
  | .typP a => mkAppN (mkIL ``Param.typP) #[mkStrLit a]
  | .defP a b c => mkAppN (mkIL ``Param.defP) #[mkStrLit a, qParams b, qTyp c]
  | .gramP a b c => mkAppN (mkIL ``Param.gramP) #[mkStrLit a, qParams b, qTyp c]

/-- Reflect a `List IL.Param` as a term. -/
partial def qParams : List Param → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Param)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Param, qParam x, qParams xs]

/-- Reflect an `IL.Prem` as a term. -/
partial def qPrem : Prem → Expr
  | .rulePr a b c d => mkAppN (mkIL ``Prem.rulePr) #[mkStrLit a, qArgs b, mkStrLit c, qExp d]
  | .ifPr a => mkAppN (mkIL ``Prem.ifPr) #[qExp a]
  | .letPr a b => mkAppN (mkIL ``Prem.letPr) #[qExp a, qExp b]
  | .elsePr => mkIL ``Prem.elsePr
  | .iterPr a b => mkAppN (mkIL ``Prem.iterPr) #[qPrem a, qIterExp b]

/-- Reflect a `List IL.Prem` as a term. -/
partial def qPrems : List Prem → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Prem)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Prem, qPrem x, qPrems xs]

/-- Reflect an `IL.Def` as a term. -/
partial def qDef : Def → Expr
  | .typD a b c => mkAppN (mkIL ``Def.typD) #[mkStrLit a, qParams b, qInsts c]
  | .relD a b c d e =>
      mkAppN (mkIL ``Def.relD)
        #[mkStrLit a, qParams b, mkStrLit c, qTyp d, qRules e]
  | .decD a b c d => mkAppN (mkIL ``Def.decD) #[mkStrLit a, qParams b, qTyp c, qClauses d]
  | .gramD a b c d => mkAppN (mkIL ``Def.gramD) #[mkStrLit a, qParams b, qTyp c, qProds d]
  | .recD a => mkAppN (mkIL ``Def.recD) #[qDefs a]

/-- Reflect a `List IL.Def` as a term. -/
partial def qDefs : List Def → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Def)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Def, qDef x, qDefs xs]

/-- Reflect an `IL.Inst` as a term. -/
partial def qInst : Inst → Expr
  | .instD a b c => mkAppN (mkIL ``Inst.instD) #[qParams a, qArgs b, qDefTyp c]

/-- Reflect a `List IL.Inst` as a term. -/
partial def qInsts : List Inst → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Inst)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Inst, qInst x, qInsts xs]

/-- Reflect an `IL.Rule` as a term. -/
partial def qRule : Rule → Expr
  | .ruleD a b c d e =>
      mkAppN (mkIL ``Rule.ruleD)
        #[mkStrLit a, qParams b, mkStrLit c, qExp d, qPrems e]

/-- Reflect a `List IL.Rule` as a term. -/
partial def qRules : List Rule → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Rule)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Rule, qRule x, qRules xs]

/-- Reflect an `IL.Clause` as a term. -/
partial def qClause : Clause → Expr
  | .defD a b c d => mkAppN (mkIL ``Clause.defD) #[qParams a, qArgs b, qExp c, qPrems d]

/-- Reflect a `List IL.Clause` as a term. -/
partial def qClauses : List Clause → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Clause)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Clause, qClause x, qClauses xs]

/-- Reflect an `IL.Prod` as a term. -/
partial def qProd : Prod → Expr
  | .prodD a b c d => mkAppN (mkIL ``Prod.prodD) #[qParams a, qSym b, qExp c, qPrems d]

/-- Reflect a `List IL.Prod` as a term. -/
partial def qProds : List Prod → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkIL ``Prod)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero]) #[mkIL ``Prod, qProd x, qProds xs]

end

mutual

/-- Reflect a `SExp` as a term. -/
partial def qSExp : SExp → Expr
  | .atom s => mkApp (mkConst ``Silmaril.SpecTec.SExp.atom) (mkStrLit s)
  | .node t cs => mkAppN (mkConst ``Silmaril.SpecTec.SExp.node) #[mkStrLit t, qSExps cs]

/-- Reflect a `List SExp` as a term. -/
partial def qSExps : List SExp → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Silmaril.SpecTec.SExp)
  | x :: xs =>
      mkAppN (mkConst ``List.cons [Level.zero])
        #[mkConst ``Silmaril.SpecTec.SExp, qSExp x, qSExps xs]

end

/-! ## Un-reflection

`qDef` above is ordinary meta code: nothing in the kernel relates the `Expr`
it builds to the `IL.Def` it was handed, so an elaborator that only emitted
its output would be trusting all 300 lines of it.  The functions below invert
it.  They are not derived from `qDef` — each one reads its constructor names
and argument positions off `Silmaril/SpecTec/IL/Ast.lean` — so a transposed
argument in `qDef` has to be mirrored exactly here to escape notice.

The terms `qDef` builds are in constructor normal form, so no `whnf` and no
instantiation is needed and the traversal is linear in the size of the term.
Type arguments — `List`'s and `Option`'s `α` — are deliberately not inspected:
the kernel has already accepted the emitted constant at type `IL.Def`, so they
are determined by typing. -/

/-- Read a reflected `String` literal. -/
def unqStr : Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

/-- Read a reflected `Nat`.  `mkNatLit` wraps a raw literal in `OfNat.ofNat`;
the bare literal is accepted too. -/
def unqNat (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => some n
    | _ => none

/-- Read a reflected `Int`.  `ToExpr Int` emits an `OfNat.ofNat` literal, or
`Neg.neg` of one for a negative; the `Int.ofNat`/`Int.negSucc` forms are
accepted as well. -/
partial def unqInt (e : Expr) : Option Int :=
  match e.getAppFnArgs with
  | (``Neg.neg, #[_, _, a]) => (fun i => -i) <$> unqInt a
  | (``Int.ofNat, #[a]) => Int.ofNat <$> unqNat a
  | (``Int.negSucc, #[a]) => Int.negSucc <$> unqNat a
  | _ => Int.ofNat <$> unqNat e

/-- Read a reflected `Bool`. -/
def unqBool (e : Expr) : Option Bool :=
  match e.getAppFnArgs with
  | (``Bool.true, #[]) => some true
  | (``Bool.false, #[]) => some false
  | _ => none

/-- Read a reflected `Rat`.  `qNum` rebuilds a rational with `mkRat`, and a
`Rat`'s numerator and denominator are already coprime, so `mkRat q.num q.den`
is `q`. -/
def unqRat (e : Expr) : Option Rat :=
  match e.getAppFnArgs with
  | (``mkRat, #[n, d]) => do return mkRat (← unqInt n) (← unqNat d)
  | _ => none

/-- Read a reflected `List α`, given a reader for `α`. -/
partial def unqList (f : Expr → Option α) (e : Expr) : Option (List α) :=
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => some []
  | (``List.cons, #[_, x, xs]) => do return (← f x) :: (← unqList f xs)
  | _ => none

/-- Read a reflected `Option α`, given a reader for `α`. -/
def unqOption (f : Expr → Option α) (e : Expr) : Option (Option α) :=
  match e.getAppFnArgs with
  | (``Option.none, #[_]) => some none
  | (``Option.some, #[_, a]) => some <$> f a
  | _ => none

/-- Read a reflected `IL.NumTyp`. -/
def unqNumTyp (e : Expr) : Option NumTyp :=
  match e.getAppFnArgs with
  | (``NumTyp.natT, #[]) => some .natT
  | (``NumTyp.intT, #[]) => some .intT
  | (``NumTyp.ratT, #[]) => some .ratT
  | (``NumTyp.realT, #[]) => some .realT
  | _ => none

/-- Read a reflected `IL.OpTyp`. -/
def unqOpTyp (e : Expr) : Option OpTyp :=
  match e.getAppFnArgs with
  | (``OpTyp.boolT, #[]) => some .boolT
  | (``OpTyp.numT, #[a]) => OpTyp.numT <$> unqNumTyp a
  | _ => none

/-- Read a reflected `IL.Num`. -/
def unqNum (e : Expr) : Option Num :=
  match e.getAppFnArgs with
  | (``Num.natN, #[a]) => Num.natN <$> unqNat a
  | (``Num.intN, #[a]) => Num.intN <$> unqInt a
  | (``Num.ratN, #[a]) => Num.ratN <$> unqRat a
  | (``Num.realN, #[a]) => Num.realN <$> unqStr a
  | _ => none

/-- Read a reflected `IL.UnOp`. -/
def unqUnOp (e : Expr) : Option UnOp :=
  match e.getAppFnArgs with
  | (``UnOp.notOp, #[]) => some .notOp
  | (``UnOp.plusOp, #[]) => some .plusOp
  | (``UnOp.minusOp, #[]) => some .minusOp
  | _ => none

/-- Read a reflected `IL.BinOp`. -/
def unqBinOp (e : Expr) : Option BinOp :=
  match e.getAppFnArgs with
  | (``BinOp.andOp, #[]) => some .andOp
  | (``BinOp.orOp, #[]) => some .orOp
  | (``BinOp.implOp, #[]) => some .implOp
  | (``BinOp.equivOp, #[]) => some .equivOp
  | (``BinOp.addOp, #[]) => some .addOp
  | (``BinOp.subOp, #[]) => some .subOp
  | (``BinOp.mulOp, #[]) => some .mulOp
  | (``BinOp.divOp, #[]) => some .divOp
  | (``BinOp.modOp, #[]) => some .modOp
  | (``BinOp.powOp, #[]) => some .powOp
  | _ => none

/-- Read a reflected `IL.CmpOp`. -/
def unqCmpOp (e : Expr) : Option CmpOp :=
  match e.getAppFnArgs with
  | (``CmpOp.eqOp, #[]) => some .eqOp
  | (``CmpOp.neOp, #[]) => some .neOp
  | (``CmpOp.ltOp, #[]) => some .ltOp
  | (``CmpOp.gtOp, #[]) => some .gtOp
  | (``CmpOp.leOp, #[]) => some .leOp
  | (``CmpOp.geOp, #[]) => some .geOp
  | _ => none

mutual

/-- Read a reflected `IL.Iter` (`Ast.lean`, `inductive Iter`). -/
partial def unqIter (e : Expr) : Option Iter :=
  match e.getAppFnArgs with
  | (``Iter.opt, #[]) => some .opt
  | (``Iter.list, #[]) => some .list
  | (``Iter.list1, #[]) => some .list1
  | (``Iter.listN, #[a, b]) => do return .listN (← unqExp a) (← unqOption unqStr b)
  | _ => none

/-- Read a reflected `IL.Typ` (`Ast.lean`, `inductive Typ`). -/
partial def unqTyp (e : Expr) : Option Typ :=
  match e.getAppFnArgs with
  | (``Typ.varT, #[a, b]) => do return .varT (← unqStr a) (← unqList unqArg b)
  | (``Typ.boolT, #[]) => some .boolT
  | (``Typ.numT, #[a]) => Typ.numT <$> unqNumTyp a
  | (``Typ.textT, #[]) => some .textT
  | (``Typ.tupT, #[a]) => Typ.tupT <$> unqList unqTypBind a
  | (``Typ.iterT, #[a, b]) => do return .iterT (← unqTyp a) (← unqIter b)
  | _ => none

/-- Read a reflected `IL.TypBind` (`Ast.lean`, `inductive TypBind`). -/
partial def unqTypBind (e : Expr) : Option TypBind :=
  match e.getAppFnArgs with
  | (``TypBind.mk, #[a, b]) => do return .mk (← unqStr a) (← unqTyp b)
  | _ => none

/-- Read a reflected `IL.DefTyp` (`Ast.lean`, `inductive DefTyp`). -/
partial def unqDefTyp (e : Expr) : Option DefTyp :=
  match e.getAppFnArgs with
  | (``DefTyp.aliasT, #[a]) => DefTyp.aliasT <$> unqTyp a
  | (``DefTyp.structT, #[a]) => DefTyp.structT <$> unqList unqTypField a
  | (``DefTyp.variantT, #[a]) => DefTyp.variantT <$> unqList unqTypCase a
  | _ => none

/-- Read a reflected `IL.TypField` (`Ast.lean`, `inductive TypField`). -/
partial def unqTypField (e : Expr) : Option TypField :=
  match e.getAppFnArgs with
  | (``TypField.mk, #[a, b, c, d]) =>
      do return .mk (← unqStr a) (← unqTyp b) (← unqList unqParam c) (← unqList unqPrem d)
  | _ => none

/-- Read a reflected `IL.TypCase` (`Ast.lean`, `inductive TypCase`). -/
partial def unqTypCase (e : Expr) : Option TypCase :=
  match e.getAppFnArgs with
  | (``TypCase.mk, #[a, b, c, d]) =>
      do return .mk (← unqStr a) (← unqTyp b) (← unqList unqParam c) (← unqList unqPrem d)
  | _ => none

/-- Read a reflected `IL.Exp` (`Ast.lean`, `inductive Exp`). -/
partial def unqExp (e : Expr) : Option Exp :=
  match e.getAppFnArgs with
  | (``Exp.varE, #[a]) => Exp.varE <$> unqStr a
  | (``Exp.boolE, #[a]) => Exp.boolE <$> unqBool a
  | (``Exp.numE, #[a]) => Exp.numE <$> unqNum a
  | (``Exp.textE, #[a]) => Exp.textE <$> unqStr a
  | (``Exp.unE, #[a, b, c]) => do return .unE (← unqUnOp a) (← unqOpTyp b) (← unqExp c)
  | (``Exp.binE, #[a, b, c, d]) =>
      do return .binE (← unqBinOp a) (← unqOpTyp b) (← unqExp c) (← unqExp d)
  | (``Exp.cmpE, #[a, b, c, d]) =>
      do return .cmpE (← unqCmpOp a) (← unqOpTyp b) (← unqExp c) (← unqExp d)
  | (``Exp.tupE, #[a]) => Exp.tupE <$> unqList unqExp a
  | (``Exp.projE, #[a, b]) => do return .projE (← unqExp a) (← unqInt b)
  | (``Exp.caseE, #[a, b]) => do return .caseE (← unqStr a) (← unqExp b)
  | (``Exp.uncaseE, #[a, b]) => do return .uncaseE (← unqExp a) (← unqStr b)
  | (``Exp.optE, #[a]) => Exp.optE <$> unqOption unqExp a
  | (``Exp.theE, #[a]) => Exp.theE <$> unqExp a
  | (``Exp.strE, #[a]) => Exp.strE <$> unqList unqExpField a
  | (``Exp.dotE, #[a, b]) => do return .dotE (← unqExp a) (← unqStr b)
  | (``Exp.compE, #[a, b]) => do return .compE (← unqExp a) (← unqExp b)
  | (``Exp.listE, #[a]) => Exp.listE <$> unqList unqExp a
  | (``Exp.liftE, #[a]) => Exp.liftE <$> unqExp a
  | (``Exp.memE, #[a, b]) => do return .memE (← unqExp a) (← unqExp b)
  | (``Exp.lenE, #[a]) => Exp.lenE <$> unqExp a
  | (``Exp.catE, #[a, b]) => do return .catE (← unqExp a) (← unqExp b)
  | (``Exp.idxE, #[a, b]) => do return .idxE (← unqExp a) (← unqExp b)
  | (``Exp.sliceE, #[a, b, c]) => do return .sliceE (← unqExp a) (← unqExp b) (← unqExp c)
  | (``Exp.updE, #[a, b, c]) => do return .updE (← unqExp a) (← unqPath b) (← unqExp c)
  | (``Exp.extE, #[a, b, c]) => do return .extE (← unqExp a) (← unqPath b) (← unqExp c)
  | (``Exp.callE, #[a, b]) => do return .callE (← unqStr a) (← unqList unqArg b)
  | (``Exp.iterE, #[a, b]) => do return .iterE (← unqExp a) (← unqIterExp b)
  | (``Exp.cvtE, #[a, b, c]) => do return .cvtE (← unqExp a) (← unqNumTyp b) (← unqNumTyp c)
  | (``Exp.subE, #[a, b, c]) => do return .subE (← unqExp a) (← unqTyp b) (← unqTyp c)
  | _ => none

/-- Read a reflected `IL.ExpField` (`Ast.lean`, `inductive ExpField`). -/
partial def unqExpField (e : Expr) : Option ExpField :=
  match e.getAppFnArgs with
  | (``ExpField.mk, #[a, b]) => do return .mk (← unqStr a) (← unqExp b)
  | _ => none

/-- Read a reflected `IL.Path` (`Ast.lean`, `inductive Path`). -/
partial def unqPath (e : Expr) : Option Path :=
  match e.getAppFnArgs with
  | (``Path.rootP, #[]) => some .rootP
  | (``Path.idxP, #[a, b]) => do return .idxP (← unqPath a) (← unqExp b)
  | (``Path.sliceP, #[a, b, c]) => do return .sliceP (← unqPath a) (← unqExp b) (← unqExp c)
  | (``Path.dotP, #[a, b]) => do return .dotP (← unqPath a) (← unqStr b)
  | _ => none

/-- Read a reflected `IL.IterExp` (`Ast.lean`, `inductive IterExp`). -/
partial def unqIterExp (e : Expr) : Option IterExp :=
  match e.getAppFnArgs with
  | (``IterExp.mk, #[a, b]) => do return .mk (← unqIter a) (← unqList unqDom b)
  | _ => none

/-- Read a reflected `IL.Dom` (`Ast.lean`, `inductive Dom`). -/
partial def unqDom (e : Expr) : Option Dom :=
  match e.getAppFnArgs with
  | (``Dom.mk, #[a, b]) => do return .mk (← unqStr a) (← unqExp b)
  | _ => none

/-- Read a reflected `IL.Sym` (`Ast.lean`, `inductive Sym`). -/
partial def unqSym (e : Expr) : Option Sym :=
  match e.getAppFnArgs with
  | (``Sym.varG, #[a, b]) => do return .varG (← unqStr a) (← unqList unqArg b)
  | (``Sym.numG, #[a]) => Sym.numG <$> unqNat a
  | (``Sym.textG, #[a]) => Sym.textG <$> unqStr a
  | (``Sym.epsG, #[]) => some .epsG
  | (``Sym.seqG, #[a]) => Sym.seqG <$> unqList unqSym a
  | (``Sym.altG, #[a]) => Sym.altG <$> unqList unqSym a
  | (``Sym.rangeG, #[a, b]) => do return .rangeG (← unqSym a) (← unqSym b)
  | (``Sym.iterG, #[a, b]) => do return .iterG (← unqSym a) (← unqIterExp b)
  | (``Sym.attrG, #[a, b]) => do return .attrG (← unqExp a) (← unqSym b)
  | _ => none

/-- Read a reflected `IL.Arg` (`Ast.lean`, `inductive Arg`). -/
partial def unqArg (e : Expr) : Option Arg :=
  match e.getAppFnArgs with
  | (``Arg.expA, #[a]) => Arg.expA <$> unqExp a
  | (``Arg.typA, #[a]) => Arg.typA <$> unqTyp a
  | (``Arg.defA, #[a]) => Arg.defA <$> unqStr a
  | (``Arg.gramA, #[a]) => Arg.gramA <$> unqSym a
  | _ => none

/-- Read a reflected `IL.Param` (`Ast.lean`, `inductive Param`). -/
partial def unqParam (e : Expr) : Option Param :=
  match e.getAppFnArgs with
  | (``Param.expP, #[a, b]) => do return .expP (← unqStr a) (← unqTyp b)
  | (``Param.typP, #[a]) => Param.typP <$> unqStr a
  | (``Param.defP, #[a, b, c]) =>
      do return .defP (← unqStr a) (← unqList unqParam b) (← unqTyp c)
  | (``Param.gramP, #[a, b, c]) =>
      do return .gramP (← unqStr a) (← unqList unqParam b) (← unqTyp c)
  | _ => none

/-- Read a reflected `IL.Prem` (`Ast.lean`, `inductive Prem`). -/
partial def unqPrem (e : Expr) : Option Prem :=
  match e.getAppFnArgs with
  | (``Prem.rulePr, #[a, b, c, d]) =>
      do return .rulePr (← unqStr a) (← unqList unqArg b) (← unqStr c) (← unqExp d)
  | (``Prem.ifPr, #[a]) => Prem.ifPr <$> unqExp a
  | (``Prem.letPr, #[a, b]) => do return .letPr (← unqExp a) (← unqExp b)
  | (``Prem.elsePr, #[]) => some .elsePr
  | (``Prem.iterPr, #[a, b]) => do return .iterPr (← unqPrem a) (← unqIterExp b)
  | _ => none

/-- Read a reflected `IL.Def` (`Ast.lean`, `inductive Def`). -/
partial def unqDef (e : Expr) : Option Def :=
  match e.getAppFnArgs with
  | (``Def.typD, #[a, b, c]) =>
      do return .typD (← unqStr a) (← unqList unqParam b) (← unqList unqInst c)
  | (``Def.relD, #[a, b, c, d, f]) =>
      do return .relD (← unqStr a) (← unqList unqParam b) (← unqStr c) (← unqTyp d)
          (← unqList unqRule f)
  | (``Def.decD, #[a, b, c, d]) =>
      do return .decD (← unqStr a) (← unqList unqParam b) (← unqTyp c) (← unqList unqClause d)
  | (``Def.gramD, #[a, b, c, d]) =>
      do return .gramD (← unqStr a) (← unqList unqParam b) (← unqTyp c) (← unqList unqProd d)
  | (``Def.recD, #[a]) => Def.recD <$> unqList unqDef a
  | _ => none

/-- Read a reflected `IL.Inst` (`Ast.lean`, `inductive Inst`). -/
partial def unqInst (e : Expr) : Option Inst :=
  match e.getAppFnArgs with
  | (``Inst.instD, #[a, b, c]) =>
      do return .instD (← unqList unqParam a) (← unqList unqArg b) (← unqDefTyp c)
  | _ => none

/-- Read a reflected `IL.Rule` (`Ast.lean`, `inductive Rule`). -/
partial def unqRule (e : Expr) : Option Rule :=
  match e.getAppFnArgs with
  | (``Rule.ruleD, #[a, b, c, d, f]) =>
      do return .ruleD (← unqStr a) (← unqList unqParam b) (← unqStr c) (← unqExp d)
          (← unqList unqPrem f)
  | _ => none

/-- Read a reflected `IL.Clause` (`Ast.lean`, `inductive Clause`). -/
partial def unqClause (e : Expr) : Option Clause :=
  match e.getAppFnArgs with
  | (``Clause.defD, #[a, b, c, d]) =>
      do return .defD (← unqList unqParam a) (← unqList unqArg b) (← unqExp c)
          (← unqList unqPrem d)
  | _ => none

/-- Read a reflected `IL.Prod` (`Ast.lean`, `inductive Prod`). -/
partial def unqProd (e : Expr) : Option Prod :=
  match e.getAppFnArgs with
  | (``Prod.prodD, #[a, b, c, d]) =>
      do return .prodD (← unqList unqParam a) (← unqSym b) (← unqExp c) (← unqList unqPrem d)
  | _ => none

end

/-- Read a reflected `List IL.Def`. -/
def unqDefs : Expr → Option (List Def) := unqList unqDef

/-! ## The import command -/

/-- `List α` at a reflected element type. -/
def mkListType (ty : Expr) : Expr := mkApp (mkConst ``List [Level.zero]) ty

/-- Add a definition built directly as an `Expr`, bypassing the term
elaborator: the generated terms are large and already fully elaborated. -/
def addDefn (name : Name) (type value : Expr) : CoreM Unit := do
  let decl : DefinitionVal :=
    { name := name, levelParams := [], type := type, value := value,
      hints := .regular 0, safety := .safe }
  addDecl (.defnDecl decl)

/-- Add a theorem built directly as an `Expr`. -/
def addThm (name : Name) (type value : Expr) : CoreM Unit := do
  let decl : TheoremVal :=
    { name := name, levelParams := [], type := type, value := value }
  addDecl (.thmDecl decl)

/-- Read, parse and decode an `--ast` file. -/
def readScript (path : String) : CommandElabM (List SExp × Script) := do
  unless (← System.FilePath.pathExists path) do
    throwError "spectec_import: no such file: {path} (paths are relative to {← IO.currentDir})"
  let contents ← IO.FS.readFile path
  let forms ← match SExp.parseStream contents with
    | .error message => throwError "spectec_import: {path} is not an S-expression stream: {message}"
    | .ok forms => pure forms
  let some script := decodeScript? forms
    | throwError "spectec_import: {path} is not a printed SpecTec IL script"
  pure (forms, script)

/-- The value the kernel accepted for the constant `n`. -/
def constValue (n : Name) : CommandElabM Expr := do
  let some info := (← getEnv).find? n
    | throwError "spectec_import: {n} is not in the environment"
  let some value := info.value?
    | throwError "spectec_import: {n} has no value"
  pure value

/-- Re-read the term the kernel accepted for `n` and check that it denotes the
definition that `s` decoded to.

`unqDef` recovers the `IL.Def` the term stands for; the comparison is then
made through the printer, because `IL.Def` has no `DecidableEq` instance.
That loses nothing: when `decodeDef? s = some d`, `defS d' = s` is
*equivalent* to `d' = d` — left to right by `IL.decodeDef?_defS`, right to
left by `IL.defS_of_decodeDef?`. -/
def checkDefn (n : Name) (s : SExp) : CommandElabM Unit := do
  let value ← constValue n
  let some d := unqDef value
    | throwError "spectec_import: the term emitted for {n} is not a reflected IL.Def"
  unless defS d == s do
    throwError "spectec_import: the term emitted for {n} does not denote the \
      definition it was decoded from; `qDef` and `unqDef` disagree"

/-- Check that the script constant `name` is exactly the `len` per-definition
constants `chunk.0 … chunk.(len-1)`, in that order. -/
def checkSpine (name chunk : Name) (len : Nat) : CommandElabM Unit := do
  let value ← constValue name
  let some names := unqList (·.constName?) value
    | throwError "spectec_import: the term emitted for {name} is not a list of constants"
  let expected := (List.range len).map (Name.mkNum chunk ·)
  unless names == expected do
    throwError "spectec_import: {name} is not its {len} definitions in order"

/-- Check that `name.sexps` is `IL.scriptS` applied to `name`, which is what
makes `name.decodes` say anything about `name`. -/
def checkSexps (name : Name) : CommandElabM Unit := do
  let value ← constValue (name ++ `sexps)
  match value.getAppFnArgs with
  | (``scriptS, #[a]) =>
      unless a.constName? == some name do
        throwError "spectec_import: {name}.sexps is `IL.scriptS` of the wrong script"
  | _ => throwError "spectec_import: {name}.sexps is not `IL.scriptS {name}`"

/-- `spectec_import name from "file"` — see the module documentation. -/
syntax (name := spectecImport) "spectec_import " ident " from " str : command

/-- Elaborate `spectec_import`. -/
@[command_elab spectecImport]
def elabSpectecImport : CommandElab := fun stx => do
  let `(command| spectec_import $id:ident from $path:str) := stx | throwUnsupportedSyntax
  let path := path.getString
  let (forms, script) ← readScript path
  let name := (← getCurrNamespace) ++ id.getId
  let defTy := mkIL ``Def
  let chunk := name ++ `defs
  let mut refs : List Expr := []
  for i in [0:script.length] do
    let n := Name.mkNum chunk i
    liftCoreM <| addDefn n defTy (qDef script[i]!)
    refs := mkConst n :: refs
  let scriptTy := mkListType defTy
  let value := refs.foldl (fun acc e =>
    mkAppN (mkConst ``List.cons [Level.zero]) #[defTy, e, acc])
    (mkApp (mkConst ``List.nil [Level.zero]) defTy)
  liftCoreM <| addDefn name scriptTy value
  let sexpTy := mkListType (mkConst ``Silmaril.SpecTec.SExp)
  liftCoreM <| addDefn (name ++ `sexps) sexpTy (mkApp (mkIL ``scriptS) (mkConst name))
  let lhs := mkApp (mkIL ``decodeScript?) (mkConst (name ++ `sexps))
  let rhs := mkAppN (mkConst ``Option.some [Level.zero])
    #[mkApp (mkConst ``List [Level.zero]) defTy, mkConst name]
  let ty := mkAppN (mkConst ``Eq [Level.succ Level.zero])
    #[mkApp (mkConst ``Option [Level.zero]) (mkApp (mkConst ``List [Level.zero]) defTy), lhs, rhs]
  liftCoreM <| addThm (name ++ `decodes) ty (mkApp (mkIL ``decodeScript?_scriptS) (mkConst name))
  let start ← IO.monoMsNow
  let formArr := forms.toArray
  unless formArr.size == script.length do
    throwError "spectec_import: {formArr.size} forms decoded to {script.length} definitions"
  for i in [0:script.length] do
    checkDefn (Name.mkNum chunk i) formArr[i]!
  checkSpine name chunk script.length
  checkSexps name
  let elapsed := (← IO.monoMsNow) - start
  logInfo m!"spectec_import {id.getId}: {script.length} definitions from {path} \
    ({forms.length} top-level S-expressions, re-read from the environment in {elapsed} ms)"

/-- `spectec_sexp% "(…)"` elaborates a literal S-expression. -/
syntax (name := spectecSexp) "spectec_sexp% " str : term

/-- Elaborate `spectec_sexp%`. -/
@[term_elab spectecSexp]
def elabSpectecSexp : TermElab := fun stx _ => do
  let `(spectec_sexp% $s:str) := stx | throwUnsupportedSyntax
  match SExp.parse s.getString with
  | .error message => throwError "spectec_sexp%: {message}"
  | .ok e => pure (qSExp e)

/-- `spectec_def% "(…)"` elaborates a literal top-level IL definition. -/
syntax (name := spectecDef) "spectec_def% " str : term

/-- Elaborate `spectec_def%`. -/
@[term_elab spectecDef]
def elabSpectecDef : TermElab := fun stx _ => do
  let `(spectec_def% $s:str) := stx | throwUnsupportedSyntax
  match SExp.parse s.getString with
  | .error message => throwError "spectec_def%: {message}"
  | .ok e =>
      let some d := decodeDef? e | throwError "spectec_def%: not a printed SpecTec IL definition"
      pure (qDef d)

end Silmaril.SpecTec.IL
