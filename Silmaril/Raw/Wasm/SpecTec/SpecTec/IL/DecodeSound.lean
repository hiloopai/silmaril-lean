module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.EscapeFacts

/-!
# `Decode.lean` inverts `Print.lean`

`decodeDef? (defS d) = some d` for every `d : IL.Def`, with no side
conditions, and the companion statement for every other function in
`Silmaril/SpecTec/IL/Print.lean`.  Consequently `defS` is injective, so the
`--ast` rendering of a script determines the script.

## Structure of the proof

Everything below the leaf lemmas is one `mutual` block of theorems, written
as a mutual *structural* recursion over `spectec/src/il/ast.ml`'s recursive
group — the same shape as the printers in `Print.lean` and
`SExp.ofTExpr_toTExpr` in `Silmaril/SpecTec/SExp/Basic.lean`.

The only non-mechanical part is the `param`/`arg` prefix that
`spectec/src/backend-ast/print.ml:186,196` and friends concatenate into a
single child list with no separator.  Reading it back relies on three facts,
all proved before the block because none of them needs induction:

* every printed `param` is `isParamShaped` and every printed `arg` is not
  (`isParamShaped_paramS`, `isParamShaped_argS`); the `typ` case of the
  second is where `decodeText?_typS` is used — a printed `typ` is never a
  quoted atom;
* every printed `param` and `arg` is `isPATag`, and nothing that can *follow*
  such a prefix is (`isPATag_expS`, `isPATag_typS`, …);
* `isParamShaped` refines `isPATag` (`isParamShaped_eq_false`).

`NotPA` packages "this child list does not start with a `param` or an `arg`",
which is the side condition the two splitting lemmas
`decodeArgsRest?_argsS` and `decodeParamsRest?_paramsS` carry.  It is
discharged at each use site from the `isPATag_*` facts.

`decodeParamsRest?_paramsArgsS`, the one site where a parameter prefix and an
argument prefix meet (`inst` and `clause`), takes the argument half as a
*hypothesis* rather than calling the argument lemma from its own base case:
that keeps its recursion structural in the parameter list alone, and the
caller — which has both lists as subterms of the same constructor — supplies
the hypothesis.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

open Silmaril.SpecTec (SExp)

/-! ## Leaves

Each of these inverts one of the non-recursive printers of
`spectec/src/backend-ast/print.ml:11-68`. -/

/-- `decodeText?` inverts `textS` (`print.ml:12`). -/
@[simp] theorem decodeText?_textS (x : String) : decodeText? (textS x) = some x := by
  simp [decodeText?, textS]

/-- `decodeBool?` inverts `boolS` (`print.ml:11`). -/
@[simp] theorem decodeBool?_boolS (b : Bool) : decodeBool? (boolS b) = some b := by
  cases b <;> rfl

/-- `decodeUnOp?` inverts `unOpS` (`print.ml:25`). -/
@[simp] theorem decodeUnOp?_unOpS (op : UnOp) : decodeUnOp? (unOpS op) = some op := by
  cases op <;> rfl

/-- `decodeBinOp?` inverts `binOpS` (`print.ml:32`). -/
@[simp] theorem decodeBinOp?_binOpS (op : BinOp) : decodeBinOp? (binOpS op) = some op := by
  cases op <;> rfl

/-- `decodeCmpOp?` inverts `cmpOpS` (`print.ml:44`). -/
@[simp] theorem decodeCmpOp?_cmpOpS (op : CmpOp) : decodeCmpOp? (cmpOpS op) = some op := by
  cases op <;> rfl

/-- `decodeNumTyp?` inverts `numTypS` (`print.ml:65`). -/
@[simp] theorem decodeNumTyp?_numTypS (t : NumTyp) : decodeNumTyp? (numTypS t) = some t := by
  cases t <;> rfl

/-- `decodeOpTyp?` inverts `opTypS` (`print.ml:67`). -/
@[simp] theorem decodeOpTyp?_opTypS (t : OpTyp) : decodeOpTyp? (opTypS t) = some t := by
  cases t with
  | boolT => rfl
  | numT t => cases t <;> rfl

/-- `decodeNum?` inverts `numS` (`print.ml:16`).  The rational case is the
only one with a side condition in `decodeNum?`, and `Rat` discharges it:
`Rat.den_nz` and `Rat.reduced` say exactly that a Lean rational is in the
reduced form zarith's `Q.num`/`Q.den` print. -/
@[simp] theorem decodeNum?_numS (n : Num) : decodeNum? (numS n) = some n := by
  cases n with
  | natN n => simp [numS, decodeNum?]
  | intN i => simp [numS, decodeNum?]
  | ratN q =>
      simp [numS, decodeNum?, Digits.parseRatString?_ratString _ q.den_pos]
      exact q.reduced
  | realN r => rfl

/-! ## Shape facts for `param`/`arg` prefixes

`print.ml:186,191,196,201,206` glue a parameter list, an argument list and a
fixed tail into one child list.  These are the finite case splits that make
the three boundaries readable; none of them needs induction, because the tag
of a printed child is fixed by its head constructor. -/

/-- A printed `typ` is never a quoted atom: it is a node tagged `var`, `tup`
or `iter` (`print.ml:73,77,78`), or one of the six bare atoms `bool`, `text`,
`nat`, `int`, `rat`, `real` (`print.ml:65,74,76`).  This is what distinguishes
the argument `(typ t)` from the parameter `(typ x)`. -/
theorem decodeText?_typS (t : Typ) : decodeText? (typS t) = none := by
  cases t with
  | varT => rfl
  | boolT => decide
  | numT t => cases t <;> decide
  | textT => decide
  | tupT => rfl
  | iterT => rfl

/-- A quoted atom is not tagged `exp`, `typ`, `def` or `gram`: it is an atom. -/
theorem isPATag_textS (x : String) : isPATag (textS x) = false := rfl

/-- A printed `typ` never looks like a `param` or an `arg`. -/
theorem isPATag_typS (t : Typ) : isPATag (typS t) = false := by
  cases t with
  | numT t => cases t <;> rfl
  | _ => rfl

/-- A printed `exp` never looks like a `param` or an `arg`. -/
theorem isPATag_expS (e : Exp) : isPATag (expS e) = false := by
  cases e <;> try rfl
  case optE o => cases o <;> rfl

/-- A printed `sym` never looks like a `param` or an `arg`. -/
theorem isPATag_symS (g : Sym) : isPATag (symS g) = false := by cases g <;> rfl

/-- A printed `prem` never looks like a `param` or an `arg`. -/
theorem isPATag_premS (p : Prem) : isPATag (premS p) = false := by cases p <;> rfl

/-- A printed `deftyp` never looks like a `param` or an `arg`. -/
theorem isPATag_defTypS (dt : DefTyp) : isPATag (defTypS dt) = false := by cases dt <;> rfl

/-- A printed `inst` never looks like a `param` or an `arg`. -/
theorem isPATag_instS (i : Inst) : isPATag (instS i) = false := by cases i; rfl

/-- A printed `rule` never looks like a `param` or an `arg`. -/
theorem isPATag_ruleS (r : Rule) : isPATag (ruleS r) = false := by cases r; rfl

/-- A printed `clause` never looks like a `param` or an `arg`. -/
theorem isPATag_clauseS (c : Clause) : isPATag (clauseS c) = false := by cases c; rfl

/-- A printed `prod` never looks like a `param` or an `arg`. -/
theorem isPATag_prodS (q : Prod) : isPATag (prodS q) = false := by cases q; rfl

/-- Every printed `arg` is tagged `exp`, `typ`, `def` or `gram`
(`print.ml:172`). -/
theorem isPATag_argS (a : Arg) : isPATag (argS a) = true := by cases a <;> rfl

/-- Every printed `param` is tagged `exp`, `typ`, `def` or `gram`
(`print.ml:179`). -/
theorem isPATag_paramS (p : Param) : isPATag (paramS p) = true := by cases p <;> rfl

/-- Every printed `param` has the parameter shape (`print.ml:179`). -/
theorem isParamShaped_paramS (p : Param) : isParamShaped (paramS p) = true := by
  cases p with
  | expP => rfl
  | typP x => simp [paramS, isParamShaped]
  | defP x ps t => simp [paramS, isParamShaped]
  | gramP x ps t => simp [paramS, isParamShaped]

/-- No printed `arg` has the parameter shape (`print.ml:172`). -/
theorem isParamShaped_argS (a : Arg) : isParamShaped (argS a) = false := by
  cases a with
  | expA => rfl
  | typA t => simp [argS, isParamShaped, decodeText?_typS]
  | defA => rfl
  | gramA => rfl

/-- `isParamShaped` refines `isPATag`: a child that is not even tagged
`exp`, `typ`, `def` or `gram` cannot have the parameter shape. -/
theorem isParamShaped_eq_false {k : SExp} (h : isPATag k = false) :
    isParamShaped k = false := by
  unfold isParamShaped
  split <;> simp_all [isPATag]

/-! ## The side condition on a tail -/

/-- A child list that does not start with something that could be a `param`
or an `arg`.  This is the hypothesis under which `decodeArgsRest?` and
`decodeParamsRest?` stop exactly where the printer's prefix ends. -/
def NotPA : List SExp → Prop
  | [] => True
  | k :: _ => isPATag k = false

/-- The empty tail satisfies `NotPA`. -/
theorem notPA_nil : NotPA [] := trivial

/-- A tail headed by a non-`isPATag` child satisfies `NotPA`. -/
theorem notPA_cons {k : SExp} {ks : List SExp} (h : isPATag k = false) :
    NotPA (k :: ks) := h

/-- A tail headed by a quoted atom satisfies `NotPA`. -/
theorem notPA_textS (x : String) (ks : List SExp) : NotPA (textS x :: ks) :=
  notPA_cons (isPATag_textS x)

/-- A tail headed by a printed `typ` satisfies `NotPA`. -/
theorem notPA_typS (t : Typ) (ks : List SExp) : NotPA (typS t :: ks) :=
  notPA_cons (isPATag_typS t)

/-- A tail headed by a printed `exp` satisfies `NotPA`. -/
theorem notPA_expS (e : Exp) (ks : List SExp) : NotPA (expS e :: ks) :=
  notPA_cons (isPATag_expS e)

/-- A tail headed by a printed `sym` satisfies `NotPA`. -/
theorem notPA_symS (g : Sym) (ks : List SExp) : NotPA (symS g :: ks) :=
  notPA_cons (isPATag_symS g)

/-- A tail headed by a printed `deftyp` satisfies `NotPA`. -/
theorem notPA_defTypS (dt : DefTyp) (ks : List SExp) : NotPA (defTypS dt :: ks) :=
  notPA_cons (isPATag_defTypS dt)

/-- A printed `prem` list satisfies `NotPA`. -/
theorem notPA_premsS (ps : List Prem) : NotPA (premsS ps) := by
  cases ps with
  | nil => trivial
  | cons p _ => exact isPATag_premS p

/-- A printed `inst` list satisfies `NotPA`. -/
theorem notPA_instsS (is : List Inst) : NotPA (instsS is) := by
  cases is with
  | nil => trivial
  | cons i _ => exact isPATag_instS i

/-- Under `NotPA`, `decodeArgsRest?` reads no arguments at all. -/
theorem decodeArgsRest?_of_notPA {rest : List SExp} (h : NotPA rest) :
    decodeArgsRest? rest = some ([], rest) := by
  cases rest with
  | nil => rfl
  | cons k ks => simp [decodeArgsRest?, show isPATag k = false from h]

/-- Under `NotPA`, `decodeParamsRest?` reads no parameters and no arguments. -/
theorem decodeParamsRest?_of_notPA {rest : List SExp} (h : NotPA rest) :
    decodeParamsRest? rest = some ([], [], rest) := by
  cases rest with
  | nil => rfl
  | cons k ks =>
      have h1 : isPATag k = false := h
      simp [decodeParamsRest?, h1, isParamShaped_eq_false h1]

/-! ## The recursive group

One mutual structural recursion over `il/ast.ml`'s recursive group, in the
order of `Print.lean`. -/

mutual

/-- `decodeIter?` inverts `iterS` (`print.ml:55`). -/
theorem decodeIter?_iterS : ∀ it : Iter, decodeIter? (iterS it) = some it
  | .opt => rfl
  | .list => rfl
  | .list1 => rfl
  | .listN e none => by simp [iterS, decodeIter?, decodeExp?_expS e]
  | .listN e (some x) => by simp [iterS, decodeIter?, decodeExp?_expS e]

/-- `decodeTyp?` inverts `typS` (`print.ml:71`). -/
theorem decodeTyp?_typS : ∀ t : Typ, decodeTyp? (typS t) = some t
  | .varT x args => by simp [typS, decodeTyp?, decodeArgs?_argsS args]
  | .boolT => rfl
  | .numT t => by cases t <;> rfl
  | .textT => rfl
  | .tupT binds => by simp [typS, decodeTyp?, decodeTypBinds?_typBindsS binds]
  | .iterT t it => by simp [typS, decodeTyp?, decodeTyp?_typS t, decodeIter?_iterS it]

/-- `decodeTypBinds?` inverts `typBindsS` (`print.ml:77`). -/
theorem decodeTypBinds?_typBindsS :
    ∀ bs : List TypBind, decodeTypBinds? (typBindsS bs) = some bs
  | [] => rfl
  | b :: bs => by
      simp [typBindsS, decodeTypBinds?, decodeTypBind?_typBindS b,
        decodeTypBinds?_typBindsS bs]

/-- `decodeTypBind?` inverts `typBindS` (`print.ml:86`). -/
theorem decodeTypBind?_typBindS : ∀ b : TypBind, decodeTypBind? (typBindS b) = some b
  | .mk x t => by simp [typBindS, decodeTypBind?, decodeTyp?_typS t]

/-- `decodeDefTyp?` inverts `defTypS` (`print.ml:80`). -/
theorem decodeDefTyp?_defTypS : ∀ dt : DefTyp, decodeDefTyp? (defTypS dt) = some dt
  | .aliasT t => by simp [defTypS, decodeDefTyp?, decodeTyp?_typS t]
  | .structT fs => by simp [defTypS, decodeDefTyp?, decodeTypFields?_typFieldsS fs]
  | .variantT cs => by simp [defTypS, decodeDefTyp?, decodeTypCases?_typCasesS cs]

/-- `decodeTypFields?` inverts `typFieldsS` (`print.ml:83`). -/
theorem decodeTypFields?_typFieldsS :
    ∀ fs : List TypField, decodeTypFields? (typFieldsS fs) = some fs
  | [] => rfl
  | f :: fs => by
      simp [typFieldsS, decodeTypFields?, decodeTypField?_typFieldS f,
        decodeTypFields?_typFieldsS fs]

/-- `decodeTypField?` inverts `typFieldS` (`print.ml:89`).  The parameter
prefix is followed by the premise list, which never starts with a `param` or
an `arg`. -/
theorem decodeTypField?_typFieldS : ∀ f : TypField, decodeTypField? (typFieldS f) = some f
  | .mk a t quants prems => by
      simp [typFieldS, decodeTypField?, decodeTyp?_typS t,
        decodeParamsRest?_paramsS quants (premsS prems) (notPA_premsS prems),
        decodePrems?_premsS prems]

/-- `decodeTypCases?` inverts `typCasesS` (`print.ml:84`). -/
theorem decodeTypCases?_typCasesS :
    ∀ cs : List TypCase, decodeTypCases? (typCasesS cs) = some cs
  | [] => rfl
  | c :: cs => by
      simp [typCasesS, decodeTypCases?, decodeTypCase?_typCaseS c,
        decodeTypCases?_typCasesS cs]

/-- `decodeTypCase?` inverts `typCaseS` (`print.ml:92`). -/
theorem decodeTypCase?_typCaseS : ∀ c : TypCase, decodeTypCase? (typCaseS c) = some c
  | .mk op t quants prems => by
      simp [typCaseS, decodeTypCase?, decodeTyp?_typS t,
        decodeParamsRest?_paramsS quants (premsS prems) (notPA_premsS prems),
        decodePrems?_premsS prems]

/-- `decodeExp?` inverts `expS` (`print.ml:98`). -/
theorem decodeExp?_expS : ∀ e : Exp, decodeExp? (expS e) = some e
  | .varE x => by simp [expS, decodeExp?]
  | .boolE b => by simp [expS, decodeExp?]
  | .numE n => by simp [expS, decodeExp?]
  | .textE t => by simp [expS, decodeExp?]
  | .unE op t e => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .binE op t e₁ e₂ => by
      simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .cmpE op t e₁ e₂ => by
      simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .idxE e₁ e₂ => by simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .sliceE e₁ e₂ e₃ => by
      simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂, decodeExp?_expS e₃]
  | .updE e₁ p e₂ => by
      simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂, decodePath?_pathS p]
  | .extE e₁ p e₂ => by
      simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂, decodePath?_pathS p]
  | .strE fields => by simp [expS, decodeExp?, decodeExpFields?_expFieldsS fields]
  | .dotE e a => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .compE e₁ e₂ => by simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .memE e₁ e₂ => by simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .lenE e => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .tupE es => by simp [expS, decodeExp?, decodeExps?_expsS es]
  | .callE x args => by simp [expS, decodeExp?, decodeArgs?_argsS args]
  | .iterE e it => by
      simp [expS, decodeExp?, decodeExp?_expS e, decodeIterExp?_iterExpS it]
  | .projE e i => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .caseE op e => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .uncaseE e op => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .optE none => by simp [expS, decodeExp?]
  | .optE (some e) => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .theE e => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .listE es => by simp [expS, decodeExp?, decodeExps?_expsS es]
  | .liftE e => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .catE e₁ e₂ => by simp [expS, decodeExp?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .cvtE e t₁ t₂ => by simp [expS, decodeExp?, decodeExp?_expS e]
  | .subE e t₁ t₂ => by
      simp [expS, decodeExp?, decodeExp?_expS e, decodeTyp?_typS t₁, decodeTyp?_typS t₂]

/-- `decodeExps?` inverts `expsS` (`print.ml:116,124`). -/
theorem decodeExps?_expsS : ∀ es : List Exp, decodeExps? (expsS es) = some es
  | [] => rfl
  | e :: es => by
      simp [expsS, decodeExps?, decodeExp?_expS e, decodeExps?_expsS es]

/-- `decodeExpFields?` inverts `expFieldsS` (`print.ml:111`). -/
theorem decodeExpFields?_expFieldsS :
    ∀ fs : List ExpField, decodeExpFields? (expFieldsS fs) = some fs
  | [] => rfl
  | f :: fs => by
      simp [expFieldsS, decodeExpFields?, decodeExpField?_expFieldS f,
        decodeExpFields?_expFieldsS fs]

/-- `decodeExpField?` inverts `expFieldS` (`print.ml:130`). -/
theorem decodeExpField?_expFieldS :
    ∀ f : ExpField, decodeExpField? (expFieldS f) = some f
  | .mk a e => by simp [expFieldS, decodeExpField?, decodeExp?_expS e]

/-- `decodePath?` inverts `pathS` (`print.ml:133`). -/
theorem decodePath?_pathS : ∀ p : Path, decodePath? (pathS p) = some p
  | .rootP => rfl
  | .idxP p e => by simp [pathS, decodePath?, decodePath?_pathS p, decodeExp?_expS e]
  | .sliceP p e₁ e₂ => by
      simp [pathS, decodePath?, decodePath?_pathS p, decodeExp?_expS e₁,
        decodeExp?_expS e₂]
  | .dotP p a => by simp [pathS, decodePath?, decodePath?_pathS p]

/-- `decodeIterExp?` inverts `iterExpS` (`print.ml:140`). -/
theorem decodeIterExp?_iterExpS :
    ∀ it : IterExp, decodeIterExp? (iterExpS it) = some it
  | .mk i doms => by
      simp [iterExpS, decodeIterExp?, decodeIter?_iterS i, decodeDoms?_domsS doms]

/-- `decodeDoms?` inverts `domsS` (`print.ml:141`). -/
theorem decodeDoms?_domsS : ∀ ds : List Dom, decodeDoms? (domsS ds) = some ds
  | [] => rfl
  | d :: ds => by simp [domsS, decodeDoms?, decodeDom?_domS d, decodeDoms?_domsS ds]

/-- `decodeDom?` inverts `domS` (`print.ml:141`). -/
theorem decodeDom?_domS : ∀ d : Dom, decodeDom? (domS d) = some d
  | .mk x e => by simp [domS, decodeDom?, decodeExp?_expS e]

/-- `decodeSym?` inverts `symS` (`print.ml:146`). -/
theorem decodeSym?_symS : ∀ g : Sym, decodeSym? (symS g) = some g
  | .varG x args => by simp [symS, decodeSym?, decodeArgs?_argsS args]
  | .numG n => by simp [symS, decodeSym?]
  | .textG t => by simp [symS, decodeSym?]
  | .epsG => rfl
  | .seqG gs => by simp [symS, decodeSym?, decodeSyms?_symsS gs]
  | .altG gs => by simp [symS, decodeSym?, decodeSyms?_symsS gs]
  | .rangeG g₁ g₂ => by
      simp [symS, decodeSym?, decodeSym?_symS g₁, decodeSym?_symS g₂]
  | .iterG g it => by
      simp [symS, decodeSym?, decodeSym?_symS g, decodeIterExp?_iterExpS it]
  | .attrG e g => by simp [symS, decodeSym?, decodeExp?_expS e, decodeSym?_symS g]

/-- `decodeSyms?` inverts `symsS` (`print.ml:152,153`). -/
theorem decodeSyms?_symsS : ∀ gs : List Sym, decodeSyms? (symsS gs) = some gs
  | [] => rfl
  | g :: gs => by simp [symsS, decodeSyms?, decodeSym?_symS g, decodeSyms?_symsS gs]

/-- `decodePrem?` inverts `premS` (`print.ml:161`).  The `rule` premise is
the one place where an argument prefix is followed by a two-element tail
(`print.ml:163`), whose head is a quoted mixop. -/
theorem decodePrem?_premS : ∀ p : Prem, decodePrem? (premS p) = some p
  | .rulePr x args op e => by
      simp [premS, decodePrem?,
        decodeArgsRest?_argsS args [textS op, expS e] (notPA_textS op _),
        decodeExp?_expS e]
  | .ifPr e => by simp [premS, decodePrem?, decodeExp?_expS e]
  | .letPr e₁ e₂ => by
      simp [premS, decodePrem?, decodeExp?_expS e₁, decodeExp?_expS e₂]
  | .elsePr => rfl
  | .iterPr pr it => by
      simp [premS, decodePrem?, decodePrem?_premS pr, decodeIterExp?_iterExpS it]

/-- `decodePrems?` inverts `premsS` (`print.ml:90,93`). -/
theorem decodePrems?_premsS : ∀ ps : List Prem, decodePrems? (premsS ps) = some ps
  | [] => rfl
  | p :: ps => by simp [premsS, decodePrems?, decodePrem?_premS p, decodePrems?_premsS ps]

/-- `decodeArg?` inverts `argS` (`print.ml:172`). -/
theorem decodeArg?_argS : ∀ a : Arg, decodeArg? (argS a) = some a
  | .expA e => by simp [argS, decodeArg?, decodeExp?_expS e]
  | .typA t => by simp [argS, decodeArg?, decodeTyp?_typS t]
  | .defA x => by simp [argS, decodeArg?]
  | .gramA g => by simp [argS, decodeArg?, decodeSym?_symS g]

/-- `decodeArgs?` inverts `argsS` (`print.ml:73,117,148`), where every
remaining child is an argument. -/
theorem decodeArgs?_argsS : ∀ as : List Arg, decodeArgs? (argsS as) = some as
  | [] => rfl
  | a :: as => by simp [argsS, decodeArgs?, decodeArg?_argS a, decodeArgs?_argsS as]

/-- `decodeArgsRest?` splits a printed argument prefix off a tail that cannot
start with a `param` or an `arg`. -/
theorem decodeArgsRest?_argsS : ∀ (as : List Arg) (rest : List SExp), NotPA rest →
    decodeArgsRest? (argsS as ++ rest) = some (as, rest)
  | [], _, h => decodeArgsRest?_of_notPA h
  | a :: as, rest, h => by
      simp [argsS, decodeArgsRest?, isPATag_argS a, decodeArg?_argS a,
        decodeArgsRest?_argsS as rest h]

/-- The same split, read by `decodeParamsRest?`: an argument prefix with no
parameters in front of it. -/
theorem decodeParamsRest?_argsS : ∀ (as : List Arg) (rest : List SExp), NotPA rest →
    decodeParamsRest? (argsS as ++ rest) = some ([], as, rest)
  | [], _, h => decodeParamsRest?_of_notPA h
  | a :: as, rest, h => by
      simp [argsS, decodeParamsRest?, isParamShaped_argS a, isPATag_argS a,
        decodeArg?_argS a, decodeArgsRest?_argsS as rest h]

/-- `decodeParam?` inverts `paramS` (`print.ml:179`).  A `def` or `gram`
parameter is itself a parameter list followed by a single `typ`. -/
theorem decodeParam?_paramS : ∀ p : Param, decodeParam? (paramS p) = some p
  | .expP x t => by simp [paramS, decodeParam?, decodeTyp?_typS t]
  | .typP x => by simp [paramS, decodeParam?]
  | .defP x ps t => by
      simp [paramS, decodeParam?,
        decodeParamsRest?_paramsS ps [typS t] (notPA_typS t []), decodeTyp?_typS t]
  | .gramP x ps t => by
      simp [paramS, decodeParam?,
        decodeParamsRest?_paramsS ps [typS t] (notPA_typS t []), decodeTyp?_typS t]

/-- `decodeParams?` inverts `paramsS` (`print.ml:183`), where every child is
a parameter. -/
theorem decodeParams?_paramsS : ∀ ps : List Param, decodeParams? (paramsS ps) = some ps
  | [] => rfl
  | p :: ps => by
      simp [paramsS, decodeParams?, decodeParam?_paramS p, decodeParams?_paramsS ps]

/-- `decodeParamsRest?` splits a printed parameter prefix off a tail that
cannot start with a `param` or an `arg`; no arguments intervene. -/
theorem decodeParamsRest?_paramsS : ∀ (ps : List Param) (rest : List SExp), NotPA rest →
    decodeParamsRest? (paramsS ps ++ rest) = some (ps, [], rest)
  | [], _, h => decodeParamsRest?_of_notPA h
  | p :: ps, rest, h => by
      simp [paramsS, decodeParamsRest?, isParamShaped_paramS p, decodeParam?_paramS p,
        decodeParamsRest?_paramsS ps rest h]

/-- `decodeParamsRest?` on a parameter prefix followed by an argument prefix
(`print.ml:189,198`).  The argument half is a hypothesis rather than a
recursive call, so that this recursion is structural in `ps` alone; callers
discharge it with `decodeParamsRest?_argsS`. -/
theorem decodeParamsRest?_paramsArgsS :
    ∀ (ps : List Param) (as : List Arg) (rest : List SExp), NotPA rest →
      decodeParamsRest? (argsS as ++ rest) = some ([], as, rest) →
      decodeParamsRest? (paramsS ps ++ (argsS as ++ rest)) = some (ps, as, rest)
  | [], _, _, _, hargs => hargs
  | p :: ps, as, rest, h, hargs => by
      simp [paramsS, decodeParamsRest?, isParamShaped_paramS p, decodeParam?_paramS p,
        decodeParamsRest?_paramsArgsS ps as rest h hargs]

/-- `decodeInst?` inverts `instS` (`print.ml:186`). -/
theorem decodeInst?_instS : ∀ i : Inst, decodeInst? (instS i) = some i
  | .instD quants args dt => by
      simp [instS, decodeInst?, List.append_assoc,
        decodeParamsRest?_paramsArgsS quants args [defTypS dt] (notPA_defTypS dt [])
          (decodeParamsRest?_argsS args [defTypS dt] (notPA_defTypS dt [])),
        decodeDefTyp?_defTypS dt]

/-- `decodeInsts?` inverts `instsS` (`print.ml:209`). -/
theorem decodeInsts?_instsS : ∀ is : List Inst, decodeInsts? (instsS is) = some is
  | [] => rfl
  | i :: is => by simp [instsS, decodeInsts?, decodeInst?_instS i, decodeInsts?_instsS is]

/-- `decodeRule?` inverts `ruleS` (`print.ml:191`). -/
theorem decodeRule?_ruleS : ∀ r : Rule, decodeRule? (ruleS r) = some r
  | .ruleD x quants op e prems => by
      simp [ruleS, decodeRule?, List.append_assoc,
        decodeParamsRest?_paramsS quants (textS op :: expS e :: premsS prems)
          (notPA_textS op _),
        decodeExp?_expS e, decodePrems?_premsS prems]

/-- `decodeRules?` inverts `rulesS` (`print.ml:211`). -/
theorem decodeRules?_rulesS : ∀ rs : List Rule, decodeRules? (rulesS rs) = some rs
  | [] => rfl
  | r :: rs => by simp [rulesS, decodeRules?, decodeRule?_ruleS r, decodeRules?_rulesS rs]

/-- `decodeClause?` inverts `clauseS` (`print.ml:196`). -/
theorem decodeClause?_clauseS : ∀ c : Clause, decodeClause? (clauseS c) = some c
  | .defD quants args e prems => by
      simp [clauseS, decodeClause?, List.append_assoc,
        decodeParamsRest?_paramsArgsS quants args (expS e :: premsS prems)
          (notPA_expS e _) (decodeParamsRest?_argsS args (expS e :: premsS prems)
            (notPA_expS e _)),
        decodeExp?_expS e, decodePrems?_premsS prems]

/-- `decodeClauses?` inverts `clausesS` (`print.ml:213`). -/
theorem decodeClauses?_clausesS :
    ∀ cs : List Clause, decodeClauses? (clausesS cs) = some cs
  | [] => rfl
  | c :: cs => by
      simp [clausesS, decodeClauses?, decodeClause?_clauseS c, decodeClauses?_clausesS cs]

/-- `decodeProd?` inverts `prodS` (`print.ml:201`). -/
theorem decodeProd?_prodS : ∀ q : Prod, decodeProd? (prodS q) = some q
  | .prodD quants g e prems => by
      simp [prodS, decodeProd?, List.append_assoc,
        decodeParamsRest?_paramsS quants (symS g :: expS e :: premsS prems)
          (notPA_symS g _),
        decodeSym?_symS g, decodeExp?_expS e, decodePrems?_premsS prems]

/-- `decodeProds?` inverts `prodsS` (`print.ml:215`). -/
theorem decodeProds?_prodsS : ∀ qs : List Prod, decodeProds? (prodsS qs) = some qs
  | [] => rfl
  | q :: qs => by simp [prodsS, decodeProds?, decodeProd?_prodS q, decodeProds?_prodsS qs]

/-- `decodeDef?` inverts `defS` (`print.ml:206`). -/
theorem decodeDef?_defS : ∀ d : Def, decodeDef? (defS d) = some d
  | .typD x ps insts => by
      simp [defS, decodeDef?,
        decodeParamsRest?_paramsS ps (instsS insts) (notPA_instsS insts),
        decodeInsts?_instsS insts]
  | .relD x ps op t rules => by
      simp [defS, decodeDef?, List.append_assoc,
        decodeParamsRest?_paramsS ps (textS op :: typS t :: rulesS rules)
          (notPA_textS op _),
        decodeTyp?_typS t, decodeRules?_rulesS rules]
  | .decD x ps t clauses => by
      simp [defS, decodeDef?, List.append_assoc,
        decodeParamsRest?_paramsS ps (typS t :: clausesS clauses) (notPA_typS t _),
        decodeTyp?_typS t, decodeClauses?_clausesS clauses]
  | .gramD x ps t prods => by
      simp [defS, decodeDef?, List.append_assoc,
        decodeParamsRest?_paramsS ps (typS t :: prodsS prods) (notPA_typS t _),
        decodeTyp?_typS t, decodeProds?_prodsS prods]
  | .recD ds => by simp [defS, decodeDef?, decodeDefs?_defsS ds]

/-- `decodeDefs?` inverts `defsS` (`print.ml:217`). -/
theorem decodeDefs?_defsS : ∀ ds : List Def, decodeDefs? (defsS ds) = some ds
  | [] => rfl
  | d :: ds => by simp [defsS, decodeDefs?, decodeDef?_defS d, decodeDefs?_defsS ds]

end

/-! ## The script level and injectivity -/

/-- `decodeScript?` inverts `scriptS` (`print.ml:224-225`).  The filter at
`print.ml:225` is vacuous on `IL.Script`, which has no `HintD`. -/
@[simp] theorem decodeScript?_scriptS (s : Script) : decodeScript? (scriptS s) = some s :=
  decodeDefs?_defsS s

/-- An encoder with a total decoder that inverts it is injective. -/
theorem injective_of_decode {α β : Type} {enc : α → β} {dec : β → Option α}
    (h : ∀ a, dec (enc a) = some a) : Function.Injective enc := by
  intro a b hab
  have ha := h a
  rw [hab, h b] at ha
  exact (Option.some.inj ha).symm

/-- `defS` is injective: the `--ast` rendering of a definition determines the
definition.  This is what makes `IL.Def` the image of `Il.Ast.def` under the
printer's erasure rather than a lossy approximation of it. -/
theorem defS_injective : Function.Injective defS :=
  injective_of_decode decodeDef?_defS

/-- `scriptS` is injective: the `--ast` child-list of a script determines the
script. -/
theorem scriptS_injective : Function.Injective scriptS :=
  injective_of_decode decodeScript?_scriptS

/-! ## Axiom check

```
#print axioms decodeDef?_defS
#print axioms decodeScript?_scriptS
#print axioms defS_injective
#print axioms scriptS_injective
```

all report `'…' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## The other direction

`decodeDef? s = some d → defS d = s` — that the decoder accepts nothing
outside the printer's image — is a separate, equally large mutual induction:
it needs a completeness companion for every decoder above
(`decodeText? a = some x → textS x = a`, and so on), plus the converse shape
facts saying that a child `decodeParamsRest?` classified as a parameter really
is one.  It is proved in `Silmaril/SpecTec/IL/DecodeComplete.lean`, as
`defS_of_decodeDef?` and `scriptS_of_decodeScript?`, on top of the layers
below (`Escape.quote_of_unquote?`,
`Digits.decString_of_parseDecString?` and friends).  The two files together
give `decodeDef? s = some d ↔ defS d = s`, which
`Silmaril/SpecTec/IL/Encoding.lean` packages as `defRel_eq_ofDecoder`: the
decoder's graph *is* the encoding relation. -/

end Silmaril.SpecTec.IL
