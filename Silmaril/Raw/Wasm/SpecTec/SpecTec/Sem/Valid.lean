module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Env
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Env
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Free
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Free
public import Mathlib.Data.Finset.Sort
public meta import Mathlib.Data.Finset.Sort
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Parse
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Parse

/-!
# Well-formedness of an internal-language script

Step 6 of `docs/projects/spectec/README.md`: a decidable well-formedness check on an
`IL.Script`, transcribed from SpecTec's own IL validator
`spectec/src/il/valid.ml` (844 lines) at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`.  `spectec` runs `Il.Valid.valid`
(`valid.ml:823-824`) before it prints anything, so every `--ast` stream is by
construction a script the OCaml validator accepts; the three pinned streams in
`specs/spectec/` are therefore the test of this transcription.  The `#eval`s at
the bottom of this file run it on all three at elaboration time, and on sixteen
small malformed scripts, each paired with the repair that makes it pass.

## What `valid.ml` is, and which half this is

`valid.ml` is **bidirectional type checking that also annotates**.  It runs in
one of two modes (`valid.ml:15-18`): in `Validate` mode `valid_exp` checks the
`typ` note every `exp` carries against the type it is being checked at
(`valid.ml:368`), and in `Annotate` mode it *overwrites* that note
(`valid.ml:369`), using global mutable state to do so — `valid.mli:18` says the
annotating entry points "use global side state and hence are not reentrant".

`IL.Exp` has no `typ` note: `spectec/src/backend-ast/print.ml` never prints one
(`docs/projects/spectec/README.md`).  So on an imported script the
`Validate`-mode note comparisons at `valid.ml:368` and `valid.ml:567` have no
data to compare and the two modes coincide with each other minus those two
lines.  What is transcribed here is that common part, restricted further to the
judgments that do not need a type:

1. **Scope and kind checking.**  Every `VarT`/`CallE`/`RulePr`/`VarG`
   identifier resolves in the environment (`env.ml:47-50`), every expression
   variable is bound, argument and parameter lists have equal length and
   agree constructor by constructor (`valid.ml:652-688`), a `RulePr`'s mixop is
   the one its relation declares (`valid.ml:619`), a `RuleD`'s mixop is the one
   its relation declares (`valid.ml:730`), a `RecD` group does not mix sorts
   (`valid.ml:805-815`), definite iterators do not occur in types
   (`valid.ml:248`), iterations are not vacuous (`valid.ml:213`), the wildcard
   variable occurs only on a left-hand side (`valid.ml:372`), operator
   annotations are consistent with their operators (`valid.ml:128-157`), and a
   record or variant declares no field or case twice (`valid.ml:170-179`).
2. **Shape checking that survives erasure.**  A `CaseE`/`UncaseE` mixop is one
   some variant in the script declares, a `DotE`/`StrE`/`DotP` atom is one some
   record in the script declares, and a `ProjE` index is non-negative
   (`valid.ml:102-110`, where a negative index runs the loop off the end of the
   tuple).
3. **Declaration uniqueness**, which `valid.ml` does *not* check: `env.ml:55-58`
   has it commented out behind `TODO(3, rossberg): reactivate?`.  It is checked
   here, as an extra, and all three pinned specifications satisfy it.

## What is deliberately left out

**Typing proper.**  `equiv_typ` and `sub_typ` (`valid.ml:115-123`) call
`Eval.equiv_typ`/`Eval.sub_typ`, and the `as_*_typ` accessors
(`valid.ml:68-100`) call `Eval.reduce_typ`/`Eval.reduce_typdef`, which unfold
type definitions and so need fuel; `proj_tup_typ` (`valid.ml:102-110`) and
`valid_args` (`valid.ml:678-688`) thread a `Subst.t`.  None of that is here.
The checker is written so that the typing layer is a *separable* addition:
`Scope` keeps exactly the five namespaces of `il/env.ml:23-29` and the
parameter lists needed to check arities, and every function that OCaml gives an
expected type takes the same arguments here minus that type.  A module
providing `reduceTyp`, `equivTyp`, `subTyp` and `substTyp` would plug in by
(a) giving `Scope.vars` a `Typ` payload instead of `Unit`, (b) adding the
expected type as a parameter of `checkExp`, `checkPath` and `checkArg`, and
(c) restoring the `as_*_typ` accessors; the scope and shape obligations below
would be unchanged.

`Silmaril/SpecTec/Sem/Type.lean` does exist — step 4 of
`docs/projects/spectec/README.md` — but it is the *value* side: `hasTyp`/`HasTyp`,
the denotation of a `Typ` as a set of `Sem.Value`s.  It transcribes none of
`eval.ml`'s type-level machinery, so none of those four functions is
available, and its own closing section records the two statements that stay
open for want of them ("no preservation theorem for the whole language", "no
subtyping theorem").  The typing layer is therefore still future work, and
nothing below depends on it.

**The three checks the `--ast` erasure makes undecidable:**

* `valid_atom` (`valid.ml:162-164`) requires every atom to carry a non-empty
  `Atom.def`, the name of the type that declares it.  `Xl.Atom.atom` is a
  record with a `note`; `IL.AtomS` is the *rendering* `Atom.to_string` produces
  (`atom.ml:111-184`), which contains no note.  There is nothing to check.
* `valid_typcase`'s arity check (`valid.ml:276-283`) compares `Mixop.arity`
  (`mixop.ml:44`, the number of `Arg` positions) with the arity of the case's
  type.  `Mixop.to_string` erases that number: `mixop.ml:92` renders
  `Seq (Atom a :: args)` as `Atom.to_string a` alone whenever every `args`
  entry is an argument position, so the `instr` case `CALL` — mixop
  `Seq [Atom CALL; Arg]`, arity 1 — prints as `CALL`, indistinguishable from an
  arity-0 mixop.  `specs/spectec/wasm-3.0.ast` has 245 distinct case mixops and
  all but six of them are `%`-free, so the check is unavailable for almost
  every case in the corpus and is omitted rather than approximated.
* `LetPr`'s quantifiers (`ast.ml:160`) are dropped by `print.ml:165`.  They are
  what `valid.ml:627` binds before checking the left-hand side, so the binders
  of a `LetPr` have to be recovered; see `checkPrem`.

**`infer_exp`'s two note-reading clauses.**  `infer_exp` returns `e.note`
verbatim for `StrE` (`valid.ml:310`) and `CaseE` (`valid.ml:356`) — the comments
there record that those are the cases inference cannot handle, which
`valid.mli:12-14` repeats.  Since inference is not transcribed at all, nothing
depends on them.

## Faithfulness of the string keys

`find_field` (`valid.ml:23-26`) compares atoms with `Eq.eq_atom` and
`find_case` (`valid.ml:28-31`) compares mixops with `Eq.eq_mixop`, both finer
relations than equality of renderings.  Within one record or one variant they
*coincide* with it, because `check_mixops` (`valid.ml:170-179`, applied at
`valid.ml:259` and `valid.ml:262`) rejects a declaration two of whose fields or
cases have the same `Print.string_of_mixop`, and `print.ml:44-46` is injective
on the image of `Mixop.to_string` (it wraps a non-alphanumeric rendering in
backticks, and no alphanumeric rendering starts with one).  So comparing
`IL.AtomS` and `IL.MixopS` as strings, as everything below does, is exact
wherever `valid.ml` looks a field or a case up.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod

/-! ## Results -/

/-- The validator's result: `unit` or the message `Error.error` would carry
(`valid.ml:10`).  OCaml raises; here the message is returned. -/
abbrev Check (α : Type) : Type := Except String α

/-- Prefix a failure with the context it occurred in.  OCaml attaches a source
region instead (`valid.ml:10`), which `IL.Def` drops. -/
def Check.within {α : Type} (ctx : String) : Check α → Check α
  | .ok a => .ok a
  | .error msg => .error s!"{ctx}: {msg}"

/-- Fail unless `b` holds. -/
def ensure (b : Bool) (msg : String) : Check Unit :=
  if b then .ok () else .error msg

/-! ## Sides

`valid_exp` carries a `side` flag (`valid.ml:361`) distinguishing a pattern
position from an ordinary one.  Three checks read it: the wildcard variable is
only allowed on the left (`valid.ml:372`), an iteration with no domain is
vacuous only on the right (`valid.ml:213`), and two arithmetic shapes are only
invertible on the left (`valid.ml:385-386`, `valid.ml:499-500`). -/

/-- `` `Lhs `` / `` `Rhs `` (`valid.ml:361`). -/
inductive Side where
  /-- A pattern position. -/
  | lhs
  /-- An ordinary expression position. -/
  | rhs
  deriving DecidableEq, Repr, Inhabited

/-! ## Numeric operator typing (`spectec/src/xl/num.ml`) -/

/-- `Num.string_of_typ` (`spectec/src/xl/num.ml:27-31`), for error messages. -/
def numTypName : NumTyp → String
  | .natT => "nat"
  | .intT => "int"
  | .ratT => "rat"
  | .realT => "real"

/-- `Num.sub` (`spectec/src/xl/num.ml:52-57`): the numeric subtyping order. -/
def numSub : NumTyp → NumTyp → Bool
  | _, .realT => true
  | .natT, _ => true
  | .intT, .ratT => true
  | t₁, t₂ => t₁ == t₂

/-- `Num.typ_unop` (`spectec/src/xl/num.ml:66-68`).  Both numeric unary
operators have the same rule, so the operator is not consulted. -/
def typUnop (_op : UnOp) (t₁ t₂ : NumTyp) : Bool := t₁ == t₂ && numSub .intT t₁

/-- `Num.typ_binop` (`spectec/src/xl/num.ml:70-76`).  The four Boolean binary
operators (`spectec/src/xl/bool.ml:4`) are not `Num.binop`s and never reach
this. -/
def typBinop (op : BinOp) (t₁ t₂ t₃ : NumTyp) : Bool :=
  match op with
  | .addOp | .mulOp => t₁ == t₂ && t₁ == t₃
  | .subOp => t₁ == t₂ && numSub .intT t₃
  | .divOp => t₁ == t₂ && numSub .ratT t₃
  | .modOp => t₁ == t₂ && t₁ == t₃ && numSub t₁ .intT
  | .powOp => t₁ == t₃ && (t₂ == .natT || (t₂ == .intT && numSub .ratT t₁))
  | .andOp | .orOp | .implOp | .equivOp => false

/-- `Bool.binop` (`spectec/src/xl/bool.ml:4`). -/
def isBoolBinop : BinOp → Bool
  | .andOp | .orOp | .implOp | .equivOp => true
  | _ => false

/-- `Bool.cmpop` (`spectec/src/xl/bool.ml:5`). -/
def isBoolCmpop : CmpOp → Bool
  | .eqOp | .neOp => true
  | _ => false

/-- `infer_unop` (`valid.ml:128-136`), keeping only whether it raises.  The
only Boolean unary operator is `` `NotOp `` (`spectec/src/xl/bool.ml:3`); the
numeric ones are `` `PlusOp `` and `` `MinusOp `` (`num.ml:16`), and
`num.ml:68` rules both out at `nat`. -/
def checkUnop (op : UnOp) (ot : OpTyp) : Check Unit :=
  match op, ot with
  | .notOp, .boolT => .ok ()
  | .plusOp, .numT nt | .minusOp, .numT nt =>
      ensure (typUnop op nt nt) s!"illegal type {numTypName nt} for unary operator"
  | _, _ => .error "malformed unary operator annotation"

/-- `infer_binop` (`valid.ml:138-151`).  `` `PowOp ``'s right operand is `nat`
at `nat` and `int` otherwise (`valid.ml:145`), which together with `num.ml:76`
makes `` `PowOp `` at `int` ill-typed; `num.ml:73-75` likewise rule out
`` `SubOp `` at `nat` and `` `DivOp `` at `nat` and `int`. -/
def checkBinop (op : BinOp) (ot : OpTyp) : Check Unit :=
  match ot with
  | .boolT => ensure (isBoolBinop op) "malformed binary operator annotation"
  | .numT nt =>
      if isBoolBinop op then .error "malformed binary operator annotation"
      else
        let nt₂ := if op == .powOp then (if nt == .natT then .natT else .intT) else nt
        ensure (typBinop op nt nt₂ nt) s!"illegal type {numTypName nt} for unary operator"

/-- `infer_cmpop` (`valid.ml:153-157`).  The Boolean comparisons take the
Boolean annotation and the numeric ones a numeric annotation; OCaml then uses
the result to decide whether the operand type is fixed, which is typing and is
not transcribed. -/
def checkCmpop (op : CmpOp) (ot : OpTyp) : Check Unit :=
  match ot with
  | .boolT => ensure (isBoolCmpop op) "malformed comparison operator annotation"
  | .numT _ => ensure (!isBoolCmpop op) "malformed comparison operator annotation"

/-! ## The scope environment

`Scope` is `Il.Env.t` (`spectec/src/il/env.ml:23-29`) with the payloads this
layer can use: an expression variable's type is dropped, and a type, relation,
definition or grammar keeps the parameter list that `valid_args`
(`valid.ml:678-688`) checks arguments against, plus, for a relation, the mixop
that `valid.ml:619` and `valid.ml:730` compare against.

`caseOps` and `fieldAtoms` are *not* scoped: they are the script-wide tables of
declared variant cases and record fields, collected once by `Scope.initial`,
which is how the shape checks of `CaseE`, `UncaseE`, `DotE`, `StrE` and `DotP`
are made without an expected type.  A definition may be used before it is
declared — `elab.ml` emits `RecD` groups for exactly that — so these have to be
global to be sound. -/
structure Scope where
  /-- `vars` (`spectec/src/il/env.ml:24`), without the types. -/
  vars : Map Unit
  /-- `typs` (`spectec/src/il/env.ml:25`), keeping only the parameters. -/
  typs : Map (List Param)
  /-- `rels` (`spectec/src/il/env.ml:27`), keeping the parameters and mixop. -/
  rels : Map (List Param × MixopS)
  /-- `defs` (`spectec/src/il/env.ml:26`), keeping only the parameters. -/
  defs : Map (List Param)
  /-- `grams` (`spectec/src/il/env.ml:28`), keeping only the parameters. -/
  grams : Map (List Param)
  /-- Every mixop declared by a `VariantT` anywhere in the script. -/
  caseOps : List MixopS
  /-- Every atom declared by a `StructT` anywhere in the script. -/
  fieldAtoms : List AtomS
  deriving Inhabited

namespace Scope

/-- `Env.empty` (`spectec/src/il/env.ml:34-40`) with empty global tables. -/
def empty : Scope := ⟨Map.empty, Map.empty, Map.empty, Map.empty, Map.empty, [], []⟩

/-- `bind_var` (`spectec/src/il/env.ml:84`); `env.ml:53-54` makes binding the
wildcard a no-op. -/
def bindVar (sc : Scope) (x : IL.Id) : Scope := { sc with vars := sc.vars.bind x () }

/-- `bind_typ` (`spectec/src/il/env.ml:85`).  As for `bindVar` and the three
below, the wildcard guard of `env.ml:53-54` is inherited from `Map.bind`
(`Silmaril/SpecTec/Sem/Env.lean`): `_` is not entered in any namespace, so a
`typD`/`relD`/`decD`/`gramD` named `_` declares nothing and a reference to it
does not resolve.  `rejectionTests` pins that. -/
def bindTyp (sc : Scope) (x : IL.Id) (ps : List Param) : Scope :=
  { sc with typs := sc.typs.bind x ps }

/-- `bind_rel` (`spectec/src/il/env.ml:87`). -/
def bindRel (sc : Scope) (x : IL.Id) (ps : List Param) (op : MixopS) : Scope :=
  { sc with rels := sc.rels.bind x (ps, op) }

/-- `bind_def` (`spectec/src/il/env.ml:86`). -/
def bindDef (sc : Scope) (x : IL.Id) (ps : List Param) : Scope :=
  { sc with defs := sc.defs.bind x ps }

/-- `bind_gram` (`spectec/src/il/env.ml:88`). -/
def bindGram (sc : Scope) (x : IL.Id) (ps : List Param) : Scope :=
  { sc with grams := sc.grams.bind x ps }

/-- `find_var` (`spectec/src/il/env.ml:78`), whose failure is `env.ml:49`. -/
def findVar (sc : Scope) (x : IL.Id) : Check Unit :=
  ensure (sc.vars.mem x) s!"undeclared variable `{x}`"

/-- `find_typ` (`spectec/src/il/env.ml:79`). -/
def findTyp (sc : Scope) (x : IL.Id) : Check (List Param) :=
  match sc.typs.find? x with
  | some ps => .ok ps
  | none => .error s!"undeclared type `{x}`"

/-- `find_rel` (`spectec/src/il/env.ml:81`). -/
def findRel (sc : Scope) (x : IL.Id) : Check (List Param × MixopS) :=
  match sc.rels.find? x with
  | some r => .ok r
  | none => .error s!"undeclared relation `{x}`"

/-- `find_def` (`spectec/src/il/env.ml:80`). -/
def findDef (sc : Scope) (x : IL.Id) : Check (List Param) :=
  match sc.defs.find? x with
  | some ps => .ok ps
  | none => .error s!"undeclared definition `{x}`"

/-- `find_gram` (`spectec/src/il/env.ml:82`). -/
def findGram (sc : Scope) (x : IL.Id) : Check (List Param) :=
  match sc.grams.find? x with
  | some ps => .ok ps
  | none => .error s!"undeclared grammar `{x}`"

/-- The case `op` must be declared by some variant in the script; this is what
survives of `find_case` (`valid.ml:28-31`) once the expected type is gone. -/
def findCaseOp (sc : Scope) (op : MixopS) : Check Unit :=
  ensure (sc.caseOps.contains op) s!"unknown case `{op}`"

/-- The field `atom` must be declared by some record in the script; this is
what survives of `find_field` (`valid.ml:23-26`). -/
def findFieldAtom (sc : Scope) (atom : AtomS) : Check Unit :=
  ensure (sc.fieldAtoms.contains atom) s!"unbound field `{atom}`"

end Scope

/-! ## Parameter sorts

`valid_arg` (`valid.ml:652-676`) matches an argument against a parameter and
fails with "sort mismatch" unless the two constructors correspond.
`Subst.subst_param` (`valid.ml:656`) rewrites the types inside a parameter and
never changes its constructor, so the correspondence is exactly what survives
without a substitution. -/

/-- Which of the four sorts a parameter declares. -/
inductive ParamSort where
  /-- `ExpP` (`spectec/src/il/ast.ml:124`). -/
  | expS
  /-- `TypP` (`spectec/src/il/ast.ml:125`). -/
  | typS
  /-- `DefP` (`spectec/src/il/ast.ml:126`). -/
  | defS
  /-- `GramP` (`spectec/src/il/ast.ml:127`). -/
  | gramS
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The sort a parameter declares. -/
def paramSort : Param → ParamSort
  | .expP _ _ => .expS
  | .typP _ => .typS
  | .defP _ _ _ => .defS
  | .gramP _ _ _ => .gramS

/-- The sorts a parameter list declares.

`Eval.equiv_functyp` (`valid.ml:662,671`) compares two parameter lists *and*
their result types up to type equivalence.  Only the sorts are compared here;
that is a necessary condition for `equiv_functyp`, so this check never rejects
a script OCaml accepts. -/
def paramSorts (ps : List Param) : List ParamSort := ps.map paramSort

/-! ## Shapes `valid_exp` looks for in a left-hand side -/

/-- `{it = NumE (`Nat _); _}` (`valid.ml:385-386`): a natural-number literal,
which makes an addition or subtraction invertible. -/
def isNatLit : Exp → Bool
  | .numE (.natN _) => true
  | _ => false

/-- `{it = ListE _ | CatE ({it = ListE _; _}, _); _}` (`valid.ml:499-500`): a
concatenand whose length is syntactically known, which makes a concatenation
invertible. -/
def isKnownLen : Exp → Bool
  | .listE _ => true
  | .catE e₁ _ => match e₁ with | .listE _ => true | _ => false
  | _ => false

/-- `ListN` (`spectec/src/il/ast.ml:20`): a *definite* iterator.  `valid.ml:213`
spells the complementary test `it <= List1`, which is OCaml's structural
comparison on `iter`; `ListN` is the last constructor, so `it <= List1` holds
for exactly `Opt`, `List` and `List1`. -/
def isDefiniteIter : Iter → Bool
  | .listN _ _ => true
  | _ => false

/-! ## The checker

One mutual block, structurally recursive on the syntax, mirroring
`valid.ml:195-709`.  Each function takes the arguments its OCaml counterpart
takes minus the expected type, and returns the environment its counterpart
returns (`Unit` where OCaml returns `unit`).

`valid_typ` (`valid.ml:226`) is `ignore (valid_typ_bind ...)`, so only
`checkTypBind` appears inside the block; `checkTyp` is defined just after it. -/

mutual

/-- `valid_iter` (`valid.ml:195-205`). -/
def checkIter (sc : Scope) (side : Side) : Iter → Check Scope
  | .opt | .list | .list1 => .ok sc
  | .listN e xo => do
      checkExp sc side e
      match xo with
      | none => .ok sc
      | some x => .ok (sc.bindVar x)

/-- `valid_iterexp` (`valid.ml:207-221`), dropping the iterator it returns —
`it'` (`valid.ml:214`) is only used to pick the type accessor. -/
def checkIterExp (sc : Scope) (side : Side) : IterExp → Check Scope
  | .mk it doms => do
      let sc' ← checkIter sc side it
      if doms.isEmpty && !isDefiniteIter it && side == .rhs then
        .error "vacuous iteration"
      else
        checkDoms sc sc' side doms

/-- The `List.fold_left` of `valid_iterexp` (`valid.ml:216-221`): each source
expression is checked in the *outer* environment `outer` and each bound
variable is added to the accumulator `acc`. -/
def checkDoms (outer : Scope) (acc : Scope) (side : Side) : List Dom → Check Scope
  | [] => .ok acc
  | .mk x e :: ds => do
      checkExp outer side e
      checkDoms outer (acc.bindVar x) side ds

/-- `valid_typ_bind` (`valid.ml:228-252`): validate a type and return the
environment its tuple binders introduce. -/
def checkTypBind (sc : Scope) : Typ → Check Scope
  | .varT x args => do
      let ps ← sc.findTyp x
      checkArgs sc args ps
      .ok sc
  | .boolT | .numT _ | .textT => .ok sc
  | .tupT binds => checkTypBinds sc binds
  | .iterT t it =>
      if isDefiniteIter it then .error "definite iterator not allowed in type"
      else do
        let sc' ← checkIter sc .rhs it
        let _ ← checkTypBind sc' t
        .ok sc

/-- The `TupT` loop of `valid_typ_bind` (`valid.ml:241-245`): each component is
validated in the scope of the ones before it. -/
def checkTypBinds (sc : Scope) : List TypBind → Check Scope
  | [] => .ok sc
  | .mk x t :: rest => do
      let _ ← checkTypBind sc t
      checkTypBinds (sc.bindVar x) rest

/-- `valid_exp` (`valid.ml:361-521`) minus the expected type: the type
equations are gone, the recursion and the `side` propagation are exact.

Two places where `side` cannot be reproduced:

* `ProjE` (`valid.ml:476`) passes `` `Rhs `` when the tuple has more than one
  component and `side` otherwise, which needs the tuple's type.  `side` is
  passed, the branch that imposes fewer obligations.
* `CmpE` (`valid.ml:400`) falls back on inferring the operand type from one
  subexpression or the other when the comparison is Boolean; that is typing,
  and only the operator annotation is checked here. -/
def checkExp (sc : Scope) (side : Side) : Exp → Check Unit
  | .varE x =>
      if x == "_" then
        ensure (side == .lhs) "wildcard variable on a right-hand side"
      else sc.findVar x
  | .boolE _ | .numE _ | .textE _ => .ok ()
  | .unE op ot e => do
      checkUnop op ot
      checkExp sc side e
  | .binE op ot e₁ e₂ => do
      checkBinop op ot
      let invertible := (op == .addOp || op == .subOp) && (isNatLit e₁ || isNatLit e₂)
      let side' := if side == .lhs && invertible then side else .rhs
      checkExp sc side' e₁
      checkExp sc side' e₂
  | .cmpE op ot e₁ e₂ => do
      checkCmpop op ot
      let side' := if op == .eqOp then Side.lhs else Side.rhs
      checkExp sc side' e₁
      checkExp sc side' e₂
  | .tupE es => checkExps sc side es
  | .projE e i => do
      ensure (0 ≤ i) "invalid tuple projection"
      checkExp sc side e
  | .caseE op e => do
      sc.findCaseOp op
      checkExp sc side e
  | .uncaseE e op => do
      sc.findCaseOp op
      checkExp sc side e
  | .optE none => .ok ()
  | .optE (some e) => checkExp sc side e
  | .theE e => checkExp sc side e
  | .strE fields => checkExpFields sc side fields
  | .dotE e atom => do
      checkExp sc .rhs e
      sc.findFieldAtom atom
  | .compE e₁ e₂ => do
      checkExp sc .rhs e₁
      checkExp sc .rhs e₂
  | .listE es => checkExps sc side es
  | .liftE e => checkExp sc side e
  | .memE e₁ e₂ => do
      checkExp sc .rhs e₁
      checkExp sc .rhs e₂
  | .lenE e => checkExp sc .rhs e
  | .catE e₁ e₂ => do
      let invertible := isKnownLen e₁ || isKnownLen e₂
      let side' := if side == .lhs && invertible then side else .rhs
      checkExp sc side' e₁
      checkExp sc side' e₂
  | .idxE e₁ e₂ => do
      checkExp sc .rhs e₁
      checkExp sc .rhs e₂
  | .sliceE e₁ e₂ e₃ => do
      checkExp sc .rhs e₁
      checkExp sc .rhs e₂
      checkExp sc .rhs e₃
  | .updE e₁ p e₂ => do
      checkExp sc .rhs e₁
      checkPath sc p
      checkExp sc .rhs e₂
  | .extE e₁ p e₂ => do
      checkExp sc .rhs e₁
      checkPath sc p
      checkExp sc .rhs e₂
  | .callE x args => do
      let ps ← sc.findDef x
      checkArgs sc args ps
  | .iterE e it => do
      let sc' ← checkIterExp sc side it
      checkExp sc' side e
  | .cvtE e _ _ => checkExp sc side e
  | .subE e t₁ t₂ => do
      let _ ← checkTypBind sc t₁
      let _ ← checkTypBind sc t₂
      checkExp sc side e

/-- `List.iter` of `valid_exp` over the components of a `TupE`
(`valid.ml:451-464`) or a `ListE` (`valid.ml:495`). -/
def checkExps (sc : Scope) (side : Side) : List Exp → Check Unit
  | [] => .ok ()
  | e :: es => do
      checkExp sc side e
      checkExps sc side es

/-- `valid_expfield` (`valid.ml:533-542`) over a record's fields
(`valid.ml:428`).  OCaml additionally requires the expression fields to match
the record type's fields one by one, in order; without the type, each atom is
only required to be a declared record field. -/
def checkExpFields (sc : Scope) (side : Side) : List ExpField → Check Unit
  | [] => .ok ()
  | .mk atom e :: fs => do
      sc.findFieldAtom atom
      checkExp sc side e
      checkExpFields sc side fs

/-- `valid_path` (`valid.ml:544-570`), dropping the type it returns. -/
def checkPath (sc : Scope) : Path → Check Unit
  | .rootP => .ok ()
  | .idxP p e => do
      checkPath sc p
      checkExp sc .rhs e
  | .sliceP p e₁ e₂ => do
      checkPath sc p
      checkExp sc .rhs e₁
      checkExp sc .rhs e₂
  | .dotP p atom => do
      checkPath sc p
      sc.findFieldAtom atom

/-- `valid_sym` (`valid.ml:575-609`), dropping the type it returns. -/
def checkSym (sc : Scope) : Sym → Check Unit
  | .varG x args => do
      let ps ← sc.findGram x
      checkArgs sc args ps
  | .numG _ | .textG _ | .epsG => .ok ()
  | .seqG gs | .altG gs => checkSyms sc gs
  | .rangeG g₁ g₂ => do
      checkSym sc g₁
      checkSym sc g₂
  | .iterG g it => do
      let sc' ← checkIterExp sc .lhs it
      checkSym sc' g
  | .attrG e g => do
      checkSym sc g
      checkExp sc .lhs e

/-- `List.map valid_sym` (`valid.ml:591,594`). -/
def checkSyms (sc : Scope) : List Sym → Check Unit
  | [] => .ok ()
  | g :: gs => do
      checkSym sc g
      checkSyms sc gs

/-- `valid_arg` (`valid.ml:652-676`), dropping the substitution it returns.

The parameter's own type is *not* validated here, although `valid.ml:658`
reaches it through `valid_exp`'s opening `valid_typ env t` (`valid.ml:366`).
That type is `Subst.subst_param s p`'s, i.e. the declared type with the
preceding arguments substituted for the preceding parameters; the unsubstituted
one may mention parameter names that are not in the caller's scope — the type
of `v` in `def f(n : nat, v : vec(n))` mentions `n` — so validating it here
would reject calls OCaml accepts.  An argument that *is* a type
(`valid.ml:659`) is validated, because that one is the caller's. -/
def checkArg (sc : Scope) : Arg → Param → Check Unit
  | .expA e, .expP _ _ => checkExp sc .lhs e
  | .typA t, .typP _ => do
      let _ ← checkTypBind sc t
      .ok ()
  | .defA x', .defP _ ps _ => do
      let ps' ← sc.findDef x'
      ensure (paramSorts ps' == paramSorts ps) "type mismatch in function argument"
  | .gramA g, .gramP _ [] _ => checkSym sc g
  | .gramA (.varG x' args'), .gramP _ ps _ => do
      let ps' ← sc.findGram x'
      ensure (args'.isEmpty && paramSorts ps' == paramSorts ps)
        "type mismatch in grammar argument"
  | _, _ => .error "sort mismatch for argument"

/-- `valid_args` (`valid.ml:678-688`), dropping the substitution it returns. -/
def checkArgs (sc : Scope) : List Arg → List Param → Check Unit
  | [], [] => .ok ()
  | _ :: _, [] => .error "too many arguments"
  | [], _ :: _ => .error "too few arguments"
  | a :: args, p :: ps => do
      checkArg sc a p
      checkArgs sc args ps

/-- `valid_param` (`valid.ml:690-704`), which `valid_quant` (`valid.ml:706`)
is the same function under another name. -/
def checkParam (sc : Scope) : Param → Check Scope
  | .expP x t => do
      let _ ← checkTypBind sc t
      .ok (sc.bindVar x)
  | .typP x => .ok (sc.bindTyp x [])
  | .defP x ps t => do
      let sc' ← checkParams sc ps
      let _ ← checkTypBind sc' t
      .ok (sc.bindDef x ps)
  | .gramP x ps t => do
      let sc' ← checkParams sc ps
      let _ ← checkTypBind sc' t
      .ok (sc.bindGram x ps)

/-- `valid_params` / `valid_quants` (`valid.ml:708-709`), i.e. `valid_binders`
(`valid.ml:190-193`) of `valid_param`. -/
def checkParams (sc : Scope) : List Param → Check Scope
  | [] => .ok sc
  | p :: ps => do
      let sc' ← checkParam sc p
      checkParams sc' ps

/-- `valid_prem` (`valid.ml:614-645`).

`LetPr` is not a transcription.  OCaml binds the premise's quantifiers first
(`valid.ml:627`) and then checks that each of them occurs free in the
left-hand side (`valid.ml:631-638`); `print.ml:165` drops the quantifiers, so
they are recovered here as *the variables free in the left-hand side that are
not already in scope*.  That is forced: `valid.ml:629` checks the left-hand
side in the extended environment, so every variable of it must be bound there,
and `valid.ml:633` says every quantifier occurs in it — so the recovered set is
exactly `bound_quants qs` minus what the outer scope already binds, which is
the same scope.  The occurrence check then holds by construction.  Nothing in
`src/frontend` or `src/middlend` builds a `LetPr` and none of the pinned
streams contains one (`Silmaril/SpecTec/IL/Free.lean`, `freePrem`), so this
branch is unreachable from an imported script.

`IterPr` returns the *unextended* environment, as OCaml does
(`valid.ml:645`, `TODO: out it`). -/
def checkPrem (sc : Scope) : Prem → Check Scope
  | .rulePr x args op e => do
      let (ps, op') ← sc.findRel x
      -- `valid.ml:619` is an OCaml `assert`, not an `error`, so it is skipped
      -- under `-noassert`; it is a check here.
      ensure (op == op')
        s!"mixin notation `{op}` does not match expected notation `{op'}`"
      checkArgs sc args ps
      checkExp sc .rhs e
      .ok sc
  | .ifPr e => do
      checkExp sc .rhs e
      .ok sc
  | .letPr e₁ e₂ => do
      let fresh := ((IL.freeExp e₁).varid.sort (· ≤ ·)).filter fun x => !sc.vars.mem x
      let sc' := fresh.foldl Scope.bindVar sc
      checkExp sc' .lhs e₁
      checkExp sc .rhs e₂
      .ok sc'
  | .elsePr => .ok sc
  | .iterPr pr it => do
      let sc' ← checkIterExp sc .rhs it
      let _ ← checkPrem sc' pr
      .ok sc

/-- `valid_prems` (`valid.ml:647`): a left fold of `valid_prem`. -/
def checkPrems (sc : Scope) : List Prem → Check Scope
  | [] => .ok sc
  | pr :: prs => do
      let sc' ← checkPrem sc pr
      checkPrems sc' prs

end

/-- `valid_typ` (`valid.ml:226`): `valid_typ_bind` with its environment
discarded. -/
def checkTyp (sc : Scope) (t : Typ) : Check Unit := do
  let _ ← checkTypBind sc t
  .ok ()

/-! ## Declarations -/

/-- The first element of a list that occurs again later, if any.

`check_mixops` (`valid.ml:170-179`) collects *every* repeated key with a
`List.fold_right`; only the first is needed to decide the check.  OCaml
compares keys with `Print.string_of_mixop` (`valid.ml:173`), which is
`Mixop.to_string` wrapped in backticks when it is not alphanumeric
(`spectec/src/il/print.ml:44-46`); that wrapping is injective on renderings, so
comparing `IL.MixopS` directly is the same test. -/
def firstDuplicate {α : Type} [BEq α] : List α → Option α
  | [] => none
  | a :: as => if as.contains a then some a else firstDuplicate as

/-- `check_mixops` as a check (`valid.ml:170-179`). -/
def checkMixops (phrase item : String) (keys : List String) : Check Unit :=
  match firstDuplicate keys with
  | some k => .error s!"{phrase} contains duplicate {item}(s) `{k}`"
  | none => .ok ()

/-- `valid_typfield` (`valid.ml:265-269`).  `valid_atom` (`valid.ml:266`) checks
that the atom carries the name of the type that declares it, which `IL.AtomS`
does not record; see the module documentation. -/
def checkTypField (sc : Scope) : TypField → Check Unit
  | .mk _ t quants prems => do
      let sc₁ ← checkTypBind sc t
      let sc₂ ← checkParams sc₁ quants
      let _ ← checkPrems sc₂ prems
      .ok ()

/-- `valid_typcase` (`valid.ml:271-287`) minus its arity check
(`valid.ml:276-283`), which `Mixop.to_string` makes undecidable; see the module
documentation. -/
def checkTypCase (sc : Scope) : TypCase → Check Unit
  | .mk _ t quants prems => do
      let sc₁ ← checkTypBind sc t
      let sc₂ ← checkParams sc₁ quants
      let _ ← checkPrems sc₂ prems
      .ok ()

/-- `valid_deftyp` (`valid.ml:254-263`). -/
def checkDefTyp (sc : Scope) : DefTyp → Check Unit
  | .aliasT t => checkTyp sc t
  | .structT fields => do
      checkMixops "record" "field" (fields.map fun | .mk a _ _ _ => a)
      fields.forM (checkTypField sc)
  | .variantT cases => do
      checkMixops "variant" "case" (cases.map fun | .mk op _ _ _ => op)
      cases.forM (checkTypCase sc)

/-- `valid_inst` (`valid.ml:711-720`). -/
def checkInst (sc : Scope) (ps : List Param) : Inst → Check Unit
  | .instD quants args dt => do
      let sc' ← checkParams sc quants
      checkArgs sc' args ps
      checkDefTyp sc' dt

/-- `valid_rule` (`valid.ml:722-731`), whose `valid_expmix` (`valid.ml:524-531`)
is the mixop comparison plus `valid_exp` on the left. -/
def checkRule (sc : Scope) (op : MixopS) : Rule → Check Unit
  | .ruleD x quants op' e prems => Check.within s!"rule `{x}`" do
      let sc' ← checkParams sc quants
      ensure (op' == op)
        s!"mixin notation `{op'}` does not match expected notation `{op}`"
      checkExp sc' .lhs e
      let _ ← checkPrems sc' prems
      .ok ()

/-- `valid_clause` (`valid.ml:733-745`). -/
def checkClause (sc : Scope) (ps : List Param) : Clause → Check Unit
  | .defD quants args e prems => do
      let sc' ← checkParams sc quants
      checkArgs sc' args ps
      let sc'' ← checkPrems sc' prems
      checkExp sc'' .rhs e

/-- `valid_prod` (`valid.ml:747-757`).  OCaml's `ps` argument is used only by
its debug trace (`valid.ml:750`). -/
def checkProd (sc : Scope) : IL.Prod → Check Unit
  | .prodD quants g e prems => do
      let sc' ← checkParams sc quants
      checkSym sc' g
      let sc'' ← checkPrems sc' prems
      checkExp sc'' .rhs e

/-! ## Definitions -/

/-- The sort of a top-level definition, for the recursion check of
`valid.ml:805-815`. -/
inductive DefSort where
  /-- `TypD` (`spectec/src/il/ast.ml:133`). -/
  | typD
  /-- `RelD` (`spectec/src/il/ast.ml:134`). -/
  | relD
  /-- `DecD` (`spectec/src/il/ast.ml:135`). -/
  | decD
  /-- `GramD` (`spectec/src/il/ast.ml:136`). -/
  | gramD
  /-- `RecD` (`spectec/src/il/ast.ml:137`). -/
  | recD
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The sort of a definition. -/
def defSort : Def → DefSort
  | .typD _ _ _ => .typD
  | .relD _ _ _ _ _ => .relD
  | .decD _ _ _ _ => .decD
  | .gramD _ _ _ _ => .gramD
  | .recD _ => .recD

/-- The identifier a definition declares, for error messages; a `RecD` group
declares none of its own. -/
def defName : Def → IL.Id
  | .typD x _ _ => x
  | .relD x _ _ _ _ => x
  | .decD x _ _ _ => x
  | .gramD x _ _ _ => x
  | .recD _ => "<rec>"

/-- `valid.ml:805-815`: every member of a `RecD` group must have the same sort
as its first member.  A nested `RecD` falls into the catch-all at
`valid.ml:812` and is rejected; so is a group whose members disagree.  An empty
group passes, because `List.hd ds` at `valid.ml:806` sits inside the closure
`List.iter` never calls.  The two `HintD` rows (`valid.ml:807`) have no
counterpart: `IL.Def` has no hint constructor (`Silmaril/SpecTec/IL/Ast.lean`,
`inductive Def`). -/
def checkRecSorts : List Def → Check Unit
  | [] => .ok ()
  | d :: ds => do
      let s := defSort d
      ensure (s != .recD) "invalid recursion between definitions of different sort"
      (d :: ds).forM fun d' =>
        ensure (defSort d' == s) "invalid recursion between definitions of different sort"

mutual

/-- `infer_def` (`valid.ml:759-776`): the pre-pass that enters a `RecD` group's
members before any of them is checked.  `RecD` and `HintD` fall into
`valid.ml:776`. -/
def inferDef (sc : Scope) : Def → Check Scope
  | .typD x ps _ => do
      let _ ← checkParams sc ps
      .ok (sc.bindTyp x ps)
  | .relD x ps op t _ => do
      let sc' ← checkParams sc ps
      checkTyp sc' t
      .ok (sc.bindRel x ps op)
  | .decD x ps t _ => do
      let sc' ← checkParams sc ps
      checkTyp sc' t
      .ok (sc.bindDef x ps)
  | .gramD x ps t _ => do
      let sc' ← checkParams sc ps
      checkTyp sc' t
      .ok (sc.bindGram x ps)
  | .recD _ => .ok sc

/-- `valid_binders infer_def` (`valid.ml:803`). -/
def inferDefs (sc : Scope) : List Def → Check Scope
  | [] => .ok sc
  | d :: ds => do
      let sc' ← inferDef sc d
      inferDefs sc' ds

end

mutual

/-- `valid_def` (`valid.ml:779-818`).

The `RelD` branch calls `valid_typcase env' (mixop, (t, [], []), [])`
(`valid.ml:789`), i.e. it validates the relation's type the way a variant case
is validated; that is reproduced with `checkTypCase`, whose only omission is
the arity check the erasure makes undecidable. -/
def checkDef (sc : Scope) : Def → Check Scope
  | .typD x ps insts => Check.within s!"syntax `{x}`" do
      let sc' ← checkParams sc ps
      insts.forM (checkInst sc' ps)
      .ok (sc.bindTyp x ps)
  | .relD x ps op t rules => Check.within s!"relation `{x}`" do
      let sc' ← checkParams sc ps
      checkTypCase sc' (.mk op t [] [])
      rules.forM (checkRule sc' op)
      .ok (sc.bindRel x ps op)
  | .decD x ps t clauses => Check.within s!"definition `{x}`" do
      let sc' ← checkParams sc ps
      checkTyp sc' t
      clauses.forM (checkClause sc' ps)
      .ok (sc.bindDef x ps)
  | .gramD x ps t prods => Check.within s!"grammar `{x}`" do
      let sc' ← checkParams sc ps
      checkTyp sc' t
      prods.forM (checkProd sc')
      .ok (sc.bindGram x ps)
  | .recD ds => do
      let sc₁ ← inferDefs sc ds
      let sc₂ ← checkDefs sc₁ ds
      checkRecSorts ds
      .ok sc₂

/-- `valid_binders valid_def` (`valid.ml:804`), and the body of `valid`
(`valid.ml:823-824`). -/
def checkDefs (sc : Scope) : List Def → Check Scope
  | [] => .ok sc
  | d :: ds => do
      let sc' ← checkDef sc d
      checkDefs sc' ds

end

/-! ## The script-wide tables

`Scope.caseOps` and `Scope.fieldAtoms` are collected from the whole script
before checking starts.  Variant cases and record fields occur only inside a
`DefTyp`, which occurs only inside a `TypD`'s instances
(`spectec/src/il/ast.ml:133,141-142`), so the traversal only has to look
through `RecD`. -/

mutual

/-- The variant case mixops and record field atoms a definition declares. -/
def declaredShapes : Def → List MixopS × List AtomS
  | .typD _ _ insts =>
      insts.foldl (init := ([], [])) fun (ops, atoms) inst =>
        match inst with
        | .instD _ _ (.variantT cases) => (ops ++ cases.map (fun | .mk op _ _ _ => op), atoms)
        | .instD _ _ (.structT fields) => (ops, atoms ++ fields.map (fun | .mk a _ _ _ => a))
        | .instD _ _ (.aliasT _) => (ops, atoms)
  | .relD _ _ _ _ _ => ([], [])
  | .decD _ _ _ _ => ([], [])
  | .gramD _ _ _ _ => ([], [])
  | .recD ds => declaredShapesList ds

/-- The variant case mixops and record field atoms a list of definitions
declares. -/
def declaredShapesList : List Def → List MixopS × List AtomS
  | [] => ([], [])
  | d :: ds =>
      let (o₁, a₁) := declaredShapes d
      let (o₂, a₂) := declaredShapesList ds
      (o₁ ++ o₂, a₁ ++ a₂)

end

/-- `Env.empty` (`spectec/src/il/env.ml:34-40`) with the script's declared
variant cases and record fields filled in. -/
def Scope.initial (s : Script) : Scope :=
  let (ops, atoms) := declaredShapesList s
  { Scope.empty with caseOps := ops.eraseDups, fieldAtoms := atoms.eraseDups }

/-! ## Declaration uniqueness

`env.ml:52-60` has the duplicate-declaration check commented out behind
`TODO(3, rossberg): reactivate?`, so `Env.bind` silently shadows.  It is
restored here as a separate pass: a `RecD` group is flattened, the wildcard is
skipped (`env.ml:53-54` never binds it), and each of the four namespaces is
checked on its own, since they are four maps. -/

/-- A declaration namespace (`spectec/src/il/env.ml:25-28`). -/
inductive Space where
  /-- `typs` (`spectec/src/il/env.ml:25`). -/
  | typs
  /-- `rels` (`spectec/src/il/env.ml:27`). -/
  | rels
  /-- `defs` (`spectec/src/il/env.ml:26`). -/
  | defs
  /-- `grams` (`spectec/src/il/env.ml:28`). -/
  | grams
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The name of a namespace, as `env.ml:78-82` spells it. -/
def Space.describe : Space → String
  | .typs => "type"
  | .rels => "relation"
  | .defs => "definition"
  | .grams => "grammar"

mutual

/-- The namespaced identifiers a definition declares, wildcards excluded. -/
def declarations : Def → List (Space × IL.Id)
  | .typD x _ _ => if x == "_" then [] else [(.typs, x)]
  | .relD x _ _ _ _ => if x == "_" then [] else [(.rels, x)]
  | .decD x _ _ _ => if x == "_" then [] else [(.defs, x)]
  | .gramD x _ _ _ => if x == "_" then [] else [(.grams, x)]
  | .recD ds => declarationsList ds

/-- The namespaced identifiers a list of definitions declares. -/
def declarationsList : List Def → List (Space × IL.Id)
  | [] => []
  | d :: ds => declarations d ++ declarationsList ds

end

/-- The check `env.ml:55-58` would perform if it were enabled. -/
def checkDeclarations (s : Script) : Check Unit :=
  match firstDuplicate (declarationsList s) with
  | some (sp, x) => .error s!"duplicate declaration for {sp.describe} `{x}`"
  | none => .ok ()

/-! ## The script -/

/-- `valid` (`valid.ml:823-824`), preceded by the declaration-uniqueness pass
and preceded in turn by the collection of the script-wide shape tables. -/
def checkScript (s : Script) : Check Unit := do
  checkDeclarations s
  let _ ← checkDefs (Scope.initial s) s
  .ok ()

/-- A script is **valid** when `checkScript` accepts it.

This is the decidable predicate `docs/projects/spectec/README.md` calls `WellFormed`,
stated directly rather than as a separate inductive that a Boolean function
decides: the content of the judgment is `checkScript`, which is a transcription
of `valid.ml`, and an inductive copy of it would be the same 500 lines written
twice with a proof of agreement in between.  `wellFormed_iff_valid` is the
duality such a pair would have. -/
def Valid (s : Script) : Prop := checkScript s = .ok ()

/-- `Il.Valid.valid` (`valid.ml:823-824`) as a Boolean: `true` when the script
passes every check this file makes. -/
def wellFormed (s : Script) : Bool := (checkScript s).isOk

/-- `wellFormed` decides `Valid`. -/
theorem wellFormed_iff_valid (s : Script) : wellFormed s = true ↔ Valid s := by
  unfold wellFormed Valid
  cases h : checkScript s with
  | error e => simp [Except.isOk, Except.toBool]
  | ok u => cases u; simp [Except.isOk, Except.toBool]

/-- Validity is decidable, by `wellFormed`. -/
instance (s : Script) : Decidable (Valid s) :=
  decidable_of_iff (wellFormed s = true) (wellFormed_iff_valid s)

/-- The instance reduces in the kernel on a small script.  It does not on a
pinned specification: `Map.find?` walks an association list of several hundred
entries per lookup and compares `String`s, and `docs/projects/spectec/README.md` records what
that costs the kernel.  The streams are therefore checked in compiled code at
the bottom of this file. -/
example : Valid [.decD "f" [] .boolT [.defD [] [] (.boolE true) []]] := by decide

/-- A call to an undeclared definition is not valid (`env.ml:49`). -/
example : ¬ Valid [.decD "f" [] .boolT [.defD [] [] (.callE "g" []) []]] := by decide

/-! ## Running the checker on the pinned specifications

`wellFormed Specs.wasm10 = true` and its siblings are the real test of this
transcription, since `spectec` runs `Il.Valid.valid` before it prints
(`valid.ml:823-824`).  They are far too expensive to reduce in the kernel, and
`Silmaril/SpecTec/Specs.lean` adds its definitions with `addDecl`, so they are
not compiled either; the check is therefore made at elaboration time on a
script re-read from the file, exactly as `Silmaril/SpecTec/Crosscheck.lean`
re-reads `wasm-3.0.ast`.

`Crosscheck.lean` wraps its check in a `command_elab`.  That is not available
here: a `meta` definition may not call a non-`meta` definition of the same
module, and the checker above is the module's whole content, so a command
elaborator in this file could not call it.  Splitting the command into its own
module would work and is what a second file would do; with one file, `#eval` of
a plain `IO` action is the same thing — compiled code, run at elaboration time,
failing the build when it throws. -/

/-- Read a `--ast` stream with `SExp.parseStream`, decode it with
`IL.decodeScript?`, and run the checker over it one top-level definition at a
time, naming the first definition that fails.  Throws on failure, so an `#eval`
of it fails the build. -/
def checkStreamFile (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let forms ← match SExp.parseStream contents with
    | .error msg => throw (IO.userError s!"{path} is not an S-expression stream: {msg}")
    | .ok forms => pure forms
  let some script := IL.decodeScript? forms
    | throw (IO.userError s!"{path} is not a printed SpecTec IL script")
  match checkDeclarations script with
  | .error msg => throw (IO.userError s!"{path}: {msg}")
  | .ok () => pure ()
  let mut sc := Scope.initial script
  for d in script do
    match checkDef sc d with
    | .error msg => throw (IO.userError s!"{path} rejects `{defName d}`: {msg}")
    | .ok sc' => sc := sc'
  -- Sensitivity on the real data: a SpecTec script declares before it uses, so
  -- the same definitions in the opposite order must *not* be accepted.
  match checkScript script.reverse with
  | .ok () => throw (IO.userError s!"{path}: the reversed script was accepted as well")
  | .error _ => pure ()
  IO.println s!"{path}: {script.length} definitions are well-formed, and rejected when reversed"

/-! ### What the checker rejects

The three streams below exercise the accepting direction.  These exercise the
rejecting one: each entry is a tiny script that fails exactly one check,
paired with the repair that makes it pass, so that the rejection is pinned to
the stated cause and not to something incidental. -/

/-- A check, a script that fails it, the repair that makes it pass, and a
fragment the rejection message must contain. -/
def rejectionTests : List (String × Script × Script × String) :=
  [ ("undeclared definition (valid.ml:466, env.ml:49)",
      [.decD "f" [] .boolT [.defD [] [] (.callE "g" []) []]],
      [.decD "g" [] .boolT [.defD [] [] (.boolE true) []],
       .decD "f" [] .boolT [.defD [] [] (.callE "g" []) []]],
      "undeclared definition `g`"),
    ("unbound variable (valid.ml:376, env.ml:49)",
      [.decD "f" [.expP "x" .boolT] .boolT
        [.defD [.expP "x" .boolT] [.expA (.varE "x")] (.varE "y") []]],
      [.decD "f" [.expP "x" .boolT] .boolT
        [.defD [.expP "x" .boolT] [.expA (.varE "x")] (.varE "x") []]],
      "undeclared variable `y`"),
    ("too few arguments (valid.ml:685)",
      [.typD "t" [.typP "X"] [], .decD "f" [] (.varT "t" []) []],
      [.typD "t" [.typP "X"] [], .decD "f" [] (.varT "t" [.typA .boolT]) []],
      "too few arguments"),
    ("sort mismatch for argument (valid.ml:674-676)",
      [.typD "t" [.typP "X"] [], .decD "f" [] (.varT "t" [.expA (.boolE true)]) []],
      [.typD "t" [.typP "X"] [], .decD "f" [] (.varT "t" [.typA .boolT]) []],
      "sort mismatch for argument"),
    ("duplicate declaration (env.ml:55-58)",
      [.decD "f" [] .boolT [], .decD "f" [] .boolT []],
      [.decD "f" [] .boolT [], .decD "g" [] .boolT []],
      "duplicate declaration for definition `f`"),
    ("recursion between different sorts (valid.ml:813)",
      [.recD [.decD "f" [] .boolT [], .typD "t" [] []]],
      [.recD [.decD "f" [] .boolT [], .decD "g" [] .boolT []]],
      "invalid recursion between definitions of different sort"),
    ("definite iterator in a type (valid.ml:248)",
      [.decD "f" [] (.iterT .boolT (.listN (.numE (.natN 3)) none)) []],
      [.decD "f" [] (.iterT .boolT .list) []],
      "definite iterator not allowed in type"),
    ("vacuous iteration (valid.ml:213)",
      [.decD "f" [] .boolT [.defD [] [] (.iterE (.boolE true) (.mk .list [])) []]],
      [.decD "f" [.expP "x" (.iterT .boolT .list)] .boolT
        [.defD [.expP "x" (.iterT .boolT .list)] [.expA (.varE "x")]
          (.iterE (.varE "y") (.mk .list [.mk "y" (.varE "x")])) []]],
      "vacuous iteration"),
    ("unknown case (valid.ml:31)",
      [.typD "t" [] [.instD [] [] (.variantT [.mk "A" (.tupT []) [] []])],
       .decD "f" [] (.varT "t" []) [.defD [] [] (.caseE "B" (.tupE [])) []]],
      [.typD "t" [] [.instD [] [] (.variantT [.mk "A" (.tupT []) [] []])],
       .decD "f" [] (.varT "t" []) [.defD [] [] (.caseE "A" (.tupE [])) []]],
      "unknown case `B`"),
    ("wildcard on a right-hand side (valid.ml:372)",
      [.decD "f" [] .boolT [.defD [] [] (.varE "_") []]],
      [.decD "f" [.expP "x" .boolT] .boolT
        [.defD [] [.expA (.varE "_")] (.boolE true) []]],
      "wildcard variable on a right-hand side"),
    ("illegal operator annotation (num.ml:73)",
      [.decD "f" [] (.numT .natT)
        [.defD [] [] (.binE .subOp (.numT .natT) (.numE (.natN 1)) (.numE (.natN 1))) []]],
      [.decD "f" [] (.numT .intT)
        [.defD [] [] (.binE .subOp (.numT .intT) (.numE (.natN 1)) (.numE (.natN 1))) []]],
      "illegal type nat"),
    ("rule mixop does not match the relation (valid.ml:730)",
      [.relD "R" [] "|-%" .boolT [.ruleD "r" [] "|-" (.boolE true) []]],
      [.relD "R" [] "|-%" .boolT [.ruleD "r" [] "|-%" (.boolE true) []]],
      "does not match expected notation"),
    -- A relation is only in scope inside its own rules when `infer_def`
    -- (`valid.ml:764-767`) has entered it, i.e. inside a `RecD` group.
    ("premise mixop does not match the relation (valid.ml:619)",
      [.recD [.relD "R" [] "|-%" .boolT
        [.ruleD "r" [] "|-%" (.boolE true) [.rulePr "R" [] "|-" (.boolE true)]]]],
      [.recD [.relD "R" [] "|-%" .boolT
        [.ruleD "r" [] "|-%" (.boolE true) [.rulePr "R" [] "|-%" (.boolE true)]]]],
      "does not match expected notation"),
    ("unbound field (valid.ml:26)",
      [.decD "f" [.expP "x" .boolT] .boolT
        [.defD [.expP "x" .boolT] [.expA (.varE "x")] (.dotE (.varE "x") "A") []]],
      [.typD "r" [] [.instD [] [] (.structT [.mk "A" .boolT [] []])],
       .decD "f" [.expP "x" .boolT] .boolT
        [.defD [.expP "x" .boolT] [.expA (.varE "x")] (.dotE (.varE "x") "A") []]],
      "unbound field `A`"),
    -- `bind` (`env.ml:52-54`) never enters a declaration named `_` in any
    -- namespace, so a `typD` that declares the wildcard declares nothing and
    -- a `varT` naming it does not resolve.  `Map.bind`
    -- (`Silmaril/SpecTec/Sem/Env.lean`) is where that guard lives, so every
    -- `Scope.bind*` below inherits it; this pins the behaviour.
    ("the wildcard is never declared (env.ml:53-54)",
      [.typD "_" [] [], .decD "f" [] (.varT "_" []) []],
      [.typD "t" [] [], .decD "f" [] (.varT "t" []) []],
      "undeclared type `_`"),
    ("duplicate variant case (valid.ml:178)",
      [.typD "t" []
        [.instD [] [] (.variantT [.mk "A" (.tupT []) [] [], .mk "A" (.tupT []) [] []])]],
      [.typD "t" []
        [.instD [] [] (.variantT [.mk "A" (.tupT []) [] [], .mk "B" (.tupT []) [] []])]],
      "duplicate case(s) `A`") ]

/-- Throw unless every entry of `rejectionTests` is rejected with the expected
message and its repair is accepted. -/
def checkRejectionTests : IO Unit := do
  for (name, bad, good, fragment) in rejectionTests do
    match checkScript bad with
    | .ok () => throw (IO.userError s!"{name}: the malformed script was accepted")
    | .error msg =>
        unless (msg.splitOn fragment).length > 1 do
          throw (IO.userError s!"{name}: rejected with \"{msg}\", expected \"{fragment}\"")
    match checkScript good with
    | .error msg => throw (IO.userError s!"{name}: the repair was rejected with \"{msg}\"")
    | .ok () => pure ()
  IO.println s!"{rejectionTests.length} malformed scripts are rejected, and their repairs \
    accepted"

end Silmaril.SpecTec.Sem

#eval Silmaril.SpecTec.Sem.checkRejectionTests

/-! ### The three pinned specifications

Each `#eval` throws, and so fails the build, if the checker rejects the
stream. -/

#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/wasm-1.0.ast"

#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/wasm-2.0.ast"

#eval Silmaril.SpecTec.Sem.checkStreamFile "specs/spectec/wasm-3.0.ast"
