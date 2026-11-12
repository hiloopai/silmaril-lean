module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Defs

/-!
# Round 7, REH route 2: abstract typing of values, and the flow check

Round 6, pass 2 (`Round7.NxSites`) checks that every comparison reachable from `Step` has an
operand whose *inferred* type (`NxSites.tyOf`) cannot hold an `EXPORTS` record. The inferred
types come from declared types: the quantifiers of rules and clauses, record fields, variant
cases and definition results. For rule quantifiers of `Step` they are checked at runtime
(`Sim.QuantsOk`); for everything else the link needs evaluator type preservation. This header
states the static side of that link.

**Abstract typing of values** (`vtB S a v`). A value `v` *conforms* to an abstract type `a`
when:

* `a` is export-free (`NxSites.nxAT`): `v` is export-free (`Swap.nxB`);
* `a` unfolds to a type name `n`: if `v` is a record, every field `k` conforms to
  `fieldAT S n k`; if `v` is a case `op`, its payload conforms to `caseAT S n op`;
* `a` unfolds to an iteration of `b`: every element of a list or option conforms to `b`;
* `a` unfolds to a tuple type: every component conforms to its type;
* otherwise (in particular for `.unk`) every value conforms.

Conformance forgets everything a value's type says beyond where export records may sit: no
numeric ranges, no premises. It is the property the site check needs, and it is what the
evaluator can preserve without proving anything about the arithmetic of the script.

**The flow check.** Three judgments on expressions in a scope `Γ` of declared quantifier
types, all Boolean so the kernel can run them over the script:

* `tyOk S T Γ e`: every subexpression's inferred type is justified: at every list literal,
  concatenation, subtype coercion, definition call and relation premise, the parts flow into
  the inferred or declared types (`ckE`);
* `ckE S T Γ a e`: the value of `e` conforms to `a`, either because the inferred type is below
  `a` (`atLe`) or by the shape of `e` (records, cases, tuples, lists, updates, …);
* `patTy S T Γ a p`: matching the pattern `p` against a value conforming to `a` binds every
  variable to a value conforming to its declared type.

`T : TSig` adds to `NxSites.Sig` the parameter types of definitions, the result types of
generic definitions, and the parameter and conclusion types of relations. Inside a generic
definition such as `$concat_`, a variable of type `X` may hold any value, since `X` is
instantiated at the call; the check substitutes the type parameters (`substTP`).

`flowItem S T d` counts the failures on one top-level definition: the entries of `T` must agree
with it, and, if it is reachable from `Step`, its clauses and rules must pass the flow check. A
generic definition is checked twice: with its type parameters unknown (`.unk`, valid for every
instantiation; its comparison sites are then checked again by `NxSites` without counting the
type parameters as export-free), and with them export-free (`.base`, valid for calls whose type
arguments are export-free). Definition parameters (`$f_`) are checked against their declared
signature, and the definitions passed for them against it (`defSub`). Pattern variables must be
quantifiers, and the variables a pattern iteration binds must not be (`freshDoms`).
`typItemOk` checks the type entries of a signature against the type definitions.

The **soundness** of the flow check, that the evaluator preserves conformance, is *not* proved
here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB)

/-! ## Conformance of values to abstract types -/

/-- The unfolded form of an abstract type, as the check and conformance read it. -/
def unf (S : Sig) (a : AT) : AT := unalias S 8 a

mutual
/-- **A value conforms to an abstract type**; see the module docstring. -/
def vtB (S : Sig) (a : AT) : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .opt none => true
  | .struct gs => if nxAT S.good a then Swap.nxBf gs else
    match unf S a with
    | .name n _ => vtF S n gs
    | _ => true
  | .case op w => if nxAT S.good a then Swap.nxB w else
    match unf S a with
    | .name n _ => vtB S (caseAT S n op) w
    | _ => true
  | .list vs => if nxAT S.good a then Swap.nxBs vs else
    match unf S a with
    | .iter b => vtL S b vs
    | _ => true
  | .opt (some w) => if nxAT S.good a then Swap.nxB w else
    match unf S a with
    | .iter b => vtB S b w
    | _ => true
  | .tuple vs => if nxAT S.good a then Swap.nxBs vs else
    match unf S a with
    | .tup xs => vtT S xs vs
    | _ => true

/-- Every element conforms to `b`. -/
def vtL (S : Sig) (b : AT) : List Value → Bool
  | [] => true
  | v :: vs => vtB S b v && vtL S b vs

/-- Every field `k` conforms to the field type of record type `n` at `k`. -/
def vtF (S : Sig) (n : String) : List (AtomS × Value) → Bool
  | [] => true
  | (k, v) :: gs => vtB S (fieldAT S n k) v && vtF S n gs

/-- The components of a tuple conform to the component types (missing types are `.unk`). -/
def vtT (S : Sig) : List AT → List Value → Bool
  | _, [] => true
  | xs, v :: vs => vtB S (xs.headD .unk) v && vtT S xs.tail vs
end

/-! ## Abstract types -/

mutual
/-- Replace the type parameters `tps` (names without arguments) by `b`. -/
def substTP (tps : List String) (b : AT) : AT → AT
  | .name n xs => if tps.contains n then b else .name n (substTPs tps b xs)
  | .iter a => .iter (substTP tps b a)
  | .tup xs => .tup (substTPs tps b xs)
  | a => a

/-- `substTP` on a list. -/
def substTPs (tps : List String) (b : AT) : List AT → List AT
  | [] => []
  | a :: xs => substTP tps b a :: substTPs tps b xs
end

/-- **Every value conforms to `a`** (with fuel): `a` is unknown, names a type the signature
records no field or case for, or is an iteration or tuple of such types. -/
def trivK (S : Sig) : Nat → AT → Bool
  | 0, _ => false
  | k + 1, a =>
    !nxAT S.good a &&
    match unf S a with
    | .unk => true
    | .name n _ => !(S.fields.any fun p => p.1 == n) && !(S.cases.any fun p => p.1 == n)
    | .iter b => trivK S k b
    | .tup xs => xs.all fun b => trivK S k b
    | _ => false

/-- `trivK` at fuel 8. -/
def triv (S : Sig) (a : AT) : Bool := trivK S 8 a

/-- **Conformance to `a` implies conformance to `b`** (a sound approximation, with fuel for the
structure of the types). -/
def atLe (S : Sig) : Nat → AT → AT → Bool
  | 0, a, b => nxAT S.good a || triv S b
  | k + 1, a, b =>
    nxAT S.good a || triv S b || (!nxAT S.good b && atEq (unf S a) (unf S b)) ||
    (!nxAT S.good b && match unf S a, unf S b with
      | .iter a', .iter b' => atLe S k a' b'
      | .tup xs, .tup ys => xs.length == ys.length && (xs.zip ys).all fun p => atLe S k p.1 p.2
      | .name n _, .name m _ => n == m
      | _, _ => false)

/-- The element type of a type, `.base` (export-free) when the type is export-free. -/
def elemOf (S : Sig) (a : AT) : AT := if nxAT S.good a then .base else elemAT S a

/-- The field type at `k`, `.base` when the type is export-free. -/
def fieldOf' (S : Sig) (a : AT) (k : String) : AT :=
  if nxAT S.good a then .base else
  match unf S a with
  | .name n _ => fieldAT S n k
  | _ => .unk

/-- The case payload type at `op`, `.base` when the type is export-free. -/
def caseOf' (S : Sig) (a : AT) (op : String) : AT :=
  if nxAT S.good a then .base else
  match unf S a with
  | .name n _ => caseAT S n op
  | _ => .unk

/-- The `i`-th component type, `.base` when the type is export-free. -/
def compOf (S : Sig) (a : AT) (i : Nat) : AT :=
  if nxAT S.good a then .base else
  match unf S a with
  | .tup xs => xs.getD i .unk
  | _ => .unk

/-- The type of the sub-value a path selects. -/
def pathAT (S : Sig) (a : AT) : Path → AT
  | .rootP => a
  | .idxP p _ => elemOf S (pathAT S a p)
  | .sliceP p _ _ => pathAT S a p
  | .dotP p k => fieldOf' S (pathAT S a p) k

/-- A type whose values are lists or options of conforming elements, or export-free. -/
def iterLike (S : Sig) (a : AT) : Bool :=
  nxAT S.good a || match unf S a with
    | .iter _ => true
    | _ => false

/-! ## The extended signature -/

/-- The type of a parameter, as the flow check reads it: an expression parameter's type; a
definition parameter's parameter types (`none` for non-expression parameters) and result type;
anything else. -/
inductive PT where
  | exp (a : AT)
  | defn (ps : List (Option AT)) (r : AT)
  | other
  deriving Repr, Inhabited

/-- **Parameter and conclusion types** the flow check uses, besides `NxSites.Sig`. Validated
against the script by `tsigDefOk` and `tsigRelOk`. -/
structure TSig where
  /-- Definitions: type parameters and parameter types. -/
  params : List (String × List String × List PT)
  /-- Generic definitions (with type parameters): type parameters and result type. -/
  gres : List (String × List String × AT)
  /-- Relations: parameter types and conclusion type. -/
  rels : List (String × List PT × AT)

/-- The type of an expression or definition parameter, if it is one. -/
def optAT : Param → Option AT
  | .expP _ t => some (toAT t)
  | _ => none

/-- The parameter types of a parameter list. -/
def paramPTs (ps : List Param) : List PT :=
  ps.map fun p => match p with
    | .expP _ t => .exp (toAT t)
    | .defP _ dps t => .defn (dps.map optAT) (toAT t)
    | _ => .other

/-- `substTP` on a parameter type. -/
def substPT (tps : List String) (b : AT) : PT → PT
  | .exp a => .exp (substTP tps b a)
  | .defn ps r => .defn (ps.map (Option.map (substTP tps b))) (substTP tps b r)
  | .other => .other

/-- Default fuel for `atLe`. -/
abbrev atFuel : Nat := 8

/-- The type arguments of a call are export-free. -/
def tyArgsNx (S : Sig) (args : List Arg) : Bool :=
  args.all fun a => match a with
    | .typA t => nxAT S.good (toAT t)
    | _ => true

/-- The type parameters of a generic definition stand for `.base` (export-free) at a call
whose type arguments are export-free, and for `.unk` otherwise. -/
def tpFill (S : Sig) (args : List Arg) : AT := if tyArgsNx S args then .base else .unk

/-- **The result type of a call**: a generic definition's result type with its type parameters
filled, else the result type `S` records. -/
def callRes (S : Sig) (T : TSig) (f : String) (args : List Arg) : AT :=
  match T.gres.lookup f with
  | some (tps, r) => substTP tps (tpFill S args) r
  | none => (S.results.lookup f).getD .unk

/-- **The parameter types of a call**, type parameters filled. -/
def callPar (S : Sig) (T : TSig) (f : String) (args : List Arg) : Option (List PT) :=
  (T.params.lookup f).map fun p => p.2.map (substPT p.1 (tpFill S args))

/-! ## The flow check -/

mutual
/-- **The value of `e` is export-free, by its form**: `NxSites.nxE`, or a part (field, case
payload, component, element or slice) of an export-free value. -/
def nxD (S : Sig) (Γ : List (String × AT)) : Exp → Bool
  | .dotE e a => nxE S Γ (.dotE e a) || nxD S Γ e
  | .uncaseE e op => nxE S Γ (.uncaseE e op) || nxD S Γ e
  | .projE e i => nxE S Γ (.projE e i) || nxD S Γ e
  | .idxE e₁ e₂ => nxE S Γ (.idxE e₁ e₂) || nxD S Γ e₁
  | .theE e => nxE S Γ (.theE e) || nxD S Γ e
  | .sliceE e₁ e₂ e₃ => nxE S Γ (.sliceE e₁ e₂ e₃) || nxD S Γ e₁
  | .caseE op e => nxE S Γ (.caseE op e) || nxD S Γ e
  | .tupE es => nxE S Γ (.tupE es) || nxDs S Γ es
  | .listE es => nxE S Γ (.listE es) || nxDs S Γ es
  | .optE (some e) => nxE S Γ (.optE (some e)) || nxD S Γ e
  | .catE e₁ e₂ => nxE S Γ (.catE e₁ e₂) || (nxD S Γ e₁ && nxD S Γ e₂)
  | .liftE e => nxE S Γ (.liftE e) || nxD S Γ e
  | .subE e t₁ t₂ => nxE S Γ (.subE e t₁ t₂) || nxD S Γ e
  | e => nxE S Γ e

/-- `nxD` on a list. -/
def nxDs (S : Sig) (Γ : List (String × AT)) : List Exp → Bool
  | [] => true
  | e :: es => nxD S Γ e && nxDs S Γ es
end

mutual
/-- **The value of `e` conforms to `a`**; see the module docstring. -/
def ckE (S : Sig) (T : TSig) (Γ : List (String × AT)) (a : AT) : Exp → Bool
  | .strE fs =>
    (nxAT S.good a && ckFsN S T Γ fs) || triv S a ||
    (!nxAT S.good a && match unf S a with
      | .name n _ => ckFs S T Γ n fs
      | _ => false)
  | .caseE op e =>
    (nxAT S.good a && ckE S T Γ .base e) || triv S a ||
    (!nxAT S.good a && match unf S a with
      | .name n _ => ckE S T Γ (caseAT S n op) e
      | _ => false)
  | .tupE es =>
    (nxAT S.good a && ckL S T Γ .base es) || triv S a ||
    (!nxAT S.good a && match unf S a with
      | .tup xs => ckT S T Γ xs es
      | _ => false)
  | .listE es =>
    atLe S atFuel (tyOf S Γ (.listE es)) a || ckL S T Γ (elemOf S a) es
  | .optE none => true
  | .optE (some e) =>
    atLe S atFuel (tyOf S Γ (.optE (some e))) a || ckE S T Γ (elemOf S a) e
  | .catE e₁ e₂ =>
    atLe S atFuel (tyOf S Γ (.catE e₁ e₂)) a ||
    (iterLike S a && ckE S T Γ a e₁ && ckE S T Γ a e₂)
  | .liftE e => triv S a || (iterLike S a && ckE S T Γ a e)
  | .iterE e (.mk it ds) =>
    atLe S atFuel (tyOf S Γ (.iterE e (.mk it ds))) a ||
    (iterLike S a && ckE S T (iterΓ S Γ it ds) (elemOf S a) e)
  | .compE e₁ e₂ => triv S a || (ckE S T Γ a e₁ && ckE S T Γ a e₂)
  | .updE e₁ p e₂ => triv S a || (ckE S T Γ a e₁ && ckE S T Γ (pathAT S a p) e₂)
  | .extE e₁ p e₂ =>
    triv S a || (ckE S T Γ a e₁ && iterLike S (pathAT S a p) && ckE S T Γ (pathAT S a p) e₂)
  | .subE e _ _ => ckE S T Γ a e
  | .callE f args =>
    atLe S atFuel (callRes S T f args) a || (nxAT S.good a && nxD S Γ (.callE f args))
  | e => atLe S atFuel (tyOf S Γ e) a || (nxAT S.good a && nxD S Γ e)

/-- `ckE` on every element. -/
def ckL (S : Sig) (T : TSig) (Γ : List (String × AT)) (a : AT) : List Exp → Bool
  | [] => true
  | e :: es => ckE S T Γ a e && ckL S T Γ a es

/-- `ckE` on tuple components. -/
def ckT (S : Sig) (T : TSig) (Γ : List (String × AT)) : List AT → List Exp → Bool
  | _, [] => true
  | xs, e :: es => ckE S T Γ (xs.headD .unk) e && ckT S T Γ xs.tail es

/-- `ckE` on record fields of an export-free record: no field is `EXPORTS`, and every field is
export-free. -/
def ckFsN (S : Sig) (T : TSig) (Γ : List (String × AT)) : List ExpField → Bool
  | [] => true
  | .mk k e :: fs => k != "EXPORTS" && ckE S T Γ .base e && ckFsN S T Γ fs

/-- `ckE` on record fields of record type `n`. -/
def ckFs (S : Sig) (T : TSig) (Γ : List (String × AT)) (n : String) : List ExpField → Bool
  | [] => true
  | .mk k e :: fs => ckE S T Γ (fieldAT S n k) e && ckFs S T Γ n fs
end

/-- The parameters of definition parameter `dps` flow into those of `g`, and `g`'s result into
`r`: `g` may stand for the parameter. -/
def defSub (S : Sig) (T : TSig) (g : String) (dps : List (Option AT)) (r : AT) : Bool :=
  atLe S atFuel ((S.results.lookup g).getD .unk) r &&
  match T.params.lookup g with
  | some ([], gps) => go dps gps
  | _ => false
where
  /-- Pointwise, contravariantly. -/
  go : List (Option AT) → List PT → Bool
    | [], [] => true
    | some d :: ds, .exp p :: ps => atLe S atFuel d p && go ds ps
    | none :: ds, .other :: ps => go ds ps
    | _, _ => false

/-- The arguments of a call flow into the parameter types. -/
def ckArgs (S : Sig) (T : TSig) (Γ : List (String × AT)) : List Arg → List PT → Bool
  | [], [] => true
  | .expA e :: xs, .exp a :: ps => ckE S T Γ a e && ckArgs S T Γ xs ps
  | .defA g :: xs, .defn dps r :: ps => defSub S T g dps r && ckArgs S T Γ xs ps
  | .typA _ :: xs, .other :: ps => ckArgs S T Γ xs ps
  | .gramA _ :: xs, .other :: ps => ckArgs S T Γ xs ps
  | _, _ => false

mutual
/-- **Every inferred type of a subexpression of `e` is justified**; see the module docstring.
Calls to names without parameter entries are accepted only when their result type is
trivial. -/
def tyOk (S : Sig) (T : TSig) (Γ : List (String × AT)) : Exp → Bool
  | .unE _ _ e => tyOk S T Γ e
  | .binE _ _ e₁ e₂ => tyOk S T Γ e₁ && tyOk S T Γ e₂
  | .cmpE _ _ e₁ e₂ => tyOk S T Γ e₁ && tyOk S T Γ e₂
  | .tupE es => tyOkL S T Γ es
  | .projE e _ => tyOk S T Γ e
  | .caseE _ e => tyOk S T Γ e
  | .uncaseE e _ => tyOk S T Γ e
  | .optE none => true
  | .optE (some e) => tyOk S T Γ e
  | .theE e => tyOk S T Γ e
  | .strE fs => tyOkF S T Γ fs
  | .dotE e _ => tyOk S T Γ e
  | .compE e₁ e₂ => tyOk S T Γ e₁ && tyOk S T Γ e₂
  | .listE es => tyOkL S T Γ es &&
    match es with
    | [] => true
    | e :: es' => ckL S T Γ (tyOf S Γ e) es'
  | .liftE e => tyOk S T Γ e
  | .memE e₁ e₂ => tyOk S T Γ e₁ && tyOk S T Γ e₂
  | .lenE e => tyOk S T Γ e
  | .catE e₁ e₂ => tyOk S T Γ e₁ && tyOk S T Γ e₂ && ckE S T Γ (tyOf S Γ e₁) e₂
  | .idxE e₁ e₂ => tyOk S T Γ e₁ && tyOk S T Γ e₂
  | .sliceE e₁ e₂ e₃ => tyOk S T Γ e₁ && tyOk S T Γ e₂ && tyOk S T Γ e₃
  | .updE e₁ p e₂ => tyOk S T Γ e₁ && tyOkP S T Γ p && tyOk S T Γ e₂
  | .extE e₁ p e₂ => tyOk S T Γ e₁ && tyOkP S T Γ p && tyOk S T Γ e₂
  | .callE f args => tyOkA S T Γ args &&
    match callPar S T f args with
    | some ps => ckArgs S T Γ args ps
    | none => triv S ((S.results.lookup f).getD .unk) && (T.gres.lookup f).isNone
  | .iterE e (.mk it ds) =>
    tyOk S T (iterΓ S Γ it ds) e && tyOkI S T Γ it && tyOkD S T Γ ds
  | .cvtE e _ _ => tyOk S T Γ e
  | .subE e _ t₂ => tyOk S T Γ e && ckE S T Γ (toAT t₂) e
  | _ => true

/-- `tyOk` on a list. -/
def tyOkL (S : Sig) (T : TSig) (Γ : List (String × AT)) : List Exp → Bool
  | [] => true
  | e :: es => tyOk S T Γ e && tyOkL S T Γ es

/-- `tyOk` on record fields. -/
def tyOkF (S : Sig) (T : TSig) (Γ : List (String × AT)) : List ExpField → Bool
  | [] => true
  | .mk _ e :: fs => tyOk S T Γ e && tyOkF S T Γ fs

/-- `tyOk` on the indices of a path. -/
def tyOkP (S : Sig) (T : TSig) (Γ : List (String × AT)) : Path → Bool
  | .rootP => true
  | .idxP p e => tyOkP S T Γ p && tyOk S T Γ e
  | .sliceP p e₁ e₂ => tyOkP S T Γ p && tyOk S T Γ e₁ && tyOk S T Γ e₂
  | .dotP p _ => tyOkP S T Γ p

/-- `tyOk` on the bound of a `ListN` iteration. -/
def tyOkI (S : Sig) (T : TSig) (Γ : List (String × AT)) : Iter → Bool
  | .listN e _ => tyOk S T Γ e
  | _ => true

/-- `tyOk` on iteration domains. -/
def tyOkD (S : Sig) (T : TSig) (Γ : List (String × AT)) : List Dom → Bool
  | [] => true
  | .mk _ e :: ds => tyOk S T Γ e && tyOkD S T Γ ds

/-- `tyOk` on the expression arguments of a call. -/
def tyOkA (S : Sig) (T : TSig) (Γ : List (String × AT)) : List Arg → Bool
  | [] => true
  | .expA e :: xs => tyOk S T Γ e && tyOkA S T Γ xs
  | _ :: xs => tyOkA S T Γ xs
end

/-- The variables a pattern iteration binds in its body (domain variables and the `ListN`
counter) are not quantifiers of the enclosing scope, so the enclosing scope never binds
them. -/
def freshDoms (Γ : List (String × AT)) (it : Iter) (ds : List Dom) : Bool :=
  ds.all (fun d => match d with | .mk x _ => (Γ.lookup x).isNone) &&
  match it with
  | .listN _ (some x) => (Γ.lookup x).isNone
  | _ => true

mutual
/-- **Matching `p` against a value conforming to `a` binds conforming values**; see the module
docstring. Forms that are evaluated and compared (`matchDefault`) bind nothing, but their
subexpressions must pass `tyOk`. -/
def patTy (S : Sig) (T : TSig) (Γ : List (String × AT)) (a : AT) : Exp → Bool
  | .varE x => (Γ.lookup x).isSome && atLe S atFuel a ((Γ.lookup x).getD .unk)
  | .boolE _ => true
  | .numE _ => true
  | .textE _ => true
  | .optE none => true
  | .unE op t e => patTy S T Γ .base e && tyOk S T Γ (.unE op t e)
  | .cvtE e t₁ t₂ => patTy S T Γ .base e && tyOk S T Γ (.cvtE e t₁ t₂)
  | .tupE es => patT S T Γ a 0 es
  | .listE es => patL S T Γ (elemOf S a) es
  | .projE e i => if i = 0 then patTy S T Γ (.tup [a]) e else tyOk S T Γ (.projE e i)
  | .caseE op e => patTy S T Γ (caseOf' S a op) e
  | .uncaseE e _ => patTy S T Γ (if nxAT S.good a then .base else .unk) e
  | .optE (some e) => patTy S T Γ (elemOf S a) e
  | .strE fs => patF S T Γ a fs
  | .catE e₁ e₂ =>
    let b := if iterLike S a then a else .unk
    patTy S T Γ b e₁ && patTy S T Γ b e₂
  | .subE e _ _ => patTy S T Γ a e
  | .iterE e (.mk it ds) =>
    patI S T Γ it && freshDoms Γ it ds && patTy S T (iterΓ S Γ it ds) (elemOf S a) e &&
      patD S T Γ (iterΓ S Γ it ds) ds
  | e => tyOk S T Γ e

/-- `patTy` on list elements. -/
def patL (S : Sig) (T : TSig) (Γ : List (String × AT)) (b : AT) : List Exp → Bool
  | [] => true
  | e :: es => patTy S T Γ b e && patL S T Γ b es

/-- `patTy` on tuple components. -/
def patT (S : Sig) (T : TSig) (Γ : List (String × AT)) (a : AT) (i : Nat) : List Exp → Bool
  | [] => true
  | e :: es => patTy S T Γ (compOf S a i) e && patT S T Γ a (i + 1) es

/-- `patTy` on record fields. -/
def patF (S : Sig) (T : TSig) (Γ : List (String × AT)) (a : AT) : List ExpField → Bool
  | [] => true
  | .mk k e :: fs => patTy S T Γ (fieldOf' S a k) e && patF S T Γ a fs

/-- The bound of a `ListN` pattern is matched against a number. -/
def patI (S : Sig) (T : TSig) (Γ : List (String × AT)) : Iter → Bool
  | .listN e _ => patTy S T Γ .base e
  | _ => true

/-- The sources of the domains of a pattern iteration are matched against the columns of the
values the body bound to the domain variables (`Γi` is the body's scope). -/
def patD (S : Sig) (T : TSig) (Γ Γi : List (String × AT)) : List Dom → Bool
  | [] => true
  | .mk x e :: ds => patTy S T Γ (.iter ((Γi.lookup x).getD .unk)) e && patD S T Γ Γi ds
end

/-- The arguments of a relation premise flow into its parameter types, and its conclusion into
its conclusion type. -/
def ckRulePr (S : Sig) (T : TSig) (Γ : List (String × AT)) (x : String) (args : List Arg)
    (e : Exp) : Bool :=
  tyOkA S T Γ args && tyOk S T Γ e &&
  match T.rels.lookup x with
  | some (ps, t) => ckArgs S T Γ args ps && ckE S T Γ t e
  | none => false

/-- **A premise passes the flow check.** -/
def premTy (S : Sig) (T : TSig) (Γ : List (String × AT)) : Prem → Bool
  | .rulePr x args _ e => ckRulePr S T Γ x args e
  | .ifPr e => tyOk S T Γ e
  | .letPr e₁ e₂ => tyOk S T Γ e₂ && patTy S T Γ (tyOf S Γ e₂) e₁
  | .elsePr => true
  | .iterPr pr (.mk it ds) =>
    premTy S T (iterΓ S Γ it ds) pr && tyOkI S T Γ it && tyOkD S T Γ ds

/-- The argument patterns of a clause, matched against conforming arguments. -/
def patArgs (S : Sig) (T : TSig) (Γ : List (String × AT)) : List Arg → List PT → Bool
  | [], [] => true
  | .expA e :: xs, .exp a :: ps => patTy S T Γ a e && patArgs S T Γ xs ps
  | .defA _ :: xs, .defn _ _ :: ps => patArgs S T Γ xs ps
  | .typA _ :: xs, .other :: ps => patArgs S T Γ xs ps
  | .gramA _ :: xs, .other :: ps => patArgs S T Γ xs ps
  | _, _ => false

/-! ## Clauses, rules and definitions -/

/-- The definition parameters among a clause's quantifiers, with their parameter types and
result type. -/
def defQuants : List Param → List (String × List (Option AT) × AT)
  | [] => []
  | .defP x dps t :: ps => (x, dps.map optAT, toAT t) :: defQuants ps
  | _ :: ps => defQuants ps

/-- **The signatures inside a clause**: its definition parameters are definitions with their
declared types, the type parameters `tps` stand for `b`, and, when `b` is `.unk`, they are no
longer export-free. -/
def clauseSig (S : Sig) (tps : List String) (b : AT) (qs : List Param) : Sig :=
  { S with
    good := if b matches .unk then S.good.filter (fun x => !tps.contains x) else S.good
    results := (defQuants qs).map (fun p => (p.1, substTP tps b p.2.2)) ++ S.results }

/-- The definition parameters of a clause as parameter entries. -/
def clauseTSig (T : TSig) (tps : List String) (b : AT) (qs : List Param) : TSig :=
  { T with params := (defQuants qs).map (fun p =>
      (p.1, ([] : List String), p.2.1.map fun o => match o with
        | some a => PT.exp (substTP tps b a)
        | none => PT.other)) ++ T.params }

/-- **The definition parameters of a clause are its definition patterns**: every `def y`
argument pattern names a definition quantifier, and every definition quantifier is such a
pattern, so a call to `y` in the clause calls what the caller passed. -/
def defPatsOk (qs : List Param) (args : List Arg) : Bool :=
  (args.all fun a => match a with
    | .defA y => (defQuants qs).any (·.1 == y)
    | _ => true) &&
  (defQuants qs).all fun d => args.any fun a => match a with
    | .defA y => y == d.1
    | _ => false

/-- **The failures of the flow check on a clause** of a definition with type parameters `tps`,
parameter types `pts` and result type `r`, with the type parameters standing for `b`: the
argument patterns, premises, body, and comparison sites (`NxSites`). -/
def clauseFlow (S : Sig) (T : TSig) (tps : List String) (b : AT) (pts : List PT) (r : AT) :
    Clause → Nat
  | .defD qs args e prems =>
    let S' := clauseSig S tps b qs
    let T' := clauseTSig T tps b qs
    let Γ := (quantsΓ qs).map fun p => (p.1, substTP tps b p.2)
    (if defPatsOk qs args && patArgs S' T' Γ args (pts.map (substPT tps b)) then 0 else 1) +
    (prems.filter fun pr => !premTy S' T' Γ pr).length +
    (if tyOk S' T' Γ e then 0 else 1) +
    (if ckE S' T' Γ (substTP tps b r) e then 0 else 1) +
    (if b matches .unk && !tps.isEmpty then
      (patAs S' Γ [] args).2 + badE S' Γ e + prems.foldl (fun k pr => k + badPr S' Γ pr) 0
    else 0)

/-- **The failures of the flow check on a rule** of a relation with parameters `ps` and
conclusion type `t`. For relations matched by `Sem.derives`, the conclusion is a pattern
matched against a value conforming to `t`. For `Step`, `Step_pure` and `Step_read` the
quantifiers are typed at runtime. -/
def ruleFlow (S : Sig) (T : TSig) (ps : List Param) (t : AT) (matched : Bool) : Rule → Nat
  | .ruleD _ qs _ e prems =>
    let Γ := quantsΓ qs ++ quantsΓ ps
    (if !matched || patTy S T Γ t e then 0 else 1) +
    (if tyOk S T Γ e then 0 else 1) +
    (prems.filter fun pr => !premTy S T Γ pr).length

/-- The result type `S` records for `f`, or, for a generic definition, the one `T` records. -/
def resOf (S : Sig) (T : TSig) (f : String) : AT :=
  match T.gres.lookup f with
  | some (_, r) => r
  | none => (S.results.lookup f).getD .unk

/-- **The entries of `T` about definition `f` agree with its declaration.** -/
def tsigDefOk (T : TSig) (f : String) (ps : List Param) (t : Typ) : Bool :=
  (T.params.all fun p => p.1 != f || (p.2.1 == typParams ps && p.2.2.length == ps.length &&
    (p.2.2.zip ps).all fun q => match q.1, q.2 with
      | .exp a, .expP _ t' => atEq a (toAT t')
      | .defn dps r, .defP _ dps' t' => atEq r (toAT t') && dps.length == dps'.length &&
          (dps.zip dps').all fun d => match d.1, optAT d.2 with
            | some a, some a' => atEq a a'
            | none, none => true
            | _, _ => false
      | .other, .typP _ => true
      | .other, .gramP _ _ _ => true
      | _, _ => false)) &&
  (T.gres.all fun p => p.1 != f || (p.2.1 == typParams ps && atEq p.2.2 (toAT t)))

/-- **The entries of `T` about relation `x` agree with its declaration.** -/
def tsigRelOk (T : TSig) (x : String) (ps : List Param) (t : Typ) : Bool :=
  T.rels.all fun p => p.1 != x || (typParams ps == [] && p.2.1.length == ps.length &&
    atEq p.2.2 (toAT t) && (p.2.1.zip ps).all fun q => match q.1, q.2 with
      | .exp a, .expP _ t' => atEq a (toAT t')
      | _, _ => false)

/-- The clause-check modes of a definition with type parameters `tps`: for a generic
definition, the type parameters stand for `.unk` (any type argument) and for `.base`
(export-free type arguments). -/
def modes (tps : List String) : List AT := if tps.isEmpty then [.unk] else [.unk, .base]

mutual
/-- **The type entries of `E` agree with one top-level definition**: `NxSites.sigTypOk` on every
type definition named in `names` (the names `E` has entries for). -/
def typItemOk (E : Sig) (names : List String) : Def → Bool
  | .typD x ps insts => !names.contains x || sigTypOk E x ps insts
  | .recD ds => typItemsOk E names ds
  | _ => true

/-- `typItemOk` on a list. -/
def typItemsOk (E : Sig) (names : List String) : List Def → Bool
  | [] => true
  | d :: ds => typItemOk E names d && typItemsOk E names ds
end

mutual
/-- **The failures of the flow check on one top-level definition** (`0` when it passes). -/
def flowItem (S : Sig) (T : TSig) : Def → Nat
  | .decD f ps t clauses =>
    (if tsigDefOk T f ps t && sigDefOk S f ps t then 0 else 1) +
    (if reach 1 f then
      ((modes (typParams ps)).map fun b =>
        (clauses.map (clauseFlow S T (typParams ps) b (paramPTs ps) (resOf S T f))).sum).sum
    else 0)
  | .relD x ps _ t rules =>
    (if tsigRelOk T x ps t then 0 else 1) +
    (if reach 0 x then
      (rules.map (ruleFlow S T ps (toAT t) (matchedRel x))).sum
    else 0)
  | .recD ds => flowItems S T ds
  | _ => 0

/-- `flowItem` on a list. -/
def flowItems (S : Sig) (T : TSig) : List Def → Nat
  | [] => 0
  | d :: ds => flowItem S T d + flowItems S T ds
end

end Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
