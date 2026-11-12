module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs

/-!
# Round 7, REH route 2: which comparisons reachable from `Step` can see a module record

Round 6, pass 1 (`docs/projects/spectec/README.md`, §3) located the places where the
`StripInj` route uses injectivity of `Swap.eraseV`: equality and membership tests
(`Swap.cmpValues_eraseV`, `Swap.memValue_eraseV`), and the two places where pattern matching
compares values (a variable bound twice, and `matchDefault`). Route 2 drops `StripInj`, so it needs
to know that none of these sites compares two values that may both contain a record with an
`EXPORTS` field. That is a typing question, since `cmpE` carries only `boolT` or `numT` as its
operand type. This header states a static IL-typed check for it.

* `AT`: an abstraction of IL types. It keeps type names, their type arguments, iteration and
  tuples, and forgets expression arguments.
* `Sig`: the facts about the script the check uses. These are the type names whose values cannot
  hold an `EXPORTS` record (`good`), aliases, record field types, variant case payloads and
  definition result types. `Sig` is data. `sigItemOk` checks it against one top-level definition
  of the script, so a kernel computation over the script validates every entry.
* `nxAT`: an abstract type is export-free (`good` names with export-free type arguments, base
  types, iterations and tuples of export-free types).
* `tyOf`: a partial type inference for expressions, from the types of the rule's or clause's
  quantifiers. `nxE`: the expression's value is export-free, by its shape or by its inferred
  type.
* `badE`: the number of equality, inequality and membership tests in an evaluated expression
  where neither operand is `nxE`. `patE`: the same for a pattern, counting a variable matched a
  second time and a `matchDefault` form.
* `ruleSites`: for a rule, the number of failing sites that are top-level positive premises
  `if e₁ = e₂` or `if e₁ <- e₂` (*binding sites*), and the number of all other failing sites.
  `clauseBad`: the number of failing sites of a definition clause.

The check is static. It says nothing about values by itself: the link from `nxE` to runtime
values needs the runtime values of quantifiers and definition parameters to have their
declared types, which is a type-preservation property of the evaluator that is **not** proved
here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSites

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Abstract types -/

/-- **An abstraction of IL types**: a type name with its type arguments, the base types,
iterations, tuples, and an unknown type. Expression arguments of a type name are dropped. -/
inductive AT where
  | base
  | name (n : String) (args : List AT)
  | iter (a : AT)
  | tup (xs : List AT)
  | unk
  deriving Repr, Inhabited

mutual
/-- Equality of abstract types, by structural recursion (so that the kernel can evaluate it). -/
def atEq : AT → AT → Bool
  | .base, .base => true
  | .name n xs, .name m ys => n == m && atEqL xs ys
  | .iter a, .iter b => atEq a b
  | .tup xs, .tup ys => atEqL xs ys
  | .unk, .unk => true
  | _, _ => false

/-- `atEq` on lists. -/
def atEqL : List AT → List AT → Bool
  | [], [] => true
  | a :: xs, b :: ys => atEq a b && atEqL xs ys
  | _, _ => false
end

instance : BEq AT := ⟨atEq⟩

mutual
/-- The abstraction of an IL type. -/
def toAT : Typ → AT
  | .varT n args => .name n (toATArgs args)
  | .boolT => .base
  | .numT _ => .base
  | .textT => .base
  | .tupT bs => .tup (toATBinds bs)
  | .iterT t _ => .iter (toAT t)

/-- The type arguments among `args`. -/
def toATArgs : List Arg → List AT
  | [] => []
  | .typA t :: xs => toAT t :: toATArgs xs
  | _ :: xs => toATArgs xs

/-- The component types of a tuple type. -/
def toATBinds : List TypBind → List AT
  | [] => []
  | .mk _ t :: bs => toAT t :: toATBinds bs
end

mutual
/-- **An export-free abstract type**: its values cannot contain a record with an `EXPORTS`
field, provided every name in `good` is export-free. -/
def nxAT (good : List String) : AT → Bool
  | .base => true
  | .name n xs => good.contains n && nxATs good xs
  | .iter a => nxAT good a
  | .tup xs => nxATs good xs
  | .unk => false

/-- `nxAT` on a list. -/
def nxATs (good : List String) : List AT → Bool
  | [] => true
  | a :: xs => nxAT good a && nxATs good xs
end

/-! ## The signature -/

/-- **The facts about the script that the check uses.** Validated against the script by
`sigItemOk`. -/
structure Sig where
  /-- Type names whose values cannot hold an `EXPORTS` record, and type parameters that stand
  for export-free type arguments. -/
  good : List String
  /-- Types every instance of which is an alias of the same type, with the aliased type. -/
  aliases : List (String × AT)
  /-- Fields of record types (the same in every instance): type, atom, field type. -/
  fields : List (String × String × AT)
  /-- Cases of variant types (the same in every instance): type, constructor, payload type. -/
  cases : List (String × String × AT)
  /-- Result types of definitions. -/
  results : List (String × AT)

/-- The field type of record type `n` at atom `a`, if `S` records it. -/
def fieldAT (S : Sig) (n a : String) : AT :=
  match S.fields.find? fun p => p.1 == n && p.2.1 == a with
  | some p => p.2.2
  | none => .unk

/-- The payload type of case `op` of variant type `n`, if `S` records it. -/
def caseAT (S : Sig) (n op : String) : AT :=
  match S.cases.find? fun p => p.1 == n && p.2.1 == op with
  | some p => p.2.2
  | none => .unk

/-- Unfold aliases, at most `k` times. -/
def unalias (S : Sig) : Nat → AT → AT
  | 0, a => a
  | k + 1, .name n xs =>
    match S.aliases.lookup n with
    | some a => unalias S k a
    | none => .name n xs
  | _ + 1, a => a

/-- The element type of an iteration type (after unfolding aliases). -/
def elemAT (S : Sig) (a : AT) : AT :=
  match unalias S 8 a with
  | .iter t => t
  | _ => .unk

/-- The counter variable of a `ListN` iteration, a number. -/
def counterΓ : Iter → List (String × AT)
  | .listN _ (some x) => [(x, .base)]
  | _ => []

/-! ## Type inference and export-freedom of expressions -/

mutual
/-- **A partial type inference for expressions**, from the types `Γ` of the variables in scope;
`.unk` when the type is not determined by the forms it handles. -/
def tyOf (S : Sig) (Γ : List (String × AT)) : Exp → AT
  | .varE x => (Γ.lookup x).getD .unk
  | .boolE _ => .base
  | .numE _ => .base
  | .textE _ => .base
  | .unE _ _ _ => .base
  | .binE _ _ _ _ => .base
  | .cmpE _ _ _ _ => .base
  | .lenE _ => .base
  | .memE _ _ => .base
  | .cvtE _ _ _ => .base
  | .dotE e a =>
    match unalias S 8 (tyOf S Γ e) with
    | .name n _ => fieldAT S n a
    | _ => .unk
  | .idxE e _ => elemAT S (tyOf S Γ e)
  | .theE e => elemAT S (tyOf S Γ e)
  | .sliceE e _ _ => tyOf S Γ e
  | .uncaseE e op =>
    match unalias S 8 (tyOf S Γ e) with
    | .name n _ => caseAT S n op
    | _ => .unk
  | .projE e i =>
    match unalias S 8 (tyOf S Γ e) with
    | .tup xs => if 0 ≤ i then xs.getD i.toNat .unk else .unk
    | _ => .unk
  | .subE _ _ t₂ => toAT t₂
  | .callE f _ => (S.results.lookup f).getD .unk
  | .catE e _ => tyOf S Γ e
  | .iterE e (.mk it ds) => .iter (tyOf S (domsΓ S Γ ds ++ counterΓ it ++ Γ) e)
  | .listE es => tyOfHead S Γ es
  | .optE eo => tyOfOpt S Γ eo
  | _ => .unk

/-- The type of a list literal: the iteration of its first element's type. -/
def tyOfHead (S : Sig) (Γ : List (String × AT)) : List Exp → AT
  | [] => .unk
  | e :: _ => .iter (tyOf S Γ e)

/-- The type of an option literal. -/
def tyOfOpt (S : Sig) (Γ : List (String × AT)) : Option Exp → AT
  | none => .unk
  | some e => .iter (tyOf S Γ e)

/-- The types of the variables an iteration binds: each domain variable has the element type of
its source. -/
def domsΓ (S : Sig) (Γ : List (String × AT)) : List Dom → List (String × AT)
  | [] => []
  | .mk x e :: ds => (x, elemAT S (tyOf S Γ e)) :: domsΓ S Γ ds
end

/-- The scope of an iteration body. -/
def iterΓ (S : Sig) (Γ : List (String × AT)) (it : Iter) (ds : List Dom) :
    List (String × AT) :=
  domsΓ S Γ ds ++ counterΓ it ++ Γ

mutual
/-- **The value of `e` cannot contain an `EXPORTS` record**: by its shape, or by its inferred
type. -/
def nxE (S : Sig) (Γ : List (String × AT)) : Exp → Bool
  | .boolE _ => true
  | .numE _ => true
  | .textE _ => true
  | .unE _ _ _ => true
  | .binE _ _ _ _ => true
  | .cmpE _ _ _ _ => true
  | .lenE _ => true
  | .memE _ _ => true
  | .cvtE _ _ _ => true
  | .caseE _ e => nxE S Γ e
  | .tupE es => nxEs S Γ es
  | .listE es => nxEs S Γ es
  | .optE none => true
  | .optE (some e) => nxE S Γ e
  | .strE fs => nxFs S Γ fs
  | .catE e₁ e₂ => nxE S Γ e₁ && nxE S Γ e₂
  | .liftE e => nxE S Γ e
  | .iterE e (.mk it ds) => nxE S (iterΓ S Γ it ds) e
  | .subE e _ t₂ => nxE S Γ e || nxAT S.good (toAT t₂)
  | e => nxAT S.good (tyOf S Γ e)

/-- `nxE` on a list. -/
def nxEs (S : Sig) (Γ : List (String × AT)) : List Exp → Bool
  | [] => true
  | e :: es => nxE S Γ e && nxEs S Γ es

/-- `nxE` on record fields, none named `EXPORTS`. -/
def nxFs (S : Sig) (Γ : List (String × AT)) : List ExpField → Bool
  | [] => true
  | .mk a e :: fs => a != "EXPORTS" && nxE S Γ e && nxFs S Γ fs
end

/-- **A comparison site passes**: one of its operands is export-free, so erasing exports neither
creates nor removes an equality. -/
def siteOk (S : Sig) (Γ : List (String × AT)) (e₁ e₂ : Exp) : Bool :=
  nxE S Γ e₁ || nxE S Γ e₂

/-- `1` for a failing equality, inequality or membership test at the root of `e`, else `0`. -/
def rootBad (S : Sig) (Γ : List (String × AT)) : Exp → Nat
  | .cmpE .eqOp _ e₁ e₂ => if siteOk S Γ e₁ e₂ then 0 else 1
  | .cmpE .neOp _ e₁ e₂ => if siteOk S Γ e₁ e₂ then 0 else 1
  | .memE e₁ e₂ => if siteOk S Γ e₁ e₂ then 0 else 1
  | _ => 0

/-! ## Failing sites of evaluated expressions -/

mutual
/-- **The failing comparison sites of an evaluated expression.** -/
def badE (S : Sig) (Γ : List (String × AT)) : Exp → Nat
  | .unE _ _ e => badE S Γ e
  | .binE _ _ e₁ e₂ => badE S Γ e₁ + badE S Γ e₂
  | .cmpE op t e₁ e₂ => rootBad S Γ (.cmpE op t e₁ e₂) + badE S Γ e₁ + badE S Γ e₂
  | .tupE es => badEs S Γ es
  | .projE e _ => badE S Γ e
  | .caseE _ e => badE S Γ e
  | .uncaseE e _ => badE S Γ e
  | .optE eo => badO S Γ eo
  | .theE e => badE S Γ e
  | .strE fs => badFs S Γ fs
  | .dotE e _ => badE S Γ e
  | .compE e₁ e₂ => badE S Γ e₁ + badE S Γ e₂
  | .listE es => badEs S Γ es
  | .liftE e => badE S Γ e
  | .memE e₁ e₂ => rootBad S Γ (.memE e₁ e₂) + badE S Γ e₁ + badE S Γ e₂
  | .lenE e => badE S Γ e
  | .catE e₁ e₂ => badE S Γ e₁ + badE S Γ e₂
  | .idxE e₁ e₂ => badE S Γ e₁ + badE S Γ e₂
  | .sliceE e₁ e₂ e₃ => badE S Γ e₁ + badE S Γ e₂ + badE S Γ e₃
  | .updE e₁ p e₂ => badE S Γ e₁ + badP S Γ p + badE S Γ e₂
  | .extE e₁ p e₂ => badE S Γ e₁ + badP S Γ p + badE S Γ e₂
  | .callE _ args => badAs S Γ args
  | .iterE e (.mk it ds) => badE S (iterΓ S Γ it ds) e + badI S Γ it + badDs S Γ ds
  | .cvtE e _ _ => badE S Γ e
  | .subE e _ _ => badE S Γ e
  | _ => 0

/-- `badE` on a list. -/
def badEs (S : Sig) (Γ : List (String × AT)) : List Exp → Nat
  | [] => 0
  | e :: es => badE S Γ e + badEs S Γ es

/-- `badE` on an option. -/
def badO (S : Sig) (Γ : List (String × AT)) : Option Exp → Nat
  | none => 0
  | some e => badE S Γ e

/-- `badE` on record fields. -/
def badFs (S : Sig) (Γ : List (String × AT)) : List ExpField → Nat
  | [] => 0
  | .mk _ e :: fs => badE S Γ e + badFs S Γ fs

/-- `badE` on the indices and bounds of a path. -/
def badP (S : Sig) (Γ : List (String × AT)) : Path → Nat
  | .rootP => 0
  | .idxP p e => badP S Γ p + badE S Γ e
  | .sliceP p e₁ e₂ => badP S Γ p + badE S Γ e₁ + badE S Γ e₂
  | .dotP p _ => badP S Γ p

/-- `badE` on the bound of a `ListN` iteration. -/
def badI (S : Sig) (Γ : List (String × AT)) : Iter → Nat
  | .listN e _ => badE S Γ e
  | _ => 0

/-- `badE` on iteration domains. -/
def badDs (S : Sig) (Γ : List (String × AT)) : List Dom → Nat
  | [] => 0
  | .mk _ e :: ds => badE S Γ e + badDs S Γ ds

/-- `badE` on arguments. -/
def badAs (S : Sig) (Γ : List (String × AT)) : List Arg → Nat
  | [] => 0
  | .expA e :: xs => badE S Γ e + badAs S Γ xs
  | _ :: xs => badAs S Γ xs
end

/-- **The failing sites of a premise.** -/
def badPr (S : Sig) (Γ : List (String × AT)) : Prem → Nat
  | .rulePr _ args _ e => badAs S Γ args + badE S Γ e
  | .ifPr e => badE S Γ e
  | .letPr e₁ e₂ => badE S Γ e₁ + badE S Γ e₂ + 1
  | .elsePr => 0
  | .iterPr pr (.mk it ds) => badPr S (iterΓ S Γ it ds) pr + badI S Γ it + badDs S Γ ds

/-! ## Failing sites of patterns -/

mutual
/-- **The failing sites of a pattern**, threading the variables bound so far. `vnx` says that
the matched value is known to be export-free (it is a number, or a part of an export-free
value), in which case no comparison made while matching can fail. A failing site is a variable
already bound whose type is not export-free, and a `matchDefault` form that is not `nxE`. The
evaluated parts of a `matchDefault` form are counted by `badE`. -/
def patE (S : Sig) (Γ : List (String × AT)) (vnx : Bool) (bd : List String) :
    Exp → List String × Nat
  | .varE x =>
    if bd.contains x then
      (bd, if vnx || nxAT S.good ((Γ.lookup x).getD .unk) then 0 else 1)
    else (x :: bd, 0)
  | .boolE _ => (bd, 0)
  | .numE _ => (bd, 0)
  | .textE _ => (bd, 0)
  | .optE none => (bd, 0)
  | .unE _ _ e => patE S Γ true bd e
  | .cvtE e _ _ => patE S Γ true bd e
  | .tupE es => patEs S Γ vnx bd es
  | .listE es => patEs S Γ vnx bd es
  | .projE e i =>
    if i = 0 then patE S Γ vnx bd e
    else (bd, (if vnx || nxE S Γ (.projE e i) then 0 else 1) + badE S Γ e)
  | .caseE _ e => patE S Γ vnx bd e
  | .uncaseE e _ => patE S Γ vnx bd e
  | .optE (some e) => patE S Γ vnx bd e
  | .strE fs => patFs S Γ vnx bd fs
  | .catE e₁ e₂ =>
    let r₁ := patE S Γ vnx bd e₁
    let r₂ := patE S Γ vnx r₁.1 e₂
    (r₂.1, r₁.2 + r₂.2)
  | .subE e _ _ => patE S Γ vnx bd e
  | .iterE e (.mk it ds) =>
    let rn := patI S Γ bd it
    let rb := patE S (iterΓ S Γ it ds) vnx rn.1 e
    let rd := patDs S Γ vnx rn.1 ds
    (rd.1, rn.2 + rb.2 + rd.2)
  | e => (bd, (if vnx || nxE S Γ e then 0 else 1) + badE S Γ e)

/-- `patE` on a list, left to right. -/
def patEs (S : Sig) (Γ : List (String × AT)) (vnx : Bool) (bd : List String) :
    List Exp → List String × Nat
  | [] => (bd, 0)
  | e :: es =>
    let r₁ := patE S Γ vnx bd e
    let r₂ := patEs S Γ vnx r₁.1 es
    (r₂.1, r₁.2 + r₂.2)

/-- `patE` on record fields. -/
def patFs (S : Sig) (Γ : List (String × AT)) (vnx : Bool) (bd : List String) :
    List ExpField → List String × Nat
  | [] => (bd, 0)
  | .mk _ e :: fs =>
    let r₁ := patE S Γ vnx bd e
    let r₂ := patFs S Γ vnx r₁.1 fs
    (r₂.1, r₁.2 + r₂.2)

/-- The bound of a `ListN` pattern iteration is matched against a number. -/
def patI (S : Sig) (Γ : List (String × AT)) (bd : List String) : Iter → List String × Nat
  | .listN e _ => patE S Γ true bd e
  | _ => (bd, 0)

/-- The sources of the domains of a pattern iteration are matched against the collected
columns. -/
def patDs (S : Sig) (Γ : List (String × AT)) (vnx : Bool) (bd : List String) :
    List Dom → List String × Nat
  | [] => (bd, 0)
  | .mk _ e :: ds =>
    let r₁ := patE S Γ vnx bd e
    let r₂ := patDs S Γ vnx r₁.1 ds
    (r₂.1, r₁.2 + r₂.2)
end

/-- `patE` on argument patterns; type, definition and grammar arguments compare nothing here. -/
def patAs (S : Sig) (Γ : List (String × AT)) (bd : List String) :
    List Arg → List String × Nat
  | [] => (bd, 0)
  | .expA e :: xs =>
    let r₁ := patE S Γ false bd e
    let r₂ := patAs S Γ r₁.1 xs
    (r₂.1, r₁.2 + r₂.2)
  | _ :: xs => patAs S Γ bd xs

/-! ## Rules and clauses -/

/-- The declared types of the expression quantifiers or parameters. -/
def quantsΓ : List Param → List (String × AT)
  | [] => []
  | .expP x t :: ps => (x, toAT t) :: quantsΓ ps
  | _ :: ps => quantsΓ ps

/-- **A binding site**: a top-level positive premise `if e₁ = e₂` or `if e₁ <- e₂` that fails
`siteOk`, while its operands have no failing site. -/
def bindSite (S : Sig) (Γ : List (String × AT)) : Prem → Bool
  | .ifPr (.cmpE .eqOp _ e₁ e₂) => !siteOk S Γ e₁ e₂ && badE S Γ e₁ + badE S Γ e₂ == 0
  | .ifPr (.memE e₁ e₂) => !siteOk S Γ e₁ e₂ && badE S Γ e₁ + badE S Γ e₂ == 0
  | _ => false

/-- **The failing sites of a rule**: the number of binding sites, and the number of all other
failing sites (in the conclusion, read as an expression and, when `matched`, as a pattern, and in
the premises). -/
def ruleSites (S : Sig) (ps : List Param) (matched : Bool) : Rule → Nat × Nat
  | .ruleD _ qs _ e prems =>
    let Γ := quantsΓ qs ++ quantsΓ ps
    let nb := (prems.filter (bindSite S Γ)).length
    let other := (prems.filter fun pr => !bindSite S Γ pr).foldl
      (fun k pr => k + badPr S Γ pr) 0
    (nb, badE S Γ e + (if matched then (patE S Γ false [] e).2 else 0) + other)

/-- **The failing sites of a definition clause**: its argument patterns, body and premises. -/
def clauseBad (S : Sig) : Clause → Nat
  | .defD qs args e prems =>
    let Γ := quantsΓ qs
    (patAs S Γ [] args).2 + badE S Γ e + prems.foldl (fun k pr => k + badPr S Γ pr) 0

/-! ## Validating the signature -/

/-- The type of field `a` of a record type, if it has one (the first such field). -/
def fieldOf (a : String) : List TypField → Option Typ
  | [] => none
  | .mk a' t _ _ :: fs => if a' == a then some t else fieldOf a fs

/-- The payload type of case `op` of a variant type (the first such case). -/
def caseOf (op : String) : List TypCase → Option Typ
  | [] => none
  | .mk op' t _ _ :: cs => if op' == op then some t else caseOf op cs

mutual
/-- **A type mentions only names in `ok`**, in its type arguments too. -/
def goodTyp (ok : List String) : Typ → Bool
  | .varT n args => ok.contains n && goodArgs ok args
  | .boolT => true
  | .numT _ => true
  | .textT => true
  | .tupT bs => goodBinds ok bs
  | .iterT t _ => goodTyp ok t

/-- `goodTyp` on the type arguments of a type name. -/
def goodArgs (ok : List String) : List Arg → Bool
  | [] => true
  | .typA t :: xs => goodTyp ok t && goodArgs ok xs
  | _ :: xs => goodArgs ok xs

/-- `goodTyp` on tuple components. -/
def goodBinds (ok : List String) : List TypBind → Bool
  | [] => true
  | .mk _ t :: bs => goodTyp ok t && goodBinds ok bs
end

/-- The type parameters of a parameter list. -/
def typParams : List Param → List String
  | [] => []
  | .typP x :: ps => x :: typParams ps
  | _ :: ps => typParams ps

/-- **A type body without `EXPORTS` records**: no field is named `EXPORTS`, and every type it
mentions is in `ok`. -/
def goodDT (ok : List String) : DefTyp → Bool
  | .aliasT t => goodTyp ok t
  | .structT fs => fs.all fun f => match f with | .mk a t _ _ => a != "EXPORTS" && goodTyp ok t
  | .variantT cs => cs.all fun c => match c with | .mk _ t _ _ => goodTyp ok t

/-- The body of an instance. -/
def instDT : Inst → DefTyp
  | .instD _ _ dt => dt

mutual
/-- The names an abstract type mentions. -/
def atNames : AT → List String
  | .base => []
  | .name n xs => n :: atNamesL xs
  | .iter a => atNames a
  | .tup xs => atNamesL xs
  | .unk => []

/-- `atNames` on a list. -/
def atNamesL : List AT → List String
  | [] => []
  | a :: xs => atNames a ++ atNamesL xs
end

/-- `a` mentions none of the type parameters `ps`, so it means the same at every instance. -/
def closedAT (ps : List Param) (a : AT) : Bool :=
  (atNames a).all fun n => !(typParams ps).contains n

/-- **The entries of `S` about type `x` agree with its definition**: every instance has the
recorded alias, field or case, and the recorded type mentions no type parameter. If `x` is
`good`, its instances mention only `good` names and have no `EXPORTS` field. A type parameter
(such as `X`) may itself be in `good`: inside an instance it is bound to an export-free type
argument, and it names no type of the script. -/
def sigTypOk (S : Sig) (x : String) (ps : List Param) (insts : List Inst) : Bool :=
  (S.aliases.all fun p => p.1 != x || (closedAT ps p.2 && !insts.isEmpty &&
    insts.all fun i => match instDT i with
      | .aliasT t => toAT t == p.2
      | _ => false)) &&
  (S.fields.all fun p => p.1 != x || (closedAT ps p.2.2 && !insts.isEmpty &&
    insts.all fun i => match instDT i with
      | .structT fs => (fieldOf p.2.1 fs).map toAT == some p.2.2
      | _ => false)) &&
  (S.cases.all fun p => p.1 != x || (closedAT ps p.2.2 && !insts.isEmpty &&
    insts.all fun i => match instDT i with
      | .variantT cs => (caseOf p.2.1 cs).map toAT == some p.2.2
      | _ => false)) &&
  (!S.good.contains x || insts.all fun i => goodDT S.good (instDT i))

/-- **The result-type entries of `S` about definition `f` agree with its declaration**, and
mention none of its type parameters. -/
def sigDefOk (S : Sig) (f : String) (ps : List Param) (t : Typ) : Bool :=
  S.results.all fun p => p.1 != f || (toAT t == p.2 && closedAT ps p.2)

/-- **The failing sites of a type instance's premises** (record field and variant case
premises, which the typing relation `Sem.HasTyp` evaluates). -/
def instBad (S : Sig) (ps : List Param) : Inst → Nat
  | .instD iqs _ dt =>
    let Γ := quantsΓ iqs ++ quantsΓ ps
    match dt with
    | .aliasT _ => 0
    | .structT fs => fs.foldl (fun k f => match f with
      | .mk _ _ qs prems => k + prems.foldl (fun k' pr => k' + badPr S (quantsΓ qs ++ Γ) pr) 0) 0
    | .variantT cs => cs.foldl (fun k c => match c with
      | .mk _ _ qs prems => k + prems.foldl (fun k' pr => k' + badPr S (quantsΓ qs ++ Γ) pr) 0) 0

/-- The relations whose rules are matched by `Sem.derives` as well as read declaratively: every
reachable relation except `Step`, `Step_pure` and `Step_read`, which are reached only through
`Round6.Reading.DDerivesB`. -/
def matchedRel (x : String) : Bool :=
  !(x == "Step" || x == "Step_pure" || x == "Step_read")

/-- A reachable name. -/
def reach (k : Nat) (x : String) : Bool := Script.stepReach.contains (k, x)

mutual
/-- **One top-level definition passes**: the signature agrees with it, and, if it is reachable
from `Step`, it has no failing site outside the binding sites of rules. -/
def itemOk (S : Sig) : Def → Bool
  | .typD x ps insts =>
    sigTypOk S x ps insts && (!reach 2 x || insts.all fun i => instBad S ps i == 0)
  | .decD f ps t clauses =>
    sigDefOk S f ps t && (!reach 1 f || clauses.all fun c => clauseBad S c == 0)
  | .relD x ps _ _ rules =>
    !reach 0 x || rules.all fun r => (ruleSites S ps (matchedRel x) r).2 == 0
  | .gramD _ _ _ _ => true
  | .recD ds => itemsOk S ds

/-- `itemOk` on a list. -/
def itemsOk (S : Sig) : List Def → Bool
  | [] => true
  | d :: ds => itemOk S d && itemsOk S ds
end

mutual
/-- **The binding sites of the reachable rules of one top-level definition**: relation, rule
name and number of binding sites, for every rule that has one. -/
def bindSites (S : Sig) : Def → List (String × String × Nat)
  | .relD x ps _ _ rules =>
    if reach 0 x then
      rules.filterMap fun r => match r with
        | .ruleD nm _ _ _ _ =>
          let k := (ruleSites S ps (matchedRel x) r).1
          if k == 0 then none else some (x, nm, k)
    else []
  | .recD ds => bindSitesL S ds
  | _ => []

/-- `bindSites` on a list. -/
def bindSitesL (S : Sig) : List Def → List (String × String × Nat)
  | [] => []
  | d :: ds => bindSites S d ++ bindSitesL S ds
end

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
