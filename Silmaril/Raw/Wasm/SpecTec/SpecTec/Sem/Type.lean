module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval

/-!
# The IL's types as subsets of the value domain

Step 4 of `docs/projects/spectec/README.md`: a type denotes a set of
`Silmaril.SpecTec.Sem.Value`s, and `hasTyp` is the fuel-indexed decision
procedure for membership.  Everything is relative to the pin
`608711107b7f1edb13efd57b7d79b49477462d36`.

## What this is a transcription of

SpecTec has no "value inhabits type" judgment: `spectec/src/il/valid.ml` is a
bidirectional checker on *expressions* and `spectec/src/il/eval.ml` reduces
expressions to normal forms.  The judgment below is the value-level reading of
the two together — it is what `valid.ml`'s `valid_exp` says about an
expression whose value is already known — and each clause cites the OCaml it
follows:

| clause | OCaml |
| --- | --- |
| `boolT`, `numT`, `textT` | `infer_exp` (`valid.ml:299-301`) |
| `numT` subsumption | `Xl.Num.sub` (`xl/num.ml:52-57`) |
| `tupT` | `valid_exp` for `TupE` (`valid.ml:451-464`) |
| `tupT`'s binders | `proj_tup_typ` (`valid.ml:102-110`), `valid_typ_bind` (`valid.ml:243-245`) |
| `iterT _ Opt` | `OptE` (`valid.ml:488-490`) |
| `iterT _ List`/`List1` | `ListE` (`valid.ml:493-495`), `as_list_typ` (`valid.ml:73-76`) |
| `iterT _ (ListN e _)` | `reduce_exp` for `IterE` (`eval.ml:401-417`) |
| `varT` resolution | `reduce_typ`/`reduce_typdef`/`reduce_typ_app` (`eval.ml:107-149`) |
| `aliasT` transparent | `eval.ml:116-117` |
| `structT` | `StrE` (`valid.ml:426-428`), `valid_expfield` (`valid.ml:533-542`) |
| `variantT` | `CaseE` (`valid.ml:508-512`), `find_case` (`valid.ml:28-31`) |
| field/case premises | `valid_typfield`/`valid_typcase` (`valid.ml:265-287`) |

## Why `Res Bool` and not `Bool`

`hasTyp` returns `Res Bool` — the same three-valued result `Sem/Eval.lean`
uses — rather than a plain `Bool`, for exactly the reason that file gives for
not using `Option`.  Resolving `varT x args` runs `reduce_typ_app`
(`eval.ml:133-149`), which tries the type family's instances **in order** and
takes the first whose argument patterns match (`eval.ml:142-144`), falling
through to the next instance only on a *definite* mismatch.  "This instance
definitely does not apply" is a negative condition, so with a two-valued
answer an instance whose match merely starved would be skipped, a later one
would fire, and more fuel could change the answer: monotonicity in fuel would
be false.  With three outcomes, `Res.elimUndef` propagates `outOfFuel` instead
of falling through, which is `eval.ml:145-146`'s
`if not !assume_coherent_matches then Ok None` — the same branch
`Sem/Eval.lean` takes.

So the four outcomes read:

* `.ok true` — `v` inhabits the type;
* `.ok false` — `v` definitely does not;
* `.error .undef` — the question is not well posed at this type (an
  undeclared type name, `eval.ml:139`; no instance of a type family applies,
  `eval.ml:140`; a type-level expression has no value);
* `.error .outOfFuel` — undecided at this budget.

`HasTyp env ρ t v` is `∃ n, hasTyp n env ρ t v = .ok true`, which is sensible
because of `hasTyp_ok_of_le`.

## Deviations from the OCaml

* **Numeric subsumption is kept.**  `Xl.Num.sub` (`num.ml:52-57`) makes
  `nat <: int <: rat <: real`, and `valid.ml` applies it through
  `infer_binop`/`infer_cmpop`, but the `NumT` clause of `Eval.sub_typ` is
  *commented out* at `eval.ml:1265`.  We follow `num.ml:52` and let a
  `Num.natN` inhabit `NumT IntT`: that is the reading under which `Sem.Value`'s
  `Num.bin`, `Num.cmp` and `Num.cvt` (transcribed from `num.ml:134,277,79`)
  are type-correct.  Making `numT` exact instead would only shrink the
  denotation.
* **Types are compared, not unified.**  Resolving a `varT` whose head is a
  *local* type variable uses `VarEnv.typs` directly, exactly as
  `Sem/Eval.lean`'s `resolveTyp` does, rather than transcribing
  `Il.Subst.subst_typ`; `Sem/Eval.lean` already explains why a value
  semantics carries an environment instead of substituting.
* **Instance arguments are matched by `Sem/Eval.lean`'s `matchArgs`.**
  `eval.ml:142` matches the *actual* arguments against the instance's
  patterns with the same `match_arg` that `reduce_exp_call` uses
  (`eval.ml:654`), so the Lean side reuses `matchArgs`, which takes the
  pattern first and an already-evaluated `ArgV` second.  Its deviations
  (`DefA` binding direction, structural comparison in `matchTypV`) are
  inherited; see `Sem/Eval.lean`.
* **A field's or case's premises are checked, and bind nothing outwards.**
  `valid_typfield` and `valid_typcase` (`valid.ml:265-287`) validate the
  premises in the scope `valid_typ_bind` builds from the carried type's tuple
  binders; `caseScope` builds that scope and `premsOk` runs
  `Sem/Eval.lean`'s `premsHold` in it, discarding the resulting bindings.  A
  premise that is a `RulePr` whose instance is not derivable at the current
  budget makes `premsOk` report `outOfFuel`, never `false`, because `derives`
  is a step-indexed least fixpoint.
* **No structural subtyping.**  `Eval.sub_typ` (`eval.ml:1253-1288`) relates
  two *types*; `hasTyp` relates a value to one type.  Where `sub_typ` would be
  needed — `SubE` — `Sem/Eval.lean` already evaluates `SubE e _ _` to the
  denotation of `e`, so the value side sees no coercion.  `sub_typ`'s width
  rules on records and variants are therefore not transcribed here, and the
  corresponding statement about denotations (`sub_typ t₁ t₂` implies
  `HasTyp … t₁ v → HasTyp … t₂ v`) is **open**.  It is not in
  `Sem/Valid.lean` either: that file transcribes the half of `valid.ml` that
  needs no type, and its own "What is deliberately left out" says that
  `equiv_typ`/`sub_typ` and the `as_*_typ` accessors are exactly what it
  omits.  Stating it needs `Eval.sub_typ` transcribed first, which nothing in
  this tree does yet; see the closing section of this file.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod
open Res

/-! ## Fuel-free auxiliaries -/

/-- Bind a dependent tuple type's binders to the components of a tuple value,
left to right (`valid_typ_bind`, `spectec/src/il/valid.ml:243-245`, which
extends the environment with `x₁ : t₁` before checking the rest).

On the value side the binder stands for the component itself, which is the
value-level reading of `proj_tup_typ`'s `Subst.add_varid s xI eI` with
`eI = ProjE (e, i)` (`valid.ml:102-110`).  A length mismatch simply stops
binding; `hasTypTup` has already rejected it. -/
def typBinds : VarEnv → List TypBind → List Value → VarEnv
  | ρ, .mk x _ :: bs, v :: vs => typBinds (ρ.bindVal x v) bs vs
  | ρ, _, _ => ρ

/-- The scope in which a record field's or a variant case's premises are
checked (`valid_typfield`, `valid_typcase`,
`spectec/src/il/valid.ml:265-287`): `valid_typ_bind env t` binds the carried
type's tuple binders, and nothing else.

`valid.ml:276-280` reads a case's arity off the same shape — `TupT ts` has
arity `List.length ts`, anything else arity 1 — so a non-tuple carried type
contributes no binder. -/
def caseScope : VarEnv → Typ → Value → VarEnv
  | ρ, .tupT bs, .tuple vs => typBinds ρ bs vs
  | ρ, _, _ => ρ

/-- A `VarT (x, [])` whose head is a *local* type variable, resolved through
the scope.

This is `Sem/Eval.lean`'s `resolveTyp` as a lookup: `eval.ml:113-115` calls
`Env.find_opt_typ`, having already substituted type parameters away, and
`reduce_typ_app` returns `Ok None` for a name that is a type parameter
(`eval.ml:139`).  Carrying the binding in `VarEnv.typs` is how this file
avoids transcribing `Il.Subst.subst_typ`; a *applied* `VarT (x, _ :: _)` is
never a type parameter, so only the empty-argument case consults the
scope. -/
def localTyp? (ρ : VarEnv) (x : IL.Id) : List Arg → Option Typ
  | [] => ρ.findTyp? x
  | _ :: _ => none

/-- Do a field's or case's premises hold?  `Sem/Eval.lean`'s `premsHold`
(`reduce_prems`, `eval.ml:672-684`) with the outward bindings discarded and a
definite failure turned into `false`.

`outOfFuel` is *not* turned into `false`: a premise that cannot be decided
leaves the whole membership question undecided, which is what keeps `hasTyp`
monotone in its fuel. -/
def premsOk (n : Nat) (env : Env) (ρ : VarEnv) (prems : List Prem) : Res Bool :=
  Res.elimUndef (premsHold n env ρ prems) (fun _ => .ok true) (fun _ => .ok false)

/-! ## Case quantifiers bound by a defining equation

(Silmaril change, see `docs/projects/spectec/README.md`.)  A variant case may quantify variables that its carried type
does not bind and that its premises only *define*: `fNmag`'s
`SUBNORM m -- if m < 2^M /\ 2 - 2^(E-1) = exp` quantifies `exp : exp`, and
`ishape`'s `% shape -- if $lanetype(shape) = Jnn` quantifies `Jnn : Jnn`.  The
case holds when *some* well-typed value of the quantifier satisfies the
premises.  Evaluating the premises with the quantifier unbound, as the
original transcription did, makes them undefined and the case uninhabited
(every subnormal float, `+0.0` included, and every integer shape).

The value is read off a defining conjunct `e = x` (or `x = e`, either side
possibly under `SubE`), exactly as SpecTec's animation turns such an `if` into
a binding: `e` is evaluated, checked against the quantifier's type and bound to
`x`, and the premises are then checked in the extended scope.  A quantifier
with no defining conjunct stays unbound, as before. -/

/-- Strip `SubE` coercions. -/
def stripSubE : Exp → Exp
  | .subE e _ _ => stripSubE e
  | e => e

/-- The quantifier `x` names, with its type, if any. -/
def quantOf (qs : List Param) : Exp → Option (IL.Id × Typ)
  | .varE x => qs.findSome? fun
      | .expP y t => if y = x then some (y, t) else none
      | _ => none
  | _ => none

/-- The defining conjuncts `e = x` of an `if` premise, for quantifiers `x`. -/
def quantEqs (qs : List Param) : Exp → List (IL.Id × Typ × Exp)
  | .binE .andOp _ a b => quantEqs qs a ++ quantEqs qs b
  | .cmpE .eqOp _ a b =>
      match quantOf qs (stripSubE b) with
      | some (x, t) => [(x, t, a)]
      | none =>
          match quantOf qs (stripSubE a) with
          | some (x, t) => [(x, t, b)]
          | none => []
  | _ => []

/-- The defining conjuncts of a case's premises. -/
def quantDefs (qs : List Param) (prems : List Prem) : List (IL.Id × Typ × Exp) :=
  prems.flatMap fun
    | .ifPr e => quantEqs qs e
    | _ => []

theorem quantOf_nil (e : Exp) : quantOf [] e = none := by
  cases e <;> simp [quantOf]

theorem quantEqs_nil (e : Exp) : quantEqs [] e = [] := by
  fun_induction quantEqs [] e <;> simp_all [quantOf_nil]

/-- A case with no quantifiers has no defining conjuncts. -/
@[simp] theorem quantDefs_nil (prems : List Prem) : quantDefs [] prems = [] := by
  induction prems with
  | nil => rfl
  | cons p ps ih =>
      cases p <;> simp_all [quantDefs, quantEqs_nil]

/-- Bind the defined quantifiers one by one: evaluate the definition, check it
against the quantifier's type, bind it.  `none` is a definite failure of the
type check. -/
def bindQuants (ev : VarEnv → Exp → Res Value) (ty : VarEnv → Typ → Value → Res Bool) :
    VarEnv → List (IL.Id × Typ × Exp) → Res (Option VarEnv)
  | ρ, [] => .ok (some ρ)
  | ρ, (x, t, e) :: ds => do
      let v ← ev ρ e
      let b ← ty ρ t v
      if b then bindQuants ev ty (ρ.bindVal x v) ds else .ok none

/-! ## The membership test

One mutual block of seven fuel-indexed functions, with every recursive call at
`n` when the caller is at `n + 1`, exactly as in `Sem/Eval.lean`. -/

mutual

/-- Does `v` inhabit `t`?  The denotation of a type as a subset of `Value`.

* `BoolT`, `NumT` and `TextT` are the three leaves `infer_exp` assigns to the
  literals (`spectec/src/il/valid.ml:299-301`).  `NumT` admits every numeral
  whose own type is below `t` in `Xl.Num.sub` (`xl/num.ml:52-57`), so a
  `Num.natN` inhabits `NumT IntT`; see the module docstring for why this
  file keeps a subsumption that `eval.ml:1265` comments out.
* `TupT` wants a `Value.tuple` of the same length whose components inhabit
  the component types, *dependently*: the `i`-th component type is read in a
  scope where the earlier binders stand for the earlier components
  (`valid.ml:451-464`, `proj_tup_typ`, `valid.ml:102-110`).  This is the
  clause that makes types depend on the evaluator.
* `IterT (t, Opt)` is `Value.opt` (`valid.ml:488-490`); `IterT (t, List)` and
  `IterT (t, List1)` are `Value.list`, the latter non-empty
  (`valid.ml:493-495`, `as_list_typ`, `valid.ml:73-76`); and
  `IterT (t, ListN (e, _))` additionally fixes the length to the value of `e`
  (`eval.ml:401-417`, where `eval.ml:405` requires every domain to have
  exactly that length).  `valid.ml:248` rejects a `ListN` *in a type*
  outright; it is accepted here because `Sem/Eval.lean` can evaluate the
  bound, and the clause is what `IterE`'s own `ListN` iteration produces.
* `VarT (x, args)` resolves the declaration and unfolds it; see
  `hasTypInsts` and `hasTypDef`. -/
def hasTyp : Nat → Env → VarEnv → Typ → Value → Res Bool
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, .boolT, v => .ok v.asBool?.isSome
  | _+1, _, _, .numT t, v =>
      .ok (match v.asNum? with | some m => Num.subTyp (Num.toTyp m) t | none => false)
  | _+1, _, _, .textT, v => .ok v.asText?.isSome
  | n+1, env, ρ, .tupT bs, v =>
      match v.asTuple? with
      | some vs => hasTypTup n env ρ bs vs
      | none => .ok false
  | n+1, env, ρ, .iterT t .opt, v =>
      match v.asOpt? with
      | some none => .ok true
      | some (some w) => hasTyp n env ρ t w
      | none => .ok false
  | n+1, env, ρ, .iterT t .list, v =>
      match v.asList? with
      | some vs => hasTypList n env ρ t vs
      | none => .ok false
  | n+1, env, ρ, .iterT t .list1, v =>
      match v.asList? with
      | some vs => if vs.isEmpty then .ok false else hasTypList n env ρ t vs
      | none => .ok false
  | n+1, env, ρ, .iterT t (.listN e _), v =>
      match v.asList? with
      | some vs => do
          let kv ← evalExp n env ρ e
          let k ← Res.ofOption kv.asNat?
          if vs.length = k then hasTypList n env ρ t vs else .ok false
      | none => .ok false
  | n+1, env, ρ, .varT x args, v =>
      match localTyp? ρ x args with
      | some t => hasTyp n env ρ t v
      | none => do
          let td ← Res.ofOption (env.findTyp? x)
          let ws ← evalArgs n env ρ args
          hasTypInsts n env td.2 ws v
termination_by n => n

/-- A dependent tuple type against a list of components
(`valid.ml:451-464`): each component is checked in the scope the earlier
binders built, and a length mismatch is a definite `false`
(`valid.ml:460-463`, the arity error). -/
def hasTypTup : Nat → Env → VarEnv → List TypBind → List Value → Res Bool
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, [], [] => .ok true
  | _+1, _, _, [], _ :: _ => .ok false
  | _+1, _, _, _ :: _, [] => .ok false
  | n+1, env, ρ, .mk x t :: bs, v :: vs => do
      let b ← hasTyp n env ρ t v
      if b then hasTypTup n env (ρ.bindVal x v) bs vs else .ok false
termination_by n => n

/-- Every element of a list inhabits the element type
(`ListE`, `valid.ml:493-495`). -/
def hasTypList : Nat → Env → VarEnv → Typ → List Value → Res Bool
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, _, [] => .ok true
  | n+1, env, ρ, t, v :: vs => do
      let b ← hasTyp n env ρ t v
      if b then hasTypList n env ρ t vs else .ok false
termination_by n => n

/-- Unfold a resolved type definition against a value
(`reduce_typdef`, `eval.ml:122-131`).

`AliasT` is transparent (`eval.ml:116-117` keeps reducing through it),
`StructT` wants a `Value.struct` with exactly those fields and `VariantT` a
`Value.case` whose operator is one of the declared cases. -/
def hasTypDef : Nat → Env → VarEnv → DefTyp → Value → Res Bool
  | 0, _, _, _, _ => .error .outOfFuel
  | n+1, env, ρ, .aliasT t, v => hasTyp n env ρ t v
  | n+1, env, ρ, .structT fs, v =>
      match v.asStruct? with
      | some gs => hasTypFields n env ρ fs gs
      | none => .ok false
  | n+1, env, ρ, .variantT cs, v =>
      match v.asCase? with
      | some (op, w) => hasTypCase n env ρ cs op w
      | none => .ok false
termination_by n => n

/-- A record value against a `StructT`'s fields.

`valid.ml:426-428` checks a `StrE` with `valid_list (valid_expfield …)`,
which demands the *same number of fields in the same order* and pairwise atom
equality (`valid.ml:533-542`, `"unexpected record field"`); `Value.struct`
keeps the fields in order, so the test is positional.  Each field's premises
are then checked in the scope its carried type binds
(`valid_typfield`, `valid.ml:265-269`). -/
def hasTypFields : Nat → Env → VarEnv → List TypField → List (AtomS × Value) → Res Bool
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, [], [] => .ok true
  | _+1, _, _, [], _ :: _ => .ok false
  | _+1, _, _, _ :: _, [] => .ok false
  | n+1, env, ρ, .mk a t _ prems :: fs, (a', w) :: gs =>
      if a = a' then
        (do
          let b ← hasTyp n env ρ t w
          if b then
            (do
              let hp ← premsOk n env (caseScope ρ t w) prems
              if hp then hasTypFields n env ρ fs gs else .ok false)
          else .ok false)
      else .ok false
termination_by n => n

/-- A `Value.case op w` against a `VariantT`'s cases.

`find_case` (`valid.ml:28-31`) looks the operator up and errors if it is
absent; `check_mixops` (`valid.ml:262`) has already made the operators
pairwise distinct, so the first match is the only one.  An operator that is
not declared is a definite `false` — the value is not of this type — rather
than `undef`.  The carried value is checked against the case's type and the
case's premises in the scope that type binds (`valid_typcase`,
`valid.ml:271-287`). -/
def hasTypCase : Nat → Env → VarEnv → List TypCase → MixopS → Value → Res Bool
  | 0, _, _, _, _, _ => .error .outOfFuel
  | _+1, _, _, [], _, _ => .ok false
  | n+1, env, ρ, .mk op t qs prems :: cs, op', w =>
      if op = op' then
        (do
          let b ← hasTyp n env ρ t w
          if b then
            Res.elimUndef
              (bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v)
                (caseScope ρ t w) (quantDefs qs prems))
              (fun o => match o with
                | some ρq => premsOk n env ρq prems
                | none => .ok false)
              (fun _ => .ok false)
          else .ok false)
      else hasTypCase n env ρ cs op' w
termination_by n => n

/-- Select the instance of a type family that applies, and unfold it
(`reduce_typ_app`, `eval.ml:133-149`).

The instances are tried in declaration order; the first whose argument
patterns match the actual arguments wins (`eval.ml:142-143`), a definite
mismatch moves on (`eval.ml:144`), and a match that cannot be decided stops
the search — `eval.ml:145-146`'s `if not !assume_coherent_matches then
Ok None`, which `Res.elimUndef` implements by propagating `outOfFuel`.
Running out of instances is `eval.ml:140`'s `Error None` on the same branch
of the flag, i.e. `.error .undef`.

The selected `deftyp` is read in a scope containing *only* the instance's
bindings, mirroring `Subst.subst_deftyp s dt` at `eval.ml:143` with `s` built
from `Subst.empty`; this is the same discipline as `Sem/Eval.lean`'s
`tryClauses`. -/
def hasTypInsts : Nat → Env → List Inst → List ArgV → Value → Res Bool
  | 0, _, _, _, _ => .error .outOfFuel
  | _+1, _, [], _, _ => .error .undef
  | n+1, env, .instD _ pats dt :: insts, ws, v =>
      Res.elimUndef (matchArgs n env VarEnv.empty pats ws)
        (fun ρ' => hasTypDef n env ρ' dt v)
        (fun _ => hasTypInsts n env insts ws v)
termination_by n => n

end


/-! ## Metatheory

### Monotonicity in fuel

As in `Sem/Eval.lean`, everything rests on this: more fuel never changes an
answer `hasTyp` has already committed to.  The order is `Res.Le`, because
`outOfFuel` is exactly the outcome more fuel is allowed to change. -/

/-- A two-sided congruence for `ite` in the `Res.Le` order: both sides test
the same decidable condition, so the same branch is taken on both. -/
theorem ite_le {c : Prop} [Decidable c] {r₁ r₂ s₁ s₂ : Res Bool}
    (h : r₁ ⊑ r₂) (h' : s₁ ⊑ s₂) : (if c then r₁ else s₁) ⊑ (if c then r₂ else s₂) := by
  split_ifs with hc
  · exact h
  · exact h'

/-- The common special case: the negative branch is the definite answer
`false`, which is below itself. -/
theorem iteFalse_le {c : Prop} [Decidable c] {r₁ r₂ : Res Bool} (h : r₁ ⊑ r₂) :
    (if c then r₁ else .ok false) ⊑ (if c then r₂ else .ok false) :=
  ite_le h (Res.Le.refl _)

/-- `if` on the literal `true`, as a rewrite rule: the clauses of the mutual
block branch on a `Bool` that the proofs below case-split, and `simp only`
needs this to see past the resulting `ite`. -/
theorem iteB_true {α : Type} (r s : α) : (if (true : Bool) then r else s) = r := rfl

/-- `if` on the literal `false`; see `iteB_true`. -/
theorem iteB_false {α : Type} (r s : α) : (if (false : Bool) then r else s) = s := rfl

/-- `ite` at a condition that holds. -/
theorem iteP_true {α : Type} {c : Prop} [Decidable c] {r s : α} (h : c) :
    (if c then r else s) = r := by
  split
  · rfl
  · rename_i hc; exact absurd h hc

/-- `ite` at a condition that fails. -/
theorem iteP_false {α : Type} {c : Prop} [Decidable c] {r s : α} (h : ¬ c) :
    (if c then r else s) = s := by
  split
  · rename_i hc; exact absurd hc h
  · rfl

/-- `premsOk` inherits `premsHold`'s monotonicity (`monoAt_of_le`). -/
theorem premsOk_le {m n : Nat} (h : m ≤ n) (env : Env) (ρ : VarEnv) (prems : List Prem) :
    premsOk m env ρ prems ⊑ premsOk n env ρ prems :=
  Res.elimUndef_le ((monoAt_of_le h).premsHold env ρ prems)
    (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)

/-- `bindQuants` is monotone in its two oracles. -/
theorem bindQuants_le {ev₁ ev₂ : VarEnv → Exp → Res Value}
    {ty₁ ty₂ : VarEnv → Typ → Value → Res Bool}
    (hev : ∀ ρ e, ev₁ ρ e ⊑ ev₂ ρ e) (hty : ∀ ρ t v, ty₁ ρ t v ⊑ ty₂ ρ t v) :
    ∀ ρ ds, bindQuants ev₁ ty₁ ρ ds ⊑ bindQuants ev₂ ty₂ ρ ds
  | _, [] => Res.Le.refl _
  | ρ, (x, t, e) :: ds => by
      simp only [bindQuants]
      refine Res.bind_le (hev _ _) fun v => Res.bind_le (hty _ _ _) fun b => ?_
      cases b
      · exact Res.Le.refl _
      · exact bindQuants_le hev hty _ _

/-- Monotonicity in fuel for all seven members of the mutual block at once.

A structure rather than a sevenfold conjunction, so that the induction can
name the hypothesis it needs; this is `Sem/Eval.lean`'s `MonoAt` for the
typing block. -/
structure MonoTypAt (m n : Nat) : Prop where
  /-- Monotonicity of `hasTyp`. -/
  typ : ∀ env ρ t v, hasTyp m env ρ t v ⊑ hasTyp n env ρ t v
  /-- Monotonicity of `hasTypTup`. -/
  tup : ∀ env ρ bs vs, hasTypTup m env ρ bs vs ⊑ hasTypTup n env ρ bs vs
  /-- Monotonicity of `hasTypList`. -/
  list : ∀ env ρ t vs, hasTypList m env ρ t vs ⊑ hasTypList n env ρ t vs
  /-- Monotonicity of `hasTypDef`. -/
  defTyp : ∀ env ρ dt v, hasTypDef m env ρ dt v ⊑ hasTypDef n env ρ dt v
  /-- Monotonicity of `hasTypFields`. -/
  fields : ∀ env ρ fs gs, hasTypFields m env ρ fs gs ⊑ hasTypFields n env ρ fs gs
  /-- Monotonicity of `hasTypCase`. -/
  case : ∀ env ρ cs op w, hasTypCase m env ρ cs op w ⊑ hasTypCase n env ρ cs op w
  /-- Monotonicity of `hasTypInsts`. -/
  insts : ∀ env is ws v, hasTypInsts m env is ws v ⊑ hasTypInsts n env is ws v

/-- Base case: with no fuel every member answers `outOfFuel`, which is below
everything. -/
theorem monoTypAt_zero (n : Nat) : MonoTypAt 0 n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; simp only [hasTyp]; exact Res.oof_le _
  · intros; simp only [hasTypTup]; exact Res.oof_le _
  · intros; simp only [hasTypList]; exact Res.oof_le _
  · intros; simp only [hasTypDef]; exact Res.oof_le _
  · intros; simp only [hasTypFields]; exact Res.oof_le _
  · intros; simp only [hasTypCase]; exact Res.oof_le _
  · intros; simp only [hasTypInsts]; exact Res.oof_le _

/-- The inductive step: one unit of fuel at a time, by structural recursion on
the fuel.  Every member is unfolded once and recombined with `Res.bind_le`,
`Res.elimUndef_le` and `ite_le`; the clauses that leave the block —
`evalExp` and `evalArgs` in `hasTyp`, `matchArgs` in `hasTypInsts`,
`premsHold` in `hasTypFields` and `hasTypCase` — appeal to `Sem/Eval.lean`'s
`monoAt_succ` and to `premsOk_le`. -/
theorem monoTypAt_succ : ∀ m, MonoTypAt m (m + 1)
  | 0 => monoTypAt_zero 1
  | m + 1 => by
      have ih := monoTypAt_succ m
      have hev := monoAt_succ m
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- `hasTyp`
      · intro env ρ t v
        cases t with
        | boolT => simp only [hasTyp]; exact Res.Le.refl _
        | numT t => simp only [hasTyp]; exact Res.Le.refl _
        | textT => simp only [hasTyp]; exact Res.Le.refl _
        | tupT bs =>
            simp only [hasTyp]
            cases hv : v.asTuple? with
            | none => exact Res.Le.refl _
            | some vs => exact ih.tup _ _ _ _
        | iterT t it =>
            cases it with
            | opt =>
                simp only [hasTyp]
                cases hv : v.asOpt? with
                | none => exact Res.Le.refl _
                | some o =>
                    cases o with
                    | none => exact Res.Le.refl _
                    | some w => exact ih.typ _ _ _ _
            | list =>
                simp only [hasTyp]
                cases hv : v.asList? with
                | none => exact Res.Le.refl _
                | some vs => exact ih.list _ _ _ _
            | list1 =>
                simp only [hasTyp]
                cases hv : v.asList? with
                | none => exact Res.Le.refl _
                | some vs => exact ite_le (Res.Le.refl _) (ih.list _ _ _ _)
            | listN e x =>
                simp only [hasTyp]
                cases hv : v.asList? with
                | none => exact Res.Le.refl _
                | some vs =>
                    refine Res.bind_le (hev.exp _ _ _) fun kv => ?_
                    refine Res.bind_le (Res.Le.refl _) fun k => ?_
                    exact iteFalse_le (ih.list _ _ _ _)
        | varT x args =>
            simp only [hasTyp]
            cases hl : localTyp? ρ x args with
            | some t => exact ih.typ _ _ _ _
            | none =>
                refine Res.bind_le (Res.Le.refl _) fun td => ?_
                refine Res.bind_le (hev.args _ _ _) fun ws => ?_
                exact ih.insts _ _ _ _
      -- `hasTypTup`
      · intro env ρ bs vs
        cases bs with
        | nil => cases vs <;> (simp only [hasTypTup]; exact Res.Le.refl _)
        | cons b bs =>
            cases b with
            | mk x t =>
                cases vs with
                | nil => simp only [hasTypTup]; exact Res.Le.refl _
                | cons v vs =>
                    simp only [hasTypTup]
                    exact Res.bind_le (ih.typ _ _ _ _) fun _ =>
                      iteFalse_le (ih.tup _ _ _ _)
      -- `hasTypList`
      · intro env ρ t vs
        cases vs with
        | nil => simp only [hasTypList]; exact Res.Le.refl _
        | cons v vs =>
            simp only [hasTypList]
            exact Res.bind_le (ih.typ _ _ _ _) fun _ => iteFalse_le (ih.list _ _ _ _)
      -- `hasTypDef`
      · intro env ρ dt v
        cases dt with
        | aliasT t => simp only [hasTypDef]; exact ih.typ _ _ _ _
        | structT fs =>
            simp only [hasTypDef]
            cases hv : v.asStruct? with
            | none => exact Res.Le.refl _
            | some gs => exact ih.fields _ _ _ _
        | variantT cs =>
            simp only [hasTypDef]
            cases hv : v.asCase? with
            | none => exact Res.Le.refl _
            | some p => exact ih.case _ _ _ _ _
      -- `hasTypFields`
      · intro env ρ fs gs
        cases fs with
        | nil => cases gs <;> (simp only [hasTypFields]; exact Res.Le.refl _)
        | cons f fs =>
            cases f with
            | mk a t qs prems =>
                cases gs with
                | nil => simp only [hasTypFields]; exact Res.Le.refl _
                | cons g gs =>
                    obtain ⟨a', w⟩ := g
                    simp only [hasTypFields]
                    refine iteFalse_le ?_
                    refine Res.bind_le (ih.typ _ _ _ _) fun _ => iteFalse_le ?_
                    exact Res.bind_le (premsOk_le (Nat.le_succ m) _ _ _) fun _ =>
                      iteFalse_le (ih.fields _ _ _ _)
      -- `hasTypCase`
      · intro env ρ cs op w
        cases cs with
        | nil => simp only [hasTypCase]; exact Res.Le.refl _
        | cons c cs =>
            cases c with
            | mk op' t qs prems =>
                simp only [hasTypCase]
                refine ite_le ?_ (ih.case _ _ _ _ _)
                refine Res.bind_le (ih.typ _ _ _ _) fun _ => iteFalse_le ?_
                refine Res.elimUndef_le (bindQuants_le (fun _ _ => hev.exp _ _ _)
                  (fun _ _ _ => ih.typ _ _ _ _) _ _) (fun o => ?_) (fun _ => Res.Le.refl _)
                cases o with
                | none => exact Res.Le.refl _
                | some ρq => exact premsOk_le (Nat.le_succ m) _ _ _
      -- `hasTypInsts`
      · intro env is ws v
        cases is with
        | nil => simp only [hasTypInsts]; exact Res.Le.refl _
        | cons i is =>
            cases i with
            | instD qs pats dt =>
                simp only [hasTypInsts]
                exact Res.elimUndef_le (hev.matchArgs _ _ _ _)
                  (fun _ => ih.defTyp _ _ _ _) (fun _ => ih.insts _ _ _ _)

/-- Reflexivity, for the composition below. -/
theorem monoTypAt_refl (m : Nat) : MonoTypAt m m :=
  ⟨fun _ _ _ _ => Res.Le.refl _, fun _ _ _ _ => Res.Le.refl _,
   fun _ _ _ _ => Res.Le.refl _, fun _ _ _ _ => Res.Le.refl _,
   fun _ _ _ _ => Res.Le.refl _, fun _ _ _ _ _ => Res.Le.refl _,
   fun _ _ _ _ => Res.Le.refl _⟩

/-- Transitivity, member by member. -/
theorem monoTypAt_trans {a b c : Nat} (h₁ : MonoTypAt a b) (h₂ : MonoTypAt b c) :
    MonoTypAt a c :=
  ⟨fun env ρ t v => (h₁.typ env ρ t v).trans (h₂.typ env ρ t v),
   fun env ρ bs vs => (h₁.tup env ρ bs vs).trans (h₂.tup env ρ bs vs),
   fun env ρ t vs => (h₁.list env ρ t vs).trans (h₂.list env ρ t vs),
   fun env ρ dt v => (h₁.defTyp env ρ dt v).trans (h₂.defTyp env ρ dt v),
   fun env ρ fs gs => (h₁.fields env ρ fs gs).trans (h₂.fields env ρ fs gs),
   fun env ρ cs op w => (h₁.case env ρ cs op w).trans (h₂.case env ρ cs op w),
   fun env is ws v => (h₁.insts env is ws v).trans (h₂.insts env is ws v)⟩

/-- Monotonicity in fuel, in the form the relations below use. -/
theorem monoTypAt_of_le {m n : Nat} (h : m ≤ n) : MonoTypAt m n := by
  induction n with
  | zero => exact Nat.le_zero.mp h ▸ monoTypAt_refl 0
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · exact monoTypAt_trans (ih (Nat.lt_succ_iff.mp hm)) (monoTypAt_succ n)
      · exact Nat.le_antisymm h hm ▸ monoTypAt_refl m


/-! ### The relations the membership test induces

As in `Sem/Eval.lean`, each fuel-indexed function gives a fuel-free relation
by existentially quantifying the budget.  `monoTypAt_of_le` is what makes the
quantifier sensible: a definite answer at one level is the answer at every
higher one. -/

/-- `v` inhabits `t` in the script `env` and the scope `ρ`. -/
def HasTyp (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) : Prop :=
  ∃ n, hasTyp n env ρ t v = .ok true

/-- `vs` inhabits the dependent tuple type `bs`. -/
def HasTypTup (env : Env) (ρ : VarEnv) (bs : List TypBind) (vs : List Value) : Prop :=
  ∃ n, hasTypTup n env ρ bs vs = .ok true

/-- Every element of `vs` inhabits `t`. -/
def HasTypList (env : Env) (ρ : VarEnv) (t : Typ) (vs : List Value) : Prop :=
  ∃ n, hasTypList n env ρ t vs = .ok true

/-- `v` inhabits the unfolded definition `dt`. -/
def HasTypDef (env : Env) (ρ : VarEnv) (dt : DefTyp) (v : Value) : Prop :=
  ∃ n, hasTypDef n env ρ dt v = .ok true

/-- `gs` inhabits the record type `fs`. -/
def HasTypFields (env : Env) (ρ : VarEnv) (fs : List TypField)
    (gs : List (AtomS × Value)) : Prop :=
  ∃ n, hasTypFields n env ρ fs gs = .ok true

/-- `Value.case op w` inhabits the variant whose cases are `cs`. -/
def HasTypCase (env : Env) (ρ : VarEnv) (cs : List TypCase) (op : MixopS)
    (w : Value) : Prop :=
  ∃ n, hasTypCase n env ρ cs op w = .ok true

/-- `v` inhabits the instance of a type family that `ws` selects. -/
def HasTypInsts (env : Env) (insts : List Inst) (ws : List ArgV) (v : Value) : Prop :=
  ∃ n, hasTypInsts n env insts ws v = .ok true

/-- A field's or case's premises hold. -/
def PremsOk (env : Env) (ρ : VarEnv) (prems : List Prem) : Prop :=
  ∃ n, premsOk n env ρ prems = .ok true

/-! ### Monotonicity, in the form the relations use -/

/-- A definite answer survives more fuel. -/
theorem hasTyp_ok_of_le {m n : Nat} {env ρ t v b} (h : m ≤ n)
    (hm : hasTyp m env ρ t v = .ok b) : hasTyp n env ρ t v = .ok b :=
  ((monoTypAt_of_le h).typ _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem hasTypTup_ok_of_le {m n : Nat} {env ρ bs vs b} (h : m ≤ n)
    (hm : hasTypTup m env ρ bs vs = .ok b) : hasTypTup n env ρ bs vs = .ok b :=
  ((monoTypAt_of_le h).tup _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem hasTypList_ok_of_le {m n : Nat} {env ρ t vs b} (h : m ≤ n)
    (hm : hasTypList m env ρ t vs = .ok b) : hasTypList n env ρ t vs = .ok b :=
  ((monoTypAt_of_le h).list _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem hasTypDef_ok_of_le {m n : Nat} {env ρ dt v b} (h : m ≤ n)
    (hm : hasTypDef m env ρ dt v = .ok b) : hasTypDef n env ρ dt v = .ok b :=
  ((monoTypAt_of_le h).defTyp _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem hasTypFields_ok_of_le {m n : Nat} {env ρ fs gs b} (h : m ≤ n)
    (hm : hasTypFields m env ρ fs gs = .ok b) : hasTypFields n env ρ fs gs = .ok b :=
  ((monoTypAt_of_le h).fields _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem hasTypCase_ok_of_le {m n : Nat} {env ρ cs op w b} (h : m ≤ n)
    (hm : hasTypCase m env ρ cs op w = .ok b) : hasTypCase n env ρ cs op w = .ok b :=
  ((monoTypAt_of_le h).case _ _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem hasTypInsts_ok_of_le {m n : Nat} {env is ws v b} (h : m ≤ n)
    (hm : hasTypInsts m env is ws v = .ok b) : hasTypInsts n env is ws v = .ok b :=
  ((monoTypAt_of_le h).insts _ _ _ _).ok hm

/-- A definite answer survives more fuel. -/
theorem premsOk_ok_of_le {m n : Nat} {env ρ prems b} (h : m ≤ n)
    (hm : premsOk m env ρ prems = .ok b) : premsOk n env ρ prems = .ok b :=
  (premsOk_le h _ _ _).ok hm

/-! ### Decidability, given a bound

`HasTyp` is an existential over the fuel, so it is not decidable outright.  It
*is* decided by any fuel level at which `hasTyp` commits: that is the content
of `hasTyp_iff_of_ok`, and `decidableHasTyp` turns it into an instance one can
discharge with `decide` once a budget is supplied. -/

/-- A definite answer at *any* fuel level settles the proposition. -/
theorem hasTyp_iff_of_ok {n : Nat} {env ρ t v} {b : Bool}
    (h : hasTyp n env ρ t v = .ok b) : HasTyp env ρ t v ↔ b = true := by
  constructor
  · rintro ⟨m, hm⟩
    have h₁ := hasTyp_ok_of_le (Nat.le_max_left m n) hm
    have h₂ := hasTyp_ok_of_le (Nat.le_max_right m n) h
    rw [h₁] at h₂
    exact (Except.ok.inj h₂).symm
  · rintro rfl; exact ⟨n, h⟩

/-- A definite `false` refutes membership. -/
theorem not_hasTyp_of_ok_false {n : Nat} {env ρ t v}
    (h : hasTyp n env ρ t v = .ok false) : ¬ HasTyp env ρ t v := by
  simpa using (hasTyp_iff_of_ok h).mp

/-- Membership is decided by any fuel level that answers definitely. -/
def decidableHasTyp {n : Nat} {env : Env} {ρ : VarEnv} {t : Typ} {v : Value}
    {b : Bool} (h : hasTyp n env ρ t v = .ok b) : Decidable (HasTyp env ρ t v) :=
  if hb : b then .isTrue ((hasTyp_iff_of_ok h).mpr hb)
  else .isFalse (fun hv => hb ((hasTyp_iff_of_ok h).mp hv))

/-- The same statement for the other six members, so that a bound settles a
record, a variant case or a type-family application too. -/
theorem hasTypDef_iff_of_ok {n : Nat} {env ρ dt v} {b : Bool}
    (h : hasTypDef n env ρ dt v = .ok b) : HasTypDef env ρ dt v ↔ b = true := by
  constructor
  · rintro ⟨m, hm⟩
    have h₁ := hasTypDef_ok_of_le (Nat.le_max_left m n) hm
    have h₂ := hasTypDef_ok_of_le (Nat.le_max_right m n) h
    rw [h₁] at h₂
    exact (Except.ok.inj h₂).symm
  · rintro rfl; exact ⟨n, h⟩

/-! ### Unfolding, one clause at a time

The equation lemmas of the mutual block, named.  They are the
compositionality statements *at a fixed budget*; the relational versions below
quantify the budget away. -/

/-- No fuel: every member is undecided. -/
theorem hasTyp_zero (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    hasTyp 0 env ρ t v = .error .outOfFuel := by simp only [hasTyp]

/-- `BoolT` is inhabited by the booleans. -/
theorem hasTyp_succ_boolT (n : Nat) (env : Env) (ρ : VarEnv) (v : Value) :
    hasTyp (n + 1) env ρ .boolT v = .ok v.asBool?.isSome := by simp only [hasTyp]

/-- `NumT t` is inhabited by the numerals whose own type is below `t`. -/
theorem hasTyp_succ_numT (n : Nat) (env : Env) (ρ : VarEnv) (t : NumTyp) (v : Value) :
    hasTyp (n + 1) env ρ (.numT t) v =
      .ok (match v.asNum? with | some m => Num.subTyp (Num.toTyp m) t | none => false) := by
  simp only [hasTyp]

/-- `TextT` is inhabited by the texts. -/
theorem hasTyp_succ_textT (n : Nat) (env : Env) (ρ : VarEnv) (v : Value) :
    hasTyp (n + 1) env ρ .textT v = .ok v.asText?.isSome := by simp only [hasTyp]

/-- `TupT` is inhabited by the tuples. -/
theorem hasTyp_succ_tupT (n : Nat) (env : Env) (ρ : VarEnv) (bs : List TypBind)
    (v : Value) :
    hasTyp (n + 1) env ρ (.tupT bs) v =
      match v.asTuple? with
      | some vs => hasTypTup n env ρ bs vs
      | none => .ok false := by simp only [hasTyp]

/-- `IterT (t, Opt)` is inhabited by the options. -/
theorem hasTyp_succ_iterT_opt (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    hasTyp (n + 1) env ρ (.iterT t .opt) v =
      match v.asOpt? with
      | some none => .ok true
      | some (some w) => hasTyp n env ρ t w
      | none => .ok false := by simp only [hasTyp]

/-- `IterT (t, List)` is inhabited by the lists. -/
theorem hasTyp_succ_iterT_list (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    hasTyp (n + 1) env ρ (.iterT t .list) v =
      match v.asList? with
      | some vs => hasTypList n env ρ t vs
      | none => .ok false := by simp only [hasTyp]

/-- `IterT (t, List1)` is inhabited by the non-empty lists. -/
theorem hasTyp_succ_iterT_list1 (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    hasTyp (n + 1) env ρ (.iterT t .list1) v =
      match v.asList? with
      | some vs => if vs.isEmpty then .ok false else hasTypList n env ρ t vs
      | none => .ok false := by simp only [hasTyp]

/-- `IterT (t, ListN (e, _))` is inhabited by the lists of the length `e`
denotes. -/
theorem hasTyp_succ_iterT_listN (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ)
    (e : Exp) (x : Option IL.Id) (v : Value) :
    hasTyp (n + 1) env ρ (.iterT t (.listN e x)) v =
      match v.asList? with
      | some vs => do
          let kv ← evalExp n env ρ e
          let k ← Res.ofOption kv.asNat?
          if vs.length = k then hasTypList n env ρ t vs else .ok false
      | none => .ok false := by simp only [hasTyp]

/-- `VarT` resolves through the scope, then through the script. -/
theorem hasTyp_succ_varT (n : Nat) (env : Env) (ρ : VarEnv) (x : IL.Id)
    (args : List Arg) (v : Value) :
    hasTyp (n + 1) env ρ (.varT x args) v =
      match localTyp? ρ x args with
      | some t => hasTyp n env ρ t v
      | none =>
          (do
            let td ← Res.ofOption (env.findTyp? x)
            let ws ← evalArgs n env ρ args
            hasTypInsts n env td.2 ws v) := by simp only [hasTyp]

/-- No fuel. -/
theorem hasTypTup_zero (env : Env) (ρ : VarEnv) (bs : List TypBind) (vs : List Value) :
    hasTypTup 0 env ρ bs vs = .error .outOfFuel := by simp only [hasTypTup]

/-- The empty tuple type is inhabited by the empty tuple only. -/
theorem hasTypTup_succ_nil_nil (n : Nat) (env : Env) (ρ : VarEnv) :
    hasTypTup (n + 1) env ρ [] [] = .ok true := by simp only [hasTypTup]

/-- Too many components. -/
theorem hasTypTup_succ_nil_cons (n : Nat) (env : Env) (ρ : VarEnv) (v : Value)
    (vs : List Value) : hasTypTup (n + 1) env ρ [] (v :: vs) = .ok false := by
  simp only [hasTypTup]

/-- Too few components. -/
theorem hasTypTup_succ_cons_nil (n : Nat) (env : Env) (ρ : VarEnv) (b : TypBind)
    (bs : List TypBind) : hasTypTup (n + 1) env ρ (b :: bs) [] = .ok false := by
  simp only [hasTypTup]

/-- The dependent step: the binder enters scope for the rest. -/
theorem hasTypTup_succ_cons_cons (n : Nat) (env : Env) (ρ : VarEnv) (x : IL.Id)
    (t : Typ) (bs : List TypBind) (v : Value) (vs : List Value) :
    hasTypTup (n + 1) env ρ (.mk x t :: bs) (v :: vs) =
      (do
        let b ← hasTyp n env ρ t v
        if b then hasTypTup n env (ρ.bindVal x v) bs vs else .ok false) := by
  simp only [hasTypTup]

/-- No fuel. -/
theorem hasTypList_zero (env : Env) (ρ : VarEnv) (t : Typ) (vs : List Value) :
    hasTypList 0 env ρ t vs = .error .outOfFuel := by simp only [hasTypList]

/-- The empty list inhabits every list type. -/
theorem hasTypList_succ_nil (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ) :
    hasTypList (n + 1) env ρ t [] = .ok true := by simp only [hasTypList]

/-- Head and tail. -/
theorem hasTypList_succ_cons (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ)
    (v : Value) (vs : List Value) :
    hasTypList (n + 1) env ρ t (v :: vs) =
      (do
        let b ← hasTyp n env ρ t v
        if b then hasTypList n env ρ t vs else .ok false) := by simp only [hasTypList]

/-- No fuel. -/
theorem hasTypDef_zero (env : Env) (ρ : VarEnv) (dt : DefTyp) (v : Value) :
    hasTypDef 0 env ρ dt v = .error .outOfFuel := by simp only [hasTypDef]

/-- An alias is transparent. -/
theorem hasTypDef_succ_aliasT (n : Nat) (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    hasTypDef (n + 1) env ρ (.aliasT t) v = hasTyp n env ρ t v := by simp only [hasTypDef]

/-- A record type wants a record value. -/
theorem hasTypDef_succ_structT (n : Nat) (env : Env) (ρ : VarEnv)
    (fs : List TypField) (v : Value) :
    hasTypDef (n + 1) env ρ (.structT fs) v =
      match v.asStruct? with
      | some gs => hasTypFields n env ρ fs gs
      | none => .ok false := by simp only [hasTypDef]

/-- A variant wants an injection. -/
theorem hasTypDef_succ_variantT (n : Nat) (env : Env) (ρ : VarEnv)
    (cs : List TypCase) (v : Value) :
    hasTypDef (n + 1) env ρ (.variantT cs) v =
      match v.asCase? with
      | some (op, w) => hasTypCase n env ρ cs op w
      | none => .ok false := by simp only [hasTypDef]

/-- No fuel. -/
theorem hasTypFields_zero (env : Env) (ρ : VarEnv) (fs : List TypField)
    (gs : List (AtomS × Value)) : hasTypFields 0 env ρ fs gs = .error .outOfFuel := by
  simp only [hasTypFields]

/-- The empty record type is inhabited by the empty record only. -/
theorem hasTypFields_succ_nil_nil (n : Nat) (env : Env) (ρ : VarEnv) :
    hasTypFields (n + 1) env ρ [] [] = .ok true := by simp only [hasTypFields]

/-- Too many fields. -/
theorem hasTypFields_succ_nil_cons (n : Nat) (env : Env) (ρ : VarEnv)
    (g : AtomS × Value) (gs : List (AtomS × Value)) :
    hasTypFields (n + 1) env ρ [] (g :: gs) = .ok false := by simp only [hasTypFields]

/-- Too few fields. -/
theorem hasTypFields_succ_cons_nil (n : Nat) (env : Env) (ρ : VarEnv) (f : TypField)
    (fs : List TypField) : hasTypFields (n + 1) env ρ (f :: fs) [] = .ok false := by
  simp only [hasTypFields]

/-- One field: same atom, inhabiting value, premises holding. -/
theorem hasTypFields_succ_cons_cons (n : Nat) (env : Env) (ρ : VarEnv) (a : AtomS)
    (t : Typ) (qs : List Param) (prems : List Prem) (fs : List TypField)
    (a' : AtomS) (w : Value) (gs : List (AtomS × Value)) :
    hasTypFields (n + 1) env ρ (.mk a t qs prems :: fs) ((a', w) :: gs) =
      (if a = a' then
        (do
          let b ← hasTyp n env ρ t w
          if b then
            (do
              let hp ← premsOk n env (caseScope ρ t w) prems
              if hp then hasTypFields n env ρ fs gs else .ok false)
          else .ok false)
      else .ok false) := by simp only [hasTypFields]

/-- No fuel. -/
theorem hasTypCase_zero (env : Env) (ρ : VarEnv) (cs : List TypCase) (op : MixopS)
    (w : Value) : hasTypCase 0 env ρ cs op w = .error .outOfFuel := by
  simp only [hasTypCase]

/-- An undeclared case operator: definitely not an inhabitant. -/
theorem hasTypCase_succ_nil (n : Nat) (env : Env) (ρ : VarEnv) (op : MixopS)
    (w : Value) : hasTypCase (n + 1) env ρ [] op w = .ok false := by simp only [hasTypCase]

/-- Look the operator up, case by case. -/
theorem hasTypCase_succ_cons (n : Nat) (env : Env) (ρ : VarEnv) (o : MixopS) (t : Typ)
    (qs : List Param) (prems : List Prem) (cs : List TypCase) (op : MixopS) (w : Value) :
    hasTypCase (n + 1) env ρ (.mk o t qs prems :: cs) op w =
      (if o = op then
        (do
          let b ← hasTyp n env ρ t w
          if b then
            Res.elimUndef
              (bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v)
                (caseScope ρ t w) (quantDefs qs prems))
              (fun o => match o with
                | some ρq => premsOk n env ρq prems
                | none => .ok false)
              (fun _ => .ok false)
          else .ok false)
      else hasTypCase n env ρ cs op w) := by simp only [hasTypCase]

/-- No fuel. -/
theorem hasTypInsts_zero (env : Env) (is : List Inst) (ws : List ArgV) (v : Value) :
    hasTypInsts 0 env is ws v = .error .outOfFuel := by simp only [hasTypInsts]

/-- No instance applies: the type application is not defined (`eval.ml:140`). -/
theorem hasTypInsts_succ_nil (n : Nat) (env : Env) (ws : List ArgV) (v : Value) :
    hasTypInsts (n + 1) env [] ws v = .error .undef := by simp only [hasTypInsts]

/-- First match wins, and an undecided match stops the search. -/
theorem hasTypInsts_succ_cons (n : Nat) (env : Env) (qs : List Param)
    (pats : List Arg) (dt : DefTyp) (is : List Inst) (ws : List ArgV) (v : Value) :
    hasTypInsts (n + 1) env (.instD qs pats dt :: is) ws v =
      Res.elimUndef (matchArgs n env VarEnv.empty pats ws)
        (fun ρ' => hasTypDef n env ρ' dt v)
        (fun _ => hasTypInsts n env is ws v) := by simp only [hasTypInsts]

/-! ### Compositionality

One lemma per clause of the membership test, stating membership in the whole
in terms of membership in the parts.  The forward direction strips one unit of
fuel; the backward direction runs the sub-derivations at a common level
(`Nat.max`) and adds one.  These are `Sem/Eval.lean`'s `evalExp_*_iff` for the
typing judgment. -/

section Compositionality

variable {env : Env} {ρ : VarEnv} {v : Value}

/-- `BoolT` denotes the booleans. -/
theorem hasTyp_boolT_iff : HasTyp env ρ .boolT v ↔ ∃ b, v = .bool b := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_boolT] at h
        cases hv : v.asBool? with
        | none => rw [hv] at h; simp at h
        | some b => exact ⟨b, Value.asBool?_eq_some.mp hv⟩
  · rintro ⟨b, rfl⟩
    exact ⟨1, by rw [hasTyp_succ_boolT]; simp⟩

/-- `NumT t` denotes the numerals below `t` in `Xl.Num.sub`
(`spectec/src/xl/num.ml:52-57`). -/
theorem hasTyp_numT_iff {t : NumTyp} :
    HasTyp env ρ (.numT t) v ↔ ∃ m, v = .num m ∧ Num.subTyp (Num.toTyp m) t := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_numT] at h
        cases hv : v.asNum? with
        | none => simp only [hv, Except.ok.injEq] at h; simp at h
        | some m =>
            simp only [hv, Except.ok.injEq] at h
            exact ⟨m, Value.asNum?_eq_some.mp hv, h⟩
  · rintro ⟨m, rfl, hm⟩
    exact ⟨1, by rw [hasTyp_succ_numT]; simpa using hm⟩

/-- `TextT` denotes the texts. -/
theorem hasTyp_textT_iff : HasTyp env ρ .textT v ↔ ∃ s, v = .text s := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_textT] at h
        cases hv : v.asText? with
        | none => rw [hv] at h; simp at h
        | some s => exact ⟨s, Value.asText?_eq_some.mp hv⟩
  · rintro ⟨s, rfl⟩
    exact ⟨1, by rw [hasTyp_succ_textT]; simp⟩

/-- `TupT` denotes the tuples whose components inhabit the component types,
dependently. -/
theorem hasTyp_tupT_iff {bs : List TypBind} :
    HasTyp env ρ (.tupT bs) v ↔ ∃ vs, v = .tuple vs ∧ HasTypTup env ρ bs vs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_tupT] at h
        cases hv : v.asTuple? with
        | none => simp only [hv] at h; simp at h
        | some vs =>
            simp only [hv] at h
            exact ⟨vs, Value.asTuple?_eq_some.mp hv, ⟨n, h⟩⟩
  · rintro ⟨vs, rfl, ⟨n, hn⟩⟩
    exact ⟨n + 1, by rw [hasTyp_succ_tupT]; simpa using hn⟩

/-- `IterT (t, Opt)` denotes the options over `t`. -/
theorem hasTyp_iterT_opt_iff {t : Typ} :
    HasTyp env ρ (.iterT t .opt) v ↔
      v = .opt none ∨ ∃ w, v = .opt (some w) ∧ HasTyp env ρ t w := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_iterT_opt] at h
        cases hv : v.asOpt? with
        | none => simp only [hv] at h; simp at h
        | some o =>
            cases o with
            | none => exact Or.inl (Value.asOpt?_eq_some.mp hv)
            | some w =>
                simp only [hv] at h
                exact Or.inr ⟨w, Value.asOpt?_eq_some.mp hv, ⟨n, h⟩⟩
  · rintro (rfl | ⟨w, rfl, ⟨n, hn⟩⟩)
    · exact ⟨1, by rw [hasTyp_succ_iterT_opt]; simp⟩
    · exact ⟨n + 1, by rw [hasTyp_succ_iterT_opt]; simpa using hn⟩

/-- `IterT (t, List)` denotes the lists over `t`. -/
theorem hasTyp_iterT_list_iff {t : Typ} :
    HasTyp env ρ (.iterT t .list) v ↔ ∃ vs, v = .list vs ∧ HasTypList env ρ t vs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_iterT_list] at h
        cases hv : v.asList? with
        | none => simp only [hv] at h; simp at h
        | some vs =>
            simp only [hv] at h
            exact ⟨vs, Value.asList?_eq_some.mp hv, ⟨n, h⟩⟩
  · rintro ⟨vs, rfl, ⟨n, hn⟩⟩
    exact ⟨n + 1, by rw [hasTyp_succ_iterT_list]; simpa using hn⟩

/-- `IterT (t, List1)` denotes the non-empty lists over `t`. -/
theorem hasTyp_iterT_list1_iff {t : Typ} :
    HasTyp env ρ (.iterT t .list1) v ↔
      ∃ vs, v = .list vs ∧ vs ≠ [] ∧ HasTypList env ρ t vs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_iterT_list1] at h
        cases hv : v.asList? with
        | none => simp only [hv] at h; simp at h
        | some vs =>
            simp only [hv] at h
            split at h
            · simp at h
            · rename_i hne
              refine ⟨vs, Value.asList?_eq_some.mp hv, ?_, ⟨n, h⟩⟩
              intro hnil; exact hne (by simp [hnil])
  · rintro ⟨vs, rfl, hne, ⟨n, hn⟩⟩
    refine ⟨n + 1, ?_⟩
    rw [hasTyp_succ_iterT_list1]
    cases vs with
    | nil => exact absurd rfl hne
    | cons w ws => simpa using hn

/-- `IterT (t, ListN (e, _))` denotes the lists over `t` whose length is the
value of `e` (`eval.ml:401-405`). -/
theorem hasTyp_iterT_listN_iff {t : Typ} {e : Exp} {x : Option IL.Id} :
    HasTyp env ρ (.iterT t (.listN e x)) v ↔
      ∃ vs k, v = .list vs ∧ EvalExp env ρ e (.num (.natN k)) ∧ vs.length = k ∧
        HasTypList env ρ t vs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_iterT_listN] at h
        cases hv : v.asList? with
        | none => simp only [hv] at h; simp at h
        | some vs =>
            simp only [hv, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
            obtain ⟨kv, hkv, k, hk, h'⟩ := h
            split at h'
            · rename_i hlen
              exact ⟨vs, k, Value.asList?_eq_some.mp hv, ⟨n, by
                  rw [Value.asNat?_eq_some] at hk; exact hk ▸ hkv⟩, hlen, ⟨n, h'⟩⟩
            · simp at h'
  · rintro ⟨vs, k, rfl, ⟨n₁, h₁⟩, hlen, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    rw [hasTyp_succ_iterT_listN]
    simp only [Value.asList?_list, Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨.num (.natN k), evalExp_ok_of_le (Nat.le_max_left _ _) h₁, k, rfl, by
      simp only [hlen]
      exact hasTypList_ok_of_le (Nat.le_max_right _ _) h₂⟩

/-- A `VarT` whose head is a local type variable is that type. -/
theorem hasTyp_varT_local_iff {x : IL.Id} {args : List Arg} {t : Typ}
    (hl : localTyp? ρ x args = some t) :
    HasTyp env ρ (.varT x args) v ↔ HasTyp env ρ t v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n => rw [hasTyp_succ_varT, hl] at h; exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by rw [hasTyp_succ_varT, hl]; exact h⟩

/-- A `VarT` whose head is a global type name resolves through the script:
the arguments are evaluated and the instances are tried in order. -/
theorem hasTyp_varT_global_iff {x : IL.Id} {args : List Arg}
    (hl : localTyp? ρ x args = none) :
    HasTyp env ρ (.varT x args) v ↔
      ∃ td ws, env.findTyp? x = some td ∧ EvalArgs env ρ args ws ∧
        HasTypInsts env td.2 ws v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTyp_zero] at h; simp at h
    | succ n =>
        rw [hasTyp_succ_varT, hl] at h
        simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h
        obtain ⟨td, htd, ws, hws, h'⟩ := h
        exact ⟨td, ws, htd, ⟨n, hws⟩, ⟨n, h'⟩⟩
  · rintro ⟨td, ws, htd, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    rw [hasTyp_succ_varT, hl]
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨td, htd, ws, evalArgs_ok_of_le (Nat.le_max_left _ _) h₁,
      hasTypInsts_ok_of_le (Nat.le_max_right _ _) h₂⟩

/-- The empty tuple type is inhabited by the empty tuple only. -/
theorem hasTypTup_nil_iff {vs : List Value} : HasTypTup env ρ [] vs ↔ vs = [] := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypTup_zero] at h; simp at h
    | succ n =>
        cases vs with
        | nil => rfl
        | cons w ws => rw [hasTypTup_succ_nil_cons] at h; simp at h
  · rintro rfl; exact ⟨1, hasTypTup_succ_nil_nil 0 env ρ⟩

/-- The dependent step: the binder is in scope for the rest of the tuple. -/
theorem hasTypTup_cons_iff {x : IL.Id} {t : Typ} {bs : List TypBind} {vs : List Value} :
    HasTypTup env ρ (.mk x t :: bs) vs ↔
      ∃ w ws, vs = w :: ws ∧ HasTyp env ρ t w ∧ HasTypTup env (ρ.bindVal x w) bs ws := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypTup_zero] at h; simp at h
    | succ n =>
        cases vs with
        | nil => rw [hasTypTup_succ_cons_nil] at h; simp at h
        | cons w ws =>
            rw [hasTypTup_succ_cons_cons] at h
            simp only [Res.bind_eq_ok] at h
            obtain ⟨b, hb, h'⟩ := h
            cases b with
            | false => simp at h'
            | true => exact ⟨w, ws, rfl, ⟨n, hb⟩, ⟨n, h'⟩⟩
  · rintro ⟨w, ws, rfl, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    rw [hasTypTup_succ_cons_cons]
    simp only [Res.bind_eq_ok]
    exact ⟨true, hasTyp_ok_of_le (Nat.le_max_left _ _) h₁,
      hasTypTup_ok_of_le (Nat.le_max_right _ _) h₂⟩

/-- A list inhabits `t*` exactly when every element inhabits `t`. -/
theorem hasTypList_iff {t : Typ} {vs : List Value} :
    HasTypList env ρ t vs ↔ ∀ w ∈ vs, HasTyp env ρ t w := by
  constructor
  · rintro ⟨n, h⟩
    induction vs generalizing n with
    | nil => simp
    | cons w ws ih =>
        cases n with
        | zero => rw [hasTypList_zero] at h; simp at h
        | succ n =>
            rw [hasTypList_succ_cons] at h
            simp only [Res.bind_eq_ok] at h
            obtain ⟨b, hb, h'⟩ := h
            cases b with
            | false => simp at h'
            | true =>
                intro u hu
                rcases List.mem_cons.mp hu with rfl | hu
                · exact ⟨n, hb⟩
                · exact ih _ h' u hu
  · intro h
    induction vs with
    | nil => exact ⟨1, hasTypList_succ_nil 0 env ρ t⟩
    | cons w ws ih =>
        obtain ⟨n₁, h₁⟩ := h w (by simp)
        obtain ⟨n₂, h₂⟩ := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
        refine ⟨max n₁ n₂ + 1, ?_⟩
        rw [hasTypList_succ_cons]
        simp only [Res.bind_eq_ok]
        exact ⟨true, hasTyp_ok_of_le (Nat.le_max_left _ _) h₁,
          hasTypList_ok_of_le (Nat.le_max_right _ _) h₂⟩

/-- An alias is transparent (`eval.ml:116-117`). -/
theorem hasTypDef_aliasT_iff {t : Typ} :
    HasTypDef env ρ (.aliasT t) v ↔ HasTyp env ρ t v := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypDef_zero] at h; simp at h
    | succ n => rw [hasTypDef_succ_aliasT] at h; exact ⟨n, h⟩
  · rintro ⟨n, h⟩; exact ⟨n + 1, by rw [hasTypDef_succ_aliasT]; exact h⟩

/-- A record type denotes the records with exactly those fields. -/
theorem hasTypDef_structT_iff {fs : List TypField} :
    HasTypDef env ρ (.structT fs) v ↔
      ∃ gs, v = .struct gs ∧ HasTypFields env ρ fs gs := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypDef_zero] at h; simp at h
    | succ n =>
        rw [hasTypDef_succ_structT] at h
        cases hv : v.asStruct? with
        | none => simp only [hv] at h; simp at h
        | some gs =>
            simp only [hv] at h
            exact ⟨gs, Value.asStruct?_eq_some.mp hv, ⟨n, h⟩⟩
  · rintro ⟨gs, rfl, ⟨n, hn⟩⟩
    exact ⟨n + 1, by rw [hasTypDef_succ_structT]; simpa using hn⟩

/-- A variant denotes the injections one of whose cases accepts the payload. -/
theorem hasTypDef_variantT_iff {cs : List TypCase} :
    HasTypDef env ρ (.variantT cs) v ↔
      ∃ op w, v = .case op w ∧ HasTypCase env ρ cs op w := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypDef_zero] at h; simp at h
    | succ n =>
        rw [hasTypDef_succ_variantT] at h
        cases hv : v.asCase? with
        | none => simp only [hv] at h; simp at h
        | some p =>
            obtain ⟨op, w⟩ := p
            simp only [hv] at h
            exact ⟨op, w, Value.asCase?_eq_some.mp hv, ⟨n, h⟩⟩
  · rintro ⟨op, w, rfl, ⟨n, hn⟩⟩
    exact ⟨n + 1, by rw [hasTypDef_succ_variantT]; simpa using hn⟩

/-- The empty record type is inhabited by the empty record only. -/
theorem hasTypFields_nil_iff {gs : List (AtomS × Value)} :
    HasTypFields env ρ [] gs ↔ gs = [] := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypFields_zero] at h; simp at h
    | succ n =>
        cases gs with
        | nil => rfl
        | cons g gs => rw [hasTypFields_succ_nil_cons] at h; simp at h
  · rintro rfl; exact ⟨1, hasTypFields_succ_nil_nil 0 env ρ⟩

/-- One field at a time: the atoms must agree, the value must inhabit the
field type, and the field's premises must hold. -/
theorem hasTypFields_cons_iff {a : AtomS} {t : Typ} {qs : List Param}
    {prems : List Prem} {fs : List TypField} {gs : List (AtomS × Value)} :
    HasTypFields env ρ (.mk a t qs prems :: fs) gs ↔
      ∃ w gs', gs = (a, w) :: gs' ∧ HasTyp env ρ t w ∧
        PremsOk env (caseScope ρ t w) prems ∧ HasTypFields env ρ fs gs' := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypFields_zero] at h; simp at h
    | succ n =>
        cases gs with
        | nil => rw [hasTypFields_succ_cons_nil] at h; simp at h
        | cons g gs =>
            obtain ⟨a', w⟩ := g
            rw [hasTypFields_succ_cons_cons] at h
            split at h
            · rename_i ha
              subst ha
              simp only [Res.bind_eq_ok] at h
              obtain ⟨b, hb, h'⟩ := h
              cases b with
              | false => simp at h'
              | true =>
                  rw [iteB_true] at h'
                  simp only [Res.bind_eq_ok] at h'
                  obtain ⟨c, hc, h''⟩ := h'
                  cases c with
                  | false => rw [iteB_false] at h''; simp at h''
                  | true =>
                      rw [iteB_true] at h''
                      exact ⟨w, gs, rfl, ⟨n, hb⟩, ⟨n, hc⟩, ⟨n, h''⟩⟩
            · simp at h
  · rintro ⟨w, gs', rfl, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, ⟨n₃, h₃⟩⟩
    refine ⟨max n₁ (max n₂ n₃) + 1, ?_⟩
    rw [hasTypFields_succ_cons_cons, iteP_true rfl]
    simp only [Res.bind_eq_ok]
    refine ⟨true, hasTyp_ok_of_le (by omega) h₁, ?_⟩
    rw [iteB_true]
    simp only [Res.bind_eq_ok]
    refine ⟨true, premsOk_ok_of_le (by omega) h₂, ?_⟩
    rw [iteB_true]
    exact hasTypFields_ok_of_le (by omega) h₃

/-- A variant with no cases has no inhabitants. -/
theorem not_hasTypCase_nil {op : MixopS} {w : Value} : ¬ HasTypCase env ρ [] op w := by
  rintro ⟨n, h⟩
  cases n with
  | zero => rw [hasTypCase_zero] at h; simp at h
  | succ n => rw [hasTypCase_succ_nil] at h; simp at h

/-- `bindQuants` with the typing block's oracles, fuel-free. -/
def BindQuants (env : Env) (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)) (ρq : VarEnv) : Prop :=
  ∃ n, bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v) ρ ds =
    .ok (some ρq)

/-- A definite answer of `bindQuants` survives more fuel. -/
theorem bindQuants_ok_of_le {m n : Nat} (h : m ≤ n) {ρ : VarEnv}
    {ds : List (IL.Id × Typ × Exp)} {r : Option VarEnv}
    (hm : bindQuants (fun ρ e => evalExp m env ρ e) (fun ρ t v => hasTyp m env ρ t v) ρ ds =
      .ok r) :
    bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v) ρ ds = .ok r :=
  ((bindQuants_le (fun _ _ => (monoAt_of_le h).exp _ _ _)
    (fun _ _ _ => (monoTypAt_of_le h).typ _ _ _ _) ρ ds).eq_of_ne_oof
    (by rw [hm]; simp)).trans hm

/-- No defining conjunct: the scope is unchanged. -/
theorem bindQuants_nil_iff {ρ ρq : VarEnv} : BindQuants env ρ [] ρq ↔ ρq = ρ := by
  constructor
  · rintro ⟨n, h⟩
    simp only [bindQuants] at h
    exact (Option.some.inj (Except.ok.inj h)).symm
  · rintro rfl
    exact ⟨0, rfl⟩

/-- One defined quantifier binds: its definition evaluates to a value of its type. -/
theorem bindQuants_cons {ρ ρq : VarEnv} {x : IL.Id} {t : Typ} {e : Exp} {v : Value}
    {ds : List (IL.Id × Typ × Exp)} (he : EvalExp env ρ e v) (ht : HasTyp env ρ t v)
    (hr : BindQuants env (ρ.bindVal x v) ds ρq) : BindQuants env ρ ((x, t, e) :: ds) ρq := by
  obtain ⟨n₁, h₁⟩ := he
  obtain ⟨n₂, h₂⟩ := ht
  obtain ⟨n₃, h₃⟩ := hr
  refine ⟨max n₁ (max n₂ n₃), ?_⟩
  simp only [bindQuants, Res.bind_eq_ok]
  refine ⟨v, evalExp_ok_of_le (by omega) h₁, true, hasTyp_ok_of_le (by omega) h₂, ?_⟩
  exact bindQuants_ok_of_le (by omega) h₃

/-- The matching case: the payload inhabits the case's type, the case's defined
quantifiers bind (`bindQuants`) and the case's premises hold in that scope. -/
theorem hasTypCase_cons_hit_iffQ {o : MixopS} {t : Typ} {qs : List Param}
    {prems : List Prem} {cs : List TypCase} {op : MixopS} {w : Value} (ho : o = op) :
    HasTypCase env ρ (.mk o t qs prems :: cs) op w ↔
      HasTyp env ρ t w ∧ ∃ ρq, BindQuants env (caseScope ρ t w) (quantDefs qs prems) ρq ∧
        PremsOk env ρq prems := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypCase_zero] at h; simp at h
    | succ n =>
        rw [hasTypCase_succ_cons, iteP_true ho] at h
        simp only [Res.bind_eq_ok] at h
        obtain ⟨b, hb, h'⟩ := h
        cases b with
        | false => simp at h'
        | true =>
            refine ⟨⟨n, hb⟩, ?_⟩
            cases hq : bindQuants (fun ρ e => evalExp n env ρ e)
                (fun ρ t v => hasTyp n env ρ t v) (caseScope ρ t w) (quantDefs qs prems) with
            | ok o =>
                rw [hq, Res.elimUndef_ok] at h'
                cases o with
                | none => simp at h'
                | some ρq => exact ⟨ρq, ⟨n, hq⟩, ⟨n, h'⟩⟩
            | error e => cases e <;> (rw [hq] at h'; simp [Res.elimUndef] at h')
  · rintro ⟨⟨n₁, h₁⟩, ρq, ⟨n₂, h₂⟩, ⟨n₃, h₃⟩⟩
    refine ⟨max n₁ (max n₂ n₃) + 1, ?_⟩
    rw [hasTypCase_succ_cons, iteP_true ho]
    simp only [Res.bind_eq_ok]
    refine ⟨true, hasTyp_ok_of_le (Nat.le_max_left _ _) h₁, ?_⟩
    rw [bindQuants_ok_of_le (by omega) h₂, Res.elimUndef_ok]
    exact premsOk_ok_of_le (by omega) h₃

/-- The matching case of a case with no defined quantifier: the payload
inhabits the case's type and the case's premises hold. -/
theorem hasTypCase_cons_hit_iff {o : MixopS} {t : Typ} {qs : List Param}
    {prems : List Prem} {cs : List TypCase} {op : MixopS} {w : Value} (ho : o = op)
    (hq : quantDefs qs prems = [] := by first | rfl | simp) :
    HasTypCase env ρ (.mk o t qs prems :: cs) op w ↔
      HasTyp env ρ t w ∧ PremsOk env (caseScope ρ t w) prems := by
  rw [hasTypCase_cons_hit_iffQ ho, hq]
  constructor
  · rintro ⟨h₁, ρq, hb, hp⟩
    rw [bindQuants_nil_iff] at hb
    exact ⟨h₁, hb ▸ hp⟩
  · rintro ⟨h₁, hp⟩
    exact ⟨h₁, _, bindQuants_nil_iff.2 rfl, hp⟩

/-- A non-matching case is skipped (`find_case`, `valid.ml:28-31`). -/
theorem hasTypCase_cons_miss_iff {o : MixopS} {t : Typ} {qs : List Param}
    {prems : List Prem} {cs : List TypCase} {op : MixopS} {w : Value} (ho : o ≠ op) :
    HasTypCase env ρ (.mk o t qs prems :: cs) op w ↔ HasTypCase env ρ cs op w := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => rw [hasTypCase_zero] at h; simp at h
    | succ n => rw [hasTypCase_succ_cons, iteP_false ho] at h; exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨n + 1, by rw [hasTypCase_succ_cons, iteP_false ho]; exact h⟩

/-- A type family with no instances has no inhabitants (`eval.ml:140`). -/
theorem not_hasTypInsts_nil {ws : List ArgV} : ¬ HasTypInsts env [] ws v := by
  rintro ⟨n, h⟩
  cases n with
  | zero => rw [hasTypInsts_zero] at h; simp at h
  | succ n => rw [hasTypInsts_succ_nil] at h; simp at h

/-- The first instance applies. -/
theorem hasTypInsts_head {qs : List Param} {pats : List Arg} {dt : DefTyp}
    {is : List Inst} {ws : List ArgV} {σ : VarEnv}
    (hm : MatchArgs env VarEnv.empty pats ws σ) (hd : HasTypDef env σ dt v) :
    HasTypInsts env (.instD qs pats dt :: is) ws v := by
  obtain ⟨n₁, h₁⟩ := hm
  obtain ⟨n₂, h₂⟩ := hd
  refine ⟨max n₁ n₂ + 1, ?_⟩
  rw [hasTypInsts_succ_cons,
    ((monoAt_of_le (Nat.le_max_left n₁ n₂)).matchArgs _ _ _ _).ok h₁]
  simpa using hasTypDef_ok_of_le (Nat.le_max_right _ _) h₂

/-- The first instance definitely does not apply, so the search moves on
(`eval.ml:144`). -/
theorem hasTypInsts_tail {qs : List Param} {pats : List Arg} {dt : DefTyp}
    {is : List Inst} {ws : List ArgV} {n : Nat}
    (hm : matchArgs n env VarEnv.empty pats ws = .error .undef)
    (ht : HasTypInsts env is ws v) :
    HasTypInsts env (.instD qs pats dt :: is) ws v := by
  obtain ⟨n₂, h₂⟩ := ht
  refine ⟨max n n₂ + 1, ?_⟩
  rw [hasTypInsts_succ_cons,
    (((monoAt_of_le (Nat.le_max_left n n₂)).matchArgs _ _ _ _).eq_of_ne_oof
      (by rw [hm]; simp))]
  simpa [hm] using hasTypInsts_ok_of_le (Nat.le_max_right _ _) h₂

/-- Inversion for a cons of instances: either the head instance matched and
its definition accepted the value, or the search moved on. -/
theorem hasTypInsts_cons_inv {qs : List Param} {pats : List Arg} {dt : DefTyp}
    {is : List Inst} {ws : List ArgV}
    (h : HasTypInsts env (.instD qs pats dt :: is) ws v) :
    (∃ σ, MatchArgs env VarEnv.empty pats ws σ ∧ HasTypDef env σ dt v) ∨
      HasTypInsts env is ws v := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => rw [hasTypInsts_zero] at h; simp at h
  | succ n =>
      rw [hasTypInsts_succ_cons] at h
      unfold Res.elimUndef at h
      split at h
      · rename_i σ hσ
        exact Or.inl ⟨σ, ⟨n, hσ⟩, ⟨n, h⟩⟩
      · simp at h
      · exact Or.inr ⟨n, h⟩

end Compositionality

/-! ### Inversion

What a value inhabiting a composite type must look like.  The leaf cases are
the `iff` lemmas above; these are the ones that see through a `VarT` to the
declaration it names. -/

section Inversion

variable {env : Env} {ρ : VarEnv} {v : Value}

/-- A value inhabiting a variant is an injection by one of its cases
(`find_case`, `spectec/src/il/valid.ml:28-31`). -/
theorem hasTypCase_mem {cs : List TypCase} {op : MixopS} {w : Value}
    (h : HasTypCase env ρ cs op w) :
    ∃ t qs prems, TypCase.mk op t qs prems ∈ cs ∧ HasTyp env ρ t w ∧
      ∃ ρq, BindQuants env (caseScope ρ t w) (quantDefs qs prems) ρq ∧ PremsOk env ρq prems := by
  induction cs with
  | nil => exact absurd h not_hasTypCase_nil
  | cons c cs ih =>
      obtain ⟨o, t, qs, prems⟩ := c
      by_cases ho : o = op
      · subst ho
        obtain ⟨h₁, h₂⟩ := (hasTypCase_cons_hit_iffQ rfl).mp h
        exact ⟨t, qs, prems, by simp, h₁, h₂⟩
      · obtain ⟨t', qs', prems', hm, h₁, h₂⟩ := ih ((hasTypCase_cons_miss_iff ho).mp h)
        exact ⟨t', qs', prems', List.mem_cons_of_mem _ hm, h₁, h₂⟩

/-- A tuple inhabiting a `TupT` has exactly as many components as binders
(`valid.ml:460-463`). -/
theorem hasTypTup_length {bs : List TypBind} {vs : List Value}
    (h : HasTypTup env ρ bs vs) : vs.length = bs.length := by
  induction bs generalizing ρ vs with
  | nil => rw [hasTypTup_nil_iff.mp h]; rfl
  | cons b bs ih =>
      obtain ⟨x, t⟩ := b
      obtain ⟨w, ws, rfl, _, ht⟩ := hasTypTup_cons_iff.mp h
      simpa using ih ht

/-- A record inhabiting a `StructT` has exactly as many fields as the type
(`valid_list`, `valid.ml:428`). -/
theorem hasTypFields_length {fs : List TypField} {gs : List (AtomS × Value)}
    (h : HasTypFields env ρ fs gs) : gs.length = fs.length := by
  induction fs generalizing gs with
  | nil => rw [hasTypFields_nil_iff.mp h]; rfl
  | cons f fs ih =>
      obtain ⟨a, t, qs, prems⟩ := f
      obtain ⟨w, gs', rfl, _, _, hr⟩ := hasTypFields_cons_iff.mp h
      simpa using ih hr

/-- If every instance of a type family unfolds to a variant, then every value
the family accepts is an injection. -/
theorem hasTypInsts_case_of_variant {is : List Inst} {ws : List ArgV}
    (hv : ∀ qs pats dt, Inst.instD qs pats dt ∈ is → ∃ cs, dt = .variantT cs)
    (h : HasTypInsts env is ws v) : ∃ op w, v = .case op w := by
  induction is with
  | nil => exact absurd h not_hasTypInsts_nil
  | cons i is ih =>
      obtain ⟨qs, pats, dt⟩ := i
      rcases hasTypInsts_cons_inv h with ⟨σ, _, hd⟩ | ht
      · obtain ⟨cs, rfl⟩ := hv qs pats dt (by simp)
        obtain ⟨op, w, rfl, _⟩ := hasTypDef_variantT_iff.mp hd
        exact ⟨op, w, rfl⟩
      · exact ih (fun qs' pats' dt' hm => hv qs' pats' dt' (List.mem_cons_of_mem _ hm)) ht

/-- The same for records. -/
theorem hasTypInsts_struct_of_struct {is : List Inst} {ws : List ArgV}
    (hv : ∀ qs pats dt, Inst.instD qs pats dt ∈ is → ∃ fs, dt = .structT fs)
    (h : HasTypInsts env is ws v) : ∃ gs, v = .struct gs := by
  induction is with
  | nil => exact absurd h not_hasTypInsts_nil
  | cons i is ih =>
      obtain ⟨qs, pats, dt⟩ := i
      rcases hasTypInsts_cons_inv h with ⟨σ, _, hd⟩ | ht
      · obtain ⟨fs, rfl⟩ := hv qs pats dt (by simp)
        obtain ⟨gs, rfl, _⟩ := hasTypDef_structT_iff.mp hd
        exact ⟨gs, rfl⟩
      · exact ih (fun qs' pats' dt' hm => hv qs' pats' dt' (List.mem_cons_of_mem _ hm)) ht

/-- **Inversion for a variant type name**: a value inhabiting `VarT (x, args)`
whose declaration unfolds to a variant in every instance is a `Value.case`. -/
theorem hasTyp_varT_case_of_variant {x : IL.Id} {args : List Arg} {td : TypDef}
    (hl : localTyp? ρ x args = none) (hd : env.findTyp? x = some td)
    (hv : ∀ qs pats dt, Inst.instD qs pats dt ∈ td.2 → ∃ cs, dt = .variantT cs)
    (h : HasTyp env ρ (.varT x args) v) : ∃ op w, v = .case op w := by
  obtain ⟨td', ws, htd, _, hi⟩ := (hasTyp_varT_global_iff hl).mp h
  rw [hd, Option.some.injEq] at htd
  subst htd
  exact hasTypInsts_case_of_variant hv hi

/-- **Inversion for a record type name**. -/
theorem hasTyp_varT_struct_of_struct {x : IL.Id} {args : List Arg} {td : TypDef}
    (hl : localTyp? ρ x args = none) (hd : env.findTyp? x = some td)
    (hv : ∀ qs pats dt, Inst.instD qs pats dt ∈ td.2 → ∃ fs, dt = .structT fs)
    (h : HasTyp env ρ (.varT x args) v) : ∃ gs, v = .struct gs := by
  obtain ⟨td', ws, htd, _, hi⟩ := (hasTyp_varT_global_iff hl).mp h
  rw [hd, Option.some.injEq] at htd
  subst htd
  exact hasTypInsts_struct_of_struct hv hi

end Inversion

/-! ### Type soundness, for the fragment in which the type is determined

The `--ast` printer erases the `typ` note on every expression
(`docs/projects/spectec/README.md`), so there is no typing judgment on expressions to
preserve.  `Sem/Valid.lean` does exist, but it transcribes only the
type-free half of `valid.ml` — scope, kind and shape checking — and it keeps
no expected type, so it supplies no such judgment.  What *can* be stated
without one splits in two:

* the constructors whose result type is fixed by the expression form alone —
  the three literals, the comparisons, `MemE` and `LenE` — for which
  soundness is unconditional;
* the first-order constructors whose result type is fixed by the component
  types — `ListE`, `OptE`, `TupE`, `CaseE` and `StrE` — for which soundness is
  conditional on the components.

Nothing here is claimed about `CallE`, `IterE`, `UpdE`, `CompE` or the paths:
those need the expression typing judgment, which is the typing layer
`Sem/Valid.lean` leaves out (`docs/projects/spectec/README.md`, step 6, and that
file's "What is deliberately left out"). -/

section Soundness

variable {env : Env} {ρ : VarEnv}

/-- `Xl.Num.sub` is reflexive (`spectec/src/xl/num.ml:52-57`), so every
numeral inhabits its own numeric type. -/
theorem Num.subTyp_refl (t : NumTyp) : Num.subTyp t t = true := by cases t <;> rfl

/-- The empty list of premises holds (`reduce_prems`, `eval.ml:678`). -/
theorem premsOk_nil : PremsOk env ρ [] :=
  ⟨1, by
    have h : premsHold 1 env ρ [] = .ok ρ := by simp only [premsHold, List.foldlM_nil]; rfl
    rw [premsOk, h, Res.elimUndef_ok]⟩

/-- A comparison always denotes a boolean (`cmpValues`, `eval.ml:256-270`). -/
theorem cmpValues_bool {op : CmpOp} {v₁ v₂ v : Value}
    (h : cmpValues op v₁ v₂ = .ok v) : ∃ b, v = .bool b := by
  unfold cmpValues at h
  split at h
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at h
    obtain ⟨b, _, rfl⟩ := h
    exact ⟨b, rfl⟩
  · simp at h

/-- Membership always denotes a boolean (`memValue`, `eval.ml:339-350`). -/
theorem memValue_bool {v₁ v₂ v : Value} (h : memValue v₁ v₂ = .ok v) :
    ∃ b, v = .bool b := by
  unfold memValue at h
  split at h
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · exact ⟨_, (Except.ok.inj h).symm⟩
  · simp at h

/-- The empty list of expressions denotes the empty list of values. -/
theorem evalExps_nil_iff {vs : List Value} : EvalExps env ρ [] vs ↔ vs = [] := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExps] at h
    | succ n =>
        simp only [evalExps, List.mapM_nil] at h
        exact (Except.ok.inj h).symm
  · rintro rfl; exact ⟨1, by simp only [evalExps, List.mapM_nil]; rfl⟩

/-- Head and tail of a list of expressions. -/
theorem evalExps_cons_iff {e : Exp} {es : List Exp} {vs : List Value} :
    EvalExps env ρ (e :: es) vs ↔
      ∃ w ws, EvalExp env ρ e w ∧ EvalExps env ρ es ws ∧ vs = w :: ws := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalExps] at h
    | succ n =>
        simp only [evalExps, List.mapM_cons, Res.bind_eq_ok, pure, Except.pure] at h
        obtain ⟨w, hw, ws, hws, hvs⟩ := h
        exact ⟨w, ws, ⟨n, hw⟩, ⟨n + 1, by simp only [evalExps]; exact hws⟩,
          (Except.ok.inj hvs).symm⟩
  · rintro ⟨w, ws, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, rfl⟩
    refine ⟨max n₁ n₂ + 1, ?_⟩
    have hw := evalExp_ok_of_le (Nat.le_max_left n₁ n₂) h₁
    have hws : evalExps (max n₁ n₂ + 1) env ρ es = .ok ws :=
      evalExps_ok_of_le (by omega) h₂
    simp only [evalExps] at hws ⊢
    simp only [List.mapM_cons, Res.bind_eq_ok]
    exact ⟨w, hw, ws, hws, rfl⟩

/-- A boolean literal inhabits `BoolT` (`valid.ml:299`). -/
theorem evalExp_boolE_hasTyp {b : Bool} {v : Value}
    (h : EvalExp env ρ (.boolE b) v) : HasTyp env ρ .boolT v := by
  rw [evalExp_boolE_iff] at h; subst h; exact hasTyp_boolT_iff.mpr ⟨b, rfl⟩

/-- A numeral inhabits its own numeric type (`infer_exp`, `valid.ml:300`). -/
theorem evalExp_numE_hasTyp {m : Num} {v : Value}
    (h : EvalExp env ρ (.numE m) v) : HasTyp env ρ (.numT (Num.toTyp m)) v := by
  rw [evalExp_numE_iff] at h; subst h
  exact hasTyp_numT_iff.mpr ⟨m, rfl, Num.subTyp_refl _⟩

/-- A text literal inhabits `TextT` (`valid.ml:301`). -/
theorem evalExp_textE_hasTyp {t : Text} {v : Value}
    (h : EvalExp env ρ (.textE t) v) : HasTyp env ρ .textT v := by
  rw [evalExp_textE_iff] at h; subst h; exact hasTyp_textT_iff.mpr ⟨t, rfl⟩

/-- A comparison inhabits `BoolT`, whatever its operands are
(`valid.ml:405`). -/
theorem evalExp_cmpE_hasTyp {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.cmpE op t e₁ e₂) v) : HasTyp env ρ .boolT v := by
  obtain ⟨v₁, v₂, _, _, hc⟩ := evalExp_cmpE_iff.mp h
  obtain ⟨b, rfl⟩ := cmpValues_bool hc
  exact hasTyp_boolT_iff.mpr ⟨b, rfl⟩

/-- A membership test inhabits `BoolT` (`valid.ml:445`). -/
theorem evalExp_memE_hasTyp {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.memE e₁ e₂) v) : HasTyp env ρ .boolT v := by
  obtain ⟨v₁, v₂, _, _, hc⟩ := evalExp_memE_iff.mp h
  obtain ⟨b, rfl⟩ := memValue_bool hc
  exact hasTyp_boolT_iff.mpr ⟨b, rfl⟩

/-- A length inhabits `NumT NatT` (`valid.ml:450`). -/
theorem evalExp_lenE_hasTyp {e : Exp} {v : Value}
    (h : EvalExp env ρ (.lenE e) v) : HasTyp env ρ (.numT .natT) v := by
  obtain ⟨vs, _, rfl⟩ := evalExp_lenE_iff.mp h
  exact hasTyp_numT_iff.mpr ⟨.natN vs.length, rfl, rfl⟩

/-- A list expression inhabits `t*` as soon as every component's value
inhabits `t` (`valid.ml:493-495`). -/
theorem evalExp_listE_hasTyp {es : List Exp} {t : Typ} {v : Value}
    (h : EvalExp env ρ (.listE es) v)
    (ht : ∀ e ∈ es, ∀ w, EvalExp env ρ e w → HasTyp env ρ t w) :
    HasTyp env ρ (.iterT t .list) v := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.mp h
  refine hasTyp_iterT_list_iff.mpr ⟨vs, rfl, hasTypList_iff.mpr ?_⟩
  clear h
  induction es generalizing vs with
  | nil => rw [evalExps_nil_iff.mp hvs]; simp
  | cons e es ih =>
      obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.mp hvs
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht e (by simp) u hw
      · exact ih (fun e' he' => ht e' (List.mem_cons_of_mem _ he')) ws hws u hu

/-- An option expression inhabits `t?` as soon as its contents do
(`valid.ml:488-490`). -/
theorem evalExp_optE_hasTyp {eo : Option Exp} {t : Typ} {v : Value}
    (h : EvalExp env ρ (.optE eo) v)
    (ht : ∀ e, eo = some e → ∀ w, EvalExp env ρ e w → HasTyp env ρ t w) :
    HasTyp env ρ (.iterT t .opt) v := by
  cases eo with
  | none =>
      rw [evalExp_optE_none_iff] at h
      exact hasTyp_iterT_opt_iff.mpr (Or.inl h)
  | some e =>
      obtain ⟨w, hw, rfl⟩ := evalExp_optE_some_iff.mp h
      exact hasTyp_iterT_opt_iff.mpr (Or.inr ⟨w, rfl, ht e rfl w hw⟩)

/-- A tuple expression inhabits `TupT bs` as soon as its components do,
*dependently* (`valid.ml:451-464`). -/
theorem evalExp_tupE_hasTyp {es : List Exp} {bs : List TypBind} {v : Value}
    (h : EvalExp env ρ (.tupE es) v)
    (ht : ∀ vs, EvalExps env ρ es vs → HasTypTup env ρ bs vs) :
    HasTyp env ρ (.tupT bs) v := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.mp h
  exact hasTyp_tupT_iff.mpr ⟨vs, rfl, ht vs hvs⟩

/-- An injection inhabits a variant as soon as its payload inhabits the
corresponding case (`valid.ml:508-512`). -/
theorem evalExp_caseE_hasTypDef {op : MixopS} {e : Exp} {cs : List TypCase} {v : Value}
    (h : EvalExp env ρ (.caseE op e) v)
    (ht : ∀ w, EvalExp env ρ e w → HasTypCase env ρ cs op w) :
    HasTypDef env ρ (.variantT cs) v := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.mp h
  exact hasTypDef_variantT_iff.mpr ⟨op, w, rfl, ht w hw⟩

/-- A record expression inhabits a record type as soon as its fields do
(`valid.ml:426-428`). -/
theorem evalExp_strE_hasTypDef {efs : List ExpField} {fs : List TypField} {v : Value}
    (h : EvalExp env ρ (.strE efs) v)
    (ht : ∀ gs, EvalExpFields env ρ efs gs → HasTypFields env ρ fs gs) :
    HasTypDef env ρ (.structT fs) v := by
  obtain ⟨gs, hgs, rfl⟩ := evalExp_strE_iff.mp h
  exact hasTypDef_structT_iff.mpr ⟨gs, rfl, ht gs hgs⟩

end Soundness

/-! ## Examples

`hasTyp` is defined by well-founded recursion on its fuel, so it does not
reduce by `rfl`; these go through the unfolding and compositionality lemmas,
which is also what a proof about a concrete script would do. -/

namespace Examples

set_option maxRecDepth 10000

/-- `3 : nat` inhabits `int`, because `Xl.Num.sub` makes `nat <: int`
(`spectec/src/xl/num.ml:52-57`). -/
example : HasTyp Env.empty VarEnv.empty (.numT .intT) (.num (.natN 3)) :=
  hasTyp_numT_iff.mpr ⟨.natN 3, rfl, rfl⟩

/-- A numeral is not a boolean. -/
example : ¬ HasTyp Env.empty VarEnv.empty .boolT (.num (.natN 3)) := by
  intro h
  obtain ⟨b, hb⟩ := hasTyp_boolT_iff.mp h
  simp at hb

/-- The empty list does not inhabit a `+` iteration (`as_list_typ`,
`valid.ml:73-76`, with `List1` at `valid.ml:493-495`). -/
example : ¬ HasTyp Env.empty VarEnv.empty (.iterT (.numT .natT) .list1) (.list []) := by
  intro h
  obtain ⟨vs, hv, hne, _⟩ := hasTyp_iterT_list1_iff.mp h
  exact hne (by simpa using hv.symm)

/-- The dependent tuple type `(n : nat, x : nat^n)`: the second component's
length is fixed by the first component's *value*, which is why `hasTyp` needs
the evaluator. -/
def depTup : Typ :=
  .tupT [.mk "n" (.numT .natT), .mk "x" (.iterT (.numT .natT) (.listN (.varE "n") none))]

/-- `(2, [7 8])` inhabits it. -/
example : HasTyp Env.empty VarEnv.empty depTup
    (.tuple [.num (.natN 2), .list [.num (.natN 7), .num (.natN 8)]]) := by
  refine hasTyp_tupT_iff.mpr ⟨_, rfl, hasTypTup_cons_iff.mpr ⟨_, _, rfl, ?_, ?_⟩⟩
  · exact hasTyp_numT_iff.mpr ⟨.natN 2, rfl, rfl⟩
  · refine hasTypTup_cons_iff.mpr ⟨_, _, rfl, ?_, hasTypTup_nil_iff.mpr rfl⟩
    refine hasTyp_iterT_listN_iff.mpr ⟨_, 2, rfl, ?_, rfl, hasTypList_iff.mpr ?_⟩
    · rw [evalExp_varE_iff]; rfl
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hasTyp_numT_iff.mpr ⟨.natN 7, rfl, rfl⟩
      · exact hasTyp_numT_iff.mpr ⟨.natN 8, rfl, rfl⟩

/-- The two cases of a one-bit variant, both carrying the empty tuple. -/
def bitCases : List TypCase := [.mk "0" (.tupT []) [] [], .mk "1" (.tupT []) [] []]

/-- The script `syntax bit = 0 | 1`, as an environment. -/
def bitEnv : Env := Env.empty.bindTyp "bit" ([], [.instD [] [] (.variantT bitCases)])

/-- `0` inhabits `bit`: the name resolves to the only instance, which unfolds
to the variant, whose first case accepts the empty tuple. -/
example : HasTyp bitEnv VarEnv.empty (.varT "bit" []) (.case "0" (.tuple [])) := by
  refine (hasTyp_varT_global_iff rfl).mpr
    ⟨([], [.instD [] [] (.variantT bitCases)]), [], rfl, ⟨1, ?_⟩, ?_⟩
  · simp only [evalArgs, List.mapM_nil]; rfl
  · refine hasTypInsts_head (σ := VarEnv.empty) ⟨1, ?_⟩ ?_
    · simp only [matchArgs]
    · refine hasTypDef_variantT_iff.mpr ⟨"0", .tuple [], rfl, ?_⟩
      refine (hasTypCase_cons_hit_iff rfl).mpr ⟨?_, premsOk_nil⟩
      exact hasTyp_tupT_iff.mpr ⟨[], rfl, hasTypTup_nil_iff.mpr rfl⟩

/-- An undeclared case operator does not inhabit the variant: there is no
`2` among `bit`'s cases (`find_case`, `valid.ml:28-31`). -/
example : ¬ HasTypDef Env.empty VarEnv.empty (.variantT bitCases)
    (.case "2" (.tuple [])) := by
  intro h
  obtain ⟨op, w, hv, hc⟩ := hasTypDef_variantT_iff.mp h
  obtain ⟨rfl, rfl⟩ : op = "2" ∧ w = .tuple [] := by simpa using hv.symm
  obtain ⟨t, qs, prems, hm, _, _⟩ := hasTypCase_mem hc
  simp [bitCases] at hm

end Examples

/-! ## Scope: what is proved, what deviates, and what is missing

### The metatheory that is here

1. **Monotonicity in fuel** — `monoTypAt_of_le`, one structural induction over
   the fuel covering all seven members of the mutual block, with the
   per-member corollaries `hasTyp_ok_of_le` … `hasTypInsts_ok_of_le`.  This is
   what makes `HasTyp env ρ t v := ∃ n, hasTyp n env ρ t v = .ok true`
   sensible.
2. **Decidability given a bound** — `hasTyp_iff_of_ok`: a definite answer at
   *any* fuel level settles the proposition, with `decidableHasTyp` as the
   instance it yields and `not_hasTyp_of_ok_false` for the negative side.
   `HasTyp` itself is an existential over the fuel and is not claimed
   decidable outright.
3. **Compositionality** — one `iff` per clause: `hasTyp_boolT_iff`,
   `hasTyp_numT_iff`, `hasTyp_textT_iff`, `hasTyp_tupT_iff`,
   `hasTyp_iterT_opt_iff`, `hasTyp_iterT_list_iff`, `hasTyp_iterT_list1_iff`,
   `hasTyp_iterT_listN_iff`, `hasTyp_varT_local_iff`,
   `hasTyp_varT_global_iff`, and the auxiliaries `hasTypTup_nil_iff`,
   `hasTypTup_cons_iff`, `hasTypList_iff`, `hasTypDef_aliasT_iff`,
   `hasTypDef_structT_iff`, `hasTypDef_variantT_iff`, `hasTypFields_nil_iff`,
   `hasTypFields_cons_iff`, `hasTypCase_cons_hit_iff`,
   `hasTypCase_cons_miss_iff` and `hasTypInsts_cons_inv`.
4. **Inversion** — `hasTypCase_mem` (an inhabitant of a variant is an
   injection by a *declared* case, and its payload and premises are the ones
   that case asks for), `hasTypTup_length`, `hasTypFields_length`, and the two
   that see through a type name: `hasTyp_varT_case_of_variant` and
   `hasTyp_varT_struct_of_struct`.
5. **Type soundness, for the determined fragment** — see the `Soundness`
   section's own note.  Precisely: `evalExp_boolE_hasTyp`,
   `evalExp_numE_hasTyp`, `evalExp_textE_hasTyp`, `evalExp_cmpE_hasTyp`,
   `evalExp_memE_hasTyp` and `evalExp_lenE_hasTyp` are unconditional;
   `evalExp_listE_hasTyp`, `evalExp_optE_hasTyp`, `evalExp_tupE_hasTyp`,
   `evalExp_caseE_hasTypDef` and `evalExp_strE_hasTypDef` are conditional on
   the components.

### The metatheory that is *not* here

* **No preservation theorem for the whole language.**  `CallE`, `IterE`,
  `UpdE`/`ExtE`, `CompE`, `SubE`, `CvtE`, the projections and the paths are
  not covered: each needs the *expression* typing judgment that
  `spectec/src/il/valid.ml` carries in the `typ` note, and the `--ast` printer
  erases that note (`docs/projects/spectec/README.md`).  Recovering it means adding the typing
  layer that `Sem/Valid.lean` deliberately omits — the expected type on
  `checkExp`/`checkPath`/`checkArg`, and `reduceTyp`/`equivTyp`/`subTyp`; the
  statement to prove once it is there is "if `valid_exp env e t` and
  `evalExp n env ρ e = .ok v` then `HasTyp env ρ t v`", under a hypothesis
  relating `ρ` to `env`.
* **No subtyping theorem.**  `Eval.sub_typ` (`eval.ml:1253-1288`) is not
  transcribed, so "`sub_typ t₁ t₂` implies `HasTyp … t₁ v → HasTyp … t₂ v`"
  is open, and `Sem/Valid.lean` does not supply it.  It belongs with the
  typing layer, because `sub_typ` needs `equiv_typ`, which needs `equiv_exp`,
  which calls the evaluator (`eval.ml:1189-1202`).
* **No type-equivalence theorem.**  Likewise `equiv_typ t₁ t₂` implying that
  `HasTyp … t₁` and `HasTyp … t₂` are the same subset of `Value`.
* **Inhabitants of a `varT` are not characterized when the instances
  disagree.**  `hasTyp_varT_case_of_variant` assumes *every* instance of the
  family unfolds to a variant.  A family mixing an `AliasT` instance with a
  `VariantT` one — which `valid.ml` permits — has no inversion lemma here.
* **A premise that is a `RulePr` can starve.**  `premsOk` reports `outOfFuel`
  whenever `Sem/Eval.lean`'s `derives` has not yet found a derivation, so
  `hasTyp` on a variant case guarded by a relational premise is undecided at
  every finite budget at which the derivation has not been found.  That is the
  honest reading of a step-indexed least fixpoint, not a gap in the proofs,
  but it does mean `hasTyp_iff_of_ok` is vacuous for such a case until the
  budget is large enough.
-/

end Silmaril.SpecTec.Sem
