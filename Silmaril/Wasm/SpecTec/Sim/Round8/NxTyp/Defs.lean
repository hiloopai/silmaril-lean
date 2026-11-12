module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSites.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Defs

/-!
# Round 8, REH route 2: typing goes to the erased side without a swap set

Round 7's `Round7.EraseDer.TypFwd` moves `Sem.HasTyp` across export erasure (`Swap.eraseV`), but
only on a swap set `Q` on which erasure is injective (its proof uses round 3's
`EraseAll.eraseAt`, which needs `QInj`). This topic drops the swap set.

The expressions inside the reachable types are few and small (bounds such as `i < 2^N`, type
arguments such as `uN(N)`, the defining conjuncts of case quantifiers). In the fixed script they
read only variables whose declared types are export-free (`NxSites.nxAT`). An export-free value is
its own erasure, so such an expression evaluates alike on the original and the erased scope, with
no evaluator-level erasure argument at all (`Sem.evalExp_agreeOn`). The check `nTy A t` says this
syntactically:

* `A` is the list of term variables that are bound to the same value on both sides. At a rule
  instance, `A` is the rule's quantifiers of export-free type (`nxNames`); inside a type instance
  both sides share the instance's scope, and `A` is the instance's quantifiers.
* every expression of `t` (a `ListN` bound, an expression argument of a type name) reads only
  variables of `A`;
* a tuple binder of export-free type extends `A`; any other binder is removed from it;
* type arguments are closed, export-free and checked;
* a record field or variant case that has premises or quantifiers carries an export-free type.
  Its value is then its own erasure, so the premises are read on the same scope and value on both
  sides. The `EXPORTS` field of `moduleinst` has type `exportinst*` and no premises, as in round
  7's `xTFields`.

`nTypMap tyB` checks every type of `tyB`, and `nRelQuants` the quantifier types of every rule of
every relation `Step` reaches. The kernel checks both on the fixed script
(`Round8.NxTyp.nTypMap_fixed`, `nRelQuants_fixed`).

`TypFwdN` is the transfer: a `Sim.QuantsOk`-typed rule instance stays typed on the erased scope.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (nxAT toAT sigFixed)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn isExpT)

/-- `t` is export-free in round 6's signature. -/
def nxT (t : Typ) : Bool := nxAT sigFixed.good (toAT t)

mutual
/-- **The check on a type**: its expressions read only the variables `A`, which agree on both
sides; the type names it uses are in `S`. -/
def nTy (S A : List String) : Typ → Bool
  | .varT x args => S.contains x && nTyArgs S A args
  | .tupT bs => nTyBinds S A bs
  | .iterT t it => nTy S A t && nIter A it
  | _ => true

/-- `nTy` on the arguments of a type name: closed, checked, export-free type arguments, and
expression arguments over `A`. -/
def nTyArgs (S A : List String) : List Arg → Bool
  | [] => true
  | .typA t :: r => varsIn [] (freeTyp t) && nTy S [] t && nxT t && nTyArgs S A r
  | .expA e :: r => varsIn A (freeExp e) && nTyArgs S A r
  | _ :: _ => false

/-- `nTy` on tuple binders: an export-free binder joins `A`, any other leaves it (the wildcard
`_` binds nothing, so it never joins). -/
def nTyBinds (S A : List String) : List TypBind → Bool
  | [] => true
  | .mk x t :: bs =>
    nTy S A t && nTyBinds S (if nxT t && x != "_" then x :: A else A.filter (· != x)) bs

/-- The bound of a `ListN` iteration reads only `A`. -/
def nIter (A : List String) : Iter → Bool
  | .listN e _ => varsIn A (freeExp e)
  | _ => true
end

/-- Record fields: `EXPORTS` has type `exportinst*` and no premises; every other field is
checked, and carries an export-free type if it has premises. -/
def nFields (S A : List String) : List TypField → Bool
  | [] => true
  | .mk a t qs prems :: fs =>
    (if a == "EXPORTS" then isExpT t && prems.isEmpty
      else nTy S A t && (prems.isEmpty && qs.isEmpty || nxT t)) && nFields S A fs

/-- Variant cases: checked, with an export-free payload type if the case has premises or
quantifiers. -/
def nCases (S A : List String) : List TypCase → Bool
  | [] => true
  | .mk _ t qs prems :: cs => nTy S A t && (prems.isEmpty && qs.isEmpty || nxT t) && nCases S A cs

/-- A type definition's body. -/
def nDefTyp (S A : List String) : DefTyp → Bool
  | .aliasT t => nTy S A t
  | .structT fs => nFields S A fs
  | .variantT cs => nCases S A cs

/-- The instances of a type family, each over its own quantifiers. -/
def nInsts (S : List String) (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD qs _ dt => nDefTyp S (Determ.quantNames qs) dt

/-- **Every type of `m` named in `S` is checked.** -/
def nTypMap (S : List String) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || nInsts S p.2.2

/-- The quantifiers of export-free type. -/
def nxNames (qs : List Param) : List String :=
  qs.filterMap fun q => match q with
    | .expP x t => if nxT t then some x else none
    | _ => none

/-- **The quantifier types of every rule `Step` reaches are checked**, over the rule's quantifiers
of export-free type. -/
def nRelQuants (S : List String) (m : Map RelDef) : Bool :=
  m.all fun p => !Script.stepReach.contains (0, p.1) || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ _ _ => qs.all fun q => match q with
      | .expP _ t => nTy S (nxNames qs) t
      | _ => true

/-! ## The statement -/

/-- **Typing of a rule instance goes to the erased side**: in a rule of a relation `Step`
reaches, quantifiers that `Sim.QuantsOk` types in the instance's scope are typed in its erased
scope. No swap set. -/
def TypFwdN (env : Env) : Prop :=
  ∀ {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp} {prems : List Prem}
    {σ : List (IL.Id × Value)},
    Script.stepReach.contains (0, x) = true → env.findRel? x = some (ps, op, t, rules) →
    rules[i]? = some (.ruleD nm qs op' e prems) →
    QuantsOk env (VarEnv.empty.bindVals σ) qs →
    QuantsOk env (Erase.eraseScope (VarEnv.empty.bindVals σ)) qs

end Silmaril.Wasm.SpecTec.Sim.Round8.NxTyp
