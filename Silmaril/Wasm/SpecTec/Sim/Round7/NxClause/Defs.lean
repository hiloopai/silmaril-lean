module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs

/-!
# Round 8, REH route 2: the clause half of the erasure copy

`Round7.NxErase` proved the expression half of round 3's `EraseAll.eraseAt` without a swap set
(`NxErase.nAt`) and froze the clause half as `NxErase.Task.clauseErase`: clause bodies commute
with export erasure (`Swap.eraseV`) at every checked call. This header states what its proof
uses.

**Argument patterns without types.** A clause's argument patterns are matched against the call's
evaluated arguments (`Sem.matchArgs`). Matching compares values only where a pattern variable is
already bound, or where a pattern is evaluated (`matchDefault`, and `patLen` for the split of a
concatenation). The comparisons read alike before and after erasure if one side is export-free
(`NxSites.eraseV_eq_iff_of_nx`). `linE vnx st e` checks that this is so without reading types:

* `st = (bd, nb)`: `bd` may be bound so far, and the variables of `nb` hold export-free values
  if they are bound. `vnx` says that the matched value is export-free: below an export-free
  argument (`nxP`), below the bound of a `ListN` pattern (a number) or below the elements of an
  iteration whose body leaves its domain variables in `nb`.
* A variable that may be bound may occur again only if `vnx` holds or it is in `nb`. A variable
  bound to a value not known to be export-free leaves `nb`.
* No pattern is evaluated (`matchDefault`) except at the lengths `patLen` reads for the split of
  a concatenation (`lenOk`), and those are `simpleE` expressions (variables, literals, `unE`,
  `cvtE` and iterations of them), whose evaluation commutes with erasure with no hypothesis.

The invariant of the proof is `Inv gd ρ st`: the wildcard is unbound, the bound variables of `ρ`
are in `bd`, those of `nb` hold export-free values, and the definition variables of `ρ` satisfy
`gd`.

**Premises.** Reachable clauses have premises `if e`, `otherwise`, and `(if e)^iter` only
(`premY`; no relation premise, no `let`), with `NxFlow.auxE` on the expressions they evaluate.

**The kernel check** `yItems`: every definition of `EraseAll.gdE` has a parameter entry in
`NxTyped.tsigFixed`, and its clauses pass `clauseY` (both of the above).

**The statement** `DefsE env n`: at fuel `n`, the clauses of a `gdE` definition applied to
conforming arguments (`NxSound.ArgsVT` at `NxSound.parV`) answer the erased value on the erased
arguments. `Round7.NxClause.defsE_all` proves it at every fuel in `utf8Env B`, and
`Round7.NxClause.clauseErase` derives `NxErase.Task.clauseErase` from it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV nxB eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (ER ArgIn DefsG)

/-! ## Simple expressions -/

mutual
/-- **An expression whose evaluation commutes with erasure unconditionally**: variables,
literals, `unE`, `cvtE`, and iterations of these over simple domains. -/
def simpleE : Exp → Bool
  | .varE _ => true
  | .boolE _ => true
  | .numE _ => true
  | .textE _ => true
  | .unE _ _ e => simpleE e
  | .cvtE e _ _ => simpleE e
  | .iterE e (.mk it ds) => simpleI it && simpleE e && simpleDs ds
  | _ => false

/-- `simpleE` on the bound of a `ListN` iteration. -/
def simpleI : Iter → Bool
  | .listN e _ => simpleE e
  | _ => true

/-- `simpleE` on iteration domains. -/
def simpleDs : List Dom → Bool
  | [] => true
  | .mk _ e :: ds => simpleE e && simpleDs ds
end

/-- **The lengths `Sem.patLen` reads are simple**: a list literal, a concatenation of such, the
bound of a `ListN` iteration, or a simple expression. -/
def lenOk : Exp → Bool
  | .listE _ => true
  | .catE e₁ e₂ => lenOk e₁ && lenOk e₂
  | .iterE _ (.mk (.listN eₙ _) _) => simpleE eₙ
  | e => simpleE e

/-- A list literal, whose `patLen` never fails. -/
def isListE : Exp → Bool
  | .listE _ => true
  | _ => false

/-! ## Linear patterns -/

/-- **The state of the pattern check**: the variables bound so far, and those of them bound to
export-free values. -/
abbrev LSt := List String × List String

mutual
/-- **The pattern check**; see the module docstring. `none` is a failure. -/
def linE (vnx : Bool) (st : LSt) : Exp → Option LSt
  | .varE x =>
    if st.1.contains x then
      (if vnx then some st else if st.2.contains x then some (st.1, st.2.filter (· != x)) else none)
    else some (x :: st.1, if vnx then x :: st.2 else st.2.filter (· != x))
  | .boolE _ => some st
  | .numE _ => some st
  | .textE _ => some st
  | .optE none => some st
  | .tupE es => linEs vnx st es
  | .listE es => linEs vnx st es
  | .projE e i => if i = 0 then linE vnx st e else none
  | .caseE _ e => linE vnx st e
  | .uncaseE e _ => linE vnx st e
  | .optE (some e) => linE vnx st e
  | .strE fs => linFs vnx st fs
  | .catE e₁ e₂ =>
    if lenOk e₁ && (isListE e₁ || lenOk e₂) then
      match linE vnx st e₁ with
      | some st₁ => linE vnx st₁ e₂
      | none => none
    else none
  | .subE e _ _ => linE vnx st e
  | .iterE e (.mk it ds) =>
    match linI st it with
    | some (st₀, stb) =>
      match linE vnx stb e with
      | some st₁ => linDs ((ds.map domVar).all fun x => st₁.2.contains x) st₀ ds
      | none => none
    | none => none
  | _ => none

/-- `linE` on a list, left to right. -/
def linEs (vnx : Bool) (st : LSt) : List Exp → Option LSt
  | [] => some st
  | e :: es =>
    match linE vnx st e with
    | some st₁ => linEs vnx st₁ es
    | none => none

/-- `linE` on record fields, none named `EXPORTS`. -/
def linFs (vnx : Bool) (st : LSt) : List ExpField → Option LSt
  | [] => some st
  | .mk a e :: fs =>
    if a = "EXPORTS" then none
    else
      match linE vnx st e with
      | some st₁ => linFs vnx st₁ fs
      | none => none

/-- The bound of a `ListN` pattern is matched against a number; the result is the state after it
and the state the body starts from (with the counter, bound to a number). -/
def linI (st : LSt) : Iter → Option (LSt × LSt)
  | .listN e ido =>
    match linE true st e with
    | some s =>
      some (s, match ido with
        | some y => (y :: s.1, y :: s.2)
        | none => s)
    | none => none
  | _ => some (st, st)

/-- `linE` on the sources of iteration domains, left to right. -/
def linDs (vnx : Bool) (st : LSt) : List Dom → Option LSt
  | [] => some st
  | .mk _ e :: ds =>
    match linE vnx st e with
    | some st₁ => linDs vnx st₁ ds
    | none => none
end

/-- **An export-free parameter**: an expression parameter whose type is export-free in `sigX` and
does not mention the type parameter `X`. -/
def nxP : Param → Bool
  | .expP _ t => nxAT sigX.good (toAT t) && xFree (toAT t)
  | _ => false

/-- `linE` on argument patterns; the flags say which arguments are export-free. -/
def linA : List Bool → LSt → List Arg → Option LSt
  | _, st, [] => some st
  | fl, st, .expA e :: xs =>
    match linE (fl.head?.getD false) st e with
    | some st₁ => linA fl.tail st₁ xs
    | none => none
  | fl, st, _ :: xs => linA fl.tail st xs

/-! ## Premises -/

/-- **A premise of a reachable clause**: `if e`, `otherwise`, or `(if e)^iter`, with
`NxFlow.auxE` on what it evaluates and distinct domain variables. -/
def premY (c : AuxCtx) : Prem → Bool
  | .ifPr e => auxE c e
  | .elsePr => true
  | .iterPr (.ifPr e) (.mk it ds) =>
    auxE c e && nodupB (ds.map domVar) && auxI c it && auxD c ds
  | _ => false

/-! ## The check on the script -/

/-- **One clause passes**: its argument patterns pass `linA` from the export-free parameters, and
its premises pass `premY`. -/
def clauseY (ps : List Param) : Clause → Bool
  | .defD qs args _ prems =>
    (linA (ps.map nxP) ([], []) args).isSome &&
      prems.all (premY (typParams ps, (defQuants qs).map (·.1)))

mutual
/-- **One top-level definition passes**: a definition of `EraseAll.gdE` has a parameter entry in
`tsigFixed`, and its clauses pass `clauseY`. -/
def yItem : Def → Bool
  | .decD f ps _ clauses =>
    !EraseAll.gdE f || ((tsigFixed.params.lookup f).isSome && clauses.all (clauseY ps))
  | .recD ds => yItems ds
  | _ => true

/-- `yItem` on a list. -/
def yItems : List Def → Bool
  | [] => true
  | d :: ds => yItem d && yItems ds
end

/-! ## The invariant of matching -/

/-- **The invariant of the pattern check at runtime**: the wildcard is unbound, the bound variables
of `ρ` are among `st.1`, those of `st.2` hold export-free values, and the definition variables of
`ρ` satisfy `gd`. -/
structure Inv (gd : String → Bool) (ρ : VarEnv) (st : LSt) : Prop where
  wild : ρ.findVal? "_" = none
  dom : ∀ x w, ρ.findVal? x = some w → st.1.contains x = true
  nx : ∀ x w, st.2.contains x = true → ρ.findVal? x = some w → nxB w = true
  defs : DefsG gd ρ

/-! ## The statement -/

/-- **Clause bodies commute with erasure at fuel `n`**: the clauses of a `gdE` definition, applied
to conforming arguments, answer the erased value on the erased arguments. -/
def DefsE (env : Env) (n : Nat) : Prop :=
  ∀ (f : String) (d : DefDef) (pts : List PT) (ws : List ArgV),
    EraseAll.gdE f = true → env.findDef? f = some d →
    NxSound.parV sigX tsigFixed f ws = some pts → NxSound.ArgsVT sigX tsigFixed ws pts →
    (∀ w ∈ ws, ArgIn QT EraseAll.gdE w) →
    ER eraseV (Swap.AllIn QT) (tryClauses n env d.2.2 ws) (tryClauses n env d.2.2 (ws.map eraseA))

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
