module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxErase.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.Defs

/-!
# Round 9, RE: the four `Ref_ok` pairs (definitions)

At `(3, 2)`, `(5, 4)`, `(66, 65)` and `(68, 67)` the earlier rule (`br_on_cast-succeed`,
`br_on_cast_fail-succeed`, `ref.test-true`, `ref.cast-succeed`) is

```
s; f; ref I  ~>  R    -- Ref_ok: s |- ref : $inst_reftype(f.MODULE, rt)
```

Its state is the pair `s; f` (store and frame), both of which carry export lists, and its premise
is a derivation of `Ref_ok` at the store. Reading it backward needs two things:

* **`Ref_ok` backward across erasure of the store** (`refRule`, `refRelIs`). Every rule of
  `Ref_ok` concludes `(s, e₂, e₃)` with `s` its one `store` quantifier, all other quantifiers of
  export-free type, and `e₂`, `e₃` reading only those; its premises are `if`s and relation
  premises on export-free expressions (`closedX`, read across erasure by round 7's equation
  `NxErase.erase_closed`), and `Ref_ok` premises of the same shape `(s, e₂', e₃')`. So a derivation
  of `Ref_ok` at `(eraseV sv, r, t)` gives one at `(sv, r, t)`, by rebinding `s` to `sv` at every
  rule.
* **The earlier rule read backward with both `s` and `f` rebound** (`cfgSF`, `lhsOkSF`,
  `refRuleJ`): its premise is `Ref_ok: (s, e₂, e₃)` with `e₂` reading export-free quantifiers
  and `e₃` (`$inst_reftype(f.MODULE, rt)`) export-free (`NxSites.nxE`).

The `otherwise` rules (3, 5, 66, 68) have the same left-hand side `s; f; L` (`lhsRuleSF`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

/-! ## Quantifiers and expressions -/

/-- The IL type named `n`, without arguments. -/
def isVarT (n : String) : Typ → Bool
  | .varT x [] => x == n
  | _ => false

/-- `z` is an expression quantifier of `qs`, and every quantifier named `z` has type `n`. -/
def typQ (qs : List Param) (z : IL.Id) (n : String) : Bool :=
  (Determ.quantNames qs).contains z && qs.all fun q => match q with
    | .expP x t => x != z || isVarT n t
    | _ => true

/-- Every quantifier is an expression quantifier of a named type without arguments. -/
def quantsVar (qs : List Param) : Bool :=
  qs.all fun q => match q with
    | .expP _ (.varT _ []) => true
    | _ => false

/-- Every quantifier is an expression quantifier, of export-free type unless it is in `zs`. -/
def quantsNxL (qs : List Param) (zs : List IL.Id) : Bool :=
  qs.all fun q => match q with
    | .expP x t => zs.contains x || Round8.NxTyp.nxT t
    | _ => false

/-- `e` reads only quantifiers of export-free type. -/
def nxIn (qs : List Param) (e : Exp) : Bool :=
  EraseDer.varsIn (Round8.NxTyp.nxNames qs) (freeExp e)

/-- **A closed expression that commutes with erasure**: the hypotheses of round 7's
`NxErase.erase_closed`, as a check. -/
def closedX (qs : List Param) (e : Exp) : Bool :=
  EraseDer.varsIn (Determ.quantNames qs) (freeExp e) &&
    NxTyped.tyOk NxTyped.sigX NxTyped.tsigFixed (NxSites.quantsΓ qs) e &&
    NxFlow.auxE NxRule.ctx0 e && NxErase.auxX NxRule.ctx0 e &&
    NxSites.badE NxTyped.sigX (NxSites.quantsΓ qs) e == 0 &&
    EraseAll.xExp EraseAll.grE EraseAll.gdE e && !(Determ.quantNames qs).contains "_"

/-- `closedX`, and export-free. -/
def closedNx (qs : List Param) (e : Exp) : Bool :=
  closedX qs e && NxSites.nxE NxTyped.sigX (NxSites.quantsΓ qs) e

/-! ## `Ref_ok` -/

/-- A triple `(s, e₂, e₃)` with `e₂`, `e₃` reading only export-free quantifiers. -/
def refConcl (qs : List Param) (s : IL.Id) : Exp → Bool
  | .tupE [.varE s', e₂, e₃] => s' == s && nxIn qs e₂ && nxIn qs e₃
  | _ => false

/-- **A premise of a `Ref_ok` rule**: a closed `if`, a `Ref_ok` premise `(s, e₂, e₃)`, or another
relation premise without arguments on a closed, export-free expression. -/
def refPrem (qs : List Param) (s : IL.Id) : Prem → Bool
  | .ifPr c => closedX qs c
  | .rulePr y [] _ c => if y == "Ref_ok" then refConcl qs s c else closedNx qs c
  | _ => false

/-- **A rule of `Ref_ok` read backward across erasure of its store**: every conclusion alternative
is `(s, e₂, e₃)` with `s` the one `store` quantifier, every other quantifier of export-free named
type, and every premise passes `refPrem`. -/
def refRule : Rule → Bool
  | .ruleD _ qs _ e prems => (Round6.Reading.conclAlts e).all fun e' => match e' with
    | .tupE [.varE s, _, _] => typQ qs s "store" && quantsNxL qs [s] && quantsVar qs &&
        !(Round8.NxTyp.nxNames qs).contains s && refConcl qs s e' && prems.all (refPrem qs s)
    | _ => false

/-- The `Ref_ok` entry of `m` has no parameters and every rule passes `refRule`. -/
def refRelIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Ref_ok" || (p.2.1.isEmpty && p.2.2.2.2.all refRule)

/-! ## The earlier rules and the pairs -/

/-- A conclusion `((s; f); L, R)` whose state is a pair of variables: `(s, f, L)`. -/
def cfgSF : Exp → Option (IL.Id × IL.Id × Exp)
  | .tupE [.caseE op (.tupE [.caseE op' (.tupE [.varE s, .varE f]), l]), _] =>
    if op = "%;%" ∧ op' = "%;%" then some (s, f, l) else none
  | _ => none

/-- **A left-hand side `s; f; L`** with `s` a `store` and `f` a `frame` quantifier and `L`
reading only quantifiers of export-free type. -/
def lhsOkSF (qs : List Param) (e : Exp) : Bool :=
  match cfgSF e with
  | some (s, f, l) => typQ qs s "store" && typQ qs f "frame" && s != f && nxIn qs l &&
      !(Round8.NxTyp.nxNames qs).contains s && !(Round8.NxTyp.nxNames qs).contains f
  | none => false

/-- Every conclusion alternative of a rule has a left-hand side `s; f; L` and passes round 3's
check. -/
def lhsRuleSF : Rule → Bool
  | .ruleD _ qs _ e _ => (Round6.Reading.conclAlts e).all fun e' =>
    lhsOkSF qs e' && EraseAll.xExp EraseAll.grE EraseAll.gdE e'

/-- **The premise of a `Ref_ok` rule `j`**: `Ref_ok: (s, e₂, e₃)` with `e₂` reading export-free
quantifiers and `e₃` closed and export-free. -/
def refPremJ (qs : List Param) (s : IL.Id) : Prem → Bool
  | .rulePr y [] _ (.tupE [.varE s', e₂, e₃]) =>
    y == "Ref_ok" && s' == s && nxIn qs e₂ && closedNx qs e₃
  | _ => false

/-- **An earlier rule `s; f; L ~> R -- Ref_ok: …`**, read backward with `s` and `f` rebound. -/
def refRuleJ : Rule → Bool
  | .ruleD _ qs _ e prems => (Round6.Reading.conclAlts e).all (fun e' => match cfgSF e' with
    | some (s, f, _) => lhsOkSF qs e' && quantsNxL qs [s, f] && quantsVar qs &&
        EraseAll.xExp EraseAll.grE EraseAll.gdE e' && prems.all (refPremJ qs s)
    | none => false)

/-- The rule list of every `Step_read` entry of `m`: at each `Ref_ok` pair the `otherwise` rule
has `lhsRuleSF` and the earlier rule passes `refRuleJ`. -/
def refPairsIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Step_read" || ElseExp.refPairs.all fun q =>
    match p.2.2.2.2[q.1]?, p.2.2.2.2[q.2]? with
    | some ri, some rj => lhsRuleSF ri && refRuleJ rj
    | _, _ => false

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseRef
