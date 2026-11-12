module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs

/-!
# Round 9, RE: `otherwise` pairs whose earlier rule has an `Expand` premise (definitions)

Round 9 pass 1 (`Round9.ElseBwd`) proved the backward firing `PairReflectB` along export erasure
at 85 of the 94 pairs of `elsePairs`; 9 were left (`ElseBwd.leftPairs''`). Four of them have an
earlier rule with a relation premise `Expand: $type(z, x) ~~ ARRAY (mut? zt)`:

* `(101, 100)`, `(102, 100)`: `array.init_data-zero`/`-num` against `array.init_data-oob2`;
* `(102, 101)`: `array.init_data-num` against `array.init_data-zero`, an `otherwise` rule whose
  own earlier rules include rule 100;
* `(92, 91)`: `array.copy-gt` against `array.copy-le`, an `otherwise` rule with an `Expand`
  premise, whose own earlier rules include the chain rule `array.copy-zero` (90).

The relation premise is read the same way on both sides. Its asserted expression is
export-free (`NxSites.nxE`): `$type(z, x)` is a defined type and `mut?`, `zt` are export-free
quantifiers. So in an instance of rule `j` the value of the expression is its own erasure, and
the erased-side derivation of `Expand` is a derivation on the original side too.

* `premR qs pr`: the premises allowed in a rule `j` read backward or forward: `if` as in
  `ElseBwd.simpleRuleE`, `otherwise`, and a relation premise `y [] c` without arguments whose
  expression `c` passes round 3's check and `nxE`.
* `simpleRuleR`: `ElseBwd.simpleRuleE` with those relation premises allowed.
* `expPairs`, `expChainPairs`, `expChain2Pairs`: the four pairs, by the argument they need.
* `leftPairs3`, `ElseBwdBLeft3`: the 5 pairs left after them (the four `Ref_ok` pairs and
  `(21, 9)`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

/-- **A premise of a rule read across erasure**: an `if` that passes round 3's check and is not a
binding site, `otherwise`, or a relation premise without arguments whose expression passes round
3's check and is export-free (`NxSites.nxE`). -/
def premR (qs : List Param) : Prem → Bool
  | .ifPr c => EraseAll.xExp EraseAll.grE EraseAll.gdE c &&
      !NxSites.bindSite NxTyped.sigX (NxSites.quantsΓ qs) (.ifPr c)
  | .elsePr => true
  | .rulePr _ [] _ c => EraseAll.xExp EraseAll.grE EraseAll.gdE c &&
      NxSites.nxE NxTyped.sigX (NxSites.quantsΓ qs) c
  | _ => false

/-- **`ElseBwd.simpleRuleE` with export-free relation premises.** -/
def simpleRuleR : Rule → Bool
  | .ruleD _ qs _ e prems =>
    (Round6.Reading.conclAlts e).all (fun e' => match cfgVar e' with
      | some (z, _) => lhsOk qs e' && quantsNx qs z && EraseAll.xExp EraseAll.grE EraseAll.gdE e'
      | none => false) &&
    prems.all (premR qs)

/-- **The `Expand` pairs**: `array.init_data-zero` and `array.init_data-num` against
`array.init_data-oob2`. The earlier rule has no `otherwise` premise. -/
def expPairs : List (Nat × Nat) := [(101, 100), (102, 100)]

/-- **The `Expand` chain pair**: `array.init_data-num` against `array.init_data-zero`, whose own
earlier rules are, against 102, head-differing, adjacency-clashing, simple or rule 100. -/
def expChainPairs : List (Nat × Nat) := [(102, 101)]

/-- **The `Expand` chain pair of the second level**: `array.copy-gt` against `array.copy-le`, whose
own earlier rules include the first-level chain rule `array.copy-zero` (90). -/
def expChain2Pairs : List (Nat × Nat) := [(92, 91)]

/-- The rule list of every `Step_read` entry of `m`: at each of the four pairs, the `otherwise`
rule has `lhsRule` and the earlier rule passes `simpleRuleR`; rule 100 has no `otherwise`
premise. -/
def expPairsIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Step_read" ||
    ((expPairs ++ expChainPairs ++ expChain2Pairs).all fun q =>
      match p.2.2.2.2[q.1]?, p.2.2.2.2[q.2]? with
      | some ri, some rj => lhsRule ri && simpleRuleR rj
      | _, _ => false) &&
    match p.2.2.2.2[100]? with
    | some r => !hasElse r
    | none => false

/-- **The pairs left after the `Expand` pairs** (5): the four `Ref_ok` pairs and `(21, 9)`. -/
def leftPairs3 : List (Nat × Nat) := [(3, 2), (5, 4), (21, 9), (66, 65), (68, 67)]

/-- **`ElseBwdB` at the 5 pairs of `leftPairs3`** (RE). -/
def ElseBwdBLeft3 (env : Env) : Prop :=
  ∀ p ∈ leftPairs3, PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

/-! ## `(21, 9)`: the handler's instructions -/

/-- The one instruction `o (n, cs, body)` of a conclusion `(z; [o (n, cs, body)], rhs)`:
`(o, body)`. -/
def cfgInner : Exp → Option (MixopS × Exp)
  | .tupE [.caseE op (.tupE [_, .listE [.caseE o (.tupE [_, _, body])]]), _] =>
    if op = "%;%" then some (o, body) else none
  | _ => none

/-- The heads of a list literal of constructors. -/
def litHeads : Exp → Option (List MixopS)
  | .listE es => es.mapM instrHead
  | _ => none

/-- The constructor in the middle of `pre ++ [o …] ++ suf`. -/
def midHead : Exp → Option MixopS
  | .catE (.catE _ (.listE [.caseE o _])) _ => some o
  | _ => none

/-- **The inner instructions cannot line up**: every conclusion alternative of `ri` holds one
instruction `o (n, cs, body)` whose body is a list literal of constructors, every one of `rj` one
instruction whose body is `pre ++ [o' …] ++ suf`, and `o'` is not among the heads of `ri`'s body. -/
def innerDiffer : Rule → Rule → Bool
  | .ruleD _ _ _ e₁ _, .ruleD _ _ _ e₂ _ =>
    (Round6.Reading.conclAlts e₁).all fun a => (Round6.Reading.conclAlts e₂).all fun b =>
      match cfgInner a, cfgInner b with
      | some (_, b₁), some (_, b₂) => match litHeads b₁, midHead b₂ with
        | some hs, some o => !hs.contains o
        | _, _ => false
      | _, _ => false

/-- **The pair with nested instructions**: `throw_ref-handler-next` against
`return_call_ref-handler`. The handler of rule 21 holds `REF.EXN_ADDR a; THROW_REF`; that of
rule 9 holds a `RETURN_CALL_REF`. -/
def innerPairs : List (Nat × Nat) := [(21, 9)]

/-- The rule list of every `Step_read` entry of `m` has `innerDiffer` at every pair of
`innerPairs`. -/
def innerPairsIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Step_read" || innerPairs.all fun q =>
    match p.2.2.2.2[q.1]?, p.2.2.2.2[q.2]? with
    | some ri, some rj => innerDiffer ri rj
    | _, _ => false

/-- **The pairs left after the `Expand` pairs and `(21, 9)`** (4): the `Ref_ok` pairs. -/
def refPairs : List (Nat × Nat) := [(3, 2), (5, 4), (66, 65), (68, 67)]

/-- **`ElseBwdB` at the 4 `Ref_ok` pairs** (RE). -/
def ElseBwdBRef (env : Env) : Prop :=
  ∀ p ∈ refPairs, PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
