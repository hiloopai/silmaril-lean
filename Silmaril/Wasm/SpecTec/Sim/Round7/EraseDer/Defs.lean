module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Det.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Defs

/-!
# Round 7, the export swap: moving derivations across erasure (round 4, pass 1)

Item 4 of the plan for `Round7.Swap.Task.stepErase`: a `DDerivesB` derivation at a swap-set input
gives one at the erased input, and back. The evaluator commutes with erasure on scopes whose term
bindings are all in the swap set (`Round7.EraseAll.eraseAt`). A rule instance's scope may bind
other names to anything, so the two scopes are related only on the free variables that matter.

* `ErRel Q gd S ρ ρ'`: on the identifiers `S`, `ρ` agrees with its swap-set part `aiPart Q ρ`,
  and `ρ'` agrees with the erasure of that part; `ρ`'s definition variables satisfy `gd`. On
  `S`, `ρ'` is `ρ` with every binding erased, and every binding `ρ` has there is in the swap set.
* `closedRels m`: every rule of every relation `Step` reaches is closed over its quantifiers: the
  free term variables of every conclusion alternative, of every premise and of every quantifier
  type are quantifiers of the rule. The kernel checks it for the fixed wasm-3.0 script
  (`Round7.EraseDer.closedRels_fixed`).
* `EImg Q r`: `r` is the erasure of a record of `Q`. The values `AllIn (EImg Q)` are the erasures
  of the values `AllIn Q` (`Round7.EraseDer.allIn_eImg_iff`), and they are the swap set of the
  erased side.
* `TypFwd`, `TypBwd`: typing commutes with erasure on the swap set, at checked types
  (`xTy tyB`, which every quantifier type of a reachable rule is). These are the typing facts the
  transfer uses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV AllIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DefsG)

open Classical in
/-- The swap-set bindings of `ρ` (`Round7.EraseAll.aiPart`, restated so that this header does
not import the unrefined proofs). -/
noncomputable def aiPart (Q : Value → Prop) (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.filter fun p => decide (AllIn Q p.2) }

/-- **`ρ'` is the erasure of `ρ` on the identifiers `S`**, and `ρ`'s bindings there are in the
swap set. -/
structure ErRel (Q : Value → Prop) (gd : String → Bool) (S : Sets) (ρ ρ' : VarEnv) : Prop where
  /-- On `S`, `ρ` is its swap-set part. -/
  ai : VarEnv.AgreeOn S ρ (aiPart Q ρ)
  /-- On `S`, `ρ'` is the erasure of that part. -/
  er : VarEnv.AgreeOn S ρ' (eraseScope (aiPart Q ρ))
  /-- The definition variables of `ρ` are `gd`. -/
  defs : DefsG gd ρ

/-! ## The closure check -/

/-- Every free term variable of `s` is in `K`. -/
def varsIn (K : List IL.Id) (s : Sets) : Bool := decide (∀ x ∈ s.varid, x ∈ K)

/-- **A rule is closed over its quantifiers**: the free term variables of every conclusion
alternative, every premise and every quantifier type are quantifiers. -/
def ruleClosed : Rule → Bool
  | .ruleD _ qs _ e prems =>
    (Round6.Reading.conclAlts e).all (fun e' => varsIn (Determ.quantNames qs) (freeExp e')) &&
    prems.all (fun pr => varsIn (Determ.quantNames qs) (freePrem pr)) &&
    qs.all (fun q => match q with
      | .expP _ t => varsIn (Determ.quantNames qs) (freeTyp t)
      | _ => true)

/-- **Every rule of every relation `Step` reaches is closed.** -/
def closedRels (m : Map RelDef) : Bool :=
  m.all fun p => !Script.stepReach.contains (0, p.1) || p.2.2.2.2.all ruleClosed

/-! ## The erased side's swap set -/

/-- **`r` is the erasure of a record of `Q`.** -/
def EImg (Q : Value → Prop) (r : Value) : Prop := ∃ r₀, Q r₀ ∧ eraseV r₀ = r

/-! ## The check on types -/

mutual
/-- **A type over the names `S` whose expressions pass the evaluator-level check**; type arguments
are closed (no free term variables). -/
def xTy (S : List String) : Typ → Bool
  | .varT x args => S.contains x && xTyArgs S args
  | .tupT bs => xTyBinds S bs
  | .iterT t it => xTy S t && EraseAll.xIter EraseAll.grE EraseAll.gdE it
  | _ => true

/-- `xTy` on the arguments of a type reference. -/
def xTyArgs (S : List String) : List Arg → Bool
  | [] => true
  | .typA t :: r => xTy S t && varsIn [] (freeTyp t) && xTyArgs S r
  | .expA e :: r => EraseAll.xExp EraseAll.grE EraseAll.gdE e && xTyArgs S r
  | _ :: _ => false

/-- `xTy` on tuple binders. -/
def xTyBinds (S : List String) : List TypBind → Bool
  | [] => true
  | .mk _ t :: bs => xTy S t && xTyBinds S bs
end

/-- The type of `moduleinst`'s `EXPORTS` field, `exportinst*`. -/
def isExpT : Typ → Bool
  | .iterT (.varT "exportinst" []) .list => true
  | _ => false

/-- Record fields: an `EXPORTS` field has type `exportinst*` and no premises; every other field
is checked. -/
def xTFields (S : List String) : List TypField → Bool
  | [] => true
  | .mk a t _ prems :: fs =>
      (if a == "EXPORTS" then isExpT t && prems.isEmpty
        else xTy S t && EraseAll.xPrems EraseAll.grE EraseAll.gdE prems) && xTFields S fs

/-- Variant cases: carried type, quantifier types and premises. -/
def xTCases (S : List String) : List TypCase → Bool
  | [] => true
  | .mk _ t qs prems :: cs =>
      xTy S t && qs.all (fun q => match q with | .expP _ t => xTy S t | _ => true) &&
        EraseAll.xPrems EraseAll.grE EraseAll.gdE prems && xTCases S cs

/-- A type definition's body. -/
def xDefTyp (S : List String) : DefTyp → Bool
  | .aliasT t => xTy S t
  | .structT fs => xTFields S fs
  | .variantT cs => xTCases S cs

/-- A type definition's body declares a record field named `EXPORTS`. -/
def defTypExp : DefTyp → Bool
  | .structT fs => fs.any fun f => match f with | .mk a _ _ _ => a == "EXPORTS"
  | _ => false

/-- The instances of a type family: argument patterns and bodies; an instance whose body declares
an `EXPORTS` field has no argument patterns. -/
def xInsts (S : List String) (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD _ pats dt => EraseAll.xArgs EraseAll.grE EraseAll.gdE pats && xDefTyp S dt &&
        (!defTypExp dt || pats.isEmpty)

/-- **Every type of `m` named in `S` is checked.** The kernel checks it for the fixed wasm-3.0
script and `S := tyB` (`Round7.EraseDer.xTypMap_fixed`). -/
def xTypMap (S : List String) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || xInsts S p.2.2

/-- **The quantifier types of every rule `Step` reaches are checked.** -/
def xRelQuants (S : List String) (m : Map RelDef) : Bool :=
  m.all fun p => !Script.stepReach.contains (0, p.1) || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ _ _ => qs.all fun q => match q with
      | .expP _ t => xTy S t
      | _ => true

/-! ## Typing across erasure -/

/-- **Typing goes to the erased side**: a swap-set value of a checked type, typed in a scope
without type or definition variables (as a rule instance's is), has its erasure typed in an erased
scope. The hypothesis `ρ.defs = []` makes the statement independent of `gd`
(`Round7.EraseDer.typFwd_gd`). -/
def TypFwd (Q : Value → Prop) (gd : String → Bool) (env : Env) : Prop :=
  ∀ ρ ρ' t w, ErRel Q gd (freeTyp t) ρ ρ' → ρ'.typs = ρ.typs → ρ.typs = [] → ρ.defs = [] →
    ρ'.defs = ρ.defs → ρ'.grams = ρ.grams → xTy TypAgree.tyB t = true →
    AllIn Q w → HasTyp env ρ t w → HasTyp env ρ' t (eraseV w)

/-- **Typing comes back from the erased side**, at swap-set values. -/
def TypBwd (Q : Value → Prop) (gd : String → Bool) (env : Env) : Prop :=
  ∀ ρ ρ' t w, ErRel Q gd (freeTyp t) ρ ρ' → ρ'.typs = ρ.typs → ρ.typs = [] → ρ.defs = [] →
    ρ'.defs = ρ.defs → ρ'.grams = ρ.grams → xTy TypAgree.tyB t = true →
    AllIn Q w → HasTyp env ρ' t (eraseV w) → HasTyp env ρ t w

/-! ## The rules of `Step` outside the check (round 4, pass 2) -/

/-- The rules of `Step` that use an excluded name. -/
def excNames : List String :=
  ["call_ref-hostfunc-res", "call_ref-hostfunc-div", "table.grow-succeed", "memory.grow-succeed"]

/-- The rules of `Step` that test `$hostcall`. -/
def hostNames : List String := ["call_ref-hostfunc-res", "call_ref-hostfunc-div"]

open Round6.Reading (DPremB conclAlts otherwiseB) in
/-- **An instance of the rule `nm` of `Step` at a swap-set input goes to the erased side.** -/
def RuleFwd (Q : Value → Prop) (env : Env) (nm : IL.Id) : Prop :=
  ∀ {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat} {qs : List Param}
    {e e' : Exp} {prems : List Prem} {σ : List (IL.Id × Value)} {v : Value},
    env.findRel? "Step" = some (ps, op, t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    e' ∈ conclAlts e → QuantsOk env (VarEnv.empty.bindVals σ) qs →
    EvalExp env (VarEnv.empty.bindVals σ) e' v →
    (∀ pr ∈ prems, DPremB env (otherwiseB env) (otherwiseB env "Step" [] i v)
      (VarEnv.empty.bindVals σ) pr) → EraseAll.InAI Q v →
    AllIn Q v ∧ ∃ σ' : List (IL.Id × Value), QuantsOk env (VarEnv.empty.bindVals σ') qs ∧
      EvalExp env (VarEnv.empty.bindVals σ') e' (eraseV v) ∧
      ∀ pr ∈ prems, DPremB env (otherwiseB env) (otherwiseB env "Step" [] i (eraseV v))
        (VarEnv.empty.bindVals σ') pr

open Round6.Reading (DPremB conclAlts otherwiseB) in
/-- **An instance of the rule `nm` of `Step` at an erased swap-set input comes back.** -/
def RuleBwd (Q : Value → Prop) (env : Env) (nm : IL.Id) : Prop :=
  ∀ {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat} {qs : List Param}
    {e e' : Exp} {prems : List Prem} {σ' : List (IL.Id × Value)} {v' : Value},
    env.findRel? "Step" = some (ps, op, t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    e' ∈ conclAlts e → QuantsOk env (VarEnv.empty.bindVals σ') qs →
    EvalExp env (VarEnv.empty.bindVals σ') e' v' →
    (∀ pr ∈ prems, DPremB env (otherwiseB env) (otherwiseB env "Step" [] i v')
      (VarEnv.empty.bindVals σ') pr) → EraseAll.InAI (EImg Q) v' →
    AllIn (EImg Q) v' ∧ ∃ σ : List (IL.Id × Value), QuantsOk env (VarEnv.empty.bindVals σ) qs ∧
      EvalExp env (VarEnv.empty.bindVals σ) e' (Swap.unerase Q v') ∧
      ∀ pr ∈ prems, DPremB env (otherwiseB env) (otherwiseB env "Step" [] i (Swap.unerase Q v'))
        (VarEnv.empty.bindVals σ) pr


open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation in
open Silmaril.Wasm.Numerics (Profile RelaxedChoice) in
/-- **The four rules of `Step` outside the check commute with erasure** (frozen, open), at round 6's
primitives, on the swap set `QC c` of a configuration in the domain of `Round7.Swap.Task.stepErase`:
`call_ref-hostfunc-res`, `call_ref-hostfunc-div` (which test `$hostcall`), `table.grow-succeed` and
`memory.grow-succeed` (which call `$with_tableinst`, `$with_meminst`). With it, the leaf
`Round7.Swap.Task.stepErase` holds (`Round7.EraseDer.stepErase_of_stepExc`). -/
def Task.stepExc : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      HostExportParam host → ∀ (nd : Bool) (r : RelaxedChoice),
        ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c → StripInj c →
          ∀ nm ∈ excNames,
            RuleFwd (Swap.QC c) (utf8Env (Round4Int.BI (Profile.spec nd r) hn host)) nm ∧
            RuleBwd (Swap.QC c) (utf8Env (Round4Int.BI (Profile.spec nd r) hn host)) nm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation in
open Silmaril.Wasm.Numerics (Profile RelaxedChoice) in
/-- **The two host-call rules of `Step` commute with erasure** (frozen, open):
`call_ref-hostfunc-res` and `call_ref-hostfunc-div`, on the swap set `QC c`, at round 6's
primitives. It is `Task.stepExc` restricted to `hostNames`; the grow rules are proved
(`Round7.EraseDer.stepExc_of_stepHost`), so it gives `Round7.Swap.Task.stepErase`
(`Round7.EraseDer.stepErase_of_stepHost`). -/
def Task.stepHost : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → HostOk host → HostExportBlind host →
      HostExportParam host → ∀ (nd : Bool) (r : RelaxedChoice),
        ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c → StripInj c →
          ∀ nm ∈ hostNames,
            RuleFwd (Swap.QC c) (utf8Env (Round4Int.BI (Profile.spec nd r) hn host)) nm ∧
            RuleBwd (Swap.QC c) (utf8Env (Round4Int.BI (Profile.spec nd r) hn host)) nm

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
