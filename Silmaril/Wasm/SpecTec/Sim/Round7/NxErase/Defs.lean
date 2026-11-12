module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Defs

/-!
# Round 7, REH route 2: the evaluator's expression members commute with erasure without `QInj`

Round 3's `Round7.EraseAll.eraseAt` shows that the evaluator commutes with export erasure
(`Swap.eraseV`) on scopes whose module records lie in a swap set `Q` on which erasure is
injective (`Swap.QInj Q`). Route 2 drops the swap set: here every value is allowed (`QT`), and
injectivity is replaced, at the comparison sites, by the site check (`NxSites.badE`) together
with the soundness of the flow check (`NxFlow.expAt`): one operand of every equality,
inequality and membership test is export-free, so the test reads alike before and after
erasure (`NxSites.cmpValues_eraseV_nx`, `NxSites.memValue_eraseV_nx`).

This header states that copy for the **twelve expression members** of the evaluator
(`evalExp` … `callDef`, `pathGet`, `pathSet`), with calls into clauses abstracted, as
`NxFlow.ExpAt` abstracts them:

* `NCalls gd S T tps env ρ k`: calls conform below fuel `k` (`NxFlow.CallH`), clause bodies
  commute with erasure below fuel `k` (`CallE`), and the definition variables of the scope name
  checked definitions (`EraseAll.DefsG gd`). With conformance of the scope (`NxFlow.ScopeVT`),
  this is the invariant of the copy.
* `auxX tps e`: the paths of `e`'s updates and extensions have index and slice bounds that pass
  `NxFlow.auxE` (which does not look into paths).
* `NAt gr gd env k`: every expression member at fuel `k`, on syntax that passes the flow check
  (`NxTyped.tyOk`), the side conditions (`NxFlow.auxE`, `auxX`), the site check
  (`NxSites.badE … = 0`) and round 3's syntactic check (`EraseAll.xExp gr gd`), gives on the
  erased scope the erased answer (`EraseAll.ER eraseV`).

The proof is `Round7.NxErase.nAt` (`Round7/NxErase/Thms.lean`), given that the primitives of
`gd` names commute with erasure (`EraseAll.BIErase QT gd env`).

`xItems` is the side condition of the copy on the script: every reachable clause, in every mode
of `NxTyped.modes`, passes the site check in the signature the soundness proof uses
(`NxTyped.clauseSig sigX`), and every reachable clause and rule passes `auxX`
(`Round7.NxErase.xItems_fixed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVf AllIn eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (ER ArgIn DefsG eraseP xExp xExps xFields xArgs xArg
  xDoms xIter xPath)

/-- **The swap set of route 2**: every value. -/
abbrev QT : Value → Prop := fun _ => True

/-! ## Paths -/

mutual
/-- **The paths of `e` pass the side conditions**: every index and slice bound of a path in an
update or extension passes `NxFlow.auxE` and, recursively, `auxX`. -/
def auxX (tps : AuxCtx) : Exp → Bool
  | .unE _ _ e => auxX tps e
  | .binE _ _ e₁ e₂ => auxX tps e₁ && auxX tps e₂
  | .cmpE _ _ e₁ e₂ => auxX tps e₁ && auxX tps e₂
  | .tupE es => auxXL tps es
  | .projE e _ => auxX tps e
  | .caseE _ e => auxX tps e
  | .uncaseE e _ => auxX tps e
  | .optE none => true
  | .optE (some e) => auxX tps e
  | .theE e => auxX tps e
  | .strE fs => auxXF tps fs
  | .dotE e _ => auxX tps e
  | .compE e₁ e₂ => auxX tps e₁ && auxX tps e₂
  | .listE es => auxXL tps es
  | .liftE e => auxX tps e
  | .memE e₁ e₂ => auxX tps e₁ && auxX tps e₂
  | .lenE e => auxX tps e
  | .catE e₁ e₂ => auxX tps e₁ && auxX tps e₂
  | .idxE e₁ e₂ => auxX tps e₁ && auxX tps e₂
  | .sliceE e₁ e₂ e₃ => auxX tps e₁ && auxX tps e₂ && auxX tps e₃
  | .updE e₁ p e₂ => auxX tps e₁ && auxXP tps p && auxX tps e₂
  | .extE e₁ p e₂ => auxX tps e₁ && auxXP tps p && auxX tps e₂
  | .callE _ args => auxXA tps args
  | .iterE e (.mk it ds) => auxX tps e && auxXI tps it && auxXD tps ds
  | .cvtE e _ _ => auxX tps e
  | .subE e _ _ => auxX tps e
  | _ => true

/-- `auxX` on a list. -/
def auxXL (tps : AuxCtx) : List Exp → Bool
  | [] => true
  | e :: es => auxX tps e && auxXL tps es

/-- `auxX` on record fields. -/
def auxXF (tps : AuxCtx) : List ExpField → Bool
  | [] => true
  | .mk _ e :: fs => auxX tps e && auxXF tps fs

/-- `auxX` on the bound of a `ListN` iteration. -/
def auxXI (tps : AuxCtx) : Iter → Bool
  | .listN e _ => auxX tps e
  | _ => true

/-- `auxX` on iteration domains. -/
def auxXD (tps : AuxCtx) : List Dom → Bool
  | [] => true
  | .mk _ e :: ds => auxX tps e && auxXD tps ds

/-- `auxX` on the expression arguments of a call. -/
def auxXA (tps : AuxCtx) : List Arg → Bool
  | [] => true
  | .expA e :: xs => auxX tps e && auxXA tps xs
  | _ :: xs => auxXA tps xs

/-- **A path whose index and slice bounds pass `NxFlow.auxE` and `auxX`.** -/
def auxXP (tps : AuxCtx) : Path → Bool
  | .rootP => true
  | .idxP p e => auxXP tps p && auxE tps e && auxX tps e
  | .sliceP p e₁ e₂ => auxXP tps p && auxE tps e₁ && auxX tps e₁ && auxE tps e₂ && auxX tps e₂
  | .dotP p _ => auxXP tps p
end

/-! ## The side conditions on the script -/

/-- `auxX` on the expressions a premise evaluates. -/
def premX (c : AuxCtx) : Prem → Bool
  | .ifPr e => auxX c e
  | .letPr e₁ e₂ => auxX c e₁ && auxX c e₂
  | .rulePr _ args _ e => auxXA c args && auxX c e
  | .elsePr => true
  | .iterPr pr (.mk it ds) => premX c pr && auxXI c it && auxXD c ds

/-- **One clause passes the site check in the signature its soundness proof uses** (the clause's
signature `NxTyped.clauseSig` in mode `b`, not `NxSites.sigFixed`), and its argument patterns,
premises and body pass `auxX`. -/
def clauseX (tps : List String) (b : AT) : Clause → Bool
  | .defD qs args e prems =>
    let S' := clauseSig sigX tps b qs
    let Γ := (quantsΓ qs).map fun p => (p.1, substTP tps b p.2)
    let c : AuxCtx := (tps, (defQuants qs).map (·.1))
    (patAs S' Γ [] args).2 + badE S' Γ e + prems.foldl (fun k pr => k + badPr S' Γ pr) 0 == 0 &&
    auxXA c args && auxX c e && prems.all (premX c)

/-- **One rule passes `auxX`**: every conclusion alternative and every premise. -/
def ruleX : Rule → Bool
  | .ruleD _ _ _ e prems =>
    (Round6.Reading.conclAlts e).all (auxX ([], [])) && prems.all (premX ([], []))

mutual
/-- **The side conditions of the copy on one top-level definition**: if it is reachable from
`Step`, every clause passes `clauseX` in every mode, or every rule passes `ruleX`. -/
def xItem : Def → Bool
  | .decD f ps _ clauses =>
    !reach 1 f || (modes (typParams ps)).all fun b => clauses.all (clauseX (typParams ps) b)
  | .relD x _ _ _ rules => !reach 0 x || rules.all ruleX
  | .recD ds => xItems ds
  | _ => true

/-- `xItem` on a list. -/
def xItems : List Def → Bool
  | [] => true
  | d :: ds => xItem d && xItems ds
end

/-! ## Calls and scopes -/

/-- **Clause bodies commute with erasure below fuel `k`**, at every call the flow check passes
in the scope `ρ`, to a checked definition. -/
def CallE (gd : String → Bool) (S : Sig) (T : TSig) (tps : AuxCtx) (env : Env) (ρ : VarEnv)
    (k : Nat) : Prop :=
  ∀ m < k, ∀ (f : String) (args : List Arg) (ws : List ArgV) (d : DefDef),
    (∀ ps, callPar S T f args = some ps → ArgsR S T ρ args ws ps) →
    typArgsOk tps args = true → gd ((ρ.findDef? f).getD f) = true →
    env.findDef? ((ρ.findDef? f).getD f) = some d → (∀ w ∈ ws, ArgIn QT gd w) →
    ER eraseV (AllIn QT) (tryClauses m env d.2.2 ws) (tryClauses m env d.2.2 (ws.map eraseA))

/-- **The invariant of a scope, besides conformance**: calls conform and their clause bodies
commute with erasure below fuel `k`, and definition variables name checked definitions. -/
structure NCalls (gd : String → Bool) (S : Sig) (T : TSig) (tps : AuxCtx) (env : Env)
    (ρ : VarEnv) (k : Nat) : Prop where
  callH : CallH S T tps env ρ k
  callE : CallE gd S T tps env ρ k
  defs : DefsG gd ρ

/-! ## The statement -/

section
variable (gr gd : String → Bool) (env : Env)

/-- **The expression members of the evaluator commute with erasure at fuel `k`**, without a swap
set. -/
structure NAt (k : Nat) : Prop where
  exp : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv) (e : Exp),
    ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOk S T Γ e = true → auxE tps e = true →
    auxX tps e = true → badE S Γ e = 0 → xExp gr gd e = true →
    ER eraseV (AllIn QT) (evalExp k env ρ e) (evalExp k env (eraseScope ρ) e)
  exps : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (es : List Exp), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkL S T Γ es = true → auxL tps es = true →
    auxXL tps es = true → badEs S Γ es = 0 → xExps gr gd es = true →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn QT v)
      (evalExps k env ρ es) (evalExps k env (eraseScope ρ) es)
  fields : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (fs : List ExpField), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkF S T Γ fs = true →
    auxF tps fs = true → auxXF tps fs = true → badFs S Γ fs = 0 → xFields gr gd fs = true →
    ER (List.map eraseP) (fun gs => ∀ p ∈ gs, AllIn QT p.2 ∧ p.1 ≠ "EXPORTS")
      (evalExpFields k env ρ fs) (evalExpFields k env (eraseScope ρ) fs)
  arg : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (x : Arg), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkA S T Γ [x] = true →
    auxA tps [x] = true → auxXA tps [x] = true → badAs S Γ [x] = 0 → xArg gr gd x = true →
    ER eraseA (ArgIn QT gd) (evalArg k env ρ x) (evalArg k env (eraseScope ρ) x)
  args : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (xs : List Arg), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkA S T Γ xs = true → auxA tps xs = true →
    auxXA tps xs = true → badAs S Γ xs = 0 → xArgs gr gd xs = true →
    ER (List.map eraseA) (fun ws => ∀ w ∈ ws, ArgIn QT gd w)
      (evalArgs k env ρ xs) (evalArgs k env (eraseScope ρ) xs)
  doms : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (ds : List Dom), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkD S T Γ ds = true → auxD tps ds = true →
    auxXD tps ds = true → badDs S Γ ds = 0 → xDoms gr gd ds = true →
    ER (List.map eraseP) (fun xvs => ∀ p ∈ xvs, AllIn QT p.2)
      (evalDoms k env ρ ds) (evalDoms k env (eraseScope ρ) ds)
  iter : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv) (e : Exp)
    (it : Iter) (ds : List Dom), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k →
    tyOk S T (iterΓ S Γ it ds) e = true → tyOkI S T Γ it = true → tyOkD S T Γ ds = true →
    nodupB (ds.map domVar) = true → auxE tps e = true → auxI tps it = true →
    auxD tps ds = true → auxX tps e = true → auxXI tps it = true → auxXD tps ds = true →
    badE S (iterΓ S Γ it ds) e = 0 → badI S Γ it = 0 → badDs S Γ ds = 0 →
    xExp gr gd e = true → xIter gr gd it = true → xDoms gr gd ds = true →
    ER eraseV (AllIn QT) (evalIterE k env ρ e it ds) (evalIterE k env (eraseScope ρ) e it ds)
  iterList : ∀ (S : Sig) (T : TSig) (Γi : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (e : Exp) (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (n : Nat),
    (∀ ds, xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds →
      (∀ p ∈ ds, p.2.length = n) → ∀ i < n, ScopeVT S Γi (ρ.bindVals (iterRow ds ido i))) →
    NCalls gd S T tps env ρ k → tyOk S T Γi e = true → auxE tps e = true →
    auxX tps e = true → badE S Γi e = 0 → xExp gr gd e = true →
    ER eraseV (AllIn QT) (evalIterList k env ρ e xvs ido n)
      (evalIterList k env (eraseScope ρ) e (xvs.map eraseP) ido n)
  rounds : ∀ (S : Sig) (T : TSig) (Γi : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (e : Exp) (rows : List (List (IL.Id × Value))), (∀ r ∈ rows, ScopeVT S Γi (ρ.bindVals r)) →
    NCalls gd S T tps env ρ k → tyOk S T Γi e = true → auxE tps e = true →
    auxX tps e = true → badE S Γi e = 0 → xExp gr gd e = true →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn QT v)
      (evalRounds k env ρ e rows) (evalRounds k env (eraseScope ρ) e (rows.map (List.map eraseP)))
  call : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (f : String) (xs : List Arg), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k →
    tyOk S T Γ (.callE f xs) = true → auxE tps (.callE f xs) = true →
    auxX tps (.callE f xs) = true → badE S Γ (.callE f xs) = 0 → xExp gr gd (.callE f xs) = true →
    ER eraseV (AllIn QT) (callDef k env ρ f xs) (callDef k env (eraseScope ρ) f xs)
  pathGet : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (v : Value) (p : Path), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkP S T Γ p = true →
    auxXP tps p = true → badP S Γ p = 0 → xPath gr gd p = true →
    ER eraseV (AllIn QT) (pathGet k env ρ v p) (pathGet k env (eraseScope ρ) (eraseV v) p)
  pathSet : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (v : Value) (p : Path) (w : Value), ScopeVT S Γ ρ → NCalls gd S T tps env ρ k → tyOkP S T Γ p = true →
    auxXP tps p = true → badP S Γ p = 0 → xPath gr gd p = true →
    pathSet k env (eraseScope ρ) (eraseV v) p (eraseV w) = eraseV <$> pathSet k env ρ v p w

end

/-! ## The clause half, open -/

/-- **The clause half of the copy** (frozen, open). In the round-7 environment, with primitives
that conform and that commute with erasure on the checked definitions (`EraseAll.gdE`), clause
bodies commute with erasure at every call the flow check passes in a scope without definition
and type bindings, which is the scope of a rule instance (`NxRule.qScope`). Its proof is the
other seventeen members of round 3's `EraseAll.eraseAt` (matching, clauses, premises,
`Sem.derives`), with the pattern sites of `NxSites.patE` in place of `QInj`; it is not done. -/
def Task.clauseErase : Prop :=
  ∀ B : Builtins, NxSound.BuiltinsVT sigX tsigFixed (utf8Env B) →
    EraseAll.BIErase QT EraseAll.gdE (utf8Env B) →
      ∀ (ρ : VarEnv) (k : Nat), ρ.defs = [] → ρ.typs = [] →
        CallE EraseAll.gdE sigX tsigFixed ([], []) (utf8Env B) ρ k

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
