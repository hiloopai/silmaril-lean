module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSound.Defs

/-!
# Round 7, REH route 2: the soundness of the flow check, the invariants

`Round7.NxSound.Task.flowSound` says that the evaluator preserves conformance (`NxTyped.vtB`)
at the types the flow check (`NxTyped.flowItems`) assigns. This header states the invariants of
its proof, which is an induction on fuel over the evaluator.

* `ScopeVT S Γ ρ`: every variable of the scope `ρ` with a declared type in `Γ` holds a
  conforming value; every bound variable has a declared type; the wildcard `_` is never bound.
* `ArgsR S T ρ args ws ps`: the evaluated arguments `ws` of the call arguments `args` conform to
  the parameter types `ps`. A definition argument resolves through the scope, and the
  definition it names may stand for the parameter (`NxTyped.defSub`); a type argument resolves
  through the scope.
* `CallH S T tps env ρ k`: below fuel `k`, a call checked by the flow check returns a conforming
  value, both at the call's result type (`NxTyped.callRes`) and at the result type `S` records.
* `EOk S T Γ e v`: the value `v` of `e` conforms to `e`'s inferred type (`NxSites.tyOf`), is
  export-free if `NxTyped.nxD` says so, and conforms to every type `NxTyped.ckE` admits.
* `auxE c e`: side conditions the flow check does not state. The domains of every
  iteration bind distinct variables. Every type argument of a call is a single type name or
  mentions none of the type parameters `c.1`. A definition argument occurs only outside
  generic definitions and is never one of the definition parameters `c.2`.
* `ExpAt env k`: at fuel `k`, the expression members of the evaluator (`evalExp`, `evalExps`,
  `evalExpFields`, `evalArg`, `evalArgs`, `evalDoms`, `evalIterE`, `evalIterList`,
  `evalRounds`, `callDef`, `pathGet`, `pathSet`) give conforming values in conforming
  scopes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-! ## Scopes, arguments and calls -/

/-- **A conforming scope.** -/
structure ScopeVT (S : Sig) (Γ : List (String × AT)) (ρ : VarEnv) : Prop where
  /-- Every bound variable with a declared type holds a conforming value. -/
  val : ∀ x a v, Γ.lookup x = some a → ρ.findVal? x = some v → vtB S a v = true
  /-- Every bound variable has a declared type. -/
  dom : ∀ x v, ρ.findVal? x = some v → (Γ.lookup x).isSome = true
  /-- The wildcard is never bound. -/
  wild : ρ.findVal? "_" = none

/-- **Evaluated arguments conform to parameter types**, relative to the call arguments they
come from. -/
def ArgsR (S : Sig) (T : TSig) (ρ : VarEnv) : List Arg → List ArgV → List PT → Prop
  | [], [], [] => True
  | .expA _ :: xs, .val v :: ws, .exp a :: ps => vtB S a v = true ∧ ArgsR S T ρ xs ws ps
  | .defA g :: xs, .defName g' :: ws, .defn dps r :: ps =>
    g' = (ρ.findDef? g).getD g ∧ defSub S T g dps r = true ∧ ArgsR S T ρ xs ws ps
  | .typA t :: xs, .typ t' :: ws, .other :: ps => t' = resolveTyp ρ t ∧ ArgsR S T ρ xs ws ps
  | .gramA _ :: xs, .gram _ :: ws, .other :: ps => ArgsR S T ρ xs ws ps
  | _, _, _ => False

/-! ## Expressions -/

/-- **The value of `e` conforms**: to the inferred type, to `.base` when `nxD` holds, and to
every type `ckE` admits. -/
structure EOk (S : Sig) (T : TSig) (Γ : List (String × AT)) (e : Exp) (v : Value) : Prop where
  ty : vtB S (tyOf S Γ e) v = true
  nx : nxD S Γ e = true → nxB v = true
  ck : ∀ a, ckE S T Γ a e = true → vtB S a v = true

/-- `b` is a list without repetitions. -/
def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-- A type argument is a single type name, or mentions none of `tps`. -/
def typArgOk (tps : List String) : Typ → Bool
  | .varT _ [] => true
  | t => (atNames (toAT t)).all fun n => !tps.contains n

/-- The context of the side conditions: the type parameters and the definition parameters of
the clause. -/
abbrev AuxCtx := List String × List String

/-- The side conditions on the arguments of a call: every type argument satisfies `typArgOk`;
a definition argument occurs only outside generic definitions and is not itself a definition
parameter. -/
def typArgsOk (c : AuxCtx) (args : List Arg) : Bool :=
  args.all fun a => match a with
    | .typA t => typArgOk c.1 t
    | .defA g => c.1.isEmpty && !c.2.contains g
    | _ => true

/-- The value a call returns at fuel `m`, from a clause or from the primitives. -/
def CallRes (env : Env) (m : Nat) (d : DefDef) (f : String) (ws : List ArgV) (v : Value) :
    Prop :=
  tryClauses m env d.2.2 ws = .ok v ∨
    (tryClauses m env d.2.2 ws = .error .undef ∧ env.builtins.call f ws = some v)

/-- **Calls conform below fuel `k`.** -/
def CallH (S : Sig) (T : TSig) (tps : AuxCtx) (env : Env) (ρ : VarEnv) (k : Nat) :
    Prop :=
  ∀ m < k, ∀ (f : String) (args : List Arg) (ws : List ArgV) (ps : List PT) (d : DefDef)
    (v : Value),
    callPar S T f args = some ps → ArgsR S T ρ args ws ps → typArgsOk tps args = true →
    env.findDef? ((ρ.findDef? f).getD f) = some d →
    CallRes env m d ((ρ.findDef? f).getD f) ws v →
    vtB S (callRes S T f args) v = true ∧ vtB S ((S.results.lookup f).getD .unk) v = true

mutual
/-- **The side conditions on an evaluated expression**: iteration domains bind distinct
variables, and type arguments satisfy `typArgOk`. -/
def auxE (tps : AuxCtx) : Exp → Bool
  | .unE _ _ e => auxE tps e
  | .binE _ _ e₁ e₂ => auxE tps e₁ && auxE tps e₂
  | .cmpE _ _ e₁ e₂ => auxE tps e₁ && auxE tps e₂
  | .tupE es => auxL tps es
  | .projE e _ => auxE tps e
  | .caseE _ e => auxE tps e
  | .uncaseE e _ => auxE tps e
  | .optE none => true
  | .optE (some e) => auxE tps e
  | .theE e => auxE tps e
  | .strE fs => auxF tps fs
  | .dotE e _ => auxE tps e
  | .compE e₁ e₂ => auxE tps e₁ && auxE tps e₂
  | .listE es => auxL tps es
  | .liftE e => auxE tps e
  | .memE e₁ e₂ => auxE tps e₁ && auxE tps e₂
  | .lenE e => auxE tps e
  | .catE e₁ e₂ => auxE tps e₁ && auxE tps e₂
  | .idxE e₁ e₂ => auxE tps e₁ && auxE tps e₂
  | .sliceE e₁ e₂ e₃ => auxE tps e₁ && auxE tps e₂ && auxE tps e₃
  | .updE e₁ _ e₂ => auxE tps e₁ && auxE tps e₂
  | .extE e₁ _ e₂ => auxE tps e₁ && auxE tps e₂
  | .callE _ args => typArgsOk tps args && auxA tps args
  | .iterE e (.mk it ds) =>
    nodupB (ds.map domVar) && auxE tps e && auxI tps it && auxD tps ds
  | .cvtE e _ _ => auxE tps e
  | .subE e _ _ => auxE tps e
  | _ => true

/-- `auxE` on a list. -/
def auxL (tps : AuxCtx) : List Exp → Bool
  | [] => true
  | e :: es => auxE tps e && auxL tps es

/-- `auxE` on record fields. -/
def auxF (tps : AuxCtx) : List ExpField → Bool
  | [] => true
  | .mk _ e :: fs => auxE tps e && auxF tps fs

/-- `auxE` on the bound of a `ListN` iteration. -/
def auxI (tps : AuxCtx) : Iter → Bool
  | .listN e _ => auxE tps e
  | _ => true

/-- `auxE` on iteration domains. -/
def auxD (tps : AuxCtx) : List Dom → Bool
  | [] => true
  | .mk _ e :: ds => auxE tps e && auxD tps ds

/-- `auxE` on the expression arguments of a call. -/
def auxA (tps : AuxCtx) : List Arg → Bool
  | [] => true
  | .expA e :: xs => auxE tps e && auxA tps xs
  | _ :: xs => auxA tps xs
end

/-- An iteration's value: a list or an option of values each satisfying `P`. -/
def IterV (P : Value → Prop) : Value → Prop
  | .list vs => ∀ w ∈ vs, P w
  | .opt none => True
  | .opt (some w) => P w
  | _ => False

/-- **The expression members of the evaluator conform at fuel `k`.** -/
structure ExpAt (env : Env) (k : Nat) : Prop where
  exp : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (e : Exp) (v : Value), ScopeVT S Γ ρ → CallH S T tps env ρ k → tyOk S T Γ e = true →
    auxE tps e = true → evalExp k env ρ e = .ok v → EOk S T Γ e v
  exps : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (es : List Exp) (vs : List Value), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOkL S T Γ es = true → auxL tps es = true → evalExps k env ρ es = .ok vs →
    List.Forall₂ (EOk S T Γ) es vs
  fields : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (fs : List ExpField) (gs : List (AtomS × Value)), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOkF S T Γ fs = true → auxF tps fs = true → evalExpFields k env ρ fs = .ok gs →
    List.Forall₂ (fun f g => match f with | .mk a e => g.1 = a ∧ EOk S T Γ e g.2) fs gs
  arg : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (x : Arg) (w : ArgV), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOkA S T Γ [x] = true → auxA tps [x] = true → evalArg k env ρ x = .ok w →
    ∀ p, ckArgs S T Γ [x] [p] = true → ArgsR S T ρ [x] [w] [p]
  args : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (xs : List Arg) (ws : List ArgV), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOkA S T Γ xs = true → auxA tps xs = true → evalArgs k env ρ xs = .ok ws →
    ∀ ps, ckArgs S T Γ xs ps = true → ArgsR S T ρ xs ws ps
  doms : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (ds : List Dom) (xvs : List (IL.Id × Value)), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOkD S T Γ ds = true → auxD tps ds = true → evalDoms k env ρ ds = .ok xvs →
    List.Forall₂ (fun d p => p.1 = domVar d ∧ EOk S T Γ (domSrc d) p.2) ds xvs
  iter : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (e : Exp) (it : Iter) (ds : List Dom) (v : Value), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOk S T (iterΓ S Γ it ds) e = true → tyOkI S T Γ it = true → tyOkD S T Γ ds = true →
    nodupB (ds.map domVar) = true → auxE tps e = true → auxI tps it = true →
    auxD tps ds = true → evalIterE k env ρ e it ds = .ok v →
    IterV (EOk S T (iterΓ S Γ it ds) e) v
  iterList : ∀ (S : Sig) (T : TSig) (Γi : List (String × AT)) (tps : AuxCtx)
    (ρ : VarEnv) (e : Exp) (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (n : Nat)
    (v : Value),
    (∀ ds, xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds →
      (∀ p ∈ ds, p.2.length = n) → ∀ i < n, ScopeVT S Γi (ρ.bindVals (iterRow ds ido i))) →
    CallH S T tps env ρ k → tyOk S T Γi e = true → auxE tps e = true →
    evalIterList k env ρ e xvs ido n = .ok v → IterV (EOk S T Γi e) v
  rounds : ∀ (S : Sig) (T : TSig) (Γi : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (e : Exp) (rows : List (List (IL.Id × Value))) (vs : List Value),
    (∀ r ∈ rows, ScopeVT S Γi (ρ.bindVals r)) → CallH S T tps env ρ k → tyOk S T Γi e = true →
    auxE tps e = true → evalRounds k env ρ e rows = .ok vs → ∀ w ∈ vs, EOk S T Γi e w
  call : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (tps : AuxCtx) (ρ : VarEnv)
    (f : String) (xs : List Arg) (v : Value), ScopeVT S Γ ρ → CallH S T tps env ρ k →
    tyOk S T Γ (.callE f xs) = true → auxE tps (.callE f xs) = true →
    callDef k env ρ f xs = .ok v → EOk S T Γ (.callE f xs) v
  pathGet : ∀ (S : Sig) (ρ : VarEnv) (a : AT) (v : Value) (p : Path) (u : Value),
    vtB S a v = true → pathGet k env ρ v p = .ok u → vtB S (pathAT S a p) u = true
  pathSet : ∀ (S : Sig) (ρ : VarEnv) (a : AT) (v : Value) (p : Path) (w u : Value),
    vtB S a v = true → vtB S (pathAT S a p) w = true → pathSet k env ρ v p w = .ok u →
    vtB S a u = true

/-! ## Patterns -/

/-- **A match keeps the scope conforming** and binds only term variables. -/
def MatchOk (S : Sig) (Γ : List (String × AT)) (ρ ρ' : VarEnv) : Prop :=
  ScopeVT S Γ ρ' ∧ ρ'.defs = ρ.defs ∧ ρ'.typs = ρ.typs

/-- The scope a round of a pattern iteration matches its body in: the counter bound to the
round number. -/
def ctrScope (ρ : VarEnv) (ido : Option IL.Id) (i : Nat) : VarEnv :=
  match ido with
  | some y => ρ.bindVal y (.num (.natN i))
  | none => ρ

/-- **The matching members of the evaluator keep scopes conforming at fuel `k`**, when the
pattern passes `NxTyped.patTy` at a type the value conforms to. -/
structure MatchAt (env : Env) (k : Nat) : Prop where
  exp : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (ρ : VarEnv) (e : Exp) (a : AT)
    (v : Value) (ρ' : VarEnv), ScopeVT S Γ ρ → patTy S T Γ a e = true → vtB S a v = true →
    matchExp k env ρ e v = .ok ρ' → MatchOk S Γ ρ ρ'
  exps : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (ρ : VarEnv) (es : List Exp)
    (vs : List Value) (ρ' : VarEnv), ScopeVT S Γ ρ →
    (∀ (i : Nat) e v, es[i]? = some e → vs[i]? = some v →
      ∃ b, patTy S T Γ b e = true ∧ vtB S b v = true) →
    matchExps k env ρ es vs = .ok ρ' → MatchOk S Γ ρ ρ'
  fields : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (ρ : VarEnv) (a : AT)
    (fs : List ExpField) (gs : List (AtomS × Value)) (ρ' : VarEnv), ScopeVT S Γ ρ →
    patF S T Γ a fs = true → (∀ g ∈ gs, vtB S (fieldOf' S a g.1) g.2 = true) →
    matchExpFields k env ρ fs gs = .ok ρ' → MatchOk S Γ ρ ρ'
  iter : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT)) (ρ : VarEnv) (e : Exp) (it : Iter)
    (ds : List Dom) (a : AT) (v : Value) (ρ' : VarEnv), ScopeVT S Γ ρ →
    patTy S T Γ a (.iterE e (.mk it ds)) = true → vtB S a v = true →
    matchIterE k env ρ e it ds v = .ok ρ' → MatchOk S Γ ρ ρ'
  iterList : ∀ (S : Sig) (T : TSig) (Γ Γi : List (String × AT)) (ρ : VarEnv) (e : Exp)
    (ds : List Dom) (ido : Option IL.Id) (b : AT) (vs : List Value) (ρ' : VarEnv),
    ScopeVT S Γ ρ → (∀ i, ScopeVT S Γi (ctrScope ρ ido i)) → patTy S T Γi b e = true →
    (∀ w ∈ vs, vtB S b w = true) → patD S T Γ Γi ds = true →
    matchIterList k env ρ e ds ido vs = .ok ρ' → MatchOk S Γ ρ ρ'
  rounds : ∀ (S : Sig) (T : TSig) (Γi : List (String × AT)) (ρ : VarEnv) (e : Exp)
    (xs : List IL.Id) (ido : Option IL.Id) (i : Nat) (b : AT) (vs : List Value)
    (rows : List (List Value)), (∀ j, ScopeVT S Γi (ctrScope ρ ido j)) →
    patTy S T Γi b e = true → (∀ w ∈ vs, vtB S b w = true) →
    matchRounds k env ρ e xs ido i vs = .ok rows →
    ∀ row ∈ rows, ∀ (j : Nat) x w, xs[j]? = some x → row[j]? = some w →
      vtB S ((Γi.lookup x).getD .unk) w = true

/-! ## Side conditions on the script -/

/-- Pointwise equality of optional abstract types. -/
def optATEq : List (Option AT) → List (Option AT) → Bool
  | [], [] => true
  | some a :: xs, some b :: ys => atEq a b && optATEq xs ys
  | none :: xs, none :: ys => optATEq xs ys
  | _, _ => false

/-- **The argument patterns of a clause align with the parameters**: an expression pattern for
an expression parameter, the type parameter itself for a type parameter, and for a definition
parameter a definition quantifier with the declared signature. -/
def argAlign (qs : List Param) : List Arg → List Param → Bool
  | [], [] => true
  | .expA _ :: xs, .expP _ _ :: ps => argAlign qs xs ps
  | .typA (.varT x []) :: xs, .typP y :: ps => x == y && argAlign qs xs ps
  | .defA y :: xs, .defP _ dps t :: ps =>
    (match (defQuants qs).lookup y with
      | some (dps', t') => optATEq dps' (dps.map optAT) && atEq t' (toAT t)
      | none => false) && argAlign qs xs ps
  | .gramA _ :: xs, .gramP _ _ _ :: ps => argAlign qs xs ps
  | _, _ => false

/-- The side conditions on a premise: the right-hand side of a `let` passes `auxE`. -/
def premAux (c : AuxCtx) : Prem → Bool
  | .letPr _ e₂ => auxE c e₂
  | _ => true

/-- **The side conditions on a clause** of a definition with parameters `ps`: the patterns align
with the parameters, the body and every `let` premise pass `auxE`, a generic definition has
no definition quantifiers, and no definition quantifier is named like a generic definition or
is the wildcard `_`. -/
def clauseAux (T : TSig) (ps : List Param) : Clause → Bool
  | .defD qs args e prems =>
    let c : AuxCtx := (typParams ps, (defQuants qs).map (·.1))
    argAlign qs args ps && auxE c e && prems.all (premAux c) &&
    ((typParams ps).isEmpty || (defQuants qs).isEmpty) &&
    (defQuants qs).all fun d => (T.gres.lookup d.1).isNone && d.1 != "_"

mutual
/-- **The side conditions on one top-level definition**: no type is named `X`; a reachable
definition has no grammar parameter and at most the type parameter `X`, and its clauses pass
`clauseAux`. -/
def auxItem (T : TSig) : Def → Bool
  | .typD x _ _ => x != "X"
  | .decD f ps _ clauses =>
    !reach 1 f || ((typParams ps).all (· == "X") && (typParams ps).length ≤ 1 &&
      (ps.all fun p => !(p matches .gramP ..)) &&
      clauses.all (clauseAux T ps))
  | .recD ds => auxItems T ds
  | _ => true

/-- `auxItem` on a list. -/
def auxItems (T : TSig) : List Def → Bool
  | [] => true
  | d :: ds => auxItem T d && auxItems T ds
end

/-- `a` does not mention `X`. -/
def xFree (a : AT) : Bool := !(atNames a).contains "X"

/-- `xFree` on a parameter type. -/
def xFreePT : PT → Bool
  | .exp a => xFree a
  | .defn dps r => dps.all (fun o => o.all xFree) && xFree r
  | .other => true

/-- **The side conditions on the signatures**: `X` is export-free in `S`; the entries of `S`
(aliases, fields, cases and result types) mention no `X`; every definition with parameter types
in `T` is reachable from `Step`, and its parameter types mention `X` only if it is a type
parameter; generic definitions have the one type parameter `X`, the same in their parameter
entry, and no result type in `S`. -/
def sigsAux (S : Sig) (T : TSig) : Bool :=
  S.good.contains "X" &&
  (S.aliases.all fun p => xFree p.2) && (S.fields.all fun p => xFree p.2.2) &&
  (S.cases.all fun p => xFree p.2.2) && (S.results.all fun p => xFree p.2) &&
  (T.params.all fun p => reach 1 p.1 && (p.2.1.contains "X" || p.2.2.all xFreePT)) &&
  (T.gres.all fun p => p.2.1 == ["X"] && (S.results.lookup p.1).isNone &&
    (T.params.lookup p.1).map (·.1) == some p.2.1)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
