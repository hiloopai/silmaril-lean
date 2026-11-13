module

public import Silmaril.Compiler.Core.Verified.FoldSub.Defs
public import Silmaril.Cerberus.Core.Interleave.Defs

/-! # The folder agrees with local runs

`eval_local`: if `Fold.eval` folds a pure expression to `v`, local steps of the Core dynamics
(`Interleave.LocalReaches`, under either call flag) reduce it to `runtimeValue v` above every
continuation, from every memory, leaving the memory unchanged. It is `Fold.eval_reaches` stated
for local steps, which the expression fragments compose under arbitrary frames; and the
environment only has to agree with the folder's on the symbols the folder binds (`EnvSub`, from
`FoldSub`), so
a closed expression folds inside the environment of a running procedure.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fold

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches Plain)

local notation "rv" => runtimeValue

section Local
variable (file : Program) (labels : Labels) (wc : Bool)

theorem plain_pureExpr (p : PE) (env : Env) : Plain (.pureExpr p env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_value (v : Val) : Plain (.value v) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
theorem plain_apply (op : Prim) (vs : List Val) : Plain (.apply op vs) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- What `eval_local` says at one fuel level. -/
def FoldsLocal (fuel : Nat) : Prop :=
  ∀ (env : WEnv) (p : PExp) (v : WVal), eval file fuel env p = some v →
    ∀ denv, EnvSub env denv → ∀ k m,
      LocalReaches file labels wc ⟨.pureExpr p denv, k, m⟩ ⟨.value (rv v), k, m⟩

theorem args_chain_local {fuel : Nat} (IH : FoldsLocal file labels wc fuel) {env : WEnv}
    {denv : Env} (hr : EnvSub env denv) (op : Prim) (k : List Frame) (m : Mem.Concrete.State) :
    ∀ (rest : List PExp) (p : PExp) (done : List Val) (v : WVal) (vs : List WVal),
    eval file fuel env p = some v → rest.mapM (eval file fuel env) = some vs →
    LocalReaches file labels wc ⟨.pureExpr p denv, .arguments op done rest denv :: k, m⟩
      ⟨.apply op (done ++ rv v :: vs.map rv), k, m⟩
  | [], p, done, v, vs, hp, hvs => by
    simp at hvs
    subst hvs
    refine (IH env p v hp denv hr _ m).trans ?_
    exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_apply _ _))
  | q :: rest, p, done, v, vs, hp, hvs => by
    obtain ⟨w, ws, hq, hws, rfl⟩ := mapM_cons_some hvs
    refine (IH env p v hp denv hr _ m).trans ?_
    refine .head (.next (c' := .pureExpr q denv) (k' := .arguments op (done ++ [rv v]) rest denv :: k)
      (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
    simpa using args_chain_local IH hr op k m rest q (done ++ [rv v]) w ws hq hws

theorem args_local {fuel : Nat} (IH : FoldsLocal file labels wc fuel) {env : WEnv} {denv : Env}
    (hr : EnvSub env denv) (op : Prim) (ps : List PExp) (ws : List WVal)
    (hps : ps.mapM (eval file fuel env) = some ws) (c : Control) (k : List Frame)
    (m : Mem.Concrete.State) (hreq : requestAux file labels m c k wc = arguments op ps denv k) :
    LocalReaches file labels wc ⟨c, k, m⟩ ⟨.apply op (ws.map rv), k, m⟩ := by
  cases ps with
  | nil =>
    simp at hps
    subst hps
    exact .single (.next (by simpa [arguments] using hreq) (plain_apply _ _))
  | cons p rest =>
    obtain ⟨v, vs, hp, hvs, rfl⟩ := mapM_cons_some hps
    exact .head (.next (by simpa [arguments] using hreq) (plain_pureExpr _ _))
      (by simpa using args_chain_local file labels wc IH hr op k m rest p [] v vs hp hvs)

/-- **Agreement under local steps**: a folded pure expression reduces to its folded value. -/
theorem eval_local : ∀ fuel, FoldsLocal file labels wc fuel
  | 0 => by intro env p v h; simp [eval] at h
  | fuel+1 => by
    have IH := eval_local fuel
    intro env p v h denv hr k m
    rcases p with ⟨a, u, e⟩
    cases e with
    | val w =>
      simp only [eval, Option.some.injEq] at h
      subst h
      exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))
    | sym s =>
      simp only [eval] at h
      exact .single (.next (by simp [requestAux, awaitsScheduling, hr s v h]) (plain_value _))
    | impl c =>
      simp only [eval] at h
      cases hc : file.impl.lookup c with
      | none => simp [hc] at h
      | some d =>
        cases d with
        | constant bt body =>
          simp only [hc] at h
          exact .head (.next (by simp [requestAux, awaitsScheduling, hc]) (plain_pureExpr _ _))
            (IH env body v h denv hr k m)
        | function _ _ _ => simp [hc] at h
    | ctor c ps =>
      simp only [eval] at h
      cases hps : ps.mapM (eval file fuel env) with
      | none => simp [hps] at h
      | some ws =>
        simp only [hps, bind, Option.bind] at h
        refine (args_local file labels wc IH hr (.ctor c) ps ws hps _ k m
          (by simp [requestAux, awaitsScheduling])).trans ?_
        exact .single (.next (by simp [requestAux, awaitsScheduling, ctor_ok h]) (plain_value _))
    | op b p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_local file labels wc IH hr (.bin b) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by simp [requestAux, awaitsScheduling])).trans ?_
          exact .single (.next (by simp [requestAux, awaitsScheduling, bin_ok h]) (plain_value _))
    | convInt ty p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_local file labels wc IH hr (.conv ty) [p] [x] (one_mapM file hx) _ k m
          (by simp [requestAux, awaitsScheduling])).trans ?_
        exact .single (.next (by simp [requestAux, awaitsScheduling, conv_ok h]) (plain_value _))
    | catchExceptionalCondition ty op p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_local file labels wc IH hr (.catchInt ty op) [p, q] [x, y] (two_mapM file hx hy)
            _ k m (by simp [requestAux, awaitsScheduling])).trans ?_
          exact .single (.next (by simp [requestAux, awaitsScheduling, catchInt_ok h]) (plain_value _))
    | wrapI ty op p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_local file labels wc IH hr (.wrapInt ty op) [p, q] [x, y] (two_mapM file hx hy)
            _ k m (by simp [requestAux, awaitsScheduling])).trans ?_
          exact .single (.next (by simp [requestAux, awaitsScheduling, wrapInt_ok h]) (plain_value _))
    | not p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_local file labels wc IH hr .notBool [p] [x] (one_mapM file hx) _ k m
          (by simp [requestAux, awaitsScheduling])).trans ?_
        exact .single (.next (by simp [requestAux, awaitsScheduling, notBool_ok h]) (plain_value _))
    | isSigned p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_local file labels wc IH hr (.isType 2) [p] [x] (one_mapM file hx) _ k m
          (by simp [requestAux, awaitsScheduling])).trans ?_
        have := fun tags => signedness_ok (s := true) h tags
        simp only [ite_true] at this
        exact .single (.next (by simp [requestAux, awaitsScheduling, this]) (plain_value _))
    | isUnsigned p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_local file labels wc IH hr (.isType 3) [p] [x] (one_mapM file hx) _ k m
          (by simp [requestAux, awaitsScheduling])).trans ?_
        have := fun tags => signedness_ok (s := false) h tags
        simp only [Bool.false_eq_true, ite_false] at this
        exact .single (.next (by simp [requestAux, awaitsScheduling, this]) (plain_value _))
    | areCompatible p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_local file labels wc IH hr .compatible [p, q] [x, y] (two_mapM file hx hy)
            _ k m (by simp [requestAux, awaitsScheduling])).trans ?_
          exact .single (.next (by simp [requestAux, awaitsScheduling, compat_ok h]) (plain_value _))
    | call name ps =>
      simp only [eval] at h
      cases hps : ps.mapM (eval file fuel env) with
      | none => simp [hps] at h
      | some ws =>
        cases hf : funBody file name with
        | none => simp [hps, hf] at h
        | some pb =>
          obtain ⟨params, body⟩ := pb
          simp only [hps, hf, bind, Option.bind] at h
          split at h
          · rename_i hl
            refine (args_local file labels wc IH hr (.call name) ps ws hps _ k m
              (by simp [requestAux, awaitsScheduling])).trans ?_
            refine .head (.next (c' := .pureExpr body (extendEnv (params.zip (ws.map rv)) ∅)) (k' := k)
              (by simp [requestAux, awaitsScheduling, funBody_sound hf hl]) (plain_pureExpr _ _)) ?_
            have he := (EnvSub.empty ∅).extend (params.zip ws)
            rw [bmap_zip] at he
            exact IH _ body v h _ he k m
          · cases h
    | let_ pat p body =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hm : matchP pat x with
        | none => simp [hx, hm] at h
        | some xs =>
          simp only [hx, hm, bind, Option.bind] at h
          refine .head (.next (c' := .pureExpr p denv) (k' := .pureBind pat body denv :: k)
            (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
          refine (IH env p x hx denv hr _ m).trans ?_
          exact .head (.next (by simp [requestAux, awaitsScheduling, matchP_rv, hm]) (plain_pureExpr _ _))
            (IH _ body v h _ (hr.extend xs) k m)
    | case_ p bs =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hm : select x bs with
        | none => simp [hx, hm] at h
        | some xb =>
          obtain ⟨xs, body⟩ := xb
          simp only [hx, hm, bind, Option.bind] at h
          refine .head (.next (c' := .pureExpr p denv) (k' := .pureCase bs denv :: k)
            (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
          refine (IH env p x hx denv hr _ m).trans ?_
          exact .head (.next (by simp [requestAux, awaitsScheduling, select_rv x bs hm])
            (plain_pureExpr _ _)) (IH _ body v h _ (hr.extend xs) k m)
    | if_ c yes no =>
      simp only [eval] at h
      cases hx : eval file fuel env c with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine .head (.next (c' := .pureExpr c denv) (k' := .pureIf yes no denv :: k)
          (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
        refine (IH env c x hx denv hr _ m).trans ?_
        cases x
        case true =>
          exact .head (.next (by simp [requestAux, awaitsScheduling, runtimeValue]) (plain_pureExpr _ _))
            (IH env yes v h denv hr k m)
        case false =>
          exact .head (.next (by simp [requestAux, awaitsScheduling, runtimeValue]) (plain_pureExpr _ _))
            (IH env no v h denv hr k m)
        all_goals simp at h
    | _ => simp [eval] at h

end Local

end Silmaril.Compile.Core.Verified.Fold
