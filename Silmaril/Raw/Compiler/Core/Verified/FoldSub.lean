module

public import Silmaril.Compiler.Core.Verified.FoldSound.Defs

/-! # Folding in a larger run-time environment

`Fold.EnvRel env denv` asks the run-time environment to be exactly the folder's environment,
seen at run time. Inside a program with objects this never holds: the run-time environment also
binds the pointers to the objects (string literals, argument objects), which have no wire value.
`EnvSub env denv` only asks every folded symbol to have its value in `denv`; `eval_reaches_sub` is
`eval_reaches` under that weaker relation (the folder only reads the symbols it binds).
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fold

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ReturnConst (Reaches next_reaches)

local notation "rv" => runtimeValue

/-- The folder's environment is part of the run-time one. -/
def EnvSub (env : WEnv) (denv : Env) : Prop :=
  ∀ s w, env.lookup s = some w → denv.lookup s = some (rv w)

theorem EnvSub.empty (denv : Env) : EnvSub ∅ denv := by
  intro s w h
  simp [Map.lookup] at h

theorem EnvSub.ofRel {env : WEnv} {denv : Env} (h : EnvRel env denv) : EnvSub env denv := by
  intro s w hs
  rw [h s, hs]
  rfl

theorem EnvSub.insert {env : WEnv} {denv : Env} (h : EnvSub env denv) (s : Sym) (v : WVal) :
    EnvSub (env.insert s v) (denv.insert s (rv v)) := by
  intro t w ht
  by_cases e : MapKey.key t = MapKey.key s
  · simp only [Map.lookup, Map.insert] at ht ⊢
    rw [e, Finmap.lookup_insert] at ht ⊢
    cases ht
    rfl
  · rw [Map.lookup_insert_of_key_ne _ _ e] at ht ⊢
    exact h t w ht

theorem EnvSub.extend {env : WEnv} {denv : Env} (h : EnvSub env denv) (xs : List (Sym × WVal)) :
    EnvSub (Fold.extend xs env) (extendEnv (bmap xs) denv) := by
  induction xs with
  | nil => simpa [Fold.extend, extendEnv, bmap] using h
  | cons x xs ih =>
    obtain ⟨s, v⟩ := x
    have := ih.insert s v
    simpa [Fold.extend, extendEnv, bmap, List.foldr] using this

/-- The run-time environment may gain a binding the folder does not have. -/
theorem EnvSub.insert_right {env : WEnv} {denv : Env} (h : EnvSub env denv) {s : Sym}
    (hs : env.lookup s = none) (v : Val) : EnvSub env (denv.insert s v) := by
  intro t w ht
  by_cases e : MapKey.key t = MapKey.key s
  · simp only [Map.lookup] at ht hs
    rw [e, hs] at ht
    cases ht
  · rw [Map.lookup_insert_of_key_ne _ _ e]
    exact h t w ht

/-- The run-time environment may gain bindings the folder does not have. -/
theorem EnvSub.extend_right {env : WEnv} {denv : Env} (h : EnvSub env denv) (xs : Bindings)
    (hs : ∀ x ∈ xs, env.lookup x.1 = none) : EnvSub env (extendEnv xs denv) := by
  induction xs with
  | nil => simpa [extendEnv] using h
  | cons x xs ih =>
    obtain ⟨s, v⟩ := x
    have := (ih fun y hy => hs y (List.mem_cons_of_mem _ hy)).insert_right
      (hs (s, v) List.mem_cons_self) v
    simpa [extendEnv, List.foldr] using this

/-! ## Agreement under `EnvSub` -/

section StepsSub
variable (file : Program) (labels : Labels)

/-- What `eval_reaches_sub` says at one fuel level. -/
def FoldsSub (fuel : Nat) : Prop :=
  ∀ (env : WEnv) (p : PExp) (v : WVal), eval file fuel env p = some v →
    ∀ denv, EnvSub env denv → ∀ k m,
      Reaches file labels ⟨.pureExpr p denv, k, m⟩ ⟨.value (rv v), k, m⟩

theorem args_chain_sub {fuel : Nat} (IH : FoldsSub file labels fuel) {env : WEnv} {denv : Env}
    (hr : EnvSub env denv) (op : Prim) (k : List Frame) (m : Mem.Concrete.State) :
    ∀ (rest : List PExp) (p : PExp) (done : List Val) (v : WVal) (vs : List WVal),
    eval file fuel env p = some v → rest.mapM (eval file fuel env) = some vs →
    Reaches file labels ⟨.pureExpr p denv, .arguments op done rest denv :: k, m⟩
      ⟨.apply op (done ++ rv v :: vs.map rv), k, m⟩
  | [], p, done, v, vs, hp, hvs => by
    simp at hvs
    subst hvs
    refine (IH env p v hp denv hr _ m).trans ?_
    apply next_reaches
    · intro o; simp
    · simp [request, requestAux, awaitsScheduling]
  | q :: rest, p, done, v, vs, hp, hvs => by
    obtain ⟨w, ws, hq, hws, rfl⟩ := mapM_cons_some hvs
    refine (IH env p v hp denv hr _ m).trans ?_
    refine Relation.ReflTransGen.trans (b :=
      ⟨.pureExpr q denv, .arguments op (done ++ [rv v]) rest denv :: k, m⟩) ?_ ?_
    · apply next_reaches
      · intro o; simp
      · simp [request, requestAux, awaitsScheduling]
    · simpa using args_chain_sub IH hr op k m rest q (done ++ [rv v]) w ws hq hws

theorem args_reaches_sub {fuel : Nat} (IH : FoldsSub file labels fuel) {env : WEnv} {denv : Env}
    (hr : EnvSub env denv) (op : Prim) (ps : List PExp) (ws : List WVal)
    (hps : ps.mapM (eval file fuel env) = some ws) (c : Control) (k : List Frame)
    (m : Mem.Concrete.State) (live : ∀ o, c ≠ .halt o)
    (hreq : request file labels ⟨c, k, m⟩ = arguments op ps denv k) :
    Reaches file labels ⟨c, k, m⟩ ⟨.apply op (ws.map rv), k, m⟩ := by
  cases ps with
  | nil =>
    simp at hps
    subst hps
    exact next_reaches file labels _ _ _ _ m live (by simpa [arguments] using hreq)
  | cons p rest =>
    obtain ⟨v, vs, hp, hvs, rfl⟩ := mapM_cons_some hps
    exact (next_reaches file labels _ _ _ _ m live (by simpa [arguments] using hreq)).trans
      (by simpa using args_chain_sub file labels IH hr op k m rest p [] v vs hp hvs)

/-- **Agreement**: a folded pure expression reduces to its folded value under `EnvSub`. -/
theorem eval_reaches_sub' : ∀ fuel, FoldsSub file labels fuel
  | 0 => by intro env p v h; simp [eval] at h
  | fuel+1 => by
    have IH := eval_reaches_sub' fuel
    intro env p v h denv hr k m
    have live : ∀ c : Control, (∀ o, c ≠ .halt o) → True := fun _ _ => trivial
    rcases p with ⟨a, u, e⟩
    cases e with
    | val w =>
      simp only [eval, Option.some.injEq] at h
      subst h
      apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
    | sym s =>
      simp only [eval] at h
      have hl : denv.lookup s = some (rv v) := hr s v h
      apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hl]
    | impl c =>
      simp only [eval] at h
      cases hc : file.impl.lookup c with
      | none => simp [hc] at h
      | some d =>
        cases d with
        | constant bt body =>
          simp only [hc] at h
          refine Relation.ReflTransGen.trans (b := ⟨.pureExpr body denv, k, m⟩) ?_ (IH env body v h denv hr k m)
          apply next_reaches <;> simp [request, requestAux, awaitsScheduling, hc]
        | function _ _ _ => simp [hc] at h
    | ctor c ps =>
      simp only [eval] at h
      cases hps : ps.mapM (eval file fuel env) with
      | none => simp [hps] at h
      | some ws =>
        simp only [hps, bind, Option.bind] at h
        refine (args_reaches_sub file labels IH hr (.ctor c) ps ws hps _ k m (by intro o; simp)
          (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, ctor_ok h]
    | op b p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches_sub file labels IH hr (.bin b) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, bin_ok h]
    | convInt ty p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches_sub file labels IH hr (.conv ty) [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, conv_ok h]
    | catchExceptionalCondition ty op p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches_sub file labels IH hr (.catchInt ty op) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, catchInt_ok h]
    | wrapI ty op p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches_sub file labels IH hr (.wrapInt ty op) [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, wrapInt_ok h]
    | not p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches_sub file labels IH hr .notBool [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, notBool_ok h]
    | isSigned p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches_sub file labels IH hr (.isType 2) [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        have := fun tags => signedness_ok (s := true) h tags
        simp only [ite_true] at this
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, this]
    | isUnsigned p =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine (args_reaches_sub file labels IH hr (.isType 3) [p] [x] (one_mapM file hx) _ k m
          (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
        have := fun tags => signedness_ok (s := false) h tags
        simp only [Bool.false_eq_true, ite_false] at this
        apply next_reaches
        · intro o; simp
        · simp [request, requestAux, awaitsScheduling, this]
    | areCompatible p q =>
      simp only [eval] at h
      cases hx : eval file fuel env p with
      | none => simp [hx] at h
      | some x =>
        cases hy : eval file fuel env q with
        | none => simp [hx, hy] at h
        | some y =>
          simp only [hx, hy, bind, Option.bind] at h
          refine (args_reaches_sub file labels IH hr .compatible [p, q] [x, y] (two_mapM file hx hy) _ k m
            (by intro o; simp) (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
          apply next_reaches
          · intro o; simp
          · simp [request, requestAux, awaitsScheduling, compat_ok h]
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
            refine (args_reaches_sub file labels IH hr (.call name) ps ws hps _ k m (by intro o; simp)
              (request_arguments file labels (by simp [requestAux, awaitsScheduling]))).trans ?_
            refine Relation.ReflTransGen.trans
              (b := ⟨.pureExpr body (extendEnv (params.zip (ws.map rv)) ∅), k, m⟩) ?_ ?_
            · apply next_reaches
              · intro o; simp
              · simp [request, requestAux, awaitsScheduling, funBody_sound hf hl]
            · have he := (EnvSub.empty ∅).extend (params.zip ws)
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
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr p denv, .pureBind pat body denv :: k, m⟩) ?_ ?_
          · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
          refine (IH env p x hx denv hr _ m).trans ?_
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr body (extendEnv (bmap xs) denv), k, m⟩) ?_ ?_
          · apply next_reaches
            · intro o; simp
            · simp [request, requestAux, awaitsScheduling, matchP_rv, hm]
          · exact IH _ body v h _ (hr.extend xs) k m
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
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr p denv, .pureCase bs denv :: k, m⟩) ?_ ?_
          · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
          refine (IH env p x hx denv hr _ m).trans ?_
          refine Relation.ReflTransGen.trans
            (b := ⟨.pureExpr body (extendEnv (bmap xs) denv), k, m⟩) ?_ ?_
          · apply next_reaches
            · intro o; simp
            · simp [request, requestAux, awaitsScheduling, select_rv x bs hm]
          · exact IH _ body v h _ (hr.extend xs) k m
    | if_ c yes no =>
      simp only [eval] at h
      cases hx : eval file fuel env c with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind] at h
        refine Relation.ReflTransGen.trans
          (b := ⟨.pureExpr c denv, .pureIf yes no denv :: k, m⟩) ?_ ?_
        · apply next_reaches <;> simp [request, requestAux, awaitsScheduling]
        refine (IH env c x hx denv hr _ m).trans ?_
        cases x
        case true =>
          refine Relation.ReflTransGen.trans (b := ⟨.pureExpr yes denv, k, m⟩) ?_ (IH env yes v h denv hr k m)
          apply next_reaches <;> simp [request, requestAux, awaitsScheduling, runtimeValue]
        case false =>
          refine Relation.ReflTransGen.trans (b := ⟨.pureExpr no denv, k, m⟩) ?_ (IH env no v h denv hr k m)
          apply next_reaches <;> simp [request, requestAux, awaitsScheduling, runtimeValue]
        all_goals simp at h
    | _ => simp [eval] at h


end StepsSub

/-- **Agreement in a larger environment**: a folded pure expression reduces to its folded
value whenever the run-time environment holds the folder's bindings. -/
theorem eval_reaches_sub (file : Program) (labels : Labels) (fuel : Nat) (env : WEnv) (p : PExp)
    (v : WVal) (h : eval file fuel env p = some v) (denv : Env) (hr : EnvSub env denv)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.pureExpr p denv, k, m⟩ ⟨.value (rv v), k, m⟩ :=
  eval_reaches_sub' file labels fuel env p v h denv hr k m

end Silmaril.Compile.Core.Verified.Fold
