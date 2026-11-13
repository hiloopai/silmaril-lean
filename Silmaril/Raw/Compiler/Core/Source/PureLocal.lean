module

public import Silmaril.Compiler.Core.Source.PureEval.Defs
public import Silmaril.Cerberus.Core.Interleave.Defs

/-! # Big-step pure evaluations are local runs

`PureEval.Eval.sound` turns an evaluation of a pure expression into a run of the Core LTS. Inside
a task of an `unseq` arena the arena drives the task by its own requests, read off `requestAux`
(`Interleave.LocalStep`), so a task needs the same evaluation as local steps. `Eval.local`: an
evaluation is a run of local steps under every call flag, over every continuation and memory with
the evaluation's tag environment; pure steps never change the memory.

This is a proof device: nothing executable uses it.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.PureLocal

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches Plain)

variable (file : Program) (tags : Mem.Concrete.Tags)

theorem plain_pureExpr (p : PE) (env : Env) : Plain (.pureExpr p env) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_apply (op : Prim) (vs : List Val) : Plain (.apply op vs) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem plain_value (v : Val) : Plain (.value v) :=
  ⟨(fun _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- A plain primitive answers by its result. -/
theorem requestAux_apply {labels : Labels} {op : Prim} (plain : PureEval.Plain op) (vs : List Val)
    (k : List Frame) (m : Mem.Concrete.State) (wc : Bool) :
    requestAux file labels m (.apply op vs) k wc =
      match primitive op vs (tagsOf file m) with
      | .ok v => .next (.value v) k
      | .error o => .end_ o := by
  unfold tagsOf
  cases op <;> simp only [PureEval.Plain] at plain <;>
    simp [requestAux, awaitsScheduling] <;> split <;> simp_all

theorem apply_local {labels : Labels} {op : Prim} (plain : PureEval.Plain op) {vs : List Val}
    {v : Val} {k : List Frame} {m : Mem.Concrete.State} (wc : Bool)
    (h : primitive op vs (tagsOf file m) = .ok v) :
    LocalReaches file labels wc ⟨.apply op vs, k, m⟩ ⟨.value v, k, m⟩ :=
  .single (.next (by rw [requestAux_apply file plain vs k m wc, h]) (plain_value v))

/-- Starting the operands of a form is one step. -/
theorem arguments_local {labels : Labels} {c : Control} (op : Prim) (ps : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (wc : Bool)
    (h : requestAux file labels m c k wc = arguments op ps env k) :
    LocalReaches file labels wc ⟨c, k, m⟩ (argState op [] ps env k m) := by
  cases ps with
  | nil => exact .single (.next (by simpa [arguments] using h) (plain_apply _ _))
  | cons p ps => exact .single (.next (by simpa [arguments] using h) (plain_pureExpr _ _))

/-- What `Eval` guarantees of local runs. -/
def LSound (wc : Bool) (env : Env) : PE ⊕ List PE → Val ⊕ List Val → Prop
  | .inl p, .inl v => ∀ labels k m, tagsOf file m = tags →
      LocalReaches file labels wc ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩
  | .inr ps, .inr vs => ∀ labels op acc k m, tagsOf file m = tags →
      LocalReaches file labels wc (argState op acc ps env k m) ⟨.apply op (acc ++ vs), k, m⟩
  | _, _ => True

theorem form_local {wc : Bool} {op : Prim} (plain : PureEval.Plain op) {p : PE} {ps : List PE}
    {vs : List Val} {v : Val} {env : Env}
    (first : ∀ labels k m, requestAux file labels m (.pureExpr p env) k wc = arguments op ps env k)
    (args : LSound file tags wc env (.inr ps) (.inr vs)) (h : primitive op vs tags = .ok v) :
    LSound file tags wc env (.inl p) (.inl v) := by
  intro labels k m htags
  refine (arguments_local file op ps env k m wc (first labels k m)).trans
    ((args labels op [] k m htags).trans ?_)
  exact apply_local file plain wc (by rw [htags]; exact h)

/-- **An evaluation is a local run**, under every call flag. -/
theorem Eval.local {wc : Bool} {env : Env} {x : PE ⊕ List PE} {y : Val ⊕ List Val}
    (h : Eval file tags env x y) : LSound file tags wc env x y := by
  induction h with
  | nil => intro labels op acc k m _; simpa [argState] using Relation.ReflTransGen.refl
  | @cons env p ps v vs _ _ ihp ihps =>
    intro labels op acc k m htags
    refine (ihp labels _ m htags).trans ?_
    cases ps with
    | nil =>
      refine .head (.next (c' := .apply op (acc ++ [v])) (k' := k)
        (by simp [requestAux, awaitsScheduling]) (plain_apply _ _)) ?_
      simpa [argState] using ihps labels op (acc ++ [v]) k m htags
    | cons q qs =>
      refine .head (.next (c' := .pureExpr q env) (k' := .arguments op (acc ++ [v]) qs env :: k)
        (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
      simpa [argState] using ihps labels op (acc ++ [v]) k m htags
  | val =>
    intro labels k m _
    exact .single (.next (by simp [requestAux, awaitsScheduling]) (plain_value _))
  | sym hs =>
    intro labels k m _
    exact .single (.next (by simp [requestAux, awaitsScheduling, hs]) (plain_value _))
  | ctor _ hp ih =>
    exact form_local file tags (op := .ctor _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih hp
  | op _ hp ih =>
    exact form_local file tags (op := .bin _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih hp
  | convInt _ hp ih =>
    exact form_local file tags (op := .conv _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih hp
  | catchInt _ hp ih =>
    exact form_local file tags (op := .catchInt _ _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih hp
  | wrapInt _ hp ih =>
    exact form_local file tags (op := .wrapInt _ _) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih hp
  | not _ hp ih =>
    exact form_local file tags (op := .notBool) trivial
      (fun _ _ _ => by simp [requestAux, awaitsScheduling]) ih hp
  | @ifTrue env ann p yes no v _ _ ihp ihy =>
    intro labels k m htags
    refine .head (.next (c' := .pureExpr p env) (k' := .pureIf yes no env :: k)
      (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
    refine (ihp labels _ m htags).trans ?_
    exact .head (.next (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _))
      (ihy labels k m htags)
  | @ifFalse env ann p yes no v _ _ ihp ihn =>
    intro labels k m htags
    refine .head (.next (c' := .pureExpr p env) (k' := .pureIf yes no env :: k)
      (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
    refine (ihp labels _ m htags).trans ?_
    exact .head (.next (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _))
      (ihn labels k m htags)
  | @case_ env ann p bs x xs body v _ hsel _ ihp ihb =>
    intro labels k m htags
    refine .head (.next (c' := .pureExpr p env) (k' := .pureCase bs env :: k)
      (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
    refine (ihp labels _ m htags).trans ?_
    exact .head (.next (by simp [requestAux, awaitsScheduling, hsel]) (plain_pureExpr _ _))
      (ihb labels k m htags)
  | @call env ann name ps vs body env' v _ hbody _ iha ihb =>
    intro labels k m htags
    refine (arguments_local file (.call name) ps env k m wc
      (by simp [requestAux, awaitsScheduling])).trans ?_
    refine (iha labels (.call name) [] k m htags).trans ?_
    exact .head (.next (by simp [requestAux, awaitsScheduling, hbody]) (plain_pureExpr _ _))
      (ihb labels k m htags)

/-- `Eval.local` for one expression. -/
theorem eval_local {wc : Bool} {labels : Labels} {env : Env} {p : PE} {v : Val}
    (h : Eval file tags env (.inl p) (.inl v)) (k : List Frame) (m : Mem.Concrete.State)
    (htags : tagsOf file m = tags) :
    LocalReaches file labels wc ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩ :=
  Eval.local file tags (wc := wc) h labels k m htags

/-- `Eval.local` for operands. -/
theorem args_local {wc : Bool} {labels : Labels} {env : Env} {ps : List PE} {vs : List Val}
    (h : Eval file tags env (.inr ps) (.inr vs)) (op : Prim) (acc : List Val) (k : List Frame)
    (m : Mem.Concrete.State) (htags : tagsOf file m = tags) :
    LocalReaches file labels wc (argState op acc ps env k m) ⟨.apply op (acc ++ vs), k, m⟩ :=
  Eval.local file tags (wc := wc) h labels op acc k m htags

end Silmaril.Cerberus.Core.PureLocal
