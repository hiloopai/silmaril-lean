module

public import Silmaril.Compiler.Core.Source.PureLocal.Defs
/-! # Big-step pure evaluation with `let` and the type predicates

`PureEval.Eval` covers the pure forms of the `int` fragments. std.core's `wrapI` (the
wrap-around of every conversion to an integer type that does not hold the value) binds with
`let`, and `conv_int` tests `is_unsigned(ty)`. `Ev` is `Eval` with these two forms: `let pat =
p in body` and `is_unsigned(p)` (`.isType 3`). `Ev.of_eval` embeds `Eval`; `Ev.sound` and
`Ev.local` are `Eval.sound` and `PureLocal.Eval.local`: an evaluation is a run of the Core
machine, and a run of local steps under every call flag.

This is a proof device: nothing executable uses it.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.PureEvalExt

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState Reaches next_reaches Sound
  arguments_reaches request_of_arguments form_sound)
open Silmaril.Cerberus.Core.PureLocal (LSound form_local arguments_local plain_pureExpr plain_apply
  plain_value)
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches)

variable (file : Program) (tags : Mem.Concrete.Tags)

/-- `Eval` with `let` and `is_unsigned`. -/
inductive Ev : Env → PE ⊕ List PE → Val ⊕ List Val → Prop where
  | nil {env : Env} : Ev env (.inr []) (.inr [])
  | cons {env : Env} {p : PE} {ps : List PE} {v : Val} {vs : List Val} :
      Ev env (.inl p) (.inl v) → Ev env (.inr ps) (.inr vs) →
      Ev env (.inr (p :: ps)) (.inr (v :: vs))
  | val {env : Env} {ann : List Annot} {v : Value Codec.wireModel} :
      Ev env (.inl (.mk ann () (.val v))) (.inl (runtimeValue v))
  | sym {env : Env} {ann : List Annot} {s : Sym} {v : Val} :
      env.lookup s = some v → Ev env (.inl (.mk ann () (.sym s))) (.inl v)
  | ctor {env : Env} {ann : List Annot} {c : Ctor} {ps : List PE} {vs : List Val} {v : Val} :
      Ev env (.inr ps) (.inr vs) → primitive (.ctor c) vs tags = .ok v →
      Ev env (.inl (.mk ann () (.ctor c ps))) (.inl v)
  | op {env : Env} {ann : List Annot} {b : BinOp} {p q : PE} {vs : List Val} {v : Val} :
      Ev env (.inr [p, q]) (.inr vs) → primitive (.bin b) vs tags = .ok v →
      Ev env (.inl (.mk ann () (.op b p q))) (.inl v)
  | convInt {env : Env} {ann : List Annot} {ty : IntegerType} {p : PE} {vs : List Val} {v : Val} :
      Ev env (.inr [p]) (.inr vs) → primitive (.conv ty) vs tags = .ok v →
      Ev env (.inl (.mk ann () (.convInt ty p))) (.inl v)
  | catchInt {env : Env} {ann : List Annot} {ty : IntegerType} {iop : IntOp} {p q : PE}
      {vs : List Val} {v : Val} :
      Ev env (.inr [p, q]) (.inr vs) → primitive (.catchInt ty iop) vs tags = .ok v →
      Ev env (.inl (.mk ann () (.catchExceptionalCondition ty iop p q))) (.inl v)
  | wrapInt {env : Env} {ann : List Annot} {ty : IntegerType} {iop : IntOp} {p q : PE}
      {vs : List Val} {v : Val} :
      Ev env (.inr [p, q]) (.inr vs) → primitive (.wrapInt ty iop) vs tags = .ok v →
      Ev env (.inl (.mk ann () (.wrapI ty iop p q))) (.inl v)
  | not {env : Env} {ann : List Annot} {p : PE} {vs : List Val} {v : Val} :
      Ev env (.inr [p]) (.inr vs) → primitive .notBool vs tags = .ok v →
      Ev env (.inl (.mk ann () (.not p))) (.inl v)
  | isUnsigned {env : Env} {ann : List Annot} {p : PE} {vs : List Val} {v : Val} :
      Ev env (.inr [p]) (.inr vs) → primitive (.isType 3) vs tags = .ok v →
      Ev env (.inl (.mk ann () (.isUnsigned p))) (.inl v)
  | ifTrue {env : Env} {ann : List Annot} {p yes no : PE} {v : Val} :
      Ev env (.inl p) (.inl .true) → Ev env (.inl yes) (.inl v) →
      Ev env (.inl (.mk ann () (.if_ p yes no))) (.inl v)
  | ifFalse {env : Env} {ann : List Annot} {p yes no : PE} {v : Val} :
      Ev env (.inl p) (.inl .false) → Ev env (.inl no) (.inl v) →
      Ev env (.inl (.mk ann () (.if_ p yes no))) (.inl v)
  | let_ {env : Env} {ann : List Annot} {pat : Pattern Sym} {p body : PE} {x : Val}
      {xs : Bindings} {v : Val} :
      Ev env (.inl p) (.inl x) → matchPattern pat x = some xs →
      Ev (extendEnv xs env) (.inl body) (.inl v) →
      Ev env (.inl (.mk ann () (.let_ pat p body))) (.inl v)
  | case_ {env : Env} {ann : List Annot} {p : PE} {bs : List (Pattern Sym × PE)} {x : Val}
      {xs : Bindings} {body : PE} {v : Val} :
      Ev env (.inl p) (.inl x) → selectCase x bs = some (xs, body) →
      Ev (extendEnv xs env) (.inl body) (.inl v) →
      Ev env (.inl (.mk ann () (.case_ p bs))) (.inl v)
  | call {env : Env} {ann : List Annot} {name : Name Sym} {ps : List PE} {vs : List Val}
      {body : PE} {env' : Env} {v : Val} :
      Ev env (.inr ps) (.inr vs) → functionBody file name vs = .ok (body, env') →
      Ev env' (.inl body) (.inl v) →
      Ev env (.inl (.mk ann () (.call name ps))) (.inl v)

/-- Every `Eval` is an `Ev`. -/
theorem Ev.of_eval {env : Env} {x : PE ⊕ List PE} {y : Val ⊕ List Val}
    (h : Eval file tags env x y) : Ev file tags env x y := by
  induction h with
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | val => exact .val
  | sym h => exact .sym h
  | ctor _ h ih => exact .ctor ih h
  | op _ h ih => exact .op ih h
  | convInt _ h ih => exact .convInt ih h
  | catchInt _ h ih => exact .catchInt ih h
  | wrapInt _ h ih => exact .wrapInt ih h
  | not _ h ih => exact .not ih h
  | ifTrue _ _ ih₁ ih₂ => exact .ifTrue ih₁ ih₂
  | ifFalse _ _ ih₁ ih₂ => exact .ifFalse ih₁ ih₂
  | case_ _ h _ ih₁ ih₂ => exact .case_ ih₁ h ih₂
  | call _ h _ ih₁ ih₂ => exact .call ih₁ h ih₂

theorem apply_isType_reaches {labels : Labels} {k' : Nat} {vs : List Val} {v : Val}
    {k : List Frame} {m : Mem.Concrete.State}
    (h : primitive (.isType k') vs (tagsOf file m) = .ok v) :
    Reaches file labels ⟨.apply (.isType k') vs, k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  unfold tagsOf at h
  simp [request, requestAux, awaitsScheduling, h]

/-- **Soundness of `Ev`**: an evaluation is a run of the Core machine. -/
theorem Ev.sound {env : Env} {x : PE ⊕ List PE} {y : Val ⊕ List Val}
    (h : Ev file tags env x y) : Sound file tags env x y := by
  induction h with
  | nil => intro labels op acc k m _; simpa [argState] using Relation.ReflTransGen.refl
  | @cons env p ps v vs _ _ ihp ihps =>
    intro labels op acc k m htags
    refine (ihp labels _ m htags).trans ?_
    cases ps with
    | nil =>
      refine (next_reaches (c' := .apply op (acc ++ [v])) (k' := k)
        (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
      simpa [argState] using ihps labels op (acc ++ [v]) k m htags
    | cons q qs =>
      refine (next_reaches (c' := .pureExpr q env) (k' := .arguments op (acc ++ [v]) qs env :: k)
        (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
      simpa [argState] using ihps labels op (acc ++ [v]) k m htags
  | val =>
    intro labels k m _
    apply next_reaches (by intro o h; cases h)
    simp [request, requestAux, awaitsScheduling]
  | sym hs =>
    intro labels k m _
    apply next_reaches (by intro o h; cases h)
    simp [request, requestAux, awaitsScheduling, hs]
  | ctor _ hp ih =>
    exact form_sound file tags (op := .ctor _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | op _ hp ih =>
    exact form_sound file tags (op := .bin _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | convInt _ hp ih =>
    exact form_sound file tags (op := .conv _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | catchInt _ hp ih =>
    exact form_sound file tags (op := .catchInt _ _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | wrapInt _ hp ih =>
    exact form_sound file tags (op := .wrapInt _ _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | not _ hp ih =>
    exact form_sound file tags (op := .notBool) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | @isUnsigned env ann p vs v _ hp ih =>
    intro labels k m htags
    refine (arguments_reaches file (.isType 3) [p] env k m _ rfl
      (request_of_arguments file (by simp [requestAux, awaitsScheduling]))
      (by intro o h; cases h)).trans ((ih labels (.isType 3) [] k m htags).trans ?_)
    exact apply_isType_reaches file (by rw [htags]; exact hp)
  | @ifTrue env ann p yes no v _ _ ihp ihy =>
    intro labels k m htags
    refine (next_reaches (c' := .pureExpr p env) (k' := .pureIf yes no env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (next_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans
      (ihy labels k m htags)
  | @ifFalse env ann p yes no v _ _ ihp ihn =>
    intro labels k m htags
    refine (next_reaches (c' := .pureExpr p env) (k' := .pureIf yes no env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (next_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans
      (ihn labels k m htags)
  | @let_ env ann pat p body x xs v _ hm _ ihp ihb =>
    intro labels k m htags
    refine (next_reaches (c' := .pureExpr p env) (k' := .pureBind pat body env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (next_reaches (by intro o h; cases h)
      (by simp [request, requestAux, awaitsScheduling, hm])).trans (ihb labels k m htags)
  | @case_ env ann p bs x xs body v _ hsel _ ihp ihb =>
    intro labels k m htags
    refine (next_reaches (c' := .pureExpr p env) (k' := .pureCase bs env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (next_reaches (by intro o h; cases h)
      (by simp [request, requestAux, awaitsScheduling, hsel])).trans (ihb labels k m htags)
  | @call env ann name ps vs body env' v _ hbody _ iha ihb =>
    intro labels k m htags
    refine (arguments_reaches file (.call name) ps env k m _ rfl
      (request_of_arguments file (by simp [requestAux, awaitsScheduling])) (by intro o h; cases h)).trans ?_
    refine (iha labels (.call name) [] k m htags).trans ?_
    exact (next_reaches (by intro o h; cases h)
      (by simp [request, requestAux, awaitsScheduling, hbody])).trans (ihb labels k m htags)

/-- `Ev.sound` for one expression. -/
theorem ev_reaches {labels : Labels} {env : Env} {p : PE} {v : Val}
    (h : Ev file tags env (.inl p) (.inl v)) (k : List Frame) (m : Mem.Concrete.State)
    (htags : tagsOf file m = tags) :
    Reaches file labels ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩ :=
  Ev.sound file tags h labels k m htags

/-- `Ev.sound` for operands. -/
theorem args_reaches {labels : Labels} {env : Env} {ps : List PE} {vs : List Val}
    (h : Ev file tags env (.inr ps) (.inr vs)) (op : Prim) (acc : List Val) (k : List Frame)
    (m : Mem.Concrete.State) (htags : tagsOf file m = tags) :
    Reaches file labels (argState op acc ps env k m) ⟨.apply op (acc ++ vs), k, m⟩ :=
  Ev.sound file tags h labels op acc k m htags

/-- **An evaluation is a local run**, under every call flag. -/
theorem Ev.local {wc : Bool} {env : Env} {x : PE ⊕ List PE} {y : Val ⊕ List Val}
    (h : Ev file tags env x y) : LSound file tags wc env x y := by
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
  | @isUnsigned env ann p vs v _ hp ih =>
    intro labels k m htags
    refine (arguments_local file (.isType 3) [p] env k m wc
      (by simp [requestAux, awaitsScheduling])).trans
      ((ih labels (.isType 3) [] k m htags).trans ?_)
    refine .single (.next ?_ (plain_value v))
    rw [← htags] at hp
    unfold tagsOf at hp
    simp [requestAux, awaitsScheduling, hp]
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
  | @let_ env ann pat p body x xs v _ hm _ ihp ihb =>
    intro labels k m htags
    refine .head (.next (c' := .pureExpr p env) (k' := .pureBind pat body env :: k)
      (by simp [requestAux, awaitsScheduling]) (plain_pureExpr _ _)) ?_
    refine (ihp labels _ m htags).trans ?_
    exact .head (.next (by simp [requestAux, awaitsScheduling, hm]) (plain_pureExpr _ _))
      (ihb labels k m htags)
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

/-- `Ev.local` for one expression. -/
theorem ev_local {wc : Bool} {labels : Labels} {env : Env} {p : PE} {v : Val}
    (h : Ev file tags env (.inl p) (.inl v)) (k : List Frame) (m : Mem.Concrete.State)
    (htags : tagsOf file m = tags) :
    LocalReaches file labels wc ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩ :=
  Ev.local file tags (wc := wc) h labels k m htags

/-- `Ev.local` for operands. -/
theorem args_local {wc : Bool} {labels : Labels} {env : Env} {ps : List PE} {vs : List Val}
    (h : Ev file tags env (.inr ps) (.inr vs)) (op : Prim) (acc : List Val) (k : List Frame)
    (m : Mem.Concrete.State) (htags : tagsOf file m = tags) :
    LocalReaches file labels wc (argState op acc ps env k m) ⟨.apply op (acc ++ vs), k, m⟩ :=
  Ev.local file tags (wc := wc) h labels op acc k m htags

end Silmaril.Cerberus.Core.PureEvalExt
