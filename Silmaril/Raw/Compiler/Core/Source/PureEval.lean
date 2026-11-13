module

public import Silmaril.Compiler.Core.Spec.Defs

/-! # Big-step evaluation of Core pure expressions, sound for the Core machine

The Core dynamics (`Silmaril.Cerberus.Core.Dynamics`) evaluates a pure expression in many small
steps: operands through `arguments` frames, then one `apply` of the primitive, calls by unfolding
the callee's body. `Eval` is the big-step relation of that evaluation for the pure forms the
verified compiler meets (literals, symbols, constructors, binary operators, integer conversions
and guards, `if`, `case`, calls of pure functions). `Eval.reaches`: an evaluation is a run of the
machine, from `pureExpr p env` to `value v`, for every continuation and memory whose tag
environment is the one of the evaluation. Pure steps never change the memory.

This relation is a proof device: nothing executable uses it.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.PureEval

open Silmaril.Cerberus.Core.Dynamics

/-- The source relation of the specification: any transition of the Core LTS. -/
abbrev Reaches (file : Program) (labels : Labels) :=
  Relation.ReflTransGen (Silmaril.Compile.Core.Spec.coreStep file labels)

/-- One deterministic `next` transition. -/
theorem next_reaches {file : Program} {labels : Labels} {c c' : Control} {k k' : List Frame}
    {m : Mem.Concrete.State} (live : ∀ o, c ≠ .halt o)
    (h : request file labels ⟨c, k, m⟩ = .next c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.tau, Step.respond live ?_⟩
  rw [h]
  exact Respond.next

/-- The tag environment of the dynamics in memory `m`. -/
def tagsOf (file : Program) (m : Mem.Concrete.State) : Mem.Concrete.Tags :=
  ⟨file.tagDefs, m.enumTypes⟩

variable (file : Program) (tags : Mem.Concrete.Tags)

/-- Big-step evaluation of pure expressions (`inl`) and of operand lists (`inr`). -/
inductive Eval : Env → PE ⊕ List PE → Val ⊕ List Val → Prop where
  | nil {env : Env} : Eval env (.inr []) (.inr [])
  | cons {env : Env} {p : PE} {ps : List PE} {v : Val} {vs : List Val} :
      Eval env (.inl p) (.inl v) → Eval env (.inr ps) (.inr vs) →
      Eval env (.inr (p :: ps)) (.inr (v :: vs))
  | val {env : Env} {ann : List Annot} {v : Value Codec.wireModel} :
      Eval env (.inl (.mk ann () (.val v))) (.inl (runtimeValue v))
  | sym {env : Env} {ann : List Annot} {s : Sym} {v : Val} :
      env.lookup s = some v → Eval env (.inl (.mk ann () (.sym s))) (.inl v)
  | ctor {env : Env} {ann : List Annot} {c : Ctor} {ps : List PE} {vs : List Val} {v : Val} :
      Eval env (.inr ps) (.inr vs) → primitive (.ctor c) vs tags = .ok v →
      Eval env (.inl (.mk ann () (.ctor c ps))) (.inl v)
  | op {env : Env} {ann : List Annot} {b : BinOp} {p q : PE} {vs : List Val} {v : Val} :
      Eval env (.inr [p, q]) (.inr vs) → primitive (.bin b) vs tags = .ok v →
      Eval env (.inl (.mk ann () (.op b p q))) (.inl v)
  | convInt {env : Env} {ann : List Annot} {ty : IntegerType} {p : PE} {vs : List Val} {v : Val} :
      Eval env (.inr [p]) (.inr vs) → primitive (.conv ty) vs tags = .ok v →
      Eval env (.inl (.mk ann () (.convInt ty p))) (.inl v)
  | catchInt {env : Env} {ann : List Annot} {ty : IntegerType} {iop : IntOp} {p q : PE}
      {vs : List Val} {v : Val} :
      Eval env (.inr [p, q]) (.inr vs) → primitive (.catchInt ty iop) vs tags = .ok v →
      Eval env (.inl (.mk ann () (.catchExceptionalCondition ty iop p q))) (.inl v)
  | wrapInt {env : Env} {ann : List Annot} {ty : IntegerType} {iop : IntOp} {p q : PE}
      {vs : List Val} {v : Val} :
      Eval env (.inr [p, q]) (.inr vs) → primitive (.wrapInt ty iop) vs tags = .ok v →
      Eval env (.inl (.mk ann () (.wrapI ty iop p q))) (.inl v)
  | not {env : Env} {ann : List Annot} {p : PE} {vs : List Val} {v : Val} :
      Eval env (.inr [p]) (.inr vs) → primitive .notBool vs tags = .ok v →
      Eval env (.inl (.mk ann () (.not p))) (.inl v)
  | ifTrue {env : Env} {ann : List Annot} {p yes no : PE} {v : Val} :
      Eval env (.inl p) (.inl .true) → Eval env (.inl yes) (.inl v) →
      Eval env (.inl (.mk ann () (.if_ p yes no))) (.inl v)
  | ifFalse {env : Env} {ann : List Annot} {p yes no : PE} {v : Val} :
      Eval env (.inl p) (.inl .false) → Eval env (.inl no) (.inl v) →
      Eval env (.inl (.mk ann () (.if_ p yes no))) (.inl v)
  | case_ {env : Env} {ann : List Annot} {p : PE} {bs : List (Pattern Sym × PE)} {x : Val}
      {xs : Bindings} {body : PE} {v : Val} :
      Eval env (.inl p) (.inl x) → selectCase x bs = some (xs, body) →
      Eval (extendEnv xs env) (.inl body) (.inl v) →
      Eval env (.inl (.mk ann () (.case_ p bs))) (.inl v)
  | call {env : Env} {ann : List Annot} {name : Name Sym} {ps : List PE} {vs : List Val}
      {body : PE} {env' : Env} {v : Val} :
      Eval env (.inr ps) (.inr vs) → functionBody file name vs = .ok (body, env') →
      Eval env' (.inl body) (.inl v) →
      Eval env (.inl (.mk ann () (.call name ps))) (.inl v)

/-- The machine state that starts evaluating the operands `ps` of `op`, `acc` already done. -/
def argState (op : Prim) (acc : List Val) (ps : List PE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) : State :=
  match ps with
  | [] => ⟨.apply op acc, k, m⟩
  | p :: rest => ⟨.pureExpr p env, .arguments op acc rest env :: k, m⟩

/-- The primitives that `requestAux` applies through `primitive`, without scheduling. -/
def Plain : Prim → Prop
  | .ctor _ | .bin _ | .conv _ | .catchInt _ _ | .wrapInt _ _ | .notBool => True
  | _ => False

theorem apply_reaches {labels : Labels} {op : Prim} (plain : Plain op) {vs : List Val} {v : Val}
    {k : List Frame} {m : Mem.Concrete.State}
    (h : primitive op vs (tagsOf file m) = .ok v) :
    Reaches file labels ⟨.apply op vs, k, m⟩ ⟨.value v, k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  unfold tagsOf at h
  cases op <;> simp only [Plain] at plain <;>
    simp [request, requestAux, awaitsScheduling, h]

/-- Starting the operands of `op` is one step. -/
theorem arguments_reaches {labels : Labels} (op : Prim) (ps : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (start : State) (hstart : start.memory = m)
    (h : request file labels start = arguments op ps env k) (live : ∀ o, start.control ≠ .halt o) :
    Reaches file labels start (argState op [] ps env k m) := by
  obtain ⟨c, k0, m0⟩ := start
  cases hstart
  cases ps <;> exact next_reaches live (by simpa [arguments, argState] using h)

/-- `arguments` never requests a label transfer, so `request` is `requestAux` there. -/
theorem request_of_arguments {labels : Labels} {c : Control} {k : List Frame}
    {m : Mem.Concrete.State} {op : Prim} {ps : List PE} {env : Env}
    (h : requestAux file labels m c k = arguments op ps env k) :
    request file labels ⟨c, k, m⟩ = arguments op ps env k := by
  unfold request
  simp only [h]
  cases ps <;> rfl

/-- What `Eval` guarantees of the machine. -/
def Sound (env : Env) : PE ⊕ List PE → Val ⊕ List Val → Prop
  | .inl p, .inl v => ∀ labels k m, tagsOf file m = tags →
      Reaches file labels ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩
  | .inr ps, .inr vs => ∀ labels op acc k m, tagsOf file m = tags →
      Reaches file labels (argState op acc ps env k m) ⟨.apply op (acc ++ vs), k, m⟩
  | _, _ => True

/-- A pure form that evaluates its operands and applies a plain primitive. -/
theorem form_sound {op : Prim} (plain : Plain op) {p : PE} {ps : List PE} {vs : List Val}
    {v : Val} {env : Env}
    (first : ∀ labels k m, request file labels ⟨.pureExpr p env, k, m⟩ = arguments op ps env k)
    (args : Sound file tags env (.inr ps) (.inr vs)) (h : primitive op vs tags = .ok v) :
    Sound file tags env (.inl p) (.inl v) := by
  intro labels k m htags
  refine (arguments_reaches file op ps env k m _ rfl (first labels k m) (by intro o h; cases h)).trans
    ((args labels op [] k m htags).trans ?_)
  exact apply_reaches file plain (by rw [htags]; exact h)

/-- **Soundness of `Eval`**: an evaluation is a run of the Core machine. -/
theorem Eval.sound {env : Env} {x : PE ⊕ List PE} {y : Val ⊕ List Val}
    (h : Eval file tags env x y) : Sound file tags env x y := by
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

end Silmaril.Cerberus.Core.PureEval
