module

public import Silmaril.Cerberus.Core.Forced.Thms
public import Silmaril.Compiler.Core.Source.PureEval.Defs

/-! Strengthen the imported PureEval soundness proof: all its administrative
requests have locally unique successors, for arbitrary continuations, labels
and memory with the stated tag environment. No global determinism is assumed.
-/

@[expose] public section

namespace Silmaril.Compiler.Core.ElaborationTotal

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval
open Silmaril.Cerberus.Core

variable (file : Program) (tags : Mem.Concrete.Tags)

private theorem apply_forced {labels : Labels} {op : Prim} (plain : Plain op) {vs : List Val} {v : Val}
    {k : List Frame} {m : Mem.Concrete.State}
    (h : primitive op vs (tagsOf file m) = .ok v) :
    Forced.Reaches file labels ⟨.apply op vs, k, m⟩ ⟨.value v, k, m⟩ := by
  apply Forced.next (by intro o h; cases h)
  unfold tagsOf at h
  cases op <;> simp only [Plain] at plain <;>
    simp [request, requestAux, awaitsScheduling, h]

/-- Starting the operands of `op` is one step. -/
private theorem arguments_forced {labels : Labels} (op : Prim) (ps : List PE) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (start : State) (hstart : start.memory = m)
    (h : request file labels start = arguments op ps env k) (live : ∀ o, start.control ≠ .halt o) :
    Forced.Reaches file labels start (argState op [] ps env k m) := by
  obtain ⟨c, k0, m0⟩ := start
  cases hstart
  cases ps <;> exact Forced.next live (by simpa [arguments, argState] using h)

/-- What `Eval` guarantees of the machine. -/
def ForcedSound (env : Env) : PE ⊕ List PE → Val ⊕ List Val → Prop
  | .inl p, .inl v => ∀ labels k m, tagsOf file m = tags →
      Forced.Reaches file labels ⟨.pureExpr p env, k, m⟩ ⟨.value v, k, m⟩
  | .inr ps, .inr vs => ∀ labels op acc k m, tagsOf file m = tags →
      Forced.Reaches file labels (argState op acc ps env k m) ⟨.apply op (acc ++ vs), k, m⟩
  | _, _ => True

/-- A pure form that evaluates its operands and applies a plain primitive. -/
private theorem form_forced {op : Prim} (plain : Plain op) {p : PE} {ps : List PE} {vs : List Val}
    {v : Val} {env : Env}
    (first : ∀ labels k m, request file labels ⟨.pureExpr p env, k, m⟩ = arguments op ps env k)
    (args : ForcedSound file tags env (.inr ps) (.inr vs)) (h : primitive op vs tags = .ok v) :
    ForcedSound file tags env (.inl p) (.inl v) := by
  intro labels k m htags
  refine (arguments_forced file op ps env k m _ rfl (first labels k m) (by intro o h; cases h)).trans
    ((args labels op [] k m htags).trans ?_)
  exact apply_forced file plain (by rw [htags]; exact h)

/-- **Soundness of `Eval`**: an evaluation is a run of the Core machine. -/
theorem pureEvaluation_forced {env : Env} {x : PE ⊕ List PE} {y : Val ⊕ List Val}
    (h : Eval file tags env x y) : ForcedSound file tags env x y := by
  induction h with
  | nil => intro labels op acc k m _; simpa [argState] using Forced.Reaches.refl
  | @cons env p ps v vs _ _ ihp ihps =>
    show ForcedSound file tags env (.inr (p :: ps)) (.inr (v :: vs))
    intro labels op acc k m htags
    refine (ihp labels _ m htags).trans ?_
    cases ps with
    | nil =>
      refine (Forced.next (c' := .apply op (acc ++ [v])) (k' := k)
        (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
      simpa [argState] using ihps labels op (acc ++ [v]) k m htags
    | cons q qs =>
      refine (Forced.next (c' := .pureExpr q env) (k' := .arguments op (acc ++ [v]) qs env :: k)
        (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
      simpa [argState] using ihps labels op (acc ++ [v]) k m htags
  | val =>
    intro labels k m _
    apply Forced.next (by intro o h; cases h)
    simp [request, requestAux, awaitsScheduling]
  | sym hs =>
    intro labels k m _
    apply Forced.next (by intro o h; cases h)
    simp [request, requestAux, awaitsScheduling, hs]
  | ctor _ hp ih =>
    exact form_forced file tags (op := .ctor _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | op _ hp ih =>
    exact form_forced file tags (op := .bin _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | convInt _ hp ih =>
    exact form_forced file tags (op := .conv _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | catchInt _ hp ih =>
    exact form_forced file tags (op := .catchInt _ _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | wrapInt _ hp ih =>
    exact form_forced file tags (op := .wrapInt _ _) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | not _ hp ih =>
    exact form_forced file tags (op := .notBool) trivial
      (fun _ _ _ => request_of_arguments file (by simp [requestAux, awaitsScheduling])) ih hp
  | @ifTrue env ann p yes no v _ _ ihp ihy =>
    intro labels k m htags
    refine (Forced.next (c' := .pureExpr p env) (k' := .pureIf yes no env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (Forced.next (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans
      (ihy labels k m htags)
  | @ifFalse env ann p yes no v _ _ ihp ihn =>
    intro labels k m htags
    refine (Forced.next (c' := .pureExpr p env) (k' := .pureIf yes no env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (Forced.next (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans
      (ihn labels k m htags)
  | @case_ env ann p bs x xs body v _ hsel _ ihp ihb =>
    intro labels k m htags
    refine (Forced.next (c' := .pureExpr p env) (k' := .pureCase bs env :: k)
      (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])).trans ?_
    refine (ihp labels _ m htags).trans ?_
    exact (Forced.next (by intro o h; cases h)
      (by simp [request, requestAux, awaitsScheduling, hsel])).trans (ihb labels k m htags)
  | @call env ann name ps vs body env' v _ hbody _ iha ihb =>
    intro labels k m htags
    refine (arguments_forced file (.call name) ps env k m _ rfl
      (request_of_arguments file (by simp [requestAux, awaitsScheduling])) (by intro o h; cases h)).trans ?_
    refine (iha labels (.call name) [] k m htags).trans ?_
    exact (Forced.next (by intro o h; cases h)
      (by simp [request, requestAux, awaitsScheduling, hbody])).trans (ihb labels k m htags)

end Silmaril.Compiler.Core.ElaborationTotal
