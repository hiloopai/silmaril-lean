module

public import Silmaril.Logic.ACL2.Recursive.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Recursive

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Recursive

variable {S R : Signature} {n : Nat}
variable {B : Block S} {M : Model S}
  {lt : Call B.members M.primitives.Value → Call B.members M.primitives.Value → Prop}

private theorem reduct_interpret (wf : WellFounded lt) (h : B.TerminatesBy M lt) :
    (fun {k} => @((B.modelBy M wf h).reduct B.inclusion).interpret k) =
      (fun {k} => @M.interpret k) := by
  funext k f args
  have hf : B.members.arity f.val ≠ some k := by
    intro hm
    have declared := f.property
    simp [B.fresh hm] at declared
  simp [Model.reduct, Block.modelBy, Signature.Hom.symbol, hf]

theorem model_reduct (wf : WellFounded lt) (h : B.TerminatesBy M lt) : (B.modelBy M wf h).reduct B.inclusion = M :=
  congrArg (Model.mk M.primitives) (reduct_interpret wf h)

theorem model_interpret (wf : WellFounded lt) (h : B.TerminatesBy M lt) (state : Call B.members M.primitives.Value) :
    (B.modelBy M wf h).interpret (B.symbol state.symbol) state.args =
      B.interpretBy M wf h state := by
  cases state with
  | mk k f args => simp [Block.modelBy, Block.symbol, f.property]

theorem interpret_unfold (wf : WellFounded lt) (h : B.TerminatesBy M lt) (state : Call B.members M.primitives.Value) :
    B.interpretBy M wf h state =
      (B.body state.symbol).evalWith M state.args
        (fun next _ => B.interpretBy M wf h next) (h state) := by
  unfold Block.interpretBy
  rw [WellFounded.fix_eq]

theorem eval_map (wf : WellFounded lt) (h : B.TerminatesBy M lt) (env : Env M n) (term : Term S n) :
    (term.map B.inclusion).eval (B.modelBy M wf h) env = term.eval M env := by
  refine (Term.eval_map B.inclusion (B.modelBy M wf h) env term).trans ?_
  let evaluate (interp : ∀ {k : Nat}, S.Symbol k → Env M k → M.primitives.Value) :
      M.primitives.Value := term.eval (Model.mk M.primitives (fun {k} => @interp k)) env
  exact congrArg evaluate (reduct_interpret wf h)

theorem eval_toTerm (wf : WellFounded lt) (h : B.TerminatesBy M lt) (caller : Call B.members M.primitives.Value) (env : Env M n)
    (body : Body S B.members n) (decreases : body.CallsSatisfy M env (fun next => lt next caller)) :
    (body.toTerm B).eval (B.modelBy M wf h) env =
      body.evalWith M env (fun next _ => B.interpretBy M wf h next) decreases := by
  induction body with
  | base term => simpa only [Body.toTerm, Body.evalWith] using eval_map wf h env term
  | call f args =>
    simp only [Body.toTerm, Body.evalWith, Term.eval, eval_map wf h]
    exact model_interpret wf h (Call.ofTerms M env f args)
  | apply context args ih =>
    rw (config := { transparency := .default })
      [Body.toTerm, Term.eval_subst, eval_map wf h]
    simp only [Body.evalWith]
    exact congrArg (fun values => context.eval M values) (funext fun i => ih i (decreases i))
  | ite test yes no ihy ihn =>
    simp only [Body.toTerm, Term.eval, Body.evalWith, Primitives.ite]
    rw (config := { transparency := .default }) [eval_map wf h env test]
    by_cases ht : test.eval M env = M.primitives.nil
    · simpa only [Block.modelBy, ht, ite_true, dite_true] using ihn (decreases.2 ht)
    · simpa only [Block.modelBy, ht, ite_false, dite_false] using ihy (decreases.1 ht)

theorem equation (wf : WellFounded lt) (h : B.TerminatesBy M lt) {k : Nat} (f : B.members.Symbol k) :
    (B.equation f).Holds (B.modelBy M wf h) := by
  apply (Sentence.holds_eq _ _ _).2
  intro env
  let state : Call B.members M.primitives.Value := ⟨k, f, env⟩
  change (B.modelBy M wf h).interpret (B.symbol f) env =
    ((B.body f).toTerm B).eval (B.modelBy M wf h) env
  rw [model_interpret wf h state, interpret_unfold wf h state]
  exact (eval_toTerm wf h state env (B.body f) (h state)).symm

theorem callsSatisfy_mono (M : Model S) (env : Env M n)
    {p q : Call R M.primitives.Value → Prop} (imp : ∀ state, p state → q state)
    (body : Body S R n) (h : body.CallsSatisfy M env p) : body.CallsSatisfy M env q := by
  induction body with
  | base => trivial
  | call => exact imp _ h
  | apply _ _ ih => exact fun i => ih i (h i)
  | ite _ _ _ ihy ihn => exact ⟨fun ht => ihy (h.1 ht), fun ht => ihn (h.2 ht)⟩

theorem callInduction (wf : WellFounded lt) (h : B.TerminatesBy M lt) (p : Call B.members M.primitives.Value → Prop)
    (step : ∀ state, (B.body state.symbol).CallsSatisfy M state.args p → p state) :
    ∀ state, p state := by
  intro state
  induction state using wf.induction with
  | h state ih => exact step state (callsSatisfy_mono M state.args ih _ (h state))

end Silmaril.Proofs.Logic.ACL2.Recursive
