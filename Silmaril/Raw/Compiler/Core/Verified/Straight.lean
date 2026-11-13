module

public import Silmaril.Compiler.Core.Verified.ConvInt.Defs
public import Silmaril.Compiler.Core.Verified.ReturnConst.Defs

/-! # Effectful steps of straight-line `main` bodies

Lemmas about the Core machine on the effectful forms of an elaborated straight-line C body:
`bound`, strong and weak sequencing, `pure`, and `run` of the procedure's return label, with
source-location annotations (`ReturnConst.focusMemory`). Each holds for every environment,
continuation and memory; none changes stdout.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Straight

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory focusMemory_stdout)

variable {file : Program} {labels : Labels}

theorem update_reaches {c c' : Control} {k k' : List Frame} {m m' : Mem.Concrete.State}
    (live : ∀ o, c ≠ .halt o) (h : request file labels ⟨c, k, m⟩ = .update m' c' k') :
    Reaches file labels ⟨c, k, m⟩ ⟨c', k', m'⟩ := by
  apply Relation.ReflTransGen.single
  refine ⟨.tau, Step.respond live ?_⟩
  rw [h]
  exact Respond.update

/-- A focused effect (one that sets the source location from its annotations) whose request,
with the focused memory, is `next c' k'`: the machine reaches `c'` with the focused memory, in
one step, or two when the location changes. -/
theorem focus_reaches {ann : List Annot} {e : ExprNode Codec.wireModel Unit Unit Sym}
    {env : Env} {k : List Frame} {m : Mem.Concrete.State} {c' : Control} {k' : List Frame}
    (h : request file labels ⟨.effectExpr (.mk ann e) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then .next c' k'
      else .next (.setLocation (focusMemory ann m).currentLocation c') k') :
    Reaches file labels ⟨.effectExpr (.mk ann e) env, k, m⟩ ⟨c', k', focusMemory ann m⟩ := by
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation
  · have same : focusMemory ann m = m := by
      have eq : (focusMemory ann m).currentLocation = m.currentLocation := by simpa using equal
      revert eq
      unfold focusMemory
      split
      · split
        · intro _; rfl
        · intro eq
          simp only at eq
          subst eq
          rfl
      · intro _; rfl
    rw [same]
    exact next_reaches (by intro o h; cases h) (by rw [h, same]; simp)
  · refine (next_reaches (c' := .setLocation (focusMemory ann m).currentLocation c') (k' := k')
      (by intro o h; cases h) (by rw [h]; simp [equal])).trans ?_
    refine update_reaches (by intro o h; cases h) ?_
    have : ({m with currentLocation := (focusMemory ann m).currentLocation} : Mem.Concrete.State) =
        focusMemory ann m := by
      unfold focusMemory
      split
      · split <;> rfl
      · rfl
    rw [← this]
    simp [request, requestAux, awaitsScheduling]

theorem request_run {ann : List Annot} {l : Sym} {p : PE} {rest : List PE} {env : Env}
    {k : List Frame} {m : Mem.Concrete.State} :
    request file labels ⟨.effectExpr (.mk ann (.run () l (p :: rest))) env, k, m⟩ =
      if (focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr p env) (.runLabel l [] rest env :: k)
      else .next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.runLabel l [] rest env :: k) := by
  simp only [request, requestAux, awaitsScheduling]
  change (match (if (focusMemory ann m).currentLocation == m.currentLocation then
        Request.next (.pureExpr p env) (.runLabel l [] rest env :: k)
      else Request.next (.setLocation (focusMemory ann m).currentLocation (.pureExpr p env))
        (.runLabel l [] rest env :: k)) with
    | .next (.jumping s vs env) k => jump labels s vs env k
    | r => r) = _
  by_cases equal : (focusMemory ann m).currentLocation == m.currentLocation <;> simp [equal]

end Silmaril.Compile.Core.Verified.Straight
