module

public import Silmaril.Cerberus.Core.LoopReach.Defs
public import Silmaril.Compiler.Core.Verified.Straight.Defs
public import Silmaril.Compiler.Core.Verified.StateMem.Defs

/-! # Annotated saved-label transfers carrying local object pointers

Real C loops carry pointers to their local objects in saved-label parameters.
Their `run` nodes carry source locations. Extend the unannotated `LoopReach`
entry rule to these nodes, retaining the original procedure context and the
source slot invariant when a parameter rebinds the same object pointer.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopTransfer

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open StateMem (Local Inv ptr)
open SeqReach (Reaches PureEval)

/-- The actual annotated, nonempty-argument transfer used by a loop with locals.
Arguments are evaluated in the old environment, then rebound simultaneously. -/
theorem run_reaches {file : Program} {labels : Labels}
    (ann : List Annot) (s : Sym) (env : Env) (p : PE) (ps : List PE) (v : Val) (vs : List Val)
    (hp : PureEval file labels p env v)
    (rest : List.Forall₂ (fun p v => PureEval file labels p env v) ps vs)
    (k retained : List Frame) (localLabels : Labels) (params : List Sym) (body : EE)
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup s = some (params, body))
    (arity : params.length = (v :: vs).length) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.effectExpr (.mk ann (.run () s (p :: ps))) env, k, m⟩
      ⟨.effectExpr body (extendEnv (params.zip (v :: vs)) env), retained,
        ReturnConst.focusMemory ann m⟩ := by
  exact (Straight.focus_reaches Straight.request_run).trans
    ((hp _ _).trans (LoopReach.run_arguments_reaches rest [] v k retained (ReturnConst.focusMemory ann m) localLabels params body
      context lookup arity))

/-- Rebinding a local parameter to the same allocation preserves every slot fact.
This permits saved-label entry to reuse the existing source-memory invariant. -/
theorem rebind {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : StateExpr.Key → Option IntExpr.Term} (inv : Inv env m ls ds)
    {l : Local} (hl : l ∈ ls) (x : Sym) (key : x.key = l.sym.key) :
    Inv (extendEnv [(x, ptr l)] env) m ls ds where
  env a ha y hy := by
    by_cases eq : a.sym.key = l.sym.key
    · have lookup := inv.env a ha y hy
      have same : ptr a = ptr l := by
        have lookup' := inv.env l hl y (hy.trans eq)
        exact Option.some.inj (lookup.symm.trans lookup')
      rw [ConvInt.lookup_one (hy.trans (eq.trans key.symm)), same]
    · rw [ConvInt.lookup_one_other (by rw [hy, key]; exact eq)]
      exact inv.env a ha y hy
  live := inv.live
  apart := inv.apart
  defs := inv.defs

end Silmaril.Compile.Core.Verified.LoopTransfer
