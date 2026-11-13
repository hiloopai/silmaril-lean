module

public import Silmaril.Compiler.Core.Source.PureLocal.Defs
public import Silmaril.Compiler.Core.Verified.Slots.Defs

/-! # Integer writes as local tasks

A positive store takes local steps under any continuation, including the excluded
continuation of a lifted negative action. The exact access records the write's range
and exclusion id. This complements `LoadTask.load_local`, whose accesses only read.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StoreTask

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)
open Mem.Concrete (LiveInt IntRange)
open Locals (stored intVal)
open LoadTask (plain_value plain_apply plain_pureExpr)

variable {file : Program} {labels : Labels}

/-- The access of an integer store, including an enclosing lifted action's id. -/
def writeAccess (k : List Frame) (addr : Int) : Access :=
  ⟨k.findSome? fun f => match f with | .excluded n => some n | _ => none,
    [], true, addr, 4⟩

theorem requestAux_store_apply (ann : List Annot) (k : List Frame) {m : Mem.Concrete.State}
    {id addr n : Int} (live : LiveInt m id addr) (hn : IntRange n) :
    requestAux file labels m (.apply (.memory .store)
      [.ctype (Mem.Concrete.intType ann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]) k false =
      .memory "Store" (stored m id addr n) (.value .unit) (.annotations [writeAccess k addr] :: k) := by
  rw [requestAux.eq_def]
  simp [awaitsScheduling, memoryRequest, toMemory, objectMemory,
    Mem.Concrete.store_int _ ann live hn, Mem.Concrete.access_int _ ann live,
    bind, Except.bind, pure, Except.pure, stored, writeAccess]
  rfl

/-- A positive store, with pure operands, can be driven inside an unsequenced arena.
It records exactly one write and touches no other local's byte range. -/
theorem store_local (ann : List Annot) (l : Loc) (u : Unit) (ty p v : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : LiveInt m id addr) (hn : IntRange n)
    (eval : Eval file (tagsOf file m) env (.inr [ty, p, v])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))])) :
    LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.value .unit, .annotations [writeAccess k addr] :: k,
        stored (ReturnConst.focusMemory ann m) id addr n⟩ := by
  have req : requestAux file labels m
      (.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env) k false =
      if (ReturnConst.focusMemory ann m).currentLocation == m.currentLocation then
        .next (.pureExpr ty env) (.arguments (.memory .store) [] [p, v] env :: k)
      else .next (.setLocation (ReturnConst.focusMemory ann m).currentLocation (.pureExpr ty env))
        (.arguments (.memory .store) [] [p, v] env :: k) := by
    simp only [requestAux, awaitsScheduling, arguments]
    rfl
  have hf : LocalReaches file labels false
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u (.store false ty p v .na))))) env, k, m⟩
      ⟨.pureExpr ty env, .arguments (.memory .store) [] [p, v] env :: k,
        ReturnConst.focusMemory ann m⟩ := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq ann m
    rw [hfocus] at req ⊢
    by_cases same : loc == m.currentLocation
    · have eq : loc = m.currentLocation := by simpa using same
      subst loc
      simpa using Relation.ReflTransGen.single (Interleave.LocalStep.next
        (by simpa using req) (plain_pureExpr ty env))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m loc _ _ false)))
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := false) eval (.memory .store) [] k
    (ReturnConst.focusMemory ann m) (Locals.tagsOf_focus ann m)
  simp only [argState, List.nil_append] at args
  exact hf.trans (args.tail (.memory
    (requestAux_store_apply cann k (Locals.liveInt_focus ann live) hn)))

end Silmaril.Compile.Core.Verified.StoreTask
