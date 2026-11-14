module

public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
public import Silmaril.Compiler.Core.Verified.ArrDesig.Defs
/-! # Stores into `int` array elements

`liftedSub_store_ann`: the store of an assignment `a[n] = e` (Cerberus lifts the negative store
to the statement's `bound` and runs it in an excluded two-task arena with the rest of the
statement) into an `int` subobject: `StateStmt.lifted_store_ann` with `IntSubobject.Live` in
place of `LiveInt` and `SubobjectTask.store_local` in place of `StoreTask.store_local`. With
`ArrDesig.elem_runs` for the designator and `IntSubobject.Slot.stored` for the neighbouring
elements, it is the source side of an element assignment.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrStore

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches next_reaches tagsOf)
open Mem.Concrete (IntRange)
open Locals (stored)

variable {file : Program} {labels : Labels}

/-- `StateStmt.lifted_store_ann` for an `int` subobject (`IntSubobject.Live`: an array element or
a member inside a larger allocation): the lifted store of an assignment `a[n] = e`, whose
annotations carry no source location. -/
theorem liftedSub_store_ann (sann : List Annot) (hann : StateStmt.noLoc sann = true) (l : Loc) (u : Unit)
    (ty p v : PE) (env : Env) (inner k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : IntSubobject.Live m id addr) (hn : IntRange n)
    (eval : ∀ m', Eval file (tagsOf file m') env (.inr [ty, p, v])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))]))
    (boundary : (inner ++ .bound :: k).span (fun f => match f with
      | .strongBind .. | .bound => false | _ => true) = (inner, .bound :: k))
    {result : Val} {xs : List Access} {m₂ : Mem.Concrete.State}
    (resume : TaskRuns file labels false
      ⟨.value .unit, excludeFrames m.nextExcluded inner,
        {m with nextExcluded := m.nextExcluded + 1}⟩ result xs m₂)
    (touched : LoadTask.Touched {m with nextExcluded := m.nextExcluded + 1} m₂)
    (excluded : ∀ a ∈ xs, m.nextExcluded ∈ a.exclusions)
    (idle : activeCall (.value .unit) (excludeFrames m.nextExcluded inner) = false) :
    Reaches file labels
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.value result, k, stored m₂ id addr n⟩ := by
  have hno : ∀ a ∈ sann, ∀ l, a ≠ .loc l := by
    intro a ha l e; subst e
    have := List.all_eq_true.mp hann _ ha
    simp at this
  have hfind : (sann.findSome? fun a => match a with | .loc l => some l | _ => none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro a ha
    cases a <;> first | rfl | exact absurd rfl (hno _ ha _)
  let act : EE := .mk [] (.action (.mk .pos (.mk l u (.store false ty p v .na))))
  let m₁ : Mem.Concrete.State := {m with nextExcluded := m.nextExcluded + 1}
  let K := Frame.liftedResult :: .bound :: k
  let a := StoreTask.writeAccess [.excluded m.nextExcluded] addr
  let tasks : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr act env, [.excluded m.nextExcluded]),
     (1, .value .unit, excludeFrames m.nextExcluded inner)]
  let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, result, xs)]
  have live₁ : IntSubobject.Live m₁ id addr := live.mono rfl rfl
  have live₂ : IntSubobject.Live m₂ id addr := by
    obtain ⟨loc, used, eq⟩ := touched
    rw [eq]
    exact live₁.mono rfl rfl
  have store := SubobjectTask.store_local [] l u ty p v env [.excluded m.nextExcluded] m₂ cann
    live₂ hn (eval m₂) (labels := labels)
  have task0 : TaskRuns file labels false
      ⟨.effectExpr act env, [.excluded m.nextExcluded], m₂⟩ .unit [a]
        (stored m₂ id addr n) := by
    refine ⟨[.annotations [a]], ?_, rfl⟩
    refine store.tail (.next ?_ (LoadTask.plain_value .unit))
    simp [requestAux, awaitsScheduling, a, ReturnConst.focusMemory]
  have flag0 : taskFlag false K [] = false := by simp [taskFlag]
  have flag1 : taskFlag false K [(0, .effectExpr act env, [.excluded m.nextExcluded])] = false := by
    simp [taskFlag, controlHasCCall, hasCCall, act]
  have run : TasksRun file labels false K tasks m₁ results (stored m₂ id addr n) := by
    have r0 : TasksRun file labels false K [(0, .effectExpr act env, [.excluded m.nextExcluded])]
        m₂ [(0, .unit, [a])] (stored m₂ id addr n) :=
      .snoc (by rw [flag0]; exact task0) .nil
    exact .snoc (by rw [flag1]; exact resume) r0
  have norace : NoRace results := by
    intro x hx y hy ne aa haa bb hbb
    simp only [results, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (ne rfl)
    · have eq : aa = a := by simpa using haa
      subst aa
      exact NegativeStore.excluded_noRace (by simp [a, StoreTask.writeAccess]) (excluded bb hbb)
    · have eq : bb = a := by simpa using hbb
      subst bb
      exact NegativeStore.excluded_noRace_rev (by simp [a, StoreTask.writeAccess]) (excluded aa haa)
    · exact False.elim (ne rfl)
  have sorted : results.Pairwise fun a b => a.1 ≤ b.1 := by simp [results]
  have arena := interleave_runs file labels run (by simp [tasks]) (by
    intro t ht
    simp only [tasks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp [activeCall]
    · exact idle) []
  have end_ := LocalStep.next (requestAux_end file labels (stored m₂ id addr n) results K false
    norace sorted) (LoadTask.plain_value _)
  have lift : liftAction m (.effectExpr act env) (Control.value .unit).resuming
      (inner ++ .bound :: k) = .update m₁ (.interleave [] tasks) K := by
    dsimp only [liftAction]
    erw [boundary]
    simp [excludePath, m₁, tasks, K]
  have start : Reaches file labels
      ⟨.effectExpr (.mk sann (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.interleave [] tasks, K, m₁⟩ := by
    apply ReturnConst.update_reaches
    · intro o h; cases h
    · simp only [act] at lift
      simp [request, requestAux, awaitsScheduling]
      erw [hfind]
      simp [lift]
  refine start.trans ?_
  have steps := arena.tail end_
  refine (reaches_of_local file labels steps).trans ?_
  have selected : Reaches file labels
      ⟨.value (.tuple [.unit, result]), .annotations (a :: xs) :: K, stored m₂ id addr n⟩
      ⟨.value result, .annotations (a :: xs) :: .bound :: k, stored m₂ id addr n⟩ :=
    next_reaches (by intro o h; cases h) (by
      simp [request, requestAux, awaitsScheduling, K])
  have finish := selected.trans
    (Locals.annotations_bound_reaches (a :: xs) result k (stored m₂ id addr n))
  unfold PureEval.Reaches Spec.coreStep at finish
  simpa [results] using finish

end Silmaril.Compile.Core.Verified.ArrStore
