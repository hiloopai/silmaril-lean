module

public import Silmaril.Compiler.Core.Verified.StoreTask.Defs
public import Silmaril.Compiler.Core.Verified.LocalsStmt.Defs

/-! # Lifted negative stores at a sequence point

A negative action is not a positive action with its sign erased. `liftAction` creates
an arena with the actual write and a resumption, tagging the write with an exclusion
id and excluding prior context accesses. This file proves the simplest complete
lifted store, under a `bound`, by driving those two tasks through the canonical arena.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.NegativeStore

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave
open Silmaril.Cerberus.Core.PureEval (Eval Reaches next_reaches tagsOf)
open Mem.Concrete (LiveInt IntRange)
open Locals (stored)

variable {file : Program} {labels : Labels}

/-- A lifted write does not race with an earlier access on its selected context path.
The same-address case is intentional: `x = x + 1` reads before its lifted write. -/
theorem excluded_noRace {a b : Access} {n : Nat} (ha : a.negative = some n)
    (hb : n ∈ b.exclusions) : races a b = false := by
  simp [races, ha, hb]

theorem excluded_noRace_rev {a b : Access} {n : Nat} (ha : a.negative = some n)
    (hb : n ∈ b.exclusions) : races b a = false := by
  simp [races, ha, hb]

/-- Every access on an excluded context frame carries the new exclusion. -/
theorem excludeFrames_annotations (n : Nat) (xs : List Access) :
    excludeFrames n [.annotations xs] =
      [.annotations (xs.map fun x => {x with exclusions := n :: x.exclusions})] := rfl

/-- A lifted store with an arbitrary selected resumption. Its context has a nearest
bound; all accesses made by the resumption carry the fresh exclusion id. This is
what permits assignment's weak-bind continuation and prior operand reads. -/
theorem lifted_store (l : Loc) (u : Unit) (ty p v : PE) (env : Env)
    (inner k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : LiveInt m id addr) (hn : IntRange n)
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
      ⟨.effectExpr (.mk [] (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.value result, k, stored m₂ id addr n⟩ := by
  let act : EE := .mk [] (.action (.mk .pos (.mk l u (.store false ty p v .na))))
  let m₁ : Mem.Concrete.State := {m with nextExcluded := m.nextExcluded + 1}
  let K := Frame.liftedResult :: .bound :: k
  let a := StoreTask.writeAccess [.excluded m.nextExcluded] addr
  let tasks : List (Nat × (Control × List Frame)) :=
    [(0, .effectExpr act env, [.excluded m.nextExcluded]),
     (1, .value .unit, excludeFrames m.nextExcluded inner)]
  let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, result, xs)]
  have live₁ : LiveInt m₁ id addr := Locals.liveInt_with live rfl rfl
  have live₂ : LiveInt m₂ id addr := by
    obtain ⟨loc, used, eq⟩ := touched
    rw [eq]
    exact Locals.liveInt_with live₁ rfl rfl
  have store := StoreTask.store_local [] l u ty p v env [.excluded m.nextExcluded] m₂ cann
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
      exact excluded_noRace (by simp [a, StoreTask.writeAccess]) (excluded bb hbb)
    · have eq : bb = a := by simpa using hbb
      subst bb
      exact excluded_noRace_rev (by simp [a, StoreTask.writeAccess]) (excluded aa haa)
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
      ⟨.effectExpr (.mk [] (.action (.mk .neg (.mk l u (.store false ty p v .na))))) env,
        inner ++ .bound :: k, m⟩
      ⟨.interleave [] tasks, K, m₁⟩ := by
    apply ReturnConst.update_reaches
    · intro o h; cases h
    · simp only [act] at lift
      simp [request, requestAux, awaitsScheduling, lift]
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

/-- `bound(store⁻(int, p, v))` runs the lifted positive store, discards its
annotations at the sequence point, and leaves the initialized slot. The action has no
outer location annotation (its internal source location is arbitrary). -/
theorem bound_store (bann : List Annot) (l : Loc) (u : Unit) (ty p v : PE)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (cann : List Annot)
    {id addr n : Int} (live : LiveInt m id addr) (hn : IntRange n)
    (eval : ∀ m', Eval file (tagsOf file m') env (.inr [ty, p, v])
      (.inr [.ctype (Mem.Concrete.intType cann), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))])) :
    Reaches file labels
      ⟨.effectExpr (.mk bann (.bound (.mk [] (.action (.mk .neg
        (.mk l u (.store false ty p v .na))))))) env, k, m⟩
      ⟨.value .unit, k, stored {m with nextExcluded := m.nextExcluded + 1} id addr n⟩ := by
  refine (ReturnLit.bound_reaches bann _ env k m).trans ?_
  exact lifted_store l u ty p v env [] k m cann live hn eval
    (by simp [List.span, List.span.loop]) ⟨[], .refl, rfl⟩ (LoadTask.Touched.refl _) (by simp) (by simp [activeCall, excludeFrames])

/-- The lifted store leaves the written integer slot initialized. -/
theorem bound_store_slot {m : Mem.Concrete.State} {id addr n : Int}
    (live : LiveInt m id addr) :
    Locals.Slot (stored {m with nextExcluded := m.nextExcluded + 1} id addr n) id addr n :=
  Locals.stored_slot (Locals.liveInt_with (m' := {m with nextExcluded := m.nextExcluded + 1}) live rfl rfl) n

/-- All disjoint locals survive the full lifted store, including its exclusion-id update. -/
theorem bound_store_frame {m : Mem.Concrete.State} {id addr value : Int}
    (h : Locals.Slot m id addr value) (wid waddr wvalue : Int)
    (apart : Slots.Apart waddr 4 addr 4) :
    Locals.Slot (stored {m with nextExcluded := m.nextExcluded + 1} wid waddr wvalue)
      id addr value :=
  Slots.slot_stored (Slots.slot_nextExcluded h _) wid waddr wvalue apart

end Silmaril.Compile.Core.Verified.NegativeStore
