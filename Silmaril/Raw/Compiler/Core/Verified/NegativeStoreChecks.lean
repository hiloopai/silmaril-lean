module

public import Silmaril.Compiler.Core.Verified.NegativeStore.Defs
public import Silmaril.Compiler.Core.Verified.SlotsChecks.Defs
public import Silmaril.Compiler.Core.Verified.Uninitialized.Defs
/-! # A complete lifted store on two concrete adjacent objects -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.NegativeStoreChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open SlotsChecks (memory first_live second_live)
open Locals (stored Slot)

/-- The address is a runtime value, supplied by the environment. -/
def withLocal (env : Env) (x : Sym) : Env :=
  env.insert x (.object (.pointer (.allocated 0 4096)))

def rhs : PE := .mk [] () (.val (.loaded (.specified (.integer 99))))

/-- An actual Core expression; no assumptions about a hypothetical task run. -/
def write (x : Sym) : EE :=
  .mk [] (.action (.mk .neg (.mk .unknown ()
    (.store false (Locals.intVal [] []) (.mk [] () (.sym x))
      rhs .na))))

def assign (x : Sym) : EE := .mk [] (.bound (write x))

/-- Running the negative store uses the canonical lifting arena and initializes the first
slot while retaining the distinct second value. -/
theorem assign_reaches (file : Program) (labels : Labels) (env : Env) (x : Sym) (k : List Frame) :
    let m := stored memory 1 4100 (-23)
    let m' := stored {m with nextExcluded := m.nextExcluded + 1} 0 4096 99
    Reaches file labels ⟨.effectExpr (assign x) (withLocal env x), k, m⟩ ⟨.value .unit, k, m'⟩ ∧
      Slot m' 0 4096 99 ∧ Slot m' 1 4100 (-23) := by
  let m := stored memory 1 4100 (-23)
  have live : Mem.Concrete.LiveInt m 0 4096 := Slots.live_stored first_live 1 4100 (-23)
  refine ⟨?_, NegativeStore.bound_store_slot live, ?_⟩
  · exact NegativeStore.bound_store [] .unknown () _ _ _ (withLocal env x) k m [] live (by unfold Mem.Concrete.IntRange; decide)
      (fun _ => .cons .val (.cons (.sym (by simp [withLocal])) (.cons .val .nil)))
  · exact NegativeStore.bound_store_frame (Locals.stored_slot second_live (-23)) 0 4096 99 (by unfold Slots.Apart; decide)

/-- The weak continuation of an assignment returns its value. A prior read of the
same address is excluded from racing with the lifted write, rather than dropped. -/
theorem assignment_tail_reaches (file : Program) (labels : Labels) (env : Env) (x : Sym) (k : List Frame) :
    let read : Access := ⟨none, [], false, 4096, 4⟩
    let body : EE := .mk [] (.pure rhs)
    let inner := [Frame.effectBind (.mk [] (.base (none, .unit))) body (withLocal env x), .annotations [read]]
    let m := stored memory 1 4100 (-23)
    Reaches file labels
      ⟨.effectExpr (write x) (withLocal env x),
        inner ++ .bound :: k, m⟩
      ⟨.value (.loaded (.specified (.integer 99))), k,
        stored {m with nextExcluded := m.nextExcluded + 1} 0 4096 99⟩ := by
  let read : Access := ⟨none, [], false, 4096, 4⟩
  let body : EE := .mk [] (.pure rhs)
  let inner := [Frame.effectBind (.mk [] (.base (none, .unit))) body (withLocal env x), .annotations [read]]
  let m := stored memory 1 4100 (-23)
  let m₁ : Mem.Concrete.State := {m with nextExcluded := m.nextExcluded + 1}
  let read' : Access := {read with exclusions := [m.nextExcluded]}
  have resume : Interleave.TaskRuns file labels false
      ⟨.value .unit, excludeFrames m.nextExcluded inner, m₁⟩
      (.loaded (.specified (.integer 99))) [read'] m₁ := by
    refine ⟨[.annotations [read']], ?_, rfl⟩
    refine Relation.ReflTransGen.head (Interleave.LocalStep.next
      (k' := [.annotations [read']]) ?_
      (LoadTask.plain_effectExpr body (withLocal env x))) ?_
    · simp [requestAux, awaitsScheduling, excludeFrames, inner, matchPattern, extendEnv, read', read]
    refine Relation.ReflTransGen.head (Interleave.LocalStep.next
      (k' := [.diagnosticLocation m₁.currentLocation, .annotations [read']]) ?_
      (LoadTask.plain_pureExpr rhs (withLocal env x))) ?_
    · simp [requestAux, awaitsScheduling, body]
    refine Relation.ReflTransGen.head (Interleave.LocalStep.next
      (k' := [.diagnosticLocation m₁.currentLocation, .annotations [read']]) ?_
      (LoadTask.plain_value (.loaded (.specified (.integer 99))))) ?_
    · simp [requestAux, awaitsScheduling, rhs, runtimeValue, runtimeLoaded, runtimeObject]
    exact .single (.next (Interleave.requestAux_value_diagnostic file labels m₁ _ _ _ false)
      (LoadTask.plain_value _))
  exact NegativeStore.lifted_store .unknown () _ _ _ (withLocal env x) inner k m []
    (Slots.live_stored first_live 1 4100 (-23)) (by unfold Mem.Concrete.IntRange; decide)
    (fun _ => .cons .val (.cons (.sym (by simp [withLocal])) (.cons .val .nil)))
    (by simp [inner, List.span, List.span.loop]) resume (LoadTask.Touched.refl _)
    (by intro a ha; obtain rfl := List.mem_singleton.mp ha; simp [read']) (by simp [activeCall, excludeFrames, inner])

/-- An unspecified initialization keeps the object live for its later assignment. -/
theorem uninitialized_then_assign (file : Program) (labels : Labels) (env : Env) (x : Sym) (k : List Frame) :
    let m := Uninitialized.stored memory 0 4096
    Reaches file labels ⟨.effectExpr (assign x) (withLocal env x), k, m⟩
      ⟨.value .unit, k, stored {m with nextExcluded := m.nextExcluded + 1} 0 4096 99⟩ :=
  NegativeStore.bound_store [] .unknown () _ _ _ (withLocal env x) k _ []
    (Uninitialized.stored_live first_live) (by unfold Mem.Concrete.IntRange; decide)
    (fun _ => .cons .val (.cons (.sym (by simp [withLocal])) (.cons .val .nil)))

end Silmaril.Compile.Core.Verified.NegativeStoreChecks
