module

public import Silmaril.Cerberus.Elaboration.Scheduling.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Scheduling
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- Deferring an existing state action changes neither success nor error paths. -/
@[simp] theorem execute_defer {α : Type} (action : State.ElabM α) :
    execute (defer action) = action := by
  funext context
  cases context
  rfl

@[simp] theorem execute_returnValue {α : Type} (value : α) :
    execute (returnValue value) = pure value := execute_defer _

/-- Construction changes only freshness before handing off to an action. -/
theorem execute_run {α : Type} (computation : Computation α) (context : State.Context) :
    State.run (execute computation) context =
      let (result, after) := computation.run context.freshness
      match result with
      | .ok action => State.run action {context with freshness := after}
      | .error error => (.error error, {context with freshness := after}) := by
  dsimp only [State.run, execute, ExceptT.run, ExceptT.mk, Bind.bind, Pure.pure,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, getThe,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift,
    MonadExcept.throw, MonadExceptOf.throw,
    Functor.map, ExceptT.map, StateT.map, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure, StateT.get, StateT.set]
  cases built : computation context.freshness with
  | mk result after => cases result <;> rfl

/-- A construction error retains consumed freshness and executes no action. -/
theorem execute_build_error {α : Type} (computation : Computation α) (context : State.Context)
    (error : State.Error) (after : Freshness.Context)
    (built : computation.run context.freshness = (.error error, after)) :
    State.run (execute computation) context = (.error error, {context with freshness := after}) := by
  rw [execute_run, built]

/-- A successful build changes only freshness before the prepared action runs. -/
theorem execute_build_ok {α : Type} (computation : Computation α) (context : State.Context)
    (action : State.ElabM α) (after : Freshness.Context)
    (built : computation.run context.freshness = (.ok action, after)) :
    State.run (execute computation) context = State.run action {context with freshness := after} := by
  rw [execute_run, built]

/-- Staged bind executes the first prepared action, then builds its continuation.
This law concerns execute, not equality with ordinary Build bind. -/
@[simp] theorem execute_bind {α β : Type} (first : Computation α) (next : α → Computation β) :
    execute (Scheduling.bind first next) = (do
      let value ← execute first
      execute (next value)) := by
  funext context
  dsimp only [execute, Scheduling.bind, ExceptT.run, Bind.bind, Pure.pure,
    MonadState.get, MonadStateOf.get, MonadStateOf.set, getThe,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift,
    MonadExcept.throw, MonadExceptOf.throw,
    Functor.map, ExceptT.map, StateT.map, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    StateT.bind, StateT.pure, StateT.get, StateT.set]
  cases built : first context.freshness with
  | mk result after => cases result <;> rfl

@[simp] theorem execute_map {α β : Type} (transform : α → β) (computation : Computation α) :
    execute (Scheduling.map transform computation) = transform <$> execute computation := by
  simp only [Scheduling.map, execute_bind, execute_returnValue]
  rfl

/-- A mapped deferred callback remains free of eager construction effects. -/
theorem map_defer {α β : Type} (transform : α → β) (action : State.ElabM α) :
    Scheduling.map transform (defer action) = defer (transform <$> action) := by
  change (pure (do
      let value ← action
      execute (returnValue (transform value))) : Build (State.ElabM β)) =
    (pure (transform <$> action) : Build (State.ElabM β))
  congr 1

/-- Immediate execution agrees with the existing state fresh primitive. -/
@[simp] theorem execute_wrappedFreshSymbol (type : BaseType) :
    execute (wrappedFreshSymbol type) = State.wrappedFreshSymbol type := by
  funext context
  dsimp only [execute, wrappedFreshSymbol, wrappedFreshSymbolWith, freshDescription,
    State.wrappedFreshSymbol, State.wrappedFreshSymbolWith, State.freshDescription,
    ExceptT.run, Bind.bind, Pure.pure, MonadState.get, MonadStateOf.get, MonadStateOf.set, getThe,
    liftM, MonadLiftT.monadLift, MonadLift.monadLift, ExceptT.lift,
    MonadExcept.throw, MonadExceptOf.throw,
    Functor.map, ExceptT.map, StateT.map, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    StateT.bind, StateT.pure, StateT.get, StateT.set]
  cases fresh : Freshness.description .none context.freshness with
  | error error => rfl
  | ok value => rcases value with ⟨symbol, after⟩; rfl

/-- Source count_map builds the tail before the head below the exact cutoff. -/
theorem buildMapAt_below {α β : Type} (counter : Nat) (callback : α → Build β)
    (first : α) (rest : List α) (below : counter < 5000) :
    buildMapAt counter callback (first :: rest) = (do
      let values ← buildMapAt (counter + 1) callback rest
      let value ← callback first
      pure (value :: values)) := by
  simp only [buildMapAt, ite_eq_left below]

/-- At5000 only the remaining tail switches to forward map_tr; the current
head is still built after that tail. -/
theorem buildMapAt_cutoff {α β : Type} (callback : α → Build β) (first : α) (rest : List α) :
    buildMapAt 5000 callback (first :: rest) = (do
      let values ← forwardBuild callback rest
      let value ← callback first
      pure (value :: values)) := rfl

end Silmaril.Cerberus.Elaboration.Scheduling
