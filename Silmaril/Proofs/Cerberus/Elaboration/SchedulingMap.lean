module

public import Silmaril.Proofs.Cerberus.Elaboration.Scheduling

/-! Pure callback construction has no freshness effects, so the pinned callback
schedule preserves the ordinary result list. Deferred existing actions can
therefore reuse ordinary left-to-right elaboration sequencing. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Scheduling

theorem forwardBuild_pure {α β : Type} (transform : α → β) (inputs : List α) :
    forwardBuild (fun value => pure (transform value)) inputs = pure (inputs.map transform) := by
  induction inputs with
  | nil => rfl
  | cons first rest induction => simp [forwardBuild, induction]

theorem buildMapAt_pure {α β : Type} (counter : Nat) (transform : α → β) (inputs : List α) :
    buildMapAt counter (fun value => pure (transform value)) inputs = pure (inputs.map transform) := by
  induction inputs generalizing counter with
  | nil => rfl
  | cons first rest induction => simp [buildMapAt, induction, forwardBuild_pure]

theorem buildMapAt_defer {α β : Type} (counter : Nat) (action : α → State.ElabM β)
    (inputs : List α) :
    buildMapAt counter (fun value => defer (action value)) inputs = pure (inputs.map action) :=
  buildMapAt_pure counter action inputs

theorem sequenceActions_map {α β : Type} (action : α → State.ElabM β) (inputs : List α) :
    sequenceActions (inputs.map action) = inputs.mapM action := by
  induction inputs with
  | nil => rfl
  | cons first rest induction => simp [sequenceActions, induction]

/-- Building deferred callbacks leaves freshness unchanged and keeps their
execution in the original input order. -/
theorem mapM_defer {α β : Type} (action : α → State.ElabM β) (inputs : List α) :
    mapM (fun value => defer (action value)) inputs = defer (inputs.mapM action) := by
  simp [mapM, buildMapAt_pure, sequenceActions_map, defer]

/-- When all callbacks are deferred, the construction/execution boundary is
exactly the existing elaboration state's ordinary list traversal. -/
theorem execute_mapM_defer {α β : Type} (action : α → State.ElabM β) (inputs : List α) :
    execute (mapM (fun value => defer (action value)) inputs) = inputs.mapM action := by
  rw [mapM_defer, execute_defer]

end Silmaril.Cerberus.Elaboration.Scheduling
