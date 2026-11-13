module

public import Silmaril.Cerberus.Elaboration.Statements.Defs

/-! The successful actual statement translator always applies its upstream
location/statement/attribute wrapper. This theorem inspects `translate`, not
only an independently defined annotation helper, so an early monadic return
that bypasses the wrapper cannot satisfy it.
-/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Statements
open Silmaril.Cerberus
open Construction

private theorem run_map {α β : Type} (transform : α → β) (action : State.ElabM α)
    (before : State.Context) :
    State.run (transform <$> action) before =
      let (result, after) := State.run action before
      (result.map transform, after) := by
  cases execution : action before with
  | mk outcome after =>
      cases outcome <;>
        simp [State.run, ExceptT.run, ExceptT.mk, Functor.map, ExceptT.map, bind, pure, StateT.bind, StateT.pure,
          Except.map, execution]

private theorem run_map_success {α β : Type} (transform : α → β) (action : State.ElabM α)
    (before : State.Context) (result : β) (after : State.Context)
    (success : State.run (transform <$> action) before = (.ok result, after)) :
    ∃ value : α, result = transform value := by
  cases execution : State.run action before with
  | mk outcome current =>
      cases outcome with
      | error error =>
          have rejected :
              ((.error error, current) : Except State.Error β × State.Context) = (.ok result, after) := by
            simpa only [run_map, execution, Except.map] using success
          have impossible : (Except.error error : Except State.Error β) = .ok result :=
            congrArg Prod.fst rejected
          exact Except.noConfusion rfl rfl (heq_of_eq impossible)
      | ok value =>
          have accepted :
              ((.ok (transform value), current) : Except State.Error β × State.Context) =
                (.ok result, after) := by
            simpa only [run_map, execution, Except.map] using success
          have valueEquality : transform value = result :=
            Except.ok.inj (congrArg Prod.fst accepted)
          exact ⟨value, valueEquality.symm⟩

/-- Every successful actual `translate` call applies all three source wrappers,
including branches which use an internal monadic return. -/
theorem translate_success_annotation (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (location : Loc) (desugaring : Ail.DesugInfo) (attributes : Attributes)
    (node : Ail.StatementNode Ail.GenTypeCategory) (before after : State.Context) (result : Effect)
    (sourceFunction : Option Sym := none)
    (success : State.run (translate config types runtime environment
      (.mk location desugaring attributes node) sourceFunction) before = (.ok result, after)) :
    ∃ core : Effect, result = addLocation location (addStatement (addAttributes attributes core)) := by
  apply run_map_success (fun core => addLocation location (addStatement (addAttributes attributes core)))
    _ before result after
  dsimp only [translate, annotate] at success
  exact success

end Silmaril.Cerberus.Elaboration.Statements
