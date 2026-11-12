module

public import Silmaril.Cerberus.Elaboration.State.Defs
public import Silmaril.Cerberus.GeneralizedTypes.Defs

/-! Direct function-designator equations from pinned `translation.lem:242–254`.
Alias lookup retains its explicit order and only matches `SD_Id` descriptions.
The source's indirect designators and other expression shapes reject explicitly.
These construct actual wire-model function pointers, not native addresses. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Designators
open Silmaril.Cerberus
open Construction

abbrev Aliases := List (String × Sym)

/-- Shared with function metadata assembly; non-identifier descriptions retain
exactly their original symbol even when their display text resembles an alias. -/
def resolveAlias (aliases : Aliases) (symbol : Sym) : Sym :=
  match symbol.description with
  | .id text => ((aliases.find? (fun entry => entry.1 == text)).map Prod.snd).getD symbol
  | _ => symbol

/-- Only the pinned direct identifier branch is implemented. The child is not
translated as an object identifier: its result is a loaded function pointer. -/
def direct (config : Target.Config) (aliases : Aliases) (type : Ctype)
    (input : Ail.TypedExpression) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI function designator")
  match type, input with
  | .mk _ (.function _ _ _), .mk _ _ _ (.ident symbol) =>
      return pureEffect (valuePure (.loaded (.specified (.pointer
        (.function (resolveAlias aliases symbol))))))
  | _, _ => throw (.message "unsupported: function designator outside direct prototype identifier")

end Silmaril.Cerberus.Elaboration.Designators
