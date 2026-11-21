module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Game.IOAccept.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.IOAccept

open Silmaril.Accept.IO Silmaril.Games.Abstract Silmaril.Wasm
open Silmaril.Wasm.Abstract (wasmHostSig)
open Silmaril.Wasm.Execution.Core

variable {X I O C : Type}

/-- Project one answered host event with the existing `TSession` roles, in event order. -/
def answerEventTags (m : Module) (mem : Option Nat) (R : Roles X I O C)
    (event : Call (wasmHostSig Nat)) : List (Tag X I O C) :=
  (m.imports[event.1.1]?).elim [] fun imp =>
    let callout := ⟨(imp.moduleName, imp.name), event.1.2.2, memOf mem event.1.2.1⟩
    R.callTags callout ++ R.answerTags callout ⟨event.2.2, memOf mem event.2.1⟩

/-- Count export entries, including entries not decoded by the role. -/
def entryCount (tags : List (Tag X I O C)) : Nat :=
  tags.countP fun | .enter _ => true | _ => false

/-- The finished outcomes of the native session triple, including store-retaining traps. -/
def nativeResult : Result → (List Val ⊕ Nat) ⊕ Unit
  | .values vs => .inl (.inl vs)
  | .throw index => .inl (.inr index)
  | .trap => .inr ()

end Silmaril.Wasm.Game.IOAccept
