module

public import Silmaril.Wasm.Binaryen.Intrinsic.Thms
public import Silmaril.Wasm.Binaryen.Behaviour
public import Silmaril.Wasm.Game.IOAccept.Defs

public section

namespace Silmaril.Wasm.Binaryen.Intrinsic

open Execution.Core Numerics

/-- The existing Core-backed observer cannot distinguish the two compilation paths. -/
theorem Expr.moduleObs_eq {context result H} (expr : Expr context result) (slot : FunctionSlot)
    (profile : Profile) (host : HostSemantics H) (store : Store H) (imports : List ExternAddr)
    (script : List Call) :
    (slot.folded expr.erase).obs profile host store imports script =
      moduleObs profile host store imports (slot.core expr.toCore.erase) script := by
  exact congrArg (fun mod => moduleObs profile host store imports mod script) (expr.lower_in_slot slot)

/-- The actual tagged-session observer commutes, for every role and environment policy. -/
theorem Expr.tagTraces_eq {context result X I O C} (expr : Expr context result) (slot : FunctionSlot)
    (profile : Profile) (envs : Store Nat → Game.SEnv Game.UImp → Prop) (memIdx : Nat)
    (roles : Game.IOAccept.Roles X I O C) :
    Game.IOAccept.tagTraces profile envs memIdx (slot.folded expr.erase).lower roles =
      Game.IOAccept.tagTraces profile envs memIdx (slot.core expr.toCore.erase) roles := by
  rw [expr.lower_in_slot slot]

end Silmaril.Wasm.Binaryen.Intrinsic
