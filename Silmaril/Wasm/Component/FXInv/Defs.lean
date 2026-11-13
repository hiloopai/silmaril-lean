module

public import Silmaril.Wasm.Component.FXEngine.Defs

/-!
# Inversion of `StepFX` at host calls: definitions

The FX engine (`Silmaril.Wasm.Component.FXEngine`) parks an FX thread whose code is
`E.plug (cs.map .core)` with `decompose? s cs` a call of a component host function. This module
names that situation and the tool used to prove that such a thread has no other step.

* `eraseA`, `eraseL`: the **Core erasure** of FX code. Core instructions are kept, FX labels,
  frames and handler frames become Core labels, frames and (catch-free) handler frames with the
  erased body, and every other FX instruction (`block`, `loop`, `if`, the stack-switching
  instructions, continuation references) becomes `unreachable`, which `decompose?` treats as an
  inert non-value. The erasure keeps exactly the structure `decompose?` looks through.
* `AtHost s code h args`: FX code at a call of component host function `h` with arguments
  `args` (the parking condition of `InternalFX`).
* `HostFree s l`: `decompose? s l` is not a call of a component host function;
  `NoHostRedex s l`: this holds for `vals pre ++ l ++ rest` for every value prefix and suffix
  (the FX-engine analogue of `SingleThreaded.NoRedex`, which forbids every host-call redex,
  including calls of FX functions).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX)
open Silmaril.Wasm.Component.FXEngine (FXCode)

mutual
/-- The Core erasure of an FX administrative instruction. -/
def eraseA : AdminFX → Admin
  | .core a => a
  | .label n _ body => .label n [] (eraseL body)
  | .frame n f body => .frame n f (eraseL body)
  | .handler _ body => .handler 0 [] (eraseL body)
  | .fx _ => .plain .unreachable
  | .block _ _ => .plain .unreachable
  | .loop _ _ => .plain .unreachable
  | .if_ _ _ _ => .plain .unreachable
  | .contRef _ => .plain .unreachable

/-- The Core erasure of FX code. -/
def eraseL : List AdminFX → List Admin
  | [] => []
  | a :: as => eraseA a :: eraseL as
end

variable {H : Type}

/-- **FX code at a call of component host function `h`** with arguments `args`: the code is
`E.plug (cs.map .core)` and `decompose? s cs` finds the call (the parking condition of the FX
engine). -/
def AtHost (s : Store (FXCode H)) (code : List AdminFX) (h : H) (args : List Execution.Core.Val) : Prop :=
  ∃ (E : Silmaril.Wasm.Models.FX.Ctx) (cs : List Admin) (Ec : SingleThreaded.Ctx) (a : Nat),
    code = E.plug (cs.map .core) ∧ SingleThreaded.decompose? s cs = some (Ec, a, FXCode.host h, args)

/-- `decompose?` does not find a call of a component host function. -/
def HostFree (s : Store (FXCode H)) (l : List Admin) : Prop :=
  ∀ (Ec : SingleThreaded.Ctx) (a : Nat) (h : H) (args : List Execution.Core.Val),
    SingleThreaded.decompose? s l ≠ some (Ec, a, FXCode.host h, args)

/-- No call of a component host function in `l`, under any value prefix and suffix. -/
def NoHostRedex (s : Store (FXCode H)) (l : List Admin) : Prop :=
  ∀ (pre : List Execution.Core.Val) (rest : List Admin), HostFree s (vals pre ++ l ++ rest)

end Silmaril.Wasm.Component.FXInv
