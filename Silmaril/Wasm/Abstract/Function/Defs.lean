module

public import Silmaril.Games.Abstract.Function.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs

/-!
# Core 3.0 functions as abstract functions

`wasmFun P host a` is the function at address `a`, under numerics profile `P`
and host semantics `host`, read as an abstract function.

* The module state is the whole store, including internal memories, globals
  and tables.
* The argument is a list of values.
* The result is values, or the address of an uncaught exception.
* A run ends in `ret` with the final store, `trap`, or `div` (a diverging
  run, `Diverges`).

Host calls are resolved by `host` inside the store semantics, so this
projection has no import interface (`Sig.empty`). Exposing them as import
calls needs the single-threaded callout machine and is a later stage. The
projection agrees with the existing `behaviours`
(`Silmaril.Wasm.Abstract.Function.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The end of a run that stopped with result `r` in store `s`. -/
def endOfResult (r : Result) (s : Store H) : End (Store H) (List Val ⊕ Nat) :=
  match r with
  | .values vs => .ret (.inl vs) s
  | .throw a => .ret (.inr a) s
  | .trap => .trap

/-- The call behaviour of an end, forgetting the store. -/
def endToBehaviour {S : Type} : End S (List Val ⊕ Nat) → Behaviour Val
  | .ret (.inl vs) _ => .returns vs
  | .ret (.inr a) _ => .throws a
  | .trap => .traps
  | .div => .diverges

/-- The function at address `a` as an abstract function. -/
def wasmFun (P : Profile) (host : HostSemantics H) (a : Nat) :
    AFun Sig.empty (Store H) (List Val) (List Val ⊕ Nat) := fun s vs =>
  {x | (∃ (c' : Config H) (r : Result), Steps P host (invoke s a vs) c' ∧
      c'.code = r.toAdmin ∧ x = ([], endOfResult r c'.store)) ∨
    (x = ([], .div) ∧ Diverges P host (invoke s a vs))}

end Silmaril.Wasm.Abstract
