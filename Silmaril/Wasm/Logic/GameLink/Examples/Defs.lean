module

public import Silmaril.Wasm.Logic.GameLink.Defs
public import Silmaril.Wasm.Logic.OpenExamples.Defs

/-!
# The logic and the Wasm game: a worked two-module example (specifications)

The two functions of `Silmaril.Wasm.Logic.OpenExamples`, now as scalar instances of
`Silmaril.Wasm.Game`:

* the **provider** exports the function `fi₁` at `a₁` whose body is
  `OpenExamples.incBody` (`local.get 0; i32.const 1; i32.add`);
* the **consumer** exports the function `fi₂` at `a₂` whose body is
  `OpenExamples.clientBody x` (`local.get 0; call x`), where `x` resolves to
  the host function `fib` at `b` with code `.host 0`: import `0` of the game,
  i.e. (in a static link) the provider's first stub.

`incISpec ts`, on any interface `ts`, is the game-level specification of both:
a question is a call on one `i32` `m`, and its answer must be the value
`m + 1`. `clientFSpec` is the consumer's Hoare-level specification (it returns
`m + 1` and leaves the store unchanged, given its code and the stub in the
store). The provider's Hoare-level specification is `OpenExamples.incSpec`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.GameLink.Examples

open Silmaril.Games Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Hoare (FSpec)
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- The scalar type `i32`. -/
abbrev i32T : ScalarType := .num (.int .i32)

/-- **The increment interface**, on any family of function types: a call on one `i32` `m`
is allowed, and its answer must be the value `m + 1`. -/
def incISpec (ts : List FnType) : ISpec (ifaceSig ts) where
  pre e := ∃ m : BitVec 32, e.2.1 = [.i32 m]
  post e v := ∀ m : BitVec 32, e.2.1 = [.i32 m] →
    Answer.toResult (ft := ts.get e.1) v = .values [.i32 (m + 1)]

/-- The consumer's Hoare specification: in a store holding its function `fi₂` at `a₂` and
the stub `fib` at `b`, on an `i32` `m`, it returns `m + 1` and leaves the store unchanged. -/
def clientFSpec (a₂ : Nat) (fi₂ : FuncInst Nat) (b : Nat) (fib : FuncInst Nat) : FSpec Nat where
  pre s args := s.funcs[a₂]? = some fi₂ ∧ s.funcs[b]? = some fib ∧ ∃ m : BitVec 32, args = [.i32 m]
  post s args s' o := s' = s ∧ ∃ m : BitVec 32, args = [.i32 m] ∧ o = .normal [.i32 (m + 1)]

end Silmaril.Wasm.Logic.GameLink.Examples
