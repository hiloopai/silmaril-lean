module

public import Silmaril.Wasm.Det.Shared.Defs
public import Silmaril.Wasm.Game.Untyped.Defs

/-!
# Determinism under store-writing hosts: the untyped game (definitions)

The untyped store-passing game of `Silmaril.Wasm.Game.Untyped` asks **every** callout raw, in the
current store, and answers export questions with the final store and the raw Core result.

* `uTraps X`: the trap answers of the untyped signature over export names `X` (result `trap`,
  any store).
* `UOk U A S`: the admissible Opponent moves: export questions carry stores of `S`, import
  answers carry stores admissible (`A`) for the store of their question.
* `UInstance.entry U`: the export addresses of `U`.

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The trap answers of the untyped signature. -/
def uTraps (X : Type) : Traps (untypedSig X) := fun _ a => a.result = .trap

/-- The admissible moves of the untyped store-passing game: export questions in stores of `S`,
import answers in stores admissible for the store of the question. -/
def UOk (U : UInstance) (A : Store Nat → Store Nat → Prop) (S : Store Nat → Prop) :
    Move U.E U.F → Prop
  | .inr (.ask f) => S f.store
  | .inl (.ans e a) => A e.store a.store
  | _ => True

/-- The export addresses of an untyped instance. -/
def uEntry (U : UInstance) (a : Nat) : Prop := ∃ x, U.addr x = a

end Silmaril.Wasm.Det.Shared
