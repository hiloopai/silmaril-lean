module

public import Silmaril.Games.Play.Thms

/-!
# Relabelling the lower interface of a game

A `Relabel E E'` sends every operation `m` of `E` to an operation `op m` of `E'`, with the
answers of `op m` in bijection with those of `m`. It acts on events, moves and positions of
`E ↠ F`, giving moves and positions of `E' ↠ F`. `Silmaril.Wasm.Spec.Attest.Defs` uses it to
rename a module's import before linking it to a provider: the `attest` import of the left
operand of a conjunction becomes the provider's export `attestL`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Spec.Attest

open Silmaril.Games

universe u

/-- A relabelling of the operations of `E` into `E'`, with answers in bijection. -/
structure Relabel (E E' : Sig.{u}) where
  /-- The image of an operation. -/
  op : E.Op → E'.Op
  /-- The answers of the image are the answers of the operation. -/
  ar : ∀ m, E'.Ar (op m) ≃ E.Ar m

namespace Relabel

variable {E E' F : Sig.{u}} (ι : Relabel E E')

/-- The image of an event. -/
def ev : Ev E → Ev E'
  | .ask m => .ask (ι.op m)
  | .ans m n => .ans (ι.op m) ((ι.ar m).symm n)

/-- The image of a move: the lower event is relabelled, the upper one kept. -/
def move : Move E F → Move E' F := Sum.map ι.ev id

/-- The image of a position. -/
def pos : Pos E F → Pos E' F
  | .idle => .idle
  | .run q => .run q
  | .wait q m => .wait q (ι.op m)

end Relabel

end Silmaril.Wasm.Spec.Attest
