module

public import Silmaril.Wasm.Component.Streams.NetSem.Defs
public import Silmaril.Wasm.Component.Algebra.StreamGame.Thms

/-!
# One stream semantics for networks and the algebra

`NetSem.VSem C` is the interface the network results of `Silmaril.Wasm.Component.Streams.NetSem`
are stated against (a compositional semantics of transformers as strategies of the component
algebra); `Algebra.StreamGame.den` is the concrete one of the algebra track (the Kahn pull
game). This module makes them **one definition**: `game C` is the `VSem` whose strategy of a
transformer is `StreamGame.den`, of width `1`, and its realisations are exactly the stream game's
(`realizes_game_iff`, by `Iff.rfl`). The network theorems instantiated at `game C` are in
`Silmaril.Wasm.Component.Streams.NetGame.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.NetGame

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.NetSem

variable {M : Type} [CoreModule M]

/-- **The stream game as the network semantics**: `VSem` with `den := StreamGame.den`. -/
def game (C : CoreSem M) : VSem C where
  width := 1
  den T := Algebra.StreamGame.den T
  den_comp T U := Algebra.StreamGame.den_comp T U
  den_congr h := Algebra.StreamGame.den_congr h

end Silmaril.Wasm.Component.Streams.NetGame
