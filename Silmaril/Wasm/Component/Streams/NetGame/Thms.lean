module

public import Silmaril.Wasm.Component.Streams.NetGame.Defs
public import Silmaril.Wasm.Component.Streams.NetSem.Thms

/-!
# The network theorems in the stream game

`game C` (`Silmaril.Wasm.Component.Streams.NetGame.Defs`) is `Algebra.StreamGame.den` as a
`NetSem.VSem`. Its strategy is the stream game's (`game_den`), its realisations are the stream
game's (`realizes_game_iff`), and the network theorems of `NetSem` hold for the stream game with
no hypothesis on the semantics:

* `chain_realizes`: a plug of components realising `T` and `U` realises `T ⟫ U` in the stream
  game, and the chain network of `T` and `U` has the outcomes of the pipe of `T ⟫ U`;
* **`equiv_compose`**: components realising equivalent transformers compose (`seq`) to
  equivalent components, and their chain networks have the same outcomes;
* `chain_compEquiv`, `tee_realizes`: the same for a fused realisation and for tees.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.NetGame

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.NetSem

variable {M : Type} [CoreModule M] {C : CoreSem M} {σ τ σ' τ' : Type}

theorem game_width : (game C).width = 1 := rfl

theorem game_den (T : Tr σ Val Val) : (game C).den T = Algebra.StreamGame.den T := rfl

/-- The realisations of `game C` are those of the stream game. -/
theorem realizes_game_iff {c : Comp M} {T : Tr σ Val Val} :
    (game C).Realizes c T ↔ Algebra.StreamGame.Realizes C c T := Iff.rfl

/-- A plug of two stream-game realisations realises the composite, and the chain network of the
two transformers has the outcomes of the pipe of the composite. -/
theorem chain_realizes {c d : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    (hc : Algebra.StreamGame.Realizes C c T) (hd : Algebra.StreamGame.Realizes C d U) :
    Algebra.StreamGame.Realizes C (Algebra.seq c d) (T.comp U) ∧
      ∀ xs, chainOut xs T U = pipeOut xs (T.comp U) :=
  NetSem.chain_realizes (game C) hc hd

/-- A realisation of a transformer equivalent to `T ⟫ U` is equivalent to the plug. -/
theorem chain_compEquiv {ρ : Type} {c d e : Comp M} {T : Tr σ Val Val} {U : Tr τ Val Val}
    {W : Tr ρ Val Val} (hc : Algebra.StreamGame.Realizes C c T)
    (hd : Algebra.StreamGame.Realizes C d U) (he : Algebra.StreamGame.Realizes C e W)
    (hW : (T.comp U).Equiv W) :
    Algebra.CompEquiv C (Algebra.seq c d) e ∧ ∀ xs, chainOut xs T U = pipeOut xs W :=
  NetSem.chain_compEquiv (game C) hc hd he hW

/-- **The composition of equivalent components is equivalent**, in the stream game: in the
algebra (`seq`) and in networks (chains). -/
theorem equiv_compose {c c' d d' : Comp M} {T : Tr σ Val Val} {T' : Tr σ' Val Val}
    {U : Tr τ Val Val} {U' : Tr τ' Val Val} (hc : Algebra.StreamGame.Realizes C c T)
    (hc' : Algebra.StreamGame.Realizes C c' T') (hd : Algebra.StreamGame.Realizes C d U)
    (hd' : Algebra.StreamGame.Realizes C d' U') (hT : T.Equiv T') (hU : U.Equiv U') :
    Algebra.CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') ∧
      ∀ xs, chainOut xs T U = chainOut xs T' U' :=
  NetSem.equiv_compose (game C) hc hc' hd hd' hT hU

/-- Tees of stream-game realisations of equivalent transformers. -/
theorem tee_realizes {c c' d d' : Comp M} {T : Tr σ Val Val} {T' : Tr σ' Val Val}
    {U : Tr τ Val Val} {U' : Tr τ' Val Val} (hc : Algebra.StreamGame.Realizes C c T)
    (hc' : Algebra.StreamGame.Realizes C c' T') (hd : Algebra.StreamGame.Realizes C d U)
    (hd' : Algebra.StreamGame.Realizes C d' U') (hT : T.Equiv T') (hU : U.Equiv U') :
    Algebra.CompEquiv C c c' ∧ Algebra.CompEquiv C d d' ∧
      ∀ xs, teeOut xs T U = teeOut xs T' U' :=
  NetSem.tee_realizes (game C) hc hc' hd hd' hT hU

end Silmaril.Wasm.Component.Streams.NetGame
