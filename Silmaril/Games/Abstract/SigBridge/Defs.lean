module

public import Silmaril.Games.Abstract.Machine.Defs
public import Silmaril.Games.LTS.Defs
public import Mathlib.Order.Hom.Basic

/-!
# The game `E ↠ F` as an abstract game

The sequential, well-bracketed game of `Silmaril.Games.Play` is an abstract
game (`sigGame E F`) with the same moves, polarity and legal plays. Its trace
models are exactly the strategies of `Silmaril.Games.Strategy`
(`Silmaril.Games.Abstract.SigBridge.Thms`: an order isomorphism), and a
transition system `LTS E F` is an abstract machine with the same runs
(`ofLTS`), so state erasure agrees with `Strategy.ofLTS`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u

variable {E F : Sig.{u}}

/-- The game `E ↠ F` as an abstract game. -/
def sigGame (E F : Sig.{u}) : Game.{u} where
  Move := Silmaril.Games.Move E F
  IsO := Silmaril.Games.Move.IsO
  Legal := {s | Silmaril.Games.Legal s}
  nil_legal := Silmaril.Games.Legal.nil
  legal_of_prefix ht h := Silmaril.Games.Legal.of_prefix ht h

namespace SigBridge

open Silmaril.Games

/-- A one-move extension is legal when the automaton can read the move. -/
theorem legal_concat_iff {s : List (Move E F)} {o : Move E F} :
    Silmaril.Games.Legal (s ++ [o]) ↔ ∃ x y, Path .idle s x ∧ Step x o y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx, hxo⟩ := Path.concat_iff.1 hz
    exact ⟨x, z, hx, hxo⟩
  · rintro ⟨x, y, hx, hxy⟩
    exact ⟨y, Path.concat_iff.2 ⟨x, hx, hxy⟩⟩

/-- A strategy as a trace model. -/
def toModel (σ : Strategy E F) : TraceModel (sigGame E F) where
  plays := σ.plays
  closed := {
    nil_mem := σ.nil_mem
    legal := σ.legal
    of_prefix := σ.of_prefix
    receptive := fun hs hl ho => by
      obtain ⟨x, y, hx, hxy⟩ := legal_concat_iff.1 hl
      exact σ.receptive hs hx hxy ho }

/-- A trace model as a strategy. -/
def ofModel (T : TraceModel (sigGame E F)) : Strategy E F where
  plays := T.plays
  nil_mem := T.closed.nil_mem
  legal := T.closed.legal
  of_prefix := T.closed.of_prefix
  receptive := fun hs hx hxy ho => T.closed.receptive hs (legal_concat_iff.2 ⟨_, _, hx, hxy⟩) ho

/-- Strategies of `E ↠ F` are the trace models of `sigGame E F`. -/
def strategyIso : Strategy E F ≃o TraceModel (sigGame E F) where
  toFun := toModel
  invFun := ofModel
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end SigBridge

/-- A transition system over `E ↠ F` as an abstract machine. -/
def Machine.ofLTS (L : LTS E F) : Machine (sigGame E F) := ⟨L.State, L.init, L.step⟩

end Silmaril.Games.Abstract
