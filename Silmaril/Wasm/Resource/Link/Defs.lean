module

public import Silmaril.Wasm.Resource.Protocol.Defs
public import Silmaril.Wasm.Logic.GameLink.Defs
public import Silmaril.Wasm.Game.DivAdequacy.Defs

@[expose] public section

/-!
# Protocols and the Wasm game: invariants and verification conditions

A protocol (`Silmaril.Wasm.Resource.Protocol`) is a property of the *history* of a play, so it is not
an assume/guarantee specification `ISpec` (which constrains each move on its own). This topic
relates protocols to plays of game-semantic strategies directly.

## Protocol invariants of transition systems (`LTSInv`)

For a transition system `L` over the moves of `E ↠ F` and a protocol `π` over those moves, an
`LTSInv L π` is a relation `J q x` between protocol states and system states such that

* `J π.init L.init`;
* silent steps keep `J q`;
* a visible step `x —o→ y` from `J q x` is accepted by the protocol, `π.step q o = some q'`,
  and `J q' y`.

With `OTotal π` (Opponent moves are never rejected; environment faults go to an absorbing
state instead) this proves that **every play of `Strategy.ofLTS L` is accepted**, including the
plays that receptivity adds. This is the "step invariant" form: the Wasm-specific obligation is
`J` under host-free Core steps (the silent steps of `I.dlts P s`, every profile).

## Provider verification conditions (`ProvSat`)

For a protocol about **export** events whose import events are neutral (`ImportNeutral`), an
export call has no protocol history inside it, so the program logic applies with a store
invariant indexed by protocol states `Inv : S → Store Nat → Prop`:

* `provSpec I π Inv q₁ j`: from a store meeting `Inv q₀` and arguments whose call event takes
  `q₀` to `q₁`, every outcome of export `j` answers with an event accepted in `q₁`, reaching a
  state `q₂` with `Inv q₂` of the final store;
* `ProvSat P I π Inv`: every export meets `provSpec … q₁ j` for every `q₁`, in the every-run
  logic (`Hoare.FSpecValid`) under the most general environment `gameHost I ISpec.top`.

Soundness (`Silmaril.Wasm.Resource.Link.Thms`): `ProvSat` and `Inv π.init s` imply that every play
of `I.strategy P s` is accepted, for every profile `P`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Logic.GameLink
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)



/-- **A protocol invariant** of a transition system. -/
structure LTSInv {E F : Sig.{0}} {S : Type} (L : LTS E F) (π : Protocol S (Move E F)) where
  /-- The invariant relating protocol states and system states. -/
  J : S → L.State → Prop
  init : J π.init L.init
  tau : ∀ {q x y}, L.step x none y → J q x → J q y
  vis : ∀ {q x o y}, L.step x (some o) y → J q x → ∃ q', π.step q o = some q' ∧ J q' y

/-- Opponent moves are never rejected. -/
def OTotal {E F : Sig.{0}} {S : Type} (π : Protocol S (Move E F)) : Prop :=
  ∀ q (o : Move E F), Move.IsO o → (π.step q o).isSome

/-- The import events of the instance leave the protocol state unchanged. -/
def ImportNeutral {S : Type} {I : ScalarInstance} (π : Protocol S (Move I.E I.F)) : Prop :=
  (∀ q e, π.step q (.inl (.ask e)) = some q) ∧ ∀ q e v, π.step q (.inl (.ans e v)) = some q

/-- The import specification allowing everything. -/
def ISpec.top (E : Sig.{0}) : ISpec E := ⟨fun _ => True, fun _ _ => True⟩

section
variable {S : Type} (I : ScalarInstance) (π : Protocol S (Move I.E I.F)) (Inv : S → Store Nat → Prop)

/-- **The provider specification of export `j` in protocol state `q₁`** (the state after the
call event). -/
def provSpec (q₁ : S) (j : Fin I.exports.length) : FSpec Nat where
  pre s args := ∃ q₀, Inv q₀ s ∧
    ∃ ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args,
      π.step q₀ (.inr (.ask ⟨j, ⟨args, ht⟩⟩)) = some q₁
  post _ args s' o :=
    ∀ (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args)
      (v : Answer (I.exports.get j)), resultOutcome v.toResult = o →
      ∃ q₂, π.step q₁ (.inr (.ans ⟨j, ⟨args, ht⟩⟩ v)) = some q₂ ∧ Inv q₂ s'

/-- **The provider verification condition**: every export meets its provider specification in
every protocol state, under the most general environment. -/
def ProvSat (P : Profile) : Prop :=
  ∀ q₁ j, FSpecValid P (gameHost I (ISpec.top I.E)) (I.addr j) (provSpec I π Inv q₁ j)

end

end Silmaril.Wasm.Resource
