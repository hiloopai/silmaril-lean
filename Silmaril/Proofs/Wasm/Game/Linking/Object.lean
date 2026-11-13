module

public import Silmaril.Proofs.Wasm.Game.Strategy.Basic
public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Proofs.Wasm.Game.GamesAux.Basic

/-!
# Closed instances as objects

A closed instance (no imports) has no lower moves, so its plays are determined
by their upper projections (`eq_map_upper`). `objPlays P s` is the set of
those projections (the "object" of an earlier development, whose state is the
store), and `interact V N` (both defined in `Silmaril.Wasm.Game.Linking.Defs`) composes a set `V` of lower event sequences with a
set `N` of plays (the old `interact` of POPL 2022 P13). These are the
intermediate notions of the old M3 proof; `Silmaril.Wasm.Game.Linking.Thms`
re-expresses the result as composition in `Silmaril.Games`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance}

/-- A closed instance has no lower events. -/
theorem not_underlay_move (hI : I.imports = []) (x : Ev I.E) : False := by
  have h0 : I.imports.length = 0 := by rw [hI]; rfl
  rcases x with e | ⟨e, -⟩
  · have := e.1.isLt; omega
  · have := e.1.isLt; omega

/-- For a closed instance every play is its upper projection, re-tagged. -/
theorem eq_map_upper (hI : I.imports = []) :
    ∀ p : List (Move I.E I.F), p = (upper p).map .inr
  | [] => rfl
  | .inl a :: _ => (not_underlay_move hI a).elim
  | .inr b :: p => by
    rw [upper_cons_inr, List.map_cons, ← eq_map_upper hI p]

/-- For a closed instance, a play is a play of the strategy exactly when its upper
projection is a play of the object. -/
theorem mem_plays_iff_objPlays (hI : I.imports = []) {P : Profile} {s : Store Nat}
    {p : List (Move I.E I.F)} : p ∈ I.plays P s ↔ upper p ∈ I.objPlays P s := by
  constructor
  · intro hp; exact ⟨p, hp, rfl⟩
  · rintro ⟨r, hr, h⟩
    rwa [eq_map_upper hI p, ← h, ← eq_map_upper hI r]

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
