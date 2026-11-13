module

public import Silmaril.Wasm.Atlas.Calls.Defs

/-!
# The Wasm call-level atlas: results

* `Calls.toBase_dir`: every chart's transition to Core is an equality transition on its class.
* `Calls.holds_core`: a sentence of a chart's class proved in that chart at a point of its domain
  holds in Core at the image point (`ChartAtlas.holds_base`).
* `Calls.link_cocycle`: **the cocycle condition on the triple overlap** linking parts / linked
  instance / Core: going from the composite of the parts to Core directly (`Games.linkToCore`)
  or through the game chart of the linked instance (`Games.linkToGame` then `Games.toCore`)
  gives the same point and the same sentence. The two paths agree as maps, and both are equal
  on `diverges`-ignoring sentences.
* `Calls.link_via_game`: the composite path, used to transfer.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Calls

open Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem toBase_dir (P : Profile) (i : Idx) : (toBase P i).dir = .equal := by
  cases i <;> rfl

/-- **Proved in a chart, holds in Core.** -/
theorem holds_core (P : Profile) (i : Idx) {p : (chart P i).Pt} {φ : (chart P i).Sen}
    (hp : (chart P i).dom p) (hφ : (toBase P i).cls φ) (h : (chart P i).Sat p φ) :
    (Core.chart P Nat).Sat ((toBase P i).pt p) ((toBase P i).sen φ) :=
  (atlas P).holds_base i (by rw [show (atlas P).toBase i = toBase P i from rfl, toBase_dir]; rfl)
    hp hφ h

/-- The host induced by an environment of the empty interface is the empty host. -/
theorem hostOf_nil (K : Env (ifaceSig [])) : hostOf [] K = Games.emptyHost := by
  funext h s args out
  simp only [hostOf, Games.emptyHost, ifaceOp?, List.length_nil, Nat.not_lt_zero, dite_false,
    reduceCtorEq, false_and, exists_false]

/-- **The cocycle condition** for linking: both paths to Core agree on points and sentences. -/
theorem link_cocycle (P : Profile) (S : Linking.Setup) (K : Env (ifaceSig []))
    (s : BSen (ifaceSig S.exportTypes).Op (Behaviour Val)) :
    ((Games.linkToGame P S).comp (Games.toCore P S.linkedI)).pt K = (Games.linkToCore P S).pt K ∧
      ((Games.linkToGame P S).comp (Games.toCore P S.linkedI)).sen s =
        (Games.linkToCore P S).sen s := by
  refine ⟨?_, ?_⟩
  · show (S.sl, hostOf [] K) = (S.sl, Games.emptyHost)
    rw [hostOf_nil]
  · show (s.rename id).rename (Games.call S.linkedI) = s.rename (Games.call S.linkedI)
    rw [BSen.rename_id]

/-- **Transfer through the linked instance's game chart** (both steps equal on the class). -/
theorem link_via_game {P : Profile} {S : Linking.Setup} {K : Env (ifaceSig [])}
    (hS : S.Scalar) {s : BSen (ifaceSig S.exportTypes).Op (Behaviour Val)}
    (hs : s.Ignores .diverges) :
    (Games.linkChart P S).Sat K s ↔
      (Core.chart P Nat).Sat (S.sl, Games.emptyHost) (s.rename (Games.call S.linkedI)) := by
  have h := ((Games.linkToGame P S).comp (Games.toCore P S.linkedI)).sat_iff rfl
    (p := K) (φ := s) hS ⟨trivial, BSen.ignores_rename id hs⟩
  obtain ⟨hpt, hsen⟩ := link_cocycle P S K s
  rw [hpt, hsen] at h
  exact h

end Silmaril.Wasm.Atlas.Calls
