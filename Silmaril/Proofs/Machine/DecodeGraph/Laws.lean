module

public import Silmaril.Machine.DecodeGraph.Defs

public section

namespace Silmaril.Machine.DecodeGraph.Proofs

open scoped SetRel

open Silmaril.Parse.DecodeGraph

variable {Context Buffer Source Block : Type*}

theorem blocks_mono {first second : Graph Context Buffer Source} (h : first ⊆ second)
    (ends : Context → Nat → Source → Prop) (fuel : Nat) : blocks first ends fuel ⊆ blocks second ends fuel := by
  rintro ⟨input, code, endPos⟩ (path : Path first ends fuel input code endPos)
  show Path second ends fuel input code endPos
  induction path with
  | last decoded advance inside stop => exact .last (h decoded) advance inside stop
  | next decoded advance inside continues _ ih => exact .next (h decoded) advance inside continues ih

theorem path_bounds {decoder : Graph Context Buffer Source} {ends : Context → Nat → Source → Prop}
    {fuel input code endPos} (path : Path decoder ends fuel input code endPos) :
    0 < code.length ∧ code.length ≤ fuel ∧ input.pos + code.length ≤ endPos ∧ endPos ≤ input.stop := by
  induction path with
  | last _ advance inside _ =>
    simp only [List.length_singleton]
    exact ⟨by omega, by omega, by omega, inside⟩
  | next _ advance _ _ _ ih =>
    obtain ⟨_, fuelBound, spanBound, stopBound⟩ := ih
    simp only [List.length_cons, Input.atPos] at *
    exact ⟨by omega, by omega, by omega, stopBound⟩

theorem blocks_deterministic {decoder : Graph Context Buffer Source} (unique : Deterministic decoder)
    (ends : Context → Nat → Source → Prop) (fuel : Nat) : Deterministic (blocks decoder ends fuel) := by
  rintro input ⟨code, endPos⟩ ⟨otherCode, otherEnd⟩
    (first : Path decoder ends fuel input code endPos) (second : Path decoder ends fuel input otherCode otherEnd)
  induction first generalizing otherCode otherEnd with
  | last decoded _ _ stop =>
    cases second with
    | last decoded' =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (unique decoded decoded')
      rfl
    | next decoded' _ _ continues _ =>
      obtain ⟨rfl, _⟩ := Prod.mk.inj (unique decoded decoded')
      exact (continues stop).elim
  | next decoded _ _ continues _ ih =>
    cases second with
    | last decoded' _ _ stop =>
      obtain ⟨rfl, _⟩ := Prod.mk.inj (unique decoded decoded')
      exact (continues stop).elim
    | next decoded' _ _ _ tail =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (unique decoded decoded')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ih _ _ tail)
      rfl

theorem dom_rebase_of_covered {Input Base Observation : Type*} (adapter : SetRel Input Base)
    (machine : Observed Base Observation) (available : adapter.cod ⊆ machine.dom) :
    (rebase adapter machine).dom = adapter.dom := by
  ext input
  constructor
  · rintro ⟨obs, base, related, _⟩
    exact ⟨base, related⟩
  · rintro ⟨base, related⟩
    obtain ⟨obs, observed⟩ := available ⟨input, related⟩
    exact ⟨obs, base, related, observed⟩

end Silmaril.Machine.DecodeGraph.Proofs
