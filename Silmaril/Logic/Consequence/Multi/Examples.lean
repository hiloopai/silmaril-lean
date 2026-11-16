module

public import Silmaril.Logic.Consequence.Multi.Thms

/-!
# Multiple-conclusion systems: a one-atom example

`litMulti` is truth-table consequence for literals over one atom `p`. The models are
valuations `m : Bool`, the formulas are `Signed Unit`, `p := pos ()` holds when `m = true` and
`-p` when `m = false`. Named judgements, for fixtures:

| judgement | holds | reading |
|---|---|---|
| `contradiction : litMulti [p, -p] []` | yes | empty succedent: the conjunction `p ∧ ¬p` is inconsistent |
| `not_p_nil : ¬ litMulti [p] []` | no | `p` alone is consistent |
| `excludedMiddle : litMulti [] [p, -p]` | yes | empty antecedent: the disjunction `p ∨ ¬p` is a tautology |
| `not_nil_p : ¬ litMulti [] [p]` | no | `p` alone is not a tautology |
| `not_rightExt_excludedMiddle : ¬ rightExt litMulti.single [] [p, -p]` | no | no single disjunct follows, so `rightExt` falls short of the semantics |
| `single_p : litMulti.single [p] p` | yes | singleton restriction |
| `posPart_unit : MultiSystem.posPart litMulti [()] [()]` | yes | the positive part, along `Signed.pos` |
| `not_posPart_nil : ¬ MultiSystem.posPart litMulti [] [()]` | no | the positive part has no tautologies here |
-/

@[expose] public section

namespace Silmaril.Consequence.Examples

/-- Satisfaction of a literal over one atom by a valuation. -/
def litSat (m : Bool) : Signed Unit → Prop
  | .pos _ => m = true
  | .neg _ => m = false

/-- Truth-table multiple-conclusion consequence for one-atom literals. -/
def litMulti : MultiSystem (Signed Unit) (Signed Unit) := multiEntails litSat litSat

/-- The atom. -/
def p : Signed Unit := .pos ()

theorem contradiction : litMulti [p, -p] [] := fun m h => by
  have h₁ := h p (by simp); have h₂ := h (-p) (by simp)
  simp_all [litSat, p]

theorem not_p_nil : ¬ litMulti [p] [] := fun h => by
  simpa using h true (by simp [litSat, p])

theorem excludedMiddle : litMulti [] [p, -p] := fun m _ => by
  cases m <;> simp [litSat, p]

theorem not_nil_p : ¬ litMulti [] [p] := fun h => by
  simpa [litSat, p] using h false (by simp)

theorem not_rightExt_excludedMiddle : ¬ rightExt litMulti.single [] [p, -p] :=
  fun ⟨d, hd, h⟩ => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · simpa [litSat, p] using h false (by simp)
  · simpa [litSat, p] using h true (by simp)

theorem single_p : litMulti.single [p] p := fun _ h => by simpa using h p (by simp)

theorem posPart_unit : MultiSystem.posPart litMulti [()] [()] := fun _ h =>
  ⟨.pos (), by simp, h _ (by simp)⟩

theorem not_posPart_nil : ¬ MultiSystem.posPart litMulti [] [()] := fun h => by
  simpa [litSat] using h false (by simp)

end Silmaril.Consequence.Examples
