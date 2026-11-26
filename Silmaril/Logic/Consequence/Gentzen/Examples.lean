module

public import Silmaril.Logic.Consequence.Gentzen.Thms

/-!
# Examples: literal sequents, by UNSAT and by TAUTO

Literals `Bool × Nat` (polarity, variable) under assignments `Nat → Bool`, with the exact
negation `lneg (b, v) = (!b, v)`. `pairs Γ` (some literal and its negation both occur) is a
decidable test that is sound and complete both as an UNSAT check and as a TAUTO check, so
`viaUnsat pairs lneg` is exactly `Valid` (`viaUnsat_pairs_eq`) and therefore closed under the
default Gentzen rules. Examples: excluded middle `⊢ p, ¬p` (TAUTO), explosion `p, ¬p ⊢`
(UNSAT), a derivation by cut, and a bounded variant of `pairs` that is sound but not cut-closed.
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Examples

open Refutation (SatAll Unsat CheckSound CheckComplete)

/-- A literal: polarity and variable. -/
abbrev Lit := Bool × Nat

/-- An assignment satisfies a literal. -/
def lsat (τ : Nat → Bool) (l : Lit) : Prop := τ l.2 = l.1

/-- The negated literal. -/
def lneg (l : Lit) : Lit := (!l.1, l.2)

/-- Some literal occurs together with its negation. -/
def pairs (Γ : List Lit) : Prop := ∃ l ∈ Γ, lneg l ∈ Γ

instance (Γ : List Lit) : Decidable (pairs Γ) := inferInstanceAs (Decidable (∃ l ∈ Γ, _))

theorem lneg_sound : NegSound lsat lneg := by
  rintro τ ⟨b, v⟩ h h'; simp_all [lsat, lneg]

theorem lneg_complete : NegComplete lsat lneg := by
  rintro τ ⟨b, v⟩ h; cases hb : τ v <;> cases b <;> simp_all [lsat, lneg]

theorem pairs_sound : CheckSound lsat pairs := by
  rintro Γ ⟨l, hl, hn⟩ τ h
  exact lneg_sound τ l (h _ hn) (h _ hl)

theorem pairs_complete : CheckComplete lsat pairs := by
  intro Γ h
  by_contra hp
  refine h (fun v => decide ((true, v) ∈ Γ)) ?_
  rintro ⟨b, v⟩ hl
  cases b
  · have : (true, v) ∉ Γ := fun ht => hp ⟨_, hl, ht⟩
    simp [lsat, this]
  · simp [lsat, hl]

theorem pairs_tautSound : TautSound lsat pairs := by
  rintro Δ ⟨l, hl, hn⟩ τ -
  by_cases h : lsat τ l
  · exact ⟨l, hl, h⟩
  · exact ⟨_, hn, lneg_complete τ l h⟩

/-- The complementary-pair test computes validity of literal sequents. -/
theorem viaUnsat_pairs_eq : viaUnsat pairs lneg = Valid lsat :=
  le_antisymm (viaUnsat_le_valid pairs_sound lneg_complete)
    (valid_le_viaUnsat pairs_complete lneg_sound)

/-- So it is closed under the default rules, cut included. -/
theorem viaUnsat_pairs_closed : Closed defaultRules (viaUnsat pairs lneg) :=
  viaUnsat_pairs_eq ▸ valid_closed

/-- Excluded middle, by TAUTO. -/
theorem excluded_middle : Valid lsat [] [(true, 0), (false, 0)] :=
  viaTauto_le_valid pairs_tautSound lneg_sound _ _ (by decide)

/-- Explosion, by UNSAT: `p, ¬p ⊢`. -/
theorem explosion : Unsat lsat [(true, 0), (false, 0)] :=
  unsat_of_viaUnsat_nil (neg := lneg) pairs_sound (by decide)

/-- Decided validity of literal sequents: `p ⊢ q, p` holds, `p ⊢ q` does not. -/
theorem valid_p_qp : Valid lsat [(true, 0)] [(true, 1), (true, 0)] :=
  viaUnsat_pairs_eq ▸ (by decide : viaUnsat pairs lneg [(true, 0)] [(true, 1), (true, 0)])

theorem not_valid_p_q : ¬ Valid lsat [(true, 0)] [(true, 1)] :=
  viaUnsat_pairs_eq ▸ (by decide : ¬ viaUnsat pairs lneg [(true, 0)] [(true, 1)])

/-! ## Derivations by cut from non-logical sequents -/

/-- Two non-logical sequents: `p ⊢ q` and `q ⊢ r`. -/
def chain : Seq Lit := fun Γ Δ =>
  (Γ = [(true, 0)] ∧ Δ = [(true, 1)]) ∨ (Γ = [(true, 1)] ∧ Δ = [(true, 2)])

theorem chain_derives : Derives defaultRules chain [(true, 0)] [(true, 2)] :=
  .cut (Γ := [(true, 0)]) (Γ' := []) (Δ := []) (Δ' := [(true, 2)]) trivial
    (.base (.inl ⟨rfl, rfl⟩)) (.base (.inr ⟨rfl, rfl⟩))

/-! ## A bounded checker: sound, not cut-closed -/

/-- `pairs`, only on lists of length at most `k`. -/
def bounded (k : Nat) (Γ : List Lit) : Prop := Γ.length ≤ k ∧ pairs Γ

instance (k : Nat) (Γ : List Lit) : Decidable (bounded k Γ) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem bounded_sound (k : Nat) : CheckSound lsat (bounded k) := fun Γ h => pairs_sound Γ h.2

/-- Its closure is sound. -/
theorem bounded_closure_sound : Derives defaultRules (viaUnsat (bounded 3) lneg) ≤ Valid lsat :=
  derives_viaUnsat_le_valid (bounded_sound 3) lneg_complete

/-- The raw relation is not cut-closed: `p, r ⊢ p` and `p, q ⊢ p` cut on `p` to
`p, r, q ⊢ p`, which has four literals with the negated conclusion. -/
theorem bounded_not_cut : ¬ Cut (viaUnsat (bounded 3) lneg) := fun h =>
  absurd (@h [(true, 0), (true, 2)] [(true, 1)] [] [(true, 0)] (true, 0) (by decide) (by decide))
    (by decide)

end Silmaril.Consequence.Gentzen.Examples
