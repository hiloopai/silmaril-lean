module

public import Silmaril.Wasm.Spec.Live.Defs

@[expose] public section

/-!
# Liveness: the response formula on finite traces and infinite words

* `holdsFin_responds_iff`, `holdsInf_responds_iff`: the response formula, unfolded;
* `not_holdsFin_responds`, `not_holdsInf_responds`: a call with no later good return refutes it;
* `not_sat_responds_of_witness`: **a divergence witness refutes the response formula** in the
  maximal-behaviour reading `ltlMax`;
* `sat_of_witness`: a sentence of `ltlMax` holds of every divergence witness.
-/

namespace Silmaril.Wasm.Spec.Live

variable {Ty A R : Type} {X : Iface Ty}

/-- The response formula on a finite trace. -/
theorem holdsFin_responds_iff (t : List (Event A R X)) (j : X.Exp) (ok : R → Prop) :
    LTL.HoldsFin t 0 (responds j ok) ↔ ∀ k (hk : k < t.length), isCall j (t.take k) t[k] →
      ∃ i, k ≤ i ∧ ∃ hi : i < t.length, isRetOk j ok (t.take i) t[i] := by
  unfold responds
  rw [LTL.holdsFin_alw]
  simp only [LTL.imp, LTL.ev, LTL.HoldsFin, List.get_eq_getElem, implies_true,
    and_true]
  constructor
  · intro h k hk hc
    rcases h k (Nat.zero_le k) hk with hn | ⟨i, hki, hi, hr⟩
    · exact absurd ⟨hk, hc⟩ hn
    · obtain ⟨hi', hr'⟩ := hr
      exact ⟨i, hki, hi', hr'⟩
  · intro h k _ hk
    by_cases hc : ∃ h : k < t.length, isCall j (t.take k) t[k]
    · obtain ⟨hk', hc'⟩ := hc
      obtain ⟨i, hki, hi, hr⟩ := h k hk' hc'
      exact .inr ⟨i, hki, hi, hi, hr⟩
    · exact .inl hc

/-- The response formula on an infinite word. -/
theorem holdsInf_responds_iff (w : ℕ → Event A R X) (j : X.Exp) (ok : R → Prop) :
    LTL.HoldsInf w 0 (responds j ok) ↔ ∀ k, isCall j (prefixList w k) (w k) →
      ∃ i, k ≤ i ∧ isRetOk j ok (prefixList w i) (w i) := by
  unfold responds
  rw [LTL.holdsInf_alw]
  simp only [LTL.imp, LTL.ev, LTL.HoldsInf, implies_true, and_true]
  constructor
  · intro h k hc
    rcases h k (Nat.zero_le k) with hn | hr
    · exact absurd hc hn
    · exact hr
  · intro h k _
    by_cases hc : isCall j (prefixList w k) (w k)
    · exact .inr (h k hc)
    · exact .inl hc

/-- A finite trace calling `j` whose returns are all bad refutes the response formula. -/
theorem not_holdsFin_responds {t : List (Event A R X)} {j : X.Exp} {a : A} {ok bad : R → Prop}
    (hbad : ∀ r, bad r → ¬ ok r) (hc : Event.call j a ∈ t)
    (hr : ∀ j' r, Event.ret j' r ∈ t → bad r) : ¬ LTL.HoldsFin t 0 (responds j ok) := by
  rw [holdsFin_responds_iff]
  intro h
  obtain ⟨k, hk, hkc⟩ : ∃ k, ∃ hk : k < t.length, t[k] = Event.call j a :=
    List.getElem_of_mem hc
  have hcall : isCall j (t.take k) t[k] := ⟨a, hkc⟩
  obtain ⟨i, -, hi, r, hok, hri⟩ := h k hk hcall
  have hmem : Event.ret j r ∈ t := hri ▸ List.getElem_mem hi
  exact hbad r (hr j r hmem) hok

/-- An infinite word calling `j` and never returning refutes the response formula. -/
theorem not_holdsInf_responds {w : ℕ → Event A R X} {j : X.Exp} {a : A} {ok : R → Prop}
    (hc : ∃ k, w k = Event.call j a) (hr : ∀ k j' r, w k ≠ Event.ret j' r) :
    ¬ LTL.HoldsInf w 0 (responds j ok) := by
  rw [holdsInf_responds_iff]
  intro h
  obtain ⟨k, hk⟩ := hc
  obtain ⟨i, -, r, -, hri⟩ := h k ⟨a, hk⟩
  exact hr i j r hri

/-- **A divergence witness refutes the response formula** over maximal behaviours. -/
theorem not_sat_responds_of_witness {T : Set (List (Event A R X))} {j : X.Exp} {a : A}
    {ok bad : R → Prop} (hbad : ∀ r, bad r → ¬ ok r) (hW : DivWitness T j a bad) :
    ¬ (ltlMax Ty A R).Sat T (responds j ok) := by
  rintro ⟨hinf, hfin⟩
  rcases hW with ⟨t, hmax, hc, hr⟩ | ⟨w, hw, hc, hr⟩
  · exact not_holdsFin_responds hbad hc hr (hfin t hmax)
  · exact not_holdsInf_responds hc hr (hinf w hw)

/-- A sentence of `ltlMax` holds of the divergence witness. -/
theorem sat_of_witness {T : Set (List (Event A R X))} {j : X.Exp} {a : A} {bad : R → Prop}
    {φ : LTLFm A R X} (hφ : (ltlMax Ty A R).Sat T φ) (hW : DivWitness T j a bad) :
    (∃ t, Maximal T t ∧ Event.call j a ∈ t ∧ (∀ j' r, Event.ret j' r ∈ t → bad r) ∧
        LTL.HoldsFin t 0 φ) ∨
      (∃ w ∈ limits T, (∃ k, w k = Event.call j a) ∧ (∀ k j' r, w k ≠ Event.ret j' r) ∧
        LTL.HoldsInf w 0 φ) := by
  rcases hW with ⟨t, hmax, hc, hr⟩ | ⟨w, hw, hc, hr⟩
  · exact .inl ⟨t, hmax, hc, hr, hφ.2 t hmax⟩
  · exact .inr ⟨w, hw, hc, hr, hφ.1 w hw⟩

end Silmaril.Wasm.Spec.Live
