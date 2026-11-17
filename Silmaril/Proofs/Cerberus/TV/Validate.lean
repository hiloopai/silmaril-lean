module

public import Silmaril.Cerberus.TV.Validate.Defs
public import Silmaril.Cerberus.TV.Explore.Thms

/-! Proofs of `Silmaril.Cerberus.TV.Validate.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Cerberus.TV

open Silmaril.Cerberus
open Silmaril.Cerberus.TV
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Spec

/-- The observations of a closed program are those its endings admit. -/
theorem Closed.allows_iff (P : Closed) (impl : Impl) (x : Obs) :
    P.Allows impl x ↔ ∃ o out, P.Ends o out ∧ admits impl o out x := by
  unfold Closed.Allows Closed.Ends Closed.start allowed
  cases initial P.file P.enums (Core.Startup.execArguments P.args) with
  | error o =>
      simp only
      constructor
      · intro h; exact ⟨o, "", ⟨rfl, rfl⟩, h⟩
      · rintro ⟨o', out, ⟨rfl, rfl⟩, h⟩; exact h
  | ok r =>
      obtain ⟨s0, labels⟩ := r
      simp only
      constructor
      · rintro ⟨s, o, hr, hc, ha⟩; exact ⟨o, _, ⟨s, hr, hc, rfl⟩, ha⟩
      · rintro ⟨o, out, ⟨s, hr, hc, rfl⟩, ha⟩; exact ⟨s, o, hr, hc, ha⟩

theorem covers_sound (impl : Impl) (s e : Outcome × String) (h : covers impl s e = true)
    (x : Obs) (hx : admits impl e.1 e.2 x) : admits impl s.1 s.2 x := by
  rcases s with ⟨o', out'⟩
  rcases e with ⟨o, out⟩
  cases o' with
  | ub l u => simp [admits]
  | defined v' =>
      cases o with
      | defined v =>
          simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨rfl, h⟩ := h
          simp only [admits] at hx ⊢
          cases hv' : exitValue v' <;> cases hv : exitValue v <;>
            simp only [hv, hv'] at h hx ⊢ <;> simp_all [Termination.isExit]
      | _ => simp [covers] at h
  | aborted =>
      cases o with
      | aborted =>
          simp only [covers] at h
          split at h
          · rename_i hf
            simp only [decide_eq_true_eq] at h
            subst h
            exact hx
          · rename_i hf
            simp only [decide_eq_true_eq] at h
            obtain ⟨h1, h2, _⟩ := hx
            exact ⟨h1, h2.trans h, fun hf' => absurd hf' hf⟩
      | _ => simp [covers] at h
  | error _ => simp [covers] at h
  | unsupported _ => simp [covers] at h

theorem witness_admits (impl : Impl) (e : Outcome × String) (x : Obs)
    (h : witness impl e = some x) : admits impl e.1 e.2 x := by
  rcases e with ⟨o, out⟩
  cases o with
  | defined v =>
      simp only [witness] at h
      simp only [admits]
      cases hv : exitValue v <;> simp only [hv] at h ⊢ <;> cases h <;>
        simp [Termination.isExit]
  | aborted =>
      simp only [witness, Option.some.injEq] at h
      subst h
      exact ⟨rfl, List.prefix_refl _, fun _ => rfl⟩
  | ub => simp [admits]
  | _ => simp [witness] at h

/-- The facts a `validated` verdict rests on. -/
theorem validate_validated_facts (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .validated) :
    (tgt.explore bounds).limited = false ∧ (tgt.explore bounds).stuck = false ∧
      (tgt.explore bounds).gap = false ∧
      ∀ e ∈ (tgt.explore bounds).ends, covered impl (src.explore bounds).ends e = true := by
  simp only [validate] at h
  split_ifs at h with h1 h2 h3 h4
  · simp only [Bool.not_eq_true] at h1
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h2
    refine ⟨h1, h2.1, h2.2, ?_⟩
    intro e he
    simp only [List.isEmpty_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
      Bool.eq_false_iff] at h3
    by_contra hc
    exact h3 e he (by simpa using hc)

/-- **Soundness of `validated`.** -/
theorem validate_sound (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .validated) : Refines impl src tgt := by
  obtain ⟨hl, hs, hg, hcov⟩ := validate_validated_facts impl src tgt bounds h
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨o, out, hend, hadm⟩ := (Closed.allows_iff tgt impl x).mp hx
    have hmem := TV.Closed.explore_complete tgt bounds hl o out hend
    obtain ⟨s, hs, hcs⟩ := List.any_eq_true.mp (hcov _ hmem)
    exact (Closed.allows_iff src impl x).mpr
      ⟨s.1, s.2, TV.Closed.explore_sound src bounds s hs,
        covers_sound impl s (o, out) hcs x hadm⟩
  · intro o out hend
    have hmem := TV.Closed.explore_complete tgt bounds hl o out hend
    unfold Leaves.gap at hg
    by_contra hgap
    have : (tgt.explore bounds).ends.any (fun e => Outcome.isGap e.1) = true :=
      List.any_eq_true.mpr ⟨(o, out), hmem, by simpa using hgap⟩
    rw [hg] at this
    cases this
  · exact TV.Closed.explore_noStuck tgt bounds hl hs
  · exact TV.Closed.explore_terminates tgt bounds hl

/-- **Soundness of `refuted`.** -/
theorem validate_refuted (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .refuted) : ¬ Refines impl src tgt := by
  simp only [validate] at h
  split_ifs at h with h1 h2 h3 h4
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h4
  obtain ⟨⟨⟨hsl, _⟩, _⟩, hany⟩ := h4
  obtain ⟨e, he, hre⟩ := List.any_eq_true.mp hany
  have heT : e ∈ (tgt.explore bounds).ends := (List.mem_filter.mp he).1
  unfold refutes at hre
  split at hre
  · rename_i x hw
    intro hR
    have htx : tgt.Allows impl x := (Closed.allows_iff tgt impl x).mpr
      ⟨e.1, e.2, TV.Closed.explore_sound tgt bounds e heT, witness_admits impl e x hw⟩
    obtain ⟨o, out, hend, hadm⟩ := (Closed.allows_iff src impl x).mp (hR.observations x htx)
    have hmem := TV.Closed.explore_complete src bounds hsl o out hend
    have := List.all_eq_true.mp hre (o, out) hmem
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this hadm
  · cases hre

/-- An exhaustive exploration without undefined behaviour proves the program UB-free. -/
theorem Closed.ubFree_of_explore (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) (hu : (P.explore bounds).ub = false) : P.UBFree := by
  intro o out hend
  have hmem := TV.Closed.explore_complete P bounds hl o out hend
  unfold Leaves.ub at hu
  by_contra hub
  have : (P.explore bounds).ends.any (fun e => Outcome.isUB e.1) = true :=
    List.any_eq_true.mpr ⟨(o, out), hmem, by simpa using hub⟩
  rw [hu] at this
  cases this

/-- **Soundness of `validateUBFree`.** -/
theorem validateUBFree_sound (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : validateUBFree impl src tgt bounds = true) : RefinesUBFree impl src tgt := by
  simp only [validateUBFree, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hv, hl⟩, hu⟩ := h
  exact ⟨validate_sound impl src tgt bounds hv,
    Closed.ubFree_of_explore src bounds (by simpa [validate] using hl) (by simpa [validate] using hu)⟩

/-- **Soundness of the equivalence validator.** -/
theorem validateEquivalent_sound (impl : Impl) (P Q : Closed) (bounds : Bounds)
    (h : validateEquivalent impl P Q bounds = true) : Equivalent impl P Q := by
  simp only [validateEquivalent, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨validate_sound impl P Q bounds h.1, validate_sound impl Q P bounds h.2⟩

end Silmaril.Proofs.Cerberus.TV
