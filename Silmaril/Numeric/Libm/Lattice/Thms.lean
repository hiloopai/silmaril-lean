module

public import Silmaril.Numeric.Libm.Lattice.Defs
import Silmaril.Proofs.Numeric.Libm.Lattice

/-!
# Edges of the libm specification lattice

For one function `S` and implementation `impl`:

* (c) → (b): `Spec.ErrorGlobal.errorOn`; (b) is monotone in the inputs and the
  bound (`Spec.ErrorOn.mono`).
* (d) → (c): `Spec.CorrectlyRounded.errorGlobal_half`, a correctly rounded
  implementation is within 1/2 ulp everywhere, overflow included.
* inside (d): `Exact → CorrectlyRounded → CRWithin n`, `CRWithin 0 →
  CorrectlyRounded`, and `CRWithin` is monotone.
* (e) → everything value-level: `Spec.BitExact.accurate` and
  `Spec.BitExact.specialValues` transfer any property of the reference function
  `ref` to an implementation returning the same encodings. In particular, if a
  bound (c) is proved or assumed for `ref`, it holds for `impl`
  (`Spec.BitExact.errorGlobal`).
* `Spec.accurate_mono`: every case of `Accuracy.Implies`.
* `validLibm_cons`: a libm problem is the conjunction of its per-function problems.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.FlagSpec Float.Model
open Silmaril.Proofs.Numeric.Libm.Lattice

/-! ## Single results -/

theorem UlpClose.mono {f : Format} {k k' r : ℝ} {y : Option (Rounded ℚ)} (hk : k ≤ k')
    (h : UlpClose f k r y) : UlpClose f k' r y := ulpClose_mono f hk h

/-- A round-to-nearest result is within half an ulp, including on overflow. -/
theorem RoundsTo.ulpClose_half {f : Format} {r : ℝ} {y : Option (Rounded ℚ)}
    (h : RoundsTo f .nearestTiesToEven r y) : UlpClose f (1 / 2) r y :=
  ulpClose_half_of_roundsTo f h

namespace LibmFloat

variable {τ : Type} [LibmFloat τ] {r : ℝ} {y : τ}

theorem Close.mono {k k' : ℝ} (hk : k ≤ k') (h : Close k r y) : Close k' r y :=
  ulpClose_mono _ hk h

theorem CR.close_half (h : CR r y) : Close (1 / 2) r y := ulpClose_half_of_roundsTo _ h

theorem IsExactly.cr (h : IsExactly r y) : CR r y := cr_of_isExactly h

theorem CR.nearCR {n : ℝ} (hn : 0 ≤ n) (h : CR r y) : NearCR n r y := nearCR_of_cr hn h

theorem NearCR.mono {n n' : ℝ} (hn : n ≤ n') (h : NearCR n r y) : NearCR n' r y :=
  nearCR_mono hn h

theorem NearCR.cr (h : NearCR 0 r y) : CR r y := cr_of_nearCR_zero h

end LibmFloat

/-! ## Nodes of one function -/

namespace Spec

variable {α τ : Type} [LibmFloat τ] {S : Spec α τ} {impl : α → Outcome τ}

/-- (b) is antitone in the input set and monotone in the bound. -/
theorem ErrorOn.mono {D D' : Set α} {k k' : ℝ} (hD : D ⊆ D') (hk : k ≤ k')
    (h : S.ErrorOn impl D' k) : S.ErrorOn impl D k' :=
  fun x hx r hr => (h x (hD hx) r hr).mono hk

/-- (c) → (b). -/
theorem ErrorGlobal.errorOn {k : ℝ} (h : S.ErrorGlobal impl k) (D : Set α) :
    S.ErrorOn impl D k :=
  h.mono (Set.subset_univ D) le_rfl

theorem ErrorGlobal.mono {k k' : ℝ} (hk : k ≤ k') (h : S.ErrorGlobal impl k) :
    S.ErrorGlobal impl k' :=
  ErrorOn.mono subset_rfl hk h

/-- (d) → (c): correct rounding is a 1/2-ulp global bound. -/
theorem CorrectlyRounded.errorGlobal_half (h : S.CorrectlyRounded impl) :
    S.ErrorGlobal impl (1 / 2) :=
  fun x _ r hr => (h x r hr).close_half

theorem Exact.correctlyRounded (h : S.Exact impl) : S.CorrectlyRounded impl :=
  fun x r hr => (h x r hr).cr

theorem CorrectlyRounded.crWithin {n : ℝ} (hn : 0 ≤ n) (h : S.CorrectlyRounded impl) :
    S.CRWithin impl n :=
  fun x r hr => (h x r hr).nearCR hn

theorem CRWithin.mono {n n' : ℝ} (hn : n ≤ n') (h : S.CRWithin impl n) : S.CRWithin impl n' :=
  fun x r hr => (h x r hr).mono hn

theorem CRWithin.correctlyRounded (h : S.CRWithin impl 0) : S.CorrectlyRounded impl :=
  fun x r hr => (h x r hr).cr

theorem half_le_ratCast {k : ℚ} (h : 1 / 2 ≤ k) : (1 / 2 : ℝ) ≤ k := by
  have := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at this
  exact this

/-- Every case of `Accuracy.Implies` is an edge of the lattice. -/
theorem accurate_mono : ∀ {a b : Accuracy}, a.Implies b → S.Accurate impl a → S.Accurate impl b
  | _, .none, _, _ => trivial
  | .none, .ulps _, hab, _ | .none, .glibc _, hab, _ | .none, .correctlyRounded, hab, _
  | .none, .exact, hab, _ | .ulps _, .glibc _, hab, _ | .ulps _, .correctlyRounded, hab, _
  | .ulps _, .exact, hab, _ | .glibc _, .exact, hab, _ | .correctlyRounded, .exact, hab, _ =>
    hab.elim
  | .ulps _, .ulps _, hab, h => ErrorGlobal.mono (Rat.cast_le.mpr hab) h
  | .glibc n, .ulps _, hab, h =>
    (CRWithin.correctlyRounded (by
      have h' : S.CRWithin impl (n : ℝ) := h
      rw [hab.1] at h'
      simpa using h')).errorGlobal_half.mono (half_le_ratCast hab.2)
  | .glibc _, .glibc _, hab, h => CRWithin.mono (Nat.cast_le.mpr hab) h
  | .glibc n, .correctlyRounded, hab, h =>
    CRWithin.correctlyRounded (by
      have h' : S.CRWithin impl (n : ℝ) := h
      rw [hab] at h'
      simpa using h')
  | .correctlyRounded, .ulps _, hab, h =>
    CorrectlyRounded.errorGlobal_half h |>.mono (half_le_ratCast hab)
  | .correctlyRounded, .glibc _, _, h => CorrectlyRounded.crWithin (Nat.cast_nonneg _) h
  | .correctlyRounded, .correctlyRounded, _, h => h
  | .exact, .ulps _, hab, h =>
    (Exact.correctlyRounded h).errorGlobal_half.mono (half_le_ratCast hab)
  | .exact, .glibc _, _, h => (Exact.correctlyRounded h).crWithin (Nat.cast_nonneg _)
  | .exact, .correctlyRounded, _, h => Exact.correctlyRounded h
  | .exact, .exact, _, h => h

theorem valid_mono {a b : Accuracy} (hab : a.Implies b) (h : S.Valid impl a) : S.Valid impl b :=
  ⟨h.1, accurate_mono hab h.2⟩

theorem Valid.validValues {a : Accuracy} (h : S.Valid impl a) : S.ValidValues impl a :=
  ⟨h.1.1, h.2⟩

end Spec

/-! ### (e) A fixed implementation determines every value-level node -/

namespace BitExact

variable {α τ : Type} [LibmFloat τ] {S : Spec α τ} {impl : α → Outcome τ} {ref : α → τ}

theorem specialValues (h : BitExact impl ref)
    (hr : S.SpecialValues (Outcome.pure ref)) : S.SpecialValues impl :=
  fun c hc x hx => (h x) ▸ hr c hc x hx

theorem errorOn {D : Set α} {k : ℝ} (h : BitExact impl ref)
    (hr : S.ErrorOn (Outcome.pure ref) D k) : S.ErrorOn impl D k :=
  fun x hx r hrx => (h x) ▸ hr x hx r hrx

/-- (e) → (c): a bound proved or assumed for the reference holds for `impl`. -/
theorem errorGlobal {k : ℝ} (h : BitExact impl ref)
    (hr : S.ErrorGlobal (Outcome.pure ref) k) : S.ErrorGlobal impl k :=
  h.errorOn hr

theorem correctlyRounded (h : BitExact impl ref)
    (hr : S.CorrectlyRounded (Outcome.pure ref)) : S.CorrectlyRounded impl :=
  fun x r hrx => (h x) ▸ hr x r hrx

theorem crWithin {n : ℝ} (h : BitExact impl ref)
    (hr : S.CRWithin (Outcome.pure ref) n) : S.CRWithin impl n :=
  fun x r hrx => (h x) ▸ hr x r hrx

theorem exact (h : BitExact impl ref) (hr : S.Exact (Outcome.pure ref)) :
    S.Exact impl :=
  fun x r hrx => (h x) ▸ hr x r hrx

/-- (e) → (d), (c): every accuracy node of the reference holds for `impl`. -/
theorem accurate {a : Accuracy} (h : BitExact impl ref)
    (hr : S.Accurate (Outcome.pure ref) a) : S.Accurate impl a := by
  cases a with
  | none => trivial
  | ulps k => exact h.errorGlobal hr
  | glibc n => exact h.crWithin hr
  | correctlyRounded => exact h.correctlyRounded hr
  | exact => exact h.exact hr

theorem validValues {a : Accuracy} (h : BitExact impl ref)
    (hr : S.ValidValues (Outcome.pure ref) a) : S.ValidValues impl a :=
  ⟨h.specialValues hr.1, h.accurate hr.2⟩

end BitExact

namespace BitExactWhere

variable {α τ : Type} [LibmFloat τ] {S : Spec α τ} {impl : α → Outcome τ} {ref : α → Option τ}

omit [LibmFloat τ] in
theorem of_bitExact {ref : α → τ} (h : BitExact impl ref) : BitExactWhere impl (some ∘ ref) :=
  fun x _ hy => (h x).trans (Option.some.inj hy)

/-- (e) → (b): a bound proved or assumed for a partial reference on `D`, where
it is defined, holds for an implementation that agrees with it there. -/
theorem errorOn {D : Set α} {k : ℝ} (h : BitExactWhere impl ref)
    (hdef : ∀ x ∈ D, (ref x).isSome) (hr : ∀ x ∈ D, ∀ r, S.exact x = some r →
      ∀ y, ref x = some y → LibmFloat.Close k r y) :
    S.ErrorOn impl D k := by
  intro x hx r hrx
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hdef x hx)
  rw [h x y hy]
  exact hr x hx r hrx y hy

end BitExactWhere

/-! ## Combined problems -/

@[simp] theorem validLibm_nil (L : String → Accuracy) (impl : LibmImpl) :
    ValidLibm [] L impl := fun _ h => nomatch h

/-- A libm problem is the conjunction of its per-function problems. -/
@[simp] theorem validLibm_cons (e : Entry) (cat : List Entry) (L : String → Accuracy)
    (impl : LibmImpl) :
    ValidLibm (e :: cat) L impl ↔ e.valid (L e.name) (impl e) ∧ ValidLibm cat L impl := by
  simp [ValidLibm]

theorem validLibm_append (cat cat' : List Entry) (L : String → Accuracy) (impl : LibmImpl) :
    ValidLibm (cat ++ cat') L impl ↔ ValidLibm cat L impl ∧ ValidLibm cat' L impl := by
  simp only [ValidLibm, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

/-- Weakening each entry's level weakens the libm problem. -/
theorem ValidLibm.mono {cat : List Entry} {L L' : String → Accuracy} {impl : LibmImpl}
    (hmono : ∀ e ∈ cat, e.valid (L e.name) (impl e) → e.valid (L' e.name) (impl e))
    (h : ValidLibm cat L impl) : ValidLibm cat L' impl :=
  fun e he => hmono e he (h e he)

/-- For catalogues of `Spec` entries, the levels are ordered by `Accuracy.Implies`. -/
theorem Spec.entry_valid_mono {α τ : Type} [LibmFloat τ] (S : Spec α τ) {a b : Accuracy}
    (hab : a.Implies b) {impl : α → Outcome τ} (h : S.entry.valid a impl) :
    S.entry.valid b impl :=
  Spec.valid_mono hab h

end Silmaril.Numeric.Libm
