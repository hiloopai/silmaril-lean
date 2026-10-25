module

public import Silmaril.Encoding.Relation
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# The lattice of encodings

For fixed carrier `σ` and syntax `α`, encodings form a complete lattice (the
pointwise `Prop` lattice): `E ≤ F` iff every `E`-spelling is an `F`-spelling.
A canonical form sits below the general grammar; a profile is a restriction;
`⊔` admits the spellings of either encoding.

* `Functional` is a down-set closed under `⊓` and (nonempty) `sInf`, but not
  under `⊔` (`not_functional_sup`).
* `Total` is an up-set, hence closed under `⊔`.
* `Deterministic` is a down-set.
* `comap f` is a complete lattice homomorphism with left adjoint `map f`.
* `push g ⊣ pull g ⊣ pushAll g` on the carrier side, and
  `pushPartial g ⊣ pullPartialAll g` for partial carrier maps.
* Decoder soundness/completeness and encoder correctness are lattice
  inequalities against the graphs `ofDecoder` / `ofFun`.
-/

@[expose] public section

namespace Silmaril

namespace EncRel

variable {σ σ' α β : Type}

instance : CompleteLattice (EncRel σ α) :=
  inferInstanceAs (CompleteLattice (σ → α → Prop))

theorem le_def {E F : EncRel σ α} : E ≤ F ↔ ∀ s a, E s a → F s a := Iff.rfl

theorem le_iff_forall {E F : EncRel σ α} : E ≤ F ↔ ∀ ⦃s a⦄, E s a → F s a := Iff.rfl

@[simp] theorem inf_apply (E F : EncRel σ α) (s : σ) (a : α) :
    (E ⊓ F) s a ↔ E s a ∧ F s a := Iff.rfl

@[simp] theorem sup_apply (E F : EncRel σ α) (s : σ) (a : α) :
    (E ⊔ F) s a ↔ E s a ∨ F s a := Iff.rfl

@[simp] theorem bot_apply (s : σ) (a : α) : (⊥ : EncRel σ α) s a ↔ False := Iff.rfl

@[simp] theorem top_apply (s : σ) (a : α) : (⊤ : EncRel σ α) s a ↔ True := Iff.rfl

@[simp] theorem sSup_apply (S : Set (EncRel σ α)) (s : σ) (a : α) :
    (sSup S) s a ↔ ∃ E ∈ S, E s a := by
  refine (Eq.to_iff (congrFun
    (@_root_.sSup_apply σ (fun _ => α → Prop) _ (S : Set (σ → α → Prop)) s) a)).trans ?_
  simp only [_root_.iSup_apply, iSup_Prop_eq]
  exact ⟨fun ⟨⟨E, hE⟩, h⟩ => ⟨E, hE, h⟩, fun ⟨E, hE, h⟩ => ⟨⟨E, hE⟩, h⟩⟩

@[simp] theorem sInf_apply (S : Set (EncRel σ α)) (s : σ) (a : α) :
    (sInf S) s a ↔ ∀ E ∈ S, E s a := by
  refine (Eq.to_iff (congrFun
    (@_root_.sInf_apply σ (fun _ => α → Prop) _ (S : Set (σ → α → Prop)) s) a)).trans ?_
  simp only [_root_.iInf_apply, iInf_Prop_eq]
  exact ⟨fun h E hE => h ⟨E, hE⟩, fun h E => h E.1 E.2⟩

@[simp] theorem iSup_apply {ι : Sort*} (E : ι → EncRel σ α) (s : σ) (a : α) :
    (⨆ i, E i) s a ↔ ∃ i, E i s a := by
  rw [iSup, sSup_apply]
  simp

@[simp] theorem iInf_apply {ι : Sort*} (E : ι → EncRel σ α) (s : σ) (a : α) :
    (⨅ i, E i) s a ↔ ∀ i, E i s a := by
  rw [iInf, sInf_apply]
  simp

/-! ## Constructions are monotone -/

theorem restrict_le (E : EncRel σ α) (P : α → Prop) : E.restrict P ≤ E :=
  fun _ _ h => h.1

theorem restrictCarrier_le (E : EncRel σ α) (Q : σ → Prop) : E.restrictCarrier Q ≤ E :=
  fun _ _ h => h.2

theorem restrict_eq_inf (E : EncRel σ α) (P : α → Prop) :
    E.restrict P = E ⊓ fun _ a => P a := rfl

theorem comap_mono (f : β → α) : Monotone (comap (σ := σ) f) :=
  fun _ _ h s b hb => h s (f b) hb

theorem map_mono (f : α → β) : Monotone (map (σ := σ) f) := by
  rintro E F h s b ⟨a, ha, rfl⟩
  exact ⟨a, h s a ha, rfl⟩

theorem push_mono (g : σ → σ') : Monotone (push (α := α) g) := by
  rintro E F h s' a ⟨s, rfl, hs⟩
  exact ⟨s, rfl, h s a hs⟩

theorem pull_mono (g : σ → σ') : Monotone (pull (α := α) g) :=
  fun _ _ h s a hs => h (g s) a hs

theorem pushPartial_mono (g : σ → Option σ') : Monotone (pushPartial (α := α) g) := by
  rintro E F h s' a ⟨s, hs, h'⟩
  exact ⟨s, hs, h s a h'⟩

theorem pullPartial_mono (g : σ → Option σ') : Monotone (pullPartial (α := α) g) := by
  rintro E F h s a ⟨s', hs, h'⟩
  exact ⟨s', hs, h s' a h'⟩

/-! ## Galois connections -/

/-- `map f ⊣ comap f`. -/
theorem gc_map_comap (f : α → β) :
    GaloisConnection (map (σ := σ) f) (comap f) := by
  intro E F
  constructor
  · intro h s a ha
    exact h s (f a) ⟨a, ha, rfl⟩
  · rintro h s b ⟨a, ha, rfl⟩
    exact h s a ha

/-- `push g ⊣ pull g` (written `g_! ⊣ g^*`). -/
theorem gc_push_pull (g : σ → σ') :
    GaloisConnection (push (α := α) g) (pull g) := by
  intro E F
  constructor
  · intro h s a ha
    exact h (g s) a ⟨s, rfl, ha⟩
  · rintro h s' a ⟨s, rfl, hs⟩
    exact h s a hs

/-- `pull g ⊣ pushAll g`. -/
theorem gc_pull_pushAll (g : σ → σ') :
    GaloisConnection (pull (α := α) g) (pushAll g) := by
  intro E F
  constructor
  · rintro h s' a hs s rfl
    exact h s a hs
  · intro h s a hs
    exact h (g s) a hs s rfl

/-- `pushPartial g ⊣ pullPartialAll g` for partial carrier maps. -/
theorem gc_pushPartial_pullPartialAll (g : σ → Option σ') :
    GaloisConnection (pushPartial (α := α) g) (pullPartialAll g) := by
  intro E F
  constructor
  · intro h s a hs s' hg
    exact h s' a ⟨s, hg, hs⟩
  · rintro h s' a ⟨s, hg, hs⟩
    exact h s a hs s' hg

/-- The strong partial pullback lies below the weak one; they agree on the
domain of `g`. -/
theorem pullPartial_le_pullPartialAll (g : σ → Option σ') (E : EncRel σ' α) :
    pullPartial g E ≤ pullPartialAll g E := by
  rintro s a ⟨t, ht, h⟩ t' ht'
  rw [ht] at ht'
  cases ht'
  exact h

/-! ## `comap` is a complete lattice homomorphism -/

theorem comap_sSup (f : β → α) (S : Set (EncRel σ α)) :
    comap f (sSup S) = sSup (comap f '' S) := by
  ext s b
  simp only [comap, sSup_apply, Set.mem_image]
  constructor
  · rintro ⟨E, hE, h⟩
    exact ⟨comap f E, ⟨E, hE, rfl⟩, h⟩
  · rintro ⟨_, ⟨E, hE, rfl⟩, h⟩
    exact ⟨E, hE, h⟩

theorem comap_sInf (f : β → α) (S : Set (EncRel σ α)) :
    comap f (sInf S) = sInf (comap f '' S) := by
  ext s b
  simp only [comap, sInf_apply, Set.mem_image]
  constructor
  · rintro h _ ⟨E, hE, rfl⟩
    exact h E hE
  · intro h E hE
    exact h (comap f E) ⟨E, hE, rfl⟩

/-- `comap f` as a complete lattice homomorphism. -/
def comapHom (f : β → α) : CompleteLatticeHom (EncRel σ α) (EncRel σ β) where
  toFun := comap f
  map_sInf' := comap_sInf f
  map_sSup' := comap_sSup f

/-- `pull g` is likewise a complete lattice homomorphism. -/
def pullHom (g : σ → σ') : CompleteLatticeHom (EncRel σ' α) (EncRel σ α) where
  toFun := pull g
  map_sInf' S := by
    ext s a
    simp only [pull, sInf_apply, Set.mem_image]
    constructor
    · rintro h _ ⟨E, hE, rfl⟩
      exact h E hE
    · intro h E hE
      exact h (pull g E) ⟨E, hE, rfl⟩
  map_sSup' S := by
    ext s a
    simp only [pull, sSup_apply, Set.mem_image]
    constructor
    · rintro ⟨E, hE, h⟩
      exact ⟨pull g E, ⟨E, hE, rfl⟩, h⟩
    · rintro ⟨_, ⟨E, hE, rfl⟩, h⟩
      exact ⟨E, hE, h⟩

/-! ## Closure properties of the basic predicates -/

section Closure

variable {E F : EncRel σ α}

/-- Functionality is a down-set. -/
theorem Functional.anti (hEF : E ≤ F) (hF : F.Functional) : E.Functional :=
  fun _ _ _ h h' => hF (hEF _ _ h) (hEF _ _ h')

theorem Functional.inf_left (hE : E.Functional) (F : EncRel σ α) : (E ⊓ F).Functional :=
  hE.anti inf_le_left

theorem Functional.inf_right (E : EncRel σ α) (hF : F.Functional) : (E ⊓ F).Functional :=
  hF.anti inf_le_right

/-- An infimum is functional as soon as one member is. -/
theorem functional_sInf {S : Set (EncRel σ α)} (h : ∃ E ∈ S, E.Functional) :
    (sInf S).Functional := by
  obtain ⟨E, hE, hF⟩ := h
  exact hF.anti (sInf_le hE)

theorem functional_bot : (⊥ : EncRel σ α).Functional := fun _ _ _ h => h.elim

/-- Functionality is not closed under `⊔`: two single-value encodings of
different values with the same spelling. -/
theorem not_functional_sup :
    ∃ E F : EncRel Unit Bool, E.Functional ∧ F.Functional ∧ ¬ (E ⊔ F).Functional := by
  refine ⟨fun _ a => a = true, fun _ a => a = false, ?_, ?_, ?_⟩
  · intro _ a a' h h'; rw [h, h']
  · intro _ a a' h h'; rw [h, h']
  · intro h
    exact Bool.noConfusion (h (s := ()) (a := true) (a' := false) (Or.inl rfl) (Or.inr rfl))

/-- Determinism is a down-set. -/
theorem Deterministic.anti (hEF : E ≤ F) (hF : F.Deterministic) : E.Deterministic :=
  fun _ _ _ h h' => hF (hEF _ _ h) (hEF _ _ h')

theorem Deterministic.inf_left (hE : E.Deterministic) (F : EncRel σ α) :
    (E ⊓ F).Deterministic :=
  hE.anti inf_le_left

theorem deterministic_sInf {S : Set (EncRel σ α)} (h : ∃ E ∈ S, E.Deterministic) :
    (sInf S).Deterministic := by
  obtain ⟨E, hE, hF⟩ := h
  exact hF.anti (sInf_le hE)

/-- Totality is an up-set. -/
theorem Total.mono (hEF : E ≤ F) (hE : E.Total) : F.Total := by
  intro a
  obtain ⟨s, h⟩ := hE a
  exact ⟨s, hEF _ _ h⟩

theorem Total.sup_left (hE : E.Total) (F : EncRel σ α) : (E ⊔ F).Total :=
  hE.mono le_sup_left

theorem Total.sup_right (E : EncRel σ α) (hF : F.Total) : (E ⊔ F).Total :=
  hF.mono le_sup_right

theorem total_sSup {S : Set (EncRel σ α)} (h : ∃ E ∈ S, E.Total) : (sSup S).Total := by
  obtain ⟨E, hE, hT⟩ := h
  exact hT.mono (le_sSup hE)

theorem total_top [Inhabited σ] : (⊤ : EncRel σ α).Total := fun _ => ⟨default, trivial⟩

theorem image_mono (hEF : E ≤ F) : E.image ⊆ F.image := by
  rintro a ⟨s, h⟩
  exact ⟨s, hEF _ _ h⟩

theorem domain_mono (hEF : E ≤ F) : E.domain ⊆ F.domain := by
  rintro s ⟨a, h⟩
  exact ⟨a, hEF _ _ h⟩

end Closure

/-! ## Codec specifications as inequalities -/

section Codecs

variable {E : EncRel σ α}

theorem decoderSound_iff_le (dec : σ → Option α) :
    E.DecoderSound dec ↔ ofDecoder dec ≤ E := Iff.rfl

theorem decoderComplete_iff_le (dec : σ → Option α) :
    E.DecoderComplete dec ↔ E ≤ ofDecoder dec := Iff.rfl

theorem encoderCorrect_iff_le (enc : α → σ) :
    E.EncoderCorrect enc ↔ ofFun enc ≤ E := by
  constructor
  · rintro h s a rfl; exact h a
  · intro h a; exact h _ a rfl

theorem partialEncoderSound_iff_le (enc : α → Option σ) :
    E.PartialEncoderSound enc ↔ ofPartialFun enc ≤ E := by
  constructor
  · intro h s a hs; exact h a s hs
  · intro h a s hs; exact h s a hs

/-- A sound and complete decoder pins the encoding down exactly. -/
theorem eq_ofDecoder (dec : σ → Option α) (hs : E.DecoderSound dec)
    (hc : E.DecoderComplete dec) : E = ofDecoder dec :=
  le_antisymm hc hs

/-- An encoding is functional iff it lies below the graph of some decoder. -/
theorem functional_iff_le_ofDecoder :
    E.Functional ↔ ∃ dec : σ → Option α, E ≤ ofDecoder dec := by
  constructor
  · intro hF
    classical
    refine ⟨fun s => if h : E.Encodable s then some (Classical.choose h) else none, ?_⟩
    intro s a h
    have he : E.Encodable s := ⟨a, h⟩
    simp only [ofDecoder, he, dite_true, Option.some.injEq]
    exact hF (Classical.choose_spec he) h
  · rintro ⟨dec, h⟩
    exact (ofDecoder_functional dec).anti h

/-- An encoding is deterministic iff it lies below the graph of some partial
encoder. -/
theorem deterministic_iff_le_ofPartialFun :
    E.Deterministic ↔ ∃ enc : α → Option σ, E ≤ ofPartialFun enc := by
  constructor
  · intro hD
    classical
    refine ⟨fun a => if h : ∃ s, E s a then some (Classical.choose h) else none, ?_⟩
    intro s a h
    have he : ∃ s, E s a := ⟨s, h⟩
    simp only [ofPartialFun, he, dite_true, Option.some.injEq]
    exact hD (Classical.choose_spec he) h
  · rintro ⟨enc, h⟩
    exact (ofPartialFun_deterministic enc).anti h

end Codecs

end EncRel

end Silmaril
