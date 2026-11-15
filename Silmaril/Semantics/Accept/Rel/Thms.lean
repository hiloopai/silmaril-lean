module

public import Silmaril.Semantics.Accept.Rel.Defs
public import Silmaril.Semantics.Accept.Thms

/-!
# Acceptance through relations, partial functions, total maps and indices: laws

* runners: `acceptsSome (outcomes R) = pullSome R`, `neverRejects (outcomes R) rej =
  pullAll R rejᶜ`, and complements (`compl_pullSome`, `compl_pullAll`);
* composition: `pullSome_comp`, `pullAll_comp` (Mathlib's `SetRel.preimage_comp`/`core_comp`);
* when the quantifiers agree: `pullAll_subset_pullSome` (every input has an output),
  `pullSome_subset_pullAll` (at most one output), and both for total maps;
* partial functions: membership, `none` (accepted universally, rejected existentially),
  Kleisli composition `ofPartial_partialComp`, total maps as partial functions, and Bool
  checkers through `Option.any`/`Option.all`;
* indexed sets: `indexedLangIso : IndexedLang A ≃o Set (Σ i, A i)`, checkers on dependent
  pairs, and the rejection quantifiers of `eraseSome`/`eraseAll`.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

open scoped SetRel

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Relations as runners -/

section Rel

variable {R : α -|> β} {S : β -|> γ} {L M : Set β} {a : α}

@[simp] theorem mem_outcomes {b : β} : b ∈ outcomes R a ↔ (a, b) ∈ R := Iff.rfl

theorem mem_pullSome : a ∈ pullSome R L ↔ ∃ b ∈ L, (a, b) ∈ R := Iff.rfl

theorem mem_pullAll : a ∈ pullAll R L ↔ ∀ ⦃b⦄, (a, b) ∈ R → b ∈ L := Iff.rfl

theorem acceptsSome_outcomes : acceptsSome (outcomes R) L = pullSome R L := by ext; simp; grind

theorem acceptsAll_outcomes : acceptsAll (outcomes R) L = pullAll R L := rfl

theorem rejectsSome_outcomes : rejectsSome (outcomes R) L = pullSome R L := acceptsSome_outcomes

/-- Never-rejection along a relation is the universal pullback of the complement. -/
theorem neverRejects_outcomes : neverRejects (outcomes R) L = pullAll R Lᶜ := rfl

/-- Not some output in `L` is every output outside `L`. -/
theorem compl_pullSome : (pullSome R L)ᶜ = pullAll R Lᶜ := by ext; simp; grind

theorem compl_pullAll : (pullAll R L)ᶜ = pullSome R Lᶜ := by
  rw [← compl_compl (pullSome R Lᶜ), compl_pullSome, compl_compl]

theorem pullSome_comp {L : Set γ} : pullSome (R ○ S) L = pullSome R (pullSome S L) :=
  SetRel.preimage_comp ..

theorem pullAll_comp {L : Set γ} : pullAll (R ○ S) L = pullAll R (pullAll S L) :=
  SetRel.core_comp ..

theorem pullSome_mono (h : L ⊆ M) : pullSome R L ⊆ pullSome R M :=
  SetRel.preimage_subset_preimage h

theorem pullAll_mono (h : L ⊆ M) : pullAll R L ⊆ pullAll R M := SetRel.core_subset_core h

/-- If every input has an output, universal pullback implies existential pullback. -/
theorem pullAll_subset_pullSome (htot : ∀ a, ∃ b, (a, b) ∈ R) : pullAll R L ⊆ pullSome R L :=
  fun a ha => let ⟨b, hb⟩ := htot a; ⟨b, ha hb, hb⟩

/-- If every input has at most one output, existential pullback implies universal pullback. -/
theorem pullSome_subset_pullAll (hfun : ∀ a b b', (a, b) ∈ R → (a, b') ∈ R → b = b') :
    pullSome R L ⊆ pullAll R L :=
  fun a ⟨b, hbL, hb⟩ b' hb' => hfun a b b' hb hb' ▸ hbL

/-- An input with no output is in every universal pullback and no existential one. -/
theorem mem_pullAll_of_forall_not (h : ∀ b, (a, b) ∉ R) : a ∈ pullAll R L :=
  fun b hb => absurd hb (h b)

theorem not_mem_pullSome_of_forall_not (h : ∀ b, (a, b) ∉ R) : a ∉ pullSome R L :=
  fun ⟨b, _, hb⟩ => h b hb

end Rel

/-! ## Total maps -/

section Total

variable {f : α → β} {L : Set β}

theorem pullSome_ofTotal : pullSome (ofTotal f) L = f ⁻¹' L := (Set.preimage_eq f L).symm

theorem pullAll_ofTotal : pullAll (ofTotal f) L = f ⁻¹' L := (Set.preimage_eq_core f L).symm

theorem outcomes_ofTotal : outcomes (ofTotal f) = detRun f := by
  funext a; ext b; simp [outcomes, eq_comm]

theorem ofTotal_comp {g : β → γ} : ofTotal (g ∘ f) = ofTotal f ○ ofTotal g :=
  Function.graph_comp g f

end Total

/-! ## Partial functions -/

section Partial

variable {f : α → Option β} {L : Set β} {a : α}

@[simp] theorem mem_ofPartial {b : β} : (a, b) ∈ ofPartial f ↔ f a = some b := Iff.rfl

theorem mem_pullSome_ofPartial : a ∈ pullSome (ofPartial f) L ↔ ∃ b, f a = some b ∧ b ∈ L := by
  simp [and_comm]

theorem mem_pullAll_ofPartial : a ∈ pullAll (ofPartial f) L ↔ ∀ b, f a = some b → b ∈ L := by
  simp

/-- `none` (no output) passes every universal pullback: it is never rejected. -/
theorem mem_pullAll_ofPartial_of_none (h : f a = none) : a ∈ pullAll (ofPartial f) L :=
  mem_pullAll_of_forall_not (by simp [h])

/-- `none` (no output) passes no existential pullback: it is never accepted. -/
theorem not_mem_pullSome_ofPartial_of_none (h : f a = none) : a ∉ pullSome (ofPartial f) L :=
  not_mem_pullSome_of_forall_not (by simp [h])

@[simp] theorem mem_pdom : a ∈ pdom f ↔ (f a).isSome := Iff.rfl

/-- Existential acceptance is universal acceptance on the domain. -/
theorem pullSome_ofPartial_eq : pullSome (ofPartial f) L = pdom f ∩ pullAll (ofPartial f) L := by
  ext a; cases h : f a <;> simp [h]

/-- Universal acceptance is existential acceptance or no output. -/
theorem pullAll_ofPartial_eq :
    pullAll (ofPartial f) L = (pdom f)ᶜ ∪ pullSome (ofPartial f) L := by
  ext a; cases h : f a <;> simp [h]

theorem ofPartial_partialComp {g : β → Option γ} :
    ofPartial (partialComp f g) = ofPartial f ○ ofPartial g := by
  ext ⟨a, c⟩; simp [partialComp, Option.bind_eq_some_iff]

/-- A total map is the partial function that always answers. -/
theorem ofPartial_some_comp {f : α → β} : ofPartial (some ∘ f) = ofTotal f := by
  ext ⟨a, b⟩; simp

theorem pdom_some_comp {f : α → β} : pdom (some ∘ f) = Set.univ := by ext; simp

/-- A checker for `L` composed with `Option.any` decides the existential pullback. -/
theorem Decides.optionAny {c : β → Bool} (hc : Decides c L) (f : α → Option β) :
    Decides (fun a => (f a).any c) (pullSome (ofPartial f) L) := fun a => by
  cases h : f a <;> simp [h, hc _]

/-- A checker for `L` composed with `Option.all` decides the universal pullback. -/
theorem Decides.optionAll {c : β → Bool} (hc : Decides c L) (f : α → Option β) :
    Decides (fun a => (f a).all c) (pullAll (ofPartial f) L) := fun a => by
  cases h : f a <;> simp [h, hc _]

end Partial

/-! ## Indexed value sets -/

section Indexed

variable {ι : Type u} {A : ι → Type v}

@[simp] theorem mem_eraseSigma {L : IndexedLang A} {p : Σ i, A i} :
    p ∈ eraseSigma L ↔ p.2 ∈ L p.1 := by simp [eraseSigma]

@[simp] theorem mem_fiberLang {M : Set (Σ i, A i)} {i : ι} {a : A i} :
    a ∈ fiberLang M i ↔ (⟨i, a⟩ : Σ i, A i) ∈ M := Iff.rfl

@[simp] theorem fiberLang_eraseSigma (L : IndexedLang A) : fiberLang (eraseSigma L) = L := by
  funext i; ext a; simp

@[simp] theorem eraseSigma_fiberLang (M : Set (Σ i, A i)) : eraseSigma (fiberLang M) = M := by
  ext ⟨i, a⟩; simp

theorem eraseSigma_subset_iff {L L' : IndexedLang A} :
    eraseSigma L ⊆ eraseSigma L' ↔ ∀ i, L i ⊆ L' i :=
  ⟨fun h i a ha => mem_eraseSigma.1 (h (a := ⟨i, a⟩) (mem_eraseSigma.2 ha)),
    fun h p hp => mem_eraseSigma.2 (h p.1 (mem_eraseSigma.1 hp))⟩

/-- Erasing the index into dependent pairs loses nothing: an order isomorphism. -/
def indexedLangIso : IndexedLang A ≃o Set (Σ i, A i) where
  toFun := eraseSigma
  invFun := fiberLang
  left_inv := fiberLang_eraseSigma
  right_inv := eraseSigma_fiberLang
  map_rel_iff' := eraseSigma_subset_iff

/-- Per-index checkers decide the erased language. -/
theorem Decides.sigma {L : IndexedLang A} {c : ∀ i, A i → Bool} (hc : ∀ i, Decides (c i) (L i)) :
    Decides (fun p => c p.1 p.2) (eraseSigma L) := fun p => (hc p.1 p.2).trans mem_eraseSigma.symm

/-- A checker on dependent pairs decides each fibre. -/
theorem Decides.fiber {M : Set (Σ i, A i)} {c : (Σ i, A i) → Bool} (hc : Decides c M) (i : ι) :
    Decides (fun a => c ⟨i, a⟩) (fiberLang M i) := fun a => hc ⟨i, a⟩

end Indexed

section Erase

variable {ι : Type u} {L L' : ι → Set α} {a : α}

@[simp] theorem mem_eraseSome : a ∈ eraseSome L ↔ ∃ i, a ∈ L i := Set.mem_iUnion

@[simp] theorem mem_eraseAll : a ∈ eraseAll L ↔ ∀ i, a ∈ L i := Set.mem_iInter

/-- Rejected by the existential erasure iff rejected at every index. -/
theorem not_mem_eraseSome : a ∉ eraseSome L ↔ ∀ i, a ∉ L i := by simp

/-- Rejected by the universal erasure iff rejected at some index. -/
theorem not_mem_eraseAll : a ∉ eraseAll L ↔ ∃ i, a ∉ L i := by simp

theorem compl_eraseSome : (eraseSome L)ᶜ = eraseAll fun i => (L i)ᶜ := by ext; simp

theorem compl_eraseAll : (eraseAll L)ᶜ = eraseSome fun i => (L i)ᶜ := by ext; simp

theorem eraseAll_subset_eraseSome [Nonempty ι] : eraseAll L ⊆ eraseSome L :=
  fun _ ha => mem_eraseSome.2 ⟨Classical.arbitrary ι, mem_eraseAll.1 ha _⟩

theorem subset_eraseSome (i : ι) : L i ⊆ eraseSome L := Set.subset_iUnion L i

theorem eraseAll_subset (i : ι) : eraseAll L ⊆ L i := Set.iInter_subset L i

theorem eraseSome_mono (h : ∀ i, L i ⊆ L' i) : eraseSome L ⊆ eraseSome L' := Set.iUnion_mono h

theorem eraseAll_mono (h : ∀ i, L i ⊆ L' i) : eraseAll L ⊆ eraseAll L' := Set.iInter_mono h

/-- Forgetting the index of a dependent pair (`Sigma.snd`) is existential erasure. -/
theorem image_snd_eraseSigma (L : ι → Set α) :
    Sigma.snd '' eraseSigma (A := fun _ => α) L = eraseSome L := by
  ext a; simp [eraseSome]

/-- Existential erasure is the existential pullback along the membership relation
`{(a, i) | a ∈ L i}`. -/
theorem eraseSome_eq_pullSome : eraseSome L = pullSome {p : α × ι | p.1 ∈ L p.2} Set.univ := by
  ext a; simp

end Erase

end Silmaril.Accept
