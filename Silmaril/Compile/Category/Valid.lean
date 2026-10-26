module

public import Silmaril.Compile.Category.Convention

@[expose] public section

/-!
# Valid compilation relations

`Valid c p p'` says that the target program `p'` is a valid compilation of the source program
`p` at the convention `c`. It is defined from the behavioural institutions: `p'` has the
translated interface, and every specification `p` satisfies transports through `c`:

  `p ⊨ φ → p' ⊨' α_c φ`   for all `φ`.

Equivalently (`valid_iff_beh`, unconditionally) the target behaviours are realisations of source
behaviours, `beh p' ⊆ c.lift (beh p)` — CompCert's backward-simulation correctness statement
(`papers/compilers/leroy-2009-compcert-backend.pdf`, §2.1, Definition 2, p. 4: "C ⇓ B ⇒ S ⇓ B",
here up to the convention), and, for read-back conventions, reading `p'` back through the
comorphism yields a model of every specification of `p` (`valid_iff_readBack`).

## Main results

* `valid_id_iff`: at the identity convention, validity is behavioural refinement.
* `valid_mono`: validity is monotone in the convention order.
* `valid_comp_le` (**the lax law**): `Valid c ∘ Valid d ⊆ Valid (c ≫ d)`: composing valid
  compilations never produces invalid ones (it may lose some valid ones).
* `valid_comp_eq`: equality holds when the intermediate language realises every behaviour set.
* `valid_comp_ne`: a counterexample to equality (the intermediate language has no programs).
* `Valid.congr_source`, `Valid.congr_target`: validity is closed under semantic equivalence
  on either side; `compilations_eq_of_behEquiv` gives equality of compilation sets.
* `Valid.trans`, `Valid.replace_intermediate`: stepwise validation and replacement of an
  intermediate program by a semantically equivalent one.
-/

namespace Silmaril.Compile.Category

open CategoryTheory

universe u

variable {L L' L'' : Language.{u}}

/-- Valid compilation at a convention: interfaces match through `Φ` and every specification of
the source transports to the target through `α`. -/
def Valid (c : L ⟶ L') (p : L.Prog) (p' : L'.Prog) : Prop :=
  c.Φ (L.iface p) = L'.iface p' ∧ ∀ φ : Set L.Obs, L.Sat p φ → L'.Sat p' (c.lift φ)

/-- Validity is behaviour refinement through the convention. -/
theorem valid_iff_beh (c : L ⟶ L') (p : L.Prog) (p' : L'.Prog) :
    Valid c p p' ↔ c.Φ (L.iface p) = L'.iface p' ∧ L'.beh p' ⊆ c.lift (L.beh p) := by
  refine and_congr Iff.rfl ⟨fun h => h _ subset_rfl, fun h φ hp => ?_⟩
  intro o' ho'
  obtain ⟨o, ho, hR⟩ := h ho'
  exact ⟨o, hp ho, hR⟩

/-- For a read-back convention, validity says that the target program, read back through the
comorphism, is a model of the strongest specification of the source. -/
theorem valid_iff_readBack {c : L ⟶ L'} (h : Convention.ReadBack c) (p : L.Prog)
    (p' : L'.Prog) :
    Valid c p p' ↔ c.Φ (L.iface p) = L'.iface p' ∧ h.g '' L'.beh p' ⊆ L.beh p := by
  rw [valid_iff_beh]
  refine and_congr Iff.rfl ?_
  rw [Set.image_subset_iff]
  refine ⟨fun H o' ho' => ?_, fun H o' ho' => ⟨h.g o', H ho', (h.spec _ _).2 rfl⟩⟩
  obtain ⟨o, ho, hR⟩ := H ho'
  rw [h.spec] at hR
  exact Set.mem_preimage.2 (hR ▸ ho)

/-- Transport of specifications along a valid compilation. -/
theorem Valid.transport {c : L ⟶ L'} {p : L.Prog} {p' : L'.Prog} (h : Valid c p p')
    {φ : Set L.Obs} (hp : L.Sat p φ) : L'.Sat p' (c.lift φ) :=
  h.2 φ hp

/-- At the identity convention, validity is behavioural refinement. -/
theorem valid_id_iff (p q : L.Prog) : Valid (𝟙 L) p q ↔ L.Refines p q := by
  rw [valid_iff_beh]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁.symm, fun o ho => ?_⟩, fun ⟨h₁, h₂⟩ => ⟨h₁.symm, fun o ho => ⟨o, h₂ ho, rfl⟩⟩⟩
  obtain ⟨o', ho', rfl⟩ := h₂ ho
  exact ho'

/-- `Valid (𝟙 L)` is a preorder: reflexive. -/
theorem valid_id_refl (p : L.Prog) : Valid (𝟙 L) p p := by
  exact (valid_id_iff p p).2 (L.refines_refl p)

/-- `Valid (𝟙 L)` is a preorder: transitive. -/
theorem valid_id_trans {p q r : L.Prog} (h₁ : Valid (𝟙 L) p q) (h₂ : Valid (𝟙 L) q r) :
    Valid (𝟙 L) p r := by
  exact (valid_id_iff p r).2
    (L.refines_trans ((valid_id_iff p q).1 h₁) ((valid_id_iff q r).1 h₂))

/-- Validity is monotone in the convention order. -/
theorem valid_mono {c d : L ⟶ L'} (h : c ≤ d) : Valid c ≤ Valid d := by
  rw [Convention.hom_le_def] at h
  intro p p' hv
  rw [valid_iff_beh] at hv ⊢
  refine ⟨by rw [← h.1]; exact hv.1, fun o' ho' => ?_⟩
  obtain ⟨o, ho, hR⟩ := hv.2 ho'
  exact ⟨o, ho, h.2 _ _ hR⟩

/-- **The lax law.** The composite of valid compilation relations is contained in the valid
relation of the composite convention. -/
theorem valid_comp_le (c : L ⟶ L') (d : L' ⟶ L'') :
    Relation.Comp (Valid c) (Valid d) ≤ Valid (c ≫ d) := by
  rintro p r ⟨q, h₁, h₂⟩
  rw [valid_iff_beh] at h₁ h₂ ⊢
  refine ⟨by simp only [Convention.comp_Φ, Function.comp_apply, h₁.1, h₂.1], fun o'' ho'' => ?_⟩
  obtain ⟨o', ho', hd⟩ := h₂.2 ho''
  obtain ⟨o, ho, hc⟩ := h₁.2 ho'
  exact ⟨o, ho, o', hc, hd⟩

/-- A language realises every behaviour set at every interface. -/
def Language.Realisable (L : Language.{u}) : Prop :=
  ∀ (S : L.Iface) (B : Set L.Obs), ∃ p, L.iface p = S ∧ L.beh p = B

/-- The lax law is an equality when the intermediate language is realisable. -/
theorem valid_comp_eq (c : L ⟶ L') (d : L' ⟶ L'') (h : L'.Realisable) :
    Relation.Comp (Valid c) (Valid d) = Valid (c ≫ d) := by
  refine le_antisymm (valid_comp_le c d) ?_
  intro p r hv
  rw [valid_iff_beh] at hv
  obtain ⟨q, hq, hb⟩ := h (c.Φ (L.iface p)) (c.lift (L.beh p))
  refine ⟨q, (valid_iff_beh c p q).2 ⟨hq.symm, hb.subset⟩,
    (valid_iff_beh d q r).2 ⟨?_, ?_⟩⟩
  · rw [hq]; exact hv.1
  · intro o'' ho''
    obtain ⟨o, ho, o', hc, hd⟩ := hv.2 ho''
    exact ⟨o', by rw [hb]; exact ⟨o, ho, hc⟩, hd⟩

/-- The one-program language: one interface, one program, every observation. -/
def unitLang : Language.{0} := ⟨Unit, Unit, fun _ => (), Unit, fun _ => Set.univ⟩

/-- The language without programs. -/
def emptyLang : Language.{0} := ⟨Unit, Empty, fun e => e.elim, Unit, fun e => e.elim⟩

/-- The total convention between `unitLang` and `emptyLang`. -/
def unitToEmpty : unitLang ⟶ emptyLang := Convention.mk (fun _ => ()) fun _ _ => True

/-- The total convention between `emptyLang` and `unitLang`. -/
def emptyToUnit : emptyLang ⟶ unitLang := Convention.mk (fun _ => ()) fun _ _ => True

/-- The lax law is strict in general: compiling the unit program to itself is valid at the
composite convention, but there is no intermediate program in `emptyLang`. -/
theorem valid_comp_ne :
    Relation.Comp (Valid unitToEmpty) (Valid emptyToUnit) ≠ Valid (unitToEmpty ≫ emptyToUnit) := by
  intro h
  have hv : Valid (unitToEmpty ≫ emptyToUnit) () () :=
    (valid_iff_beh _ () ()).2 ⟨rfl, fun _ _ => ⟨(), trivial, (), trivial, trivial⟩⟩
  rw [← h] at hv
  obtain ⟨q, _, _⟩ := hv
  cases q

/-! ## Semantic equivalence and stepwise validation

These rules use the existing interface-aware semantic relations. They do not assert that a
particular frontend, intermediate representation or machine-code validator is adequate.
Observations may include an initial input, a return value and a trace; selecting only successful
answers gives completed-answer partial correctness, while including prefixes gives a stronger
safety obligation. An empty behaviour set is permitted in either case.
-/

namespace Language.BehEquiv

theorem refl (p : L.Prog) : L.BehEquiv p p :=
  ⟨L.refines_refl p, L.refines_refl p⟩

theorem symm {p q : L.Prog} (h : L.BehEquiv p q) : L.BehEquiv q p := ⟨h.2, h.1⟩

theorem trans {p q r : L.Prog} (h : L.BehEquiv p q) (h' : L.BehEquiv q r) :
    L.BehEquiv p r := ⟨L.refines_trans h.1 h'.1, L.refines_trans h'.2 h.2⟩

end Language.BehEquiv

/-- Behavioural equivalence is an equivalence relation, independently of target expressiveness. -/
theorem Language.behEquiv_equivalence (L : Language.{u}) : Equivalence L.BehEquiv :=
  ⟨Language.BehEquiv.refl, Language.BehEquiv.symm, Language.BehEquiv.trans⟩

/-- The semantic quotient of programs retains the interface as well as the observations. -/
def Language.behSetoid (L : Language.{u}) : Setoid L.Prog :=
  ⟨L.BehEquiv, L.behEquiv_equivalence⟩

namespace Valid

variable {c : L ⟶ L'} {d : L' ⟶ L''}
  {p p' : L.Prog} {q q' : L'.Prog} {r : L''.Prog}

/-- A semantically equivalent source admits every compilation of the original source. -/
theorem congr_source (h : Valid c p q) (he : L.BehEquiv p p') : Valid c p' q := by
  rw [valid_iff_beh] at h ⊢
  obtain ⟨hi, hb⟩ := (L.behEquiv_iff _ _).mp he
  simpa only [← hi, ← hb] using h

/-- Every semantically equivalent target is also a valid compilation. -/
theorem congr_target (h : Valid c p q) (he : L'.BehEquiv q q') : Valid c p q' := by
  rw [valid_iff_beh] at h ⊢
  obtain ⟨hi, hb⟩ := (L'.behEquiv_iff _ _).mp he
  simpa only [← hi, ← hb] using h

theorem source_iff (he : L.BehEquiv p p') : Valid c p q ↔ Valid c p' q :=
  ⟨fun h => h.congr_source he, fun h => h.congr_source he.symm⟩

theorem target_iff (he : L'.BehEquiv q q') : Valid c p q ↔ Valid c p q' :=
  ⟨fun h => h.congr_target he, fun h => h.congr_target he.symm⟩

theorem congr (hs : L.BehEquiv p p') (ht : L'.BehEquiv q q') :
    Valid c p q ↔ Valid c p' q' := (source_iff hs).trans (target_iff ht)

/-- Target refinement also preserves compilation validity; equality is unnecessary. -/
theorem target_refines (h : Valid c p q) (hr : L'.Refines q q') : Valid c p q' := by
  rw [valid_iff_beh] at h ⊢
  exact ⟨h.1.trans hr.1.symm, hr.2.trans h.2⟩

/-- A source that permits more behaviours admits every previously valid compilation. -/
theorem source_weaken (h : Valid c p q) (hr : L.Refines p' p) : Valid c p' q := by
  rw [valid_iff_beh] at h ⊢
  exact ⟨by rw [← hr.1]; exact h.1, h.2.trans (c.lift_mono hr.2)⟩

/-- Vertical composition: e.g. Core → MiniC and MiniC → x86 imply Core → x86. -/
theorem trans (h : Valid c p q) (h' : Valid d q r) : Valid (c ≫ d) p r :=
  valid_comp_le c d p r ⟨q, h, h'⟩

/-- The two validators may use different, semantically equivalent intermediate programs. -/
theorem replace_intermediate (h : Valid c p q) (he : L'.BehEquiv q q')
    (h' : Valid d q' r) : Valid (c ≫ d) p r :=
  (h.congr_target he).trans h'

end Valid

/-- The full set of valid target programs, at a fixed convention. -/
def compilations (c : L ⟶ L') (p : L.Prog) : Set L'.Prog := {q | Valid c p q}

/-- Equivalent sources have exactly the same compilation possibilities. -/
theorem compilations_eq_of_behEquiv (c : L ⟶ L') {p p' : L.Prog}
    (h : L.BehEquiv p p') : compilations c p = compilations c p' := by
  ext q
  exact Valid.source_iff h

/-- A target language can probe each observation independently at every interface. This is
weaker than `Realisable`, which requires every behaviour set, not just singletons. -/
def Language.SingletonRealisable (L : Language.{u}) : Prop :=
  ∀ (S : L.Iface) (o : L.Obs), ∃ p, L.iface p = S ∧ L.beh p = {o}

/-- Under singleton expressiveness, equal compilation sets recover exactly the translated
source behaviours (at matching translated interfaces). Without that assumption the converse
can fail; even with it, a convention that hides observations need not recover source equality. -/
theorem compilations_eq_iff_lift_eq (c : L ⟶ L') (complete : L'.SingletonRealisable)
    {p p' : L.Prog} (hi : c.Φ (L.iface p) = c.Φ (L.iface p')) :
    compilations c p = compilations c p' ↔ c.lift (L.beh p) = c.lift (L.beh p') := by
  constructor
  · intro he
    apply Set.Subset.antisymm
    all_goals
      intro o ho
      obtain ⟨q, hq, hb⟩ := complete (c.Φ (L.iface p)) o
      have hsingle : L'.beh q ⊆ {o} := hb.subset
      have hmem : o ∈ L'.beh q := hb.symm ▸ Set.mem_singleton o
      first
      | have hv : q ∈ compilations c p :=
          (valid_iff_beh _ _ _).mpr ⟨hq.symm, fun x hx =>
            (Set.mem_singleton_iff.mp (hsingle hx)) ▸ ho⟩
        rw [he] at hv
        exact ((valid_iff_beh _ _ _).mp hv).2 hmem
      | have hv : q ∈ compilations c p' :=
          (valid_iff_beh _ _ _).mpr ⟨hi.symm.trans hq.symm, fun x hx =>
            (Set.mem_singleton_iff.mp (hsingle hx)) ▸ ho⟩
        rw [← he] at hv
        exact ((valid_iff_beh _ _ _).mp hv).2 hmem
  · intro hb
    ext q
    simp only [compilations, Set.mem_ofPred_eq, valid_iff_beh, hi, hb]

/-- In a language with singleton implementations, identity-convention compilation sets
determine semantic equivalence. Thus an unconditional strict non-converse would be false. -/
theorem compilations_id_eq_iff (complete : L.SingletonRealisable) {p p' : L.Prog}
    (hi : L.iface p = L.iface p') :
    compilations (𝟙 L) p = compilations (𝟙 L) p' ↔ L.BehEquiv p p' := by
  rw [compilations_eq_iff_lift_eq (𝟙 L) complete hi, Convention.lift_id,
    Convention.lift_id, L.behEquiv_iff]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

end Silmaril.Compile.Category
