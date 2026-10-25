module

public import Silmaril.Logic.Institution.Metatheory.Entailment
public import Silmaril.Logic.Institution.Metatheory.HOL.Semantics
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# HOL Light as a logic

The existing HOL Light kernel (`Silmaril.Logic.HOLLight.Derives`) and its standard model
semantics (`Silmaril.Logic.HOLLight.Model`, `HOLLight.Entails`) packaged as a logic in the sense
of Mossakowski–Diaconescu–Tarlecki: an institution `HOL.inst : HolSig ⥤ Room` together with an
entailment system on the same sentences. Nothing in `Silmaril.Logic.HOLLight` is changed; every
statement here is related to the original by name.

* **Signatures** `HolSig`: HOL signatures (`HOLLight.Signature`, lists of type-operator arities
  and constant schemes, addressed by position) ordered by *extension*: `Σ ≤ Σ'` when both lists
  of `Σ` are prefixes of those of `Σ'`. This is the signature-extension order of HOL Light's
  `new_type`/`new_constant`; the category is the preorder category.
* **Sentences** `HOL.Seq Σ`: well-typed sequents `H ⊢ p` (the conclusion and every hypothesis a
  term of type `bool` over `Σ`). Translation along an extension is the identity on syntax.
* **Models**: `HOLLight.Model Σ` (standard set-theoretic models with nonempty carriers in
  `Type u`, full function spaces and Hilbert choice), as a discrete category. The reduct along an
  extension forgets the extra constants (`Model.reduct`).
* **Satisfaction** `M ⊨ (H ⊢ p)` is `HOLLight.Entails M H p`: under every type valuation and
  free-variable valuation, if every hypothesis holds then so does the conclusion.
* **Derivability** `HOL.Derivable Σ Γ (H ⊢ p)`: either `H ⊢ p ∈ Γ`, or `HOLLight.Derives Σ T H p`
  for an object theory `T` whose members are the conclusions of hypothesis-free sequents of `Γ`.
  (HOL Light's kernel only takes closed theorems as axioms; sequents with hypotheses in `Γ` are
  inert, which keeps the relation Tarskian.)

Signatures, sequents and the syntactic lemmas are in `Metatheory.HOL.Syntax`; reducts of models
are in `Metatheory.HOL.Semantics`.

## Main statements

* `HOL.logic : LogicalSystem HolSig`.
* `HOL.sound_iff_derives_sound`: soundness of `HOL.logic` is *equivalent* to the statement of
  `HOLLight.Derives.sound` (for models in `Type u`).
* `HOL.logic_sound`: `HOL.logic` is sound, derived from `HOLLight.Derives.sound`.
-/

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory Silmaril.Logic.HOLLight

universe u

namespace HOL

/-- The room of a HOL signature: well-typed sequents, standard models and
`M ⊨ (H ⊢ p) ↔ HOLLight.Entails M H p`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.1, instantiated with the HOL Light semantics of `docs/projects/logic-hol.md`. -/
def room (S : HolSig) : Room.{0, u + 1, u + 1} where
  Sen := Seq S
  Mod := Cat.of (Discrete (Model.{u} S.sig))
  Sat M s := HOLLight.Entails (Discrete.as M) s.hyps s.concl

/-- The corridor of a signature extension: identity on sentences, reduct on models.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.4. -/
def corridor {S T : HolSig} (h : S ≤ T) : room.{u} S ⟶ room.{u} T where
  sen := Seq.map h
  mod := Discrete.functor fun M => Discrete.mk (Model.reduct h M)
  sat M s := entails_reduct_iff h (Discrete.as M) s

/-- HOL as an institution, `HolSig ⥤ Room`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.2; `goguen-burstall-1992` in `references.bib`, §2.5,
Definition 12. -/
def inst : HolSig ⥤ Room.{0, u + 1, u + 1} where
  obj := room
  map σ := corridor σ.le
  map_id _ := by
    apply Room.hom_ext
    · rfl
    · exact CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ =>
      Subsingleton.elim (h := Discrete.instSubsingletonDiscreteHom _ _) _ _
  map_comp _ _ := by
    apply Room.hom_ext
    · rfl
    · exact CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ =>
      Subsingleton.elim (h := Discrete.instSubsingletonDiscreteHom _ _) _ _

/-- HOL derivability: `H ⊢ p` is an assumption of `Γ`, or the kernel derives it from an object
theory made of conclusions of hypothesis-free members of `Γ`. -/
def Derivable (S : HolSig) (Γ : Set (Seq S)) (s : Seq S) : Prop :=
  s ∈ Γ ∨ ∃ theory : HOLLight.Theory,
    (∀ a ∈ theory, ∃ s' ∈ Γ, s'.hyps = ∅ ∧ s'.concl = a) ∧ Derives S.sig theory s.hyps s.concl

/-- HOL derivability is transitive (cut for axioms, `derives_cut_axioms`). -/
theorem derivable_trans (S : HolSig) {Γ Δ : Set (Seq S)} {ψ : Seq S}
    (hΔ : ∀ φ ∈ Δ, Derivable S Γ φ) (hψ : Derivable S (Γ ∪ Δ) ψ) : Derivable S Γ ψ := by
  rcases hψ with hm | ⟨T, hT, d⟩
  · exact hm.elim Or.inl (hΔ ψ)
  · right
    refine derives_cut_axioms (fun b => ∃ s' ∈ Γ, s'.hyps = ∅ ∧ s'.concl = b) d ?_
    intro a ha
    obtain ⟨s', hs', h0, hc⟩ := hT a ha
    have base : s' ∈ Γ → ∃ T' : HOLLight.Theory,
        (∀ b ∈ T', ∃ s' ∈ Γ, s'.hyps = ∅ ∧ s'.concl = b) ∧ Derives S.sig T' ∅ a := fun hg =>
      ⟨[a], fun b hb => by
        rw [List.mem_singleton] at hb
        exact ⟨s', hg, h0, hc.trans hb.symm⟩,
        Derives.axiom (List.mem_singleton_self a) (hc ▸ s'.typing)⟩
    rcases hs' with hg | hd
    · exact base hg
    · rcases hΔ s' hd with hg | ⟨T', hT', d'⟩
      · exact base hg
      · exact ⟨T', hT', h0 ▸ hc ▸ d'⟩

/-- HOL derivability is preserved by signature extension (`derives_of_le`). -/
theorem derivable_map {S T : HolSig} (h : S ≤ T) {Γ : Set (Seq S)} {s : Seq S}
    (hs : Derivable S Γ s) : Derivable T (Seq.map h '' Γ) (Seq.map h s) := by
  rcases hs with hm | ⟨th, hT, d⟩
  · exact Or.inl (Set.mem_image_of_mem _ hm)
  · refine Or.inr ⟨th, fun a ha => ?_, derives_of_le h d⟩
    obtain ⟨s', hs', h0, hc⟩ := hT a ha
    exact ⟨Seq.map h s', Set.mem_image_of_mem _ hs', h0, hc⟩

/-- HOL as a logic: the institution `HOL.inst` with the kernel's derivability.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2 (logics), and Definition 2.1 (entailment relations). -/
def logic : LogicalSystem.{0, 0, 0, u + 1, u + 1} HolSig where
  I := inst.{u}
  Derives := Derivable
  refl _ φ := Or.inl (Set.mem_singleton φ)
  mono := fun _ {_ _ _} h hd => hd.elim (fun hm => Or.inl (h hm))
    fun ⟨T, hT, d⟩ => Or.inr ⟨T, fun a ha => (hT a ha).imp fun _ hs => ⟨h hs.1, hs.2⟩, d⟩
  trans := fun S {_ _ _} hΔ hψ => derivable_trans S hΔ hψ
  map_derives := fun {_ _} σ {_ _} hs => derivable_map σ.le hs

/-- The statement of `HOLLight.Derives.sound` for models in `Type u`. -/
def DerivesSoundStatement : Prop :=
  ∀ {sig : Signature} {theory : HOLLight.Theory} {H : Hyps} {p : Tm},
    Derives sig theory H p → ∀ M : Model.{u} sig, Models M theory → HOLLight.Entails M H p

/-- `HOLLight.Derives.sound` proves its own statement. -/
theorem derivesSoundStatement : DerivesSoundStatement.{u} :=
  fun d M hM => Derives.sound d M hM

/-- **Soundness of HOL as a logic is the HOL Light soundness theorem.** The logic `HOL.logic`
is sound (`Γ ⊢ H ⊢ p` implies `Γ ⊨ H ⊢ p` at every signature) exactly when the statement of
`HOLLight.Derives.sound` holds.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2 ("a logic is required to be sound"); the original theorem is
`Silmaril.Logic.HOLLight.Derives.sound` (`docs/projects/logic-hol.md`). -/
theorem sound_iff_derives_sound : logic.{u}.Sound ↔ DerivesSoundStatement.{u} := by
  constructor
  · intro hS sig theory H p d M hM
    let S : HolSig := ⟨sig⟩
    have hty := derives_typed d
    let ρ : TypeValuation.{u} := fun _ => Carrier.unit
    let ν : FreeEnv M ρ := fun _ A => Classical.choice (inferInstance : Nonempty (Value M ρ A))
    have htheory : ∀ a ∈ theory, HasType sig [] a .bool := fun a ha => (hM a ha ρ ν).typing
    let Γ : Set (Seq S) := {s | s.hyps = ∅ ∧ s.concl ∈ theory}
    let s : Seq S := ⟨H, p, hty.1, hty.2⟩
    have hd : Derivable S Γ s :=
      Or.inr ⟨theory, fun a ha => ⟨Seq.closed a (htheory a ha), ⟨rfl, ha⟩, rfl, rfl⟩, d⟩
    refine hS S Γ s hd (Discrete.mk M) ?_
    rintro ψ ⟨h0, hψ⟩ ρ' ν' _
    exact hM _ hψ ρ' ν'
  · rintro hD S Γ φ (hm | ⟨T, hT, d⟩) M hM
    · exact hM φ hm
    · refine hD d (Discrete.as M) fun a ha ρ ν => ?_
      obtain ⟨s', hs', h0, hc⟩ := hT a ha
      have := hM s' hs'
      change HOLLight.Entails (Discrete.as M) s'.hyps s'.concl at this
      rw [h0, hc] at this
      exact this ρ ν (by simp [HypsTrue])

/-- HOL is a sound logic, derived from `HOLLight.Derives.sound`. -/
theorem logic_sound : logic.{u}.Sound := sound_iff_derives_sound.mpr derivesSoundStatement

end HOL

end Silmaril.Logic.Institution.Metatheory
