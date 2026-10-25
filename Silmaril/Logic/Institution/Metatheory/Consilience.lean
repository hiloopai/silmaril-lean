module

public import Silmaril.Logic.Institution.Metatheory.HOL
public import Silmaril.Logic.HOLLight.Consilience.Semantics

@[expose] public section

/-!
# The independent HOL presentation as a logic, and its comorphism into HOL Light

`Silmaril.Logic.HOLLight.Consilience` is a second, independent presentation of HOL: its own
term syntax (`Consilience.Term`), typing (`Consilience.Typed`), proof trees
(`Consilience.Proof`) and denotation (`Consilience.Denotes`), over the same signatures and the
same models as the HOL Light kernel. Its correspondence with the kernel is
`Consilience.Proof.encode_iff` (provability) and `Consilience.entails_encode_iff` (semantics).

Here the independent presentation is the logic `HOLConsilience.logic : LogicalSystem HolSig`, and the
correspondence is the logic comorphism `HOLConsilience.toHOL : HOLConsilience.logic → HOL.logic`:

* the signature functor is the identity;
* sentences are encoded (`Consilience.Term.encode`, `Consilience.encodeContext`);
* models are unchanged (the model translation is the identity functor), so the comorphism is
  model-expansive and preserves and reflects semantic entailment;
* the satisfaction condition is `Consilience.entails_encode_iff`;
* derivability is preserved and reflected (`toHOL_conservative`), derived from
  `Consilience.Proof.encode_iff`.

Soundness of the independent presentation is then borrowed from HOL Light
(`HOLConsilience.logic_sound`), and is equivalent to the statement of `Consilience.Proof.sound`
(`HOLConsilience.sound_iff_proof_sound`).
-/

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory Silmaril.Logic.HOLLight

universe u

namespace HOLConsilience

/-- Any two morphisms of a discrete category are equal. -/
theorem discreteHom_eq {α : Type*} {X Y : Discrete α} (f g : X ⟶ Y) : f = g :=
  Subsingleton.elim f g

/-- A well-typed sequent of the independent presentation over the signature `S`. -/
@[ext]
structure Seq (S : HolSig) where
  /-- The hypotheses. -/
  hyps : Consilience.Context
  /-- The conclusion. -/
  concl : Consilience.Term
  typing : Consilience.Typed S.sig [] concl .bool
  typedHyps : ∀ p ∈ hyps, Consilience.Typed S.sig [] p .bool

/-- Encoding a sequent into the kernel syntax. -/
def Seq.encode {S : HolSig} (s : Seq S) : HOL.Seq S where
  hyps := Consilience.encodeContext s.hyps
  concl := s.concl.encode
  typing := Consilience.Typed.encode s.typing
  typedHyps p hp := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Consilience.Typed.encode (s.typedHyps q hq)

/-- Translation along a signature extension: the identity on syntax. -/
def Seq.map {S T : HolSig} (h : S ≤ T) (s : Seq S) : Seq T where
  hyps := s.hyps
  concl := s.concl
  typing := Consilience.Typed.encode_iff.mp (HOL.hasType_of_le h (Consilience.Typed.encode s.typing))
  typedHyps p hp :=
    Consilience.Typed.encode_iff.mp (HOL.hasType_of_le h (Consilience.Typed.encode (s.typedHyps p hp)))

/-- The room of a signature in the independent presentation: its sequents, the standard models
and `M ⊨ (H ⊢ p) ↔ Consilience.Entails M H p`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.1. -/
def room (S : HolSig) : Room.{0, u + 1, u + 1} where
  Sen := Seq S
  Mod := Cat.of (Discrete (Model.{u} S.sig))
  Sat M s := Consilience.Entails (Discrete.as M) s.hyps s.concl

/-- The corridor of a signature extension.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.4. -/
def corridor {S T : HolSig} (h : S ≤ T) : room.{u} S ⟶ room.{u} T where
  sen := Seq.map h
  mod := Discrete.functor fun M => Discrete.mk (HOL.Model.reduct h M)
  sat M s := by
    exact Consilience.entails_encode_iff.symm.trans
      ((HOL.entails_reduct_iff h (Discrete.as M) s.encode).trans Consilience.entails_encode_iff)

/-- The independent presentation as an institution.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
Definition 4.2. -/
def inst : HolSig ⥤ Room.{0, u + 1, u + 1} where
  obj := room
  map σ := corridor σ.le
  map_id _ := Room.hom_ext (funext fun _ => Seq.ext rfl rfl)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => discreteHom_eq _ _))
  map_comp _ _ := Room.hom_ext (funext fun _ => Seq.ext rfl rfl)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => discreteHom_eq _ _))

/-- Encoding of sequents is injective (`Consilience.decode_encodeContext`,
`Consilience.Term.encode_injective`). -/
theorem Seq.encode_injective {S : HolSig} : Function.Injective (Seq.encode (S := S)) := by
  intro s t h
  have h₁ : Consilience.encodeContext s.hyps = Consilience.encodeContext t.hyps :=
    congrArg HOL.Seq.hyps h
  have h₂ : s.concl.encode = t.concl.encode := congrArg HOL.Seq.concl h
  exact Seq.ext (by simpa using congrArg Consilience.decodeContext h₁)
    (Consilience.Term.encode_injective h₂)

/-- Encoding commutes with translation along signature extensions. -/
theorem Seq.encode_map {S T : HolSig} (h : S ≤ T) (s : Seq S) :
    (Seq.map h s).encode = HOL.Seq.map h s.encode :=
  HOL.Seq.ext rfl rfl

/-- Derivability in the independent presentation, shaped like `HOL.Derivable`: an assumption,
or a `Consilience.Proof` from conclusions of hypothesis-free members of `Γ`. -/
def Derivable (S : HolSig) (Γ : Set (Seq S)) (s : Seq S) : Prop :=
  s ∈ Γ ∨ ∃ theory : Consilience.Theory,
    (∀ a ∈ theory, ∃ s' ∈ Γ, s'.hyps = ∅ ∧ s'.concl = a) ∧
      Nonempty (Consilience.Proof S.sig theory s.hyps s.concl)

/-- **Derivability is preserved and reflected by encoding.** Derived from
`Consilience.Proof.encode_iff` (and `Consilience.Proof.decode`).

Source: the provability equivalence `Silmaril.Logic.HOLLight.Consilience.Proof.encode_iff`
(`docs/projects/logic-hol.md`); conservativity in the sense of
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §2,
Definition 2.3. -/
theorem derivable_encode_iff (S : HolSig) (Γ : Set (Seq S)) (s : Seq S) :
    Derivable S Γ s ↔ HOL.Derivable S (Seq.encode '' Γ) s.encode := by
  unfold Derivable HOL.Derivable
  refine or_congr Seq.encode_injective.mem_set_image.symm ⟨?_, ?_⟩
  · rintro ⟨T, hT, ⟨d⟩⟩
    refine ⟨Consilience.encodeTheory T, fun a ha => ?_, d.encode⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨s', hs', h₀, rfl⟩ := hT b hb
    refine ⟨s'.encode, ⟨s', hs', rfl⟩, ?_, rfl⟩
    show Consilience.encodeContext s'.hyps = ∅
    rw [h₀]
    exact Consilience.encodeContext_empty
  · rintro ⟨T, hT, d⟩
    refine ⟨Consilience.decodeTheory T, fun a ha => ?_, ?_⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      obtain ⟨_, ⟨s', hs', rfl⟩, h₀, h₁⟩ := hT b hb
      refine ⟨s', hs', ?_, ?_⟩
      · have h₀' : Consilience.encodeContext s'.hyps = ∅ := h₀
        simpa using congrArg Consilience.decodeContext h₀'
      · have h₁' : s'.concl.encode = b := h₁
        rw [← h₁', Consilience.Term.decode_encode]
    · exact Consilience.Proof.encode_iff.mp (by rw [Consilience.encode_decodeTheory]; exact d)

theorem derivable_trans (S : HolSig) {Γ Δ : Set (Seq S)} {ψ : Seq S}
    (hΔ : ∀ φ ∈ Δ, Derivable S Γ φ) (hψ : Derivable S (Γ ∪ Δ) ψ) : Derivable S Γ ψ := by
  rw [derivable_encode_iff] at hψ ⊢
  rw [Set.image_union] at hψ
  refine HOL.derivable_trans S (Δ := Seq.encode '' Δ) ?_ hψ
  rintro _ ⟨φ, hφ, rfl⟩
  exact (derivable_encode_iff S Γ φ).mp (hΔ φ hφ)

theorem derivable_map {S T : HolSig} (h : S ≤ T) {Γ : Set (Seq S)} {s : Seq S}
    (hs : Derivable S Γ s) : Derivable T (Seq.map h '' Γ) (Seq.map h s) := by
  have hT := HOL.derivable_map h ((derivable_encode_iff S Γ s).mp hs)
  rw [Set.image_image] at hT
  rw [derivable_encode_iff, Set.image_image, Seq.encode_map]
  simpa only [Seq.encode_map] using hT

/-- The independent presentation as a logic.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2. -/
def logic : LogicalSystem.{0, 0, 0, u + 1, u + 1} HolSig where
  I := inst.{u}
  Derives := Derivable
  refl _ φ := Or.inl (Set.mem_singleton φ)
  mono := fun _ {_ _ _} h hd => hd.elim (fun hm => Or.inl (h hm))
    fun ⟨T, hT, d⟩ => Or.inr ⟨T, fun a ha => (hT a ha).imp fun _ hs => ⟨h hs.1, hs.2⟩, d⟩
  trans := fun S {_ _ _} hΔ hψ => derivable_trans S hΔ hψ
  map_derives := fun {_ _} σ {_ _} hs => derivable_map σ.le hs

/-- The corridor `encode` at a signature: sentences encoded, models unchanged; its satisfaction
condition is `Consilience.entails_encode_iff`.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.4. -/
def encodeCorridor (S : HolSig) : room.{u} S ⟶ HOL.room.{u} S where
  sen := Seq.encode
  mod := 𝟭 _
  sat _ _ := Consilience.entails_encode_iff

/-- **The HOL presentation correspondence as a logic comorphism** `HOLConsilience.logic →
HOL.logic`: identity on signatures and models, encoding on sentences.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4.1,
Definition 4.3 and the paragraph after it (logic comorphisms). -/
def toHOL : LogicalSystem.CoHom logic.{u} HOL.logic.{u} where
  Φ := 𝟭 HolSig
  ρ :=
    { app := encodeCorridor
      naturality := fun _ _ _ => Room.hom_ext (funext fun _ => HOL.Seq.ext rfl rfl)
        (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => discreteHom_eq _ _)) }
  map_derives S Γ φ h := (derivable_encode_iff S Γ φ).mp h

/-- The comorphism reflects derivability. -/
theorem toHOL_conservative : toHOL.{u}.Conservative :=
  fun S Γ φ h => (derivable_encode_iff S Γ φ).mpr h

/-- The comorphism is model-expansive: its model translations are identities. -/
theorem toHOL_modelExpansive : toHOL.{u}.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Semantic entailment is preserved and reflected by encoding (borrowing).

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7. -/
theorem entails_encode_iff (S : HolSig) (Γ : Set (Seq S)) (s : Seq S) :
    (room.{u} S).Entails Γ s ↔ (HOL.room.{u} S).Entails (Seq.encode '' Γ) s.encode :=
  Corridor.entails_map_iff (encodeCorridor S) (toHOL_modelExpansive S) Γ s

/-- The independent presentation is sound, borrowed from `HOL.logic_sound` along `toHOL`. -/
theorem logic_sound : logic.{u}.Sound :=
  toHOL.sound_of_sound toHOL_modelExpansive HOL.logic_sound

/-- The statement of `Consilience.Proof.sound` for models in `Type u`. -/
def ProofSoundStatement : Prop :=
  ∀ {sig : Signature} {T : Consilience.Theory} {H : Consilience.Context} {p : Consilience.Term},
    Consilience.Proof sig T H p → ∀ M : Model.{u} sig, Consilience.Models M T →
      Consilience.Entails M H p

/-- Decoding a kernel sequent into the independent presentation. -/
def Seq.decode {S : HolSig} (s : HOL.Seq S) : Seq S where
  hyps := Consilience.decodeContext s.hyps
  concl := Consilience.Term.decode s.concl
  typing := Consilience.Typed.decode s.typing
  typedHyps p hp := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact Consilience.Typed.decode (s.typedHyps q hq)

@[simp] theorem Seq.encode_decode {S : HolSig} (s : HOL.Seq S) : (Seq.decode s).encode = s :=
  HOL.Seq.ext (Consilience.encode_decodeContext _) (Consilience.Term.encode_decode _)

/-- Soundness of the independent presentation is equivalent to soundness of `HOL.logic`: the
comorphism `toHOL` is conservative, model-expansive and surjective on sentences up to
`Seq.decode`. -/
theorem logic_sound_iff_hol_sound : logic.{u}.Sound ↔ HOL.logic.{u}.Sound := by
  refine ⟨fun hs S (Γ : Set (HOL.Seq S)) (φ : HOL.Seq S) hd => ?_, toHOL.sound_of_sound toHOL_modelExpansive⟩
  have hΓ : Seq.encode '' (Seq.decode '' Γ) = Γ := by
    rw [Set.image_image]
    simp
  rw [← hΓ, ← Seq.encode_decode φ] at hd ⊢
  exact (entails_encode_iff S _ _).mp (hs S _ _ ((derivable_encode_iff S _ _).mpr hd))

/-- The statements of `HOLLight.Derives.sound` and `Consilience.Proof.sound` are equivalent,
through `Consilience.Proof.encode`, `Consilience.Proof.decode` and the semantic bridges
`Consilience.models_encode_iff`, `Consilience.entails_encode_iff`. -/
theorem derivesSoundStatement_iff_proofSoundStatement :
    HOL.DerivesSoundStatement.{u} ↔ ProofSoundStatement.{u} := by
  refine ⟨fun hD _ _ _ _ pr M hM =>
    Consilience.entails_encode_iff.mp (hD pr.encode M (Consilience.models_encode_iff.mpr hM)),
    fun hP _ _ _ _ d M hM => ?_⟩
  obtain ⟨pr⟩ := Consilience.Proof.decode d
  have hE := Consilience.entails_encode_iff.mpr (hP pr M
    (Consilience.models_encode_iff.mp (by rw [Consilience.encode_decodeTheory]; exact hM)))
  simpa using hE

/-- `Consilience.Proof.sound` proves its own statement. -/
theorem proofSoundStatement : ProofSoundStatement.{u} :=
  fun h M hM => Consilience.Proof.sound h M hM

/-- **Soundness of the independent presentation as a logic is `Consilience.Proof.sound`.**

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §4,
the paragraph after Definition 4.2; the original theorem is
`Silmaril.Logic.HOLLight.Consilience.Proof.sound` (`docs/projects/logic-hol.md`). -/
theorem sound_iff_proof_sound : logic.{u}.Sound ↔ ProofSoundStatement.{u} :=
  logic_sound_iff_hol_sound.trans
    (HOL.sound_iff_derives_sound.trans derivesSoundStatement_iff_proofSoundStatement)

end HOLConsilience

end Silmaril.Logic.Institution.Metatheory
