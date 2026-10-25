module

public import Silmaril.Logic.Metatheory.InferenceSystemCat.Properties

@[expose] public section

/-!
# Soundness and completeness against an inference system

A specification is another object of the category. An interpretation maps
conclusions into that object. Soundness preserves derivability; completeness
reflects it along the same interpretation. These are properties of provability,
not injectivity or surjectivity of proof maps.
-/

namespace Silmaril.Logic.Metatheory.InferenceSystemCat

open CategoryTheory

universe u v

/-- Every provable source conclusion is provable in the specification. -/
def Sound (S M : InferenceSystemCat.{u, v}) (interpret : S.Conclusion → M.Conclusion) : Prop :=
  ∀ a, S.Provable a → M.Provable (interpret a)

/-- Every represented conclusion provable in the specification is provable in the source. -/
def Complete (S M : InferenceSystemCat.{u, v}) (interpret : S.Conclusion → M.Conclusion) : Prop :=
  ∀ a, M.Provable (interpret a) → S.Provable a

theorem sound_and_complete_iff {S M : InferenceSystemCat.{u, v}}
    (interpret : S.Conclusion → M.Conclusion) :
    Sound S M interpret ∧ Complete S M interpret ↔
      ∀ a, S.Provable a ↔ M.Provable (interpret a) :=
  ⟨fun ⟨hs, hc⟩ a => ⟨hs a, hc a⟩, fun h => ⟨fun a => (h a).mp, fun a => (h a).mpr⟩⟩

theorem sound_of_morphism {S M : InferenceSystemCat.{u, v}} (f : S ⟶ M) :
    Sound S M f.map := fun _ => map_provable f

/-- Choice turns proof preservation into a map of the original derivation types.
The resulting morphism need not preserve distinctions between source proofs. -/
noncomputable def morphismOfSound {S M : InferenceSystemCat.{u, v}}
    (interpret : S.Conclusion → M.Conclusion) (sound : Sound S M interpret) : S ⟶ M where
  map := interpret
  mapDerivation {a} d := Classical.choice (sound a ⟨d⟩)

/-- Soundness is exactly existence of a morphism with the prescribed interpretation. -/
theorem sound_iff_morphism {S M : InferenceSystemCat.{u, v}}
    (interpret : S.Conclusion → M.Conclusion) :
    Sound S M interpret ↔ ∃ f : S ⟶ M, f.map = interpret := by
  constructor
  · exact fun h => ⟨morphismOfSound interpret h, rfl⟩
  · rintro ⟨f, rfl⟩
    exact sound_of_morphism f

/-- Completeness gives a lift of proofs at each interpreted source conclusion.
It does not assume that every conclusion of the specification is represented. -/
noncomputable def liftOfComplete {S M : InferenceSystemCat.{u, v}}
    (interpret : S.Conclusion → M.Conclusion) (complete : Complete S M interpret)
    (a : S.Conclusion) (d : M.Derivation (interpret a)) : S.Derivation a :=
  Classical.choice (complete a ⟨d⟩)

theorem complete_iff_lift {S M : InferenceSystemCat.{u, v}}
    (interpret : S.Conclusion → M.Conclusion) :
    Complete S M interpret ↔
      Nonempty (∀ a, M.Derivation (interpret a) → S.Derivation a) := by
  constructor
  · exact fun h => ⟨liftOfComplete interpret h⟩
  · rintro ⟨lift⟩ a ⟨d⟩
    exact ⟨lift a d⟩

theorem sound_id (S : InferenceSystemCat.{u, v}) : Sound S S id := fun _ h => h

theorem complete_id (S : InferenceSystemCat.{u, v}) : Complete S S id := fun _ h => h

theorem Sound.comp {S T M : InferenceSystemCat.{u, v}}
    {f : S.Conclusion → T.Conclusion} {g : T.Conclusion → M.Conclusion}
    (hg : Sound T M g) (hf : Sound S T f) : Sound S M (g ∘ f) :=
  fun a h => hg (f a) (hf a h)

theorem Complete.comp {S T M : InferenceSystemCat.{u, v}}
    {f : S.Conclusion → T.Conclusion} {g : T.Conclusion → M.Conclusion}
    (hg : Complete T M g) (hf : Complete S T f) : Complete S M (g ∘ f) :=
  fun a h => hf a (hg (f a) h)

end Silmaril.Logic.Metatheory.InferenceSystemCat
