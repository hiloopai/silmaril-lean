module

public import Silmaril.Logic.Consequence.Semantic.Defs
public import Silmaril.Logic.Consequence.Translation.Thms

/-!
# Semantic consequence systems: laws

**SZS.** `entails_iff_thm` (current ontology) and `entails_iff_thm2007` (2007 text): `a ⊢ c` is
the THM status of `problem a c`. `not_entails_iff_csa`: a failed judgement is CounterSatisfiable.
`provesAll_of_cax`: a context without models proves everything (ContradictoryAxioms).
`cax_iff_provesFalse`: if `ff` has no models, proving `ff` is exactly CAX, so then bottom-relative
consistency is satisfiability of the context; without such an `ff` they can differ
(`provesAll_ne_cax_ex`).

**Order.** `entails_monoWrt`: entailment is monotone along any relation along which `satAx` is
antitone; this is a hypothesis, not automatic. `entails_mono_models`: fewer context models
(pointwise) means more consequences.

**Morphisms.** `Hom.toTranslation_id`, `Hom.toTranslation_comp`: morphisms of satisfactions give
translations functorially. `Hom.conservative_of_surjective`: if every source model is the image
of a target model the translation is conservative (borrowing).

**Rooms.** `roomSatisfaction_entails`: the entailment of a room is `Room.Entails`;
`corridorHom_toTranslation`: the translation of a corridor is `roomSys.map`.
-/

@[expose] public section

namespace Silmaril.Consequence

open CategoryTheory Silmaril.Logic

universe u v w u' v' w' u'' v'' w'' m₁ m₂

namespace Satisfaction

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'} {Ax'' : Type u''}
  {C'' : Type v''} (S : Satisfaction.{u, v, w} Ax C)

theorem entails_iff_thm (a : Ax) (c : C) : S.entails a c ↔ Szs.Current.THM (S.problem a c) :=
  ⟨fun h m hm => h m hm, fun h _ hm => h hm⟩

theorem entails_iff_thm2007 (a : Ax) (c : C) : S.entails a c ↔ Szs.V2007.THM (S.problem a c) :=
  ⟨fun h m hm => h m hm, fun h _ hm => h hm⟩

theorem not_entails_iff_csa (a : Ax) (c : C) :
    ¬ S.entails a c ↔ Szs.Current.CSA (S.problem a c) := by
  simp only [entails, not_forall, exists_prop, Szs.Current.CSA, problem]
  exact ⟨fun ⟨m, h₁, h₂⟩ => ⟨⟨m, h₁⟩, m, h₁, h₂⟩, fun ⟨_, m, h₁, h₂⟩ => ⟨m, h₁, h₂⟩⟩

theorem provesAll_of_cax {a : Ax} (h : ∀ c, Szs.Current.CAX (S.problem a c)) :
    S.entails.ProvesAll a := fun c m hm => absurd (Set.mem_empty_iff_false m |>.1 (h c ▸ hm)) id

theorem cax_iff_provesFalse {ff : C} (hff : ∀ m, ¬ S.satC m ff) (a : Ax) :
    Szs.Current.CAX (S.problem a ff) ↔ S.entails.ProvesFalse ff a := by
  simp [Szs.Current.CAX, problem, System.ProvesFalse, entails, Set.eq_empty_iff_forall_notMem, hff]

/-- Without a conclusion that has no models, a context can prove everything and still have
models: one model, one conclusion, satisfied. -/
theorem provesAll_ne_cax_ex :
    ∃ (S : Satisfaction.{0, 0, 0} Unit Unit), S.entails.ProvesAll () ∧
      ¬ Szs.Current.CAX (S.problem () ()) :=
  ⟨⟨Unit, fun _ _ => True, fun _ _ => True⟩, fun _ _ _ => trivial,
    fun h => (Set.mem_empty_iff_false ()).1 (h ▸ trivial)⟩

theorem entails_monoWrt {r : Ax → Ax → Prop} (h : ∀ a b m, r a b → S.satAx m b → S.satAx m a) :
    S.entails.MonoWrt r := fun _ _ hab _ hs m hm => hs m (h _ _ m hab hm)

theorem entails_mono_models {T : Satisfaction.{u, v, w} Ax C} (hM : T.Model = S.Model)
    (hAx : ∀ m a, T.satAx m a → S.satAx (cast hM m) a)
    (hC : ∀ m c, S.satC (cast hM m) c → T.satC m c) : S.entails ≤ T.entails :=
  fun a c h m hm => hC m c (h _ (hAx m a hm))

theorem Hom.toTranslation_id : (Hom.id S).toTranslation = Translation.id S.entails := rfl

theorem Hom.toTranslation_comp {T : Satisfaction.{u', v', w'} Ax' C'}
    {U : Satisfaction.{u'', v'', w''} Ax'' C''} (f : Hom S T) (g : Hom T U) :
    (f.comp g).toTranslation = f.toTranslation.comp g.toTranslation := rfl

theorem Hom.conservative_of_surjective {S : Satisfaction.{u, v, w} Ax C}
    {T : Satisfaction.{u', v', w'} Ax' C'} (f : Hom S T) (hf : Function.Surjective f.model) :
    f.toTranslation.Conservative := fun a φ h m hm => by
  obtain ⟨m', rfl⟩ := hf m
  exact (f.satC m' φ).1 (h m' ((f.satAx m' a).2 hm))

end Satisfaction

theorem roomSatisfaction_entails (R : Institution.Room.{w, m₁, m₂}) :
    (roomSatisfaction R).entails = R.Entails := rfl

theorem corridorHom_toTranslation {R₁ R₂ : Institution.Room.{w, m₁, m₂}}
    (f : Institution.Corridor R₁ R₂) : (corridorHom f).toTranslation = roomSys.map f := rfl

end Silmaril.Consequence
