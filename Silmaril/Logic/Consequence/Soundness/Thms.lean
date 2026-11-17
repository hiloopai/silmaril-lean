module

public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.Concrete.Codec.Thms
public import Silmaril.Logic.Consequence.Thms

/-!
# Interpretation, soundness and consistency: the bridges

* `consistentWrt_of_sound`: soundness for an interpretation, plus a model of the context in which
  `ff` fails, gives syntactic consistency. `contextConsistent_of_sound`: likewise for
  nontriviality, with any conclusion false in the model.
* `ER.consistentWrt_of_sound`: the same for an entailment relation sound for a room.
* `consistentWrt_of_translation`: consistency transports backwards along a translation.
* `viaCodec_iff`, `viaCodec_consistentWrt_iff`, `viaCodec_soundFor`: over a concrete
  presentation, consequence, consistency and soundness are those of the abstract system.
-/

@[expose] public section

namespace Silmaril.Consequence

open Silmaril.Logic Silmaril.Logic.Institution Silmaril.Logic.Concrete

universe u v w u' v'

variable {Ax : Type u} {C : Type v}

/-- **Consistency from a model.** -/
theorem consistentWrt_of_sound {S : System Ax C} {I : Satisfaction.{u, v, w} Ax C}
    (hS : S.SoundFor I) {a : Ax} {ff : C} (m : I.Model) (hm : I.satAx m a) (hff : ¬ I.satC m ff) :
    S.ConsistentWrt ff a :=
  fun h => hff (hS a ff h m hm)

/-- **Nontriviality from a model.** -/
theorem contextConsistent_of_sound {S : System Ax C} {I : Satisfaction.{u, v, w} Ax C}
    (hS : S.SoundFor I) {a : Ax} {c : C} (m : I.Model) (hm : I.satAx m a) (hc : ¬ I.satC m c) :
    S.ContextConsistent a :=
  fun h => hc (hS a c (h c) m hm)

/-- Consistency of an entailment relation sound for a room, from a model of `Γ` falsifying `ff`. -/
theorem ER.consistentWrt_of_sound {R : Room} {D : Set R.Sen → R.Sen → Prop} (h : R.IsSound D)
    {Γ : Set R.Sen} {ff : R.Sen} (M : R.Mod) (hM : ∀ φ ∈ Γ, R.Sat M φ) (hff : ¬ R.Sat M ff) :
    ¬ D Γ ff :=
  fun d => hff (h Γ ff d M hM)

/-- **Consistency transports backwards along a translation.** -/
theorem consistentWrt_of_translation {Ax' : Type u'} {C' : Type v'} {S : System Ax C}
    {T : System Ax' C'} (t : Translation S T) {a : Ax} {ff : C}
    (h : T.ConsistentWrt (t.c ff) (t.ax a)) : S.ConsistentWrt ff a :=
  fun d => h (t.sound a ff d)

section Codec

variable {A : Type u} (S : System (List A) A) (c : SExpCodec A)

theorem viaCodec_iff (Γ : List A) (φ : A) :
    S.viaCodec c (Γ.map SExpCodec.Sen.ofAbs) (SExpCodec.Sen.ofAbs φ) ↔ S Γ φ := by
  simp only [System.viaCodec, System.pullback_apply, SExpCodec.Sen.map_toAbs_ofAbs,
    SExpCodec.Sen.toAbs_ofAbs]

/-- Over a concrete presentation, consistency is the abstract system's. -/
theorem viaCodec_consistentWrt_iff (Γ : List A) (ff : A) :
    (S.viaCodec c).ConsistentWrt (SExpCodec.Sen.ofAbs ff) (Γ.map SExpCodec.Sen.ofAbs) ↔
      S.ConsistentWrt ff Γ :=
  not_congr (viaCodec_iff S c Γ ff)

/-- A system below another stays below it over a presentation. -/
theorem viaCodec_mono {S T : System (List A) A} (h : S ≤ T) : S.viaCodec c ≤ T.viaCodec c :=
  System.pullback_mono _ _ h

end Codec

end Silmaril.Consequence
