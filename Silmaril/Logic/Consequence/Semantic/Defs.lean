module

public import Silmaril.Logic.Consequence.Translation.Defs
public import Silmaril.Logic.Institution.Room
public import Silmaril.Logic.Szs.Defs

/-!
# Semantic consequence systems: satisfaction, rooms, SZS

A `Satisfaction Ax C` has its own type of models and two **independent** satisfaction
relations, one for contexts (`satAx m a`) and one for conclusions (`satC m c`). Contexts need
not be sets of conclusions, so nothing relates the two relations unless a hypothesis says so.
Its *entailment* is the consequence system

  `entails a c := ∀ m, satAx m a → satC m c`.

* `Satisfaction.problem a c`: the judgement as an SZS problem over the models
  (`Silmaril.Logic.Szs.Problem`): the models of `a` and the models of `c`. `entails a c` is the
  THM status, in both the 2007 text and the current ontology (`Thms`).
* `Satisfaction.Hom S T`: maps of contexts and conclusions forwards and of models backwards,
  with a satisfaction condition for **each** of the two relations. It induces a sound
  translation of the entailments (`Hom.toTranslation`); identity and composition are
  respected (`Thms`).
* Rooms (fixed-signature institutions): `roomSatisfaction R` has contexts `Set R.Sen`,
  conclusions `R.Sen`, the objects of `R.Mod` as models, and `satAx M Γ := ∀ φ ∈ Γ, M ⊨ φ`.
  Its entailment is `Room.Entails` (`Thms`). A corridor gives a `Satisfaction.Hom` (its
  satisfaction condition gives both conditions) and `roomSys : Room ⥤ Sys` is a functor; an
  institution `I : Sign ⥤ Room` therefore gives `I ⋙ roomSys`, a functor from signatures to
  consequence systems (`institutionSys`). Model morphisms are forgotten: consequence only
  sees the objects of each model category.

What is *not* claimed: an arbitrary `Satisfaction` need not be monotone in any order on
contexts (`entails_monoWrt` needs `satAx` antitone along the order), and a `Satisfaction.Hom`
built from arbitrary maps need not satisfy its conditions; they are proof obligations.
-/

@[expose] public section

namespace Silmaril.Consequence

open CategoryTheory Silmaril.Logic

universe u v w u' v' w' u'' v'' w'' m₁ m₂

/-- Models of type `Model` with independent satisfaction of contexts and of conclusions. -/
structure Satisfaction (Ax : Type u) (C : Type v) where
  /-- The models. -/
  Model : Type w
  /-- `m` satisfies the context `a`. -/
  satAx : Model → Ax → Prop
  /-- `m` satisfies the conclusion `c`. -/
  satC : Model → C → Prop

namespace Satisfaction

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'} {Ax'' : Type u''}
  {C'' : Type v''}

/-- Semantic consequence: every model of the context is a model of the conclusion. -/
def entails (S : Satisfaction.{u, v, w} Ax C) : System Ax C :=
  fun a c => ∀ m, S.satAx m a → S.satC m c

/-- The judgement `a ⊢ c` as an SZS problem over the models. -/
def problem (S : Satisfaction.{u, v, w} Ax C) (a : Ax) (c : C) : Szs.Problem S.Model :=
  ⟨{m | S.satAx m a}, {m | S.satC m c}⟩

/-- A morphism of satisfactions: contexts and conclusions forwards, models backwards, with the
satisfaction condition for contexts and for conclusions. -/
structure Hom (S : Satisfaction.{u, v, w} Ax C) (T : Satisfaction.{u', v', w'} Ax' C') where
  /-- The map of contexts. -/
  ax : Ax → Ax'
  /-- The map of conclusions. -/
  c : C → C'
  /-- The (backwards) map of models. -/
  model : T.Model → S.Model
  /-- The satisfaction condition for contexts. -/
  satAx : ∀ m a, T.satAx m (ax a) ↔ S.satAx (model m) a
  /-- The satisfaction condition for conclusions. -/
  satC : ∀ m φ, T.satC m (c φ) ↔ S.satC (model m) φ

/-- The identity morphism. -/
def Hom.id (S : Satisfaction.{u, v, w} Ax C) : Hom S S :=
  ⟨fun a => a, fun c => c, fun m => m, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- Composition (first `f`, then `g`). -/
def Hom.comp {S : Satisfaction.{u, v, w} Ax C} {T : Satisfaction.{u', v', w'} Ax' C'}
    {U : Satisfaction.{u'', v'', w''} Ax'' C''} (f : Hom S T) (g : Hom T U) : Hom S U :=
  ⟨g.ax ∘ f.ax, g.c ∘ f.c, f.model ∘ g.model,
    fun m a => (g.satAx m (f.ax a)).trans (f.satAx (g.model m) a),
    fun m φ => (g.satC m (f.c φ)).trans (f.satC (g.model m) φ)⟩

/-- A morphism of satisfactions is a sound translation of their entailments. -/
def Hom.toTranslation {S : Satisfaction.{u, v, w} Ax C} {T : Satisfaction.{u', v', w'} Ax' C'}
    (f : Hom S T) : Translation S.entails T.entails :=
  ⟨f.ax, f.c, fun a φ h m hm => (f.satC m φ).2 (h _ ((f.satAx m a).1 hm))⟩

end Satisfaction

/-- A room as a satisfaction: contexts are sets of sentences, satisfied when every member is. -/
def roomSatisfaction (R : Institution.Room.{w, m₁, m₂}) :
    Satisfaction.{w, w, m₂} (Set R.Sen) R.Sen :=
  ⟨R.Mod, fun M Γ => ∀ φ ∈ Γ, R.Sat M φ, R.Sat⟩

/-- A corridor as a morphism of satisfactions: contexts translate by image. -/
def corridorHom {R₁ R₂ : Institution.Room.{w, m₁, m₂}}
    (f : Institution.Corridor R₁ R₂) : Satisfaction.Hom (roomSatisfaction R₁) (roomSatisfaction R₂) :=
  ⟨Set.image f.sen, f.sen, f.mod.obj,
    fun M _ => ⟨fun h φ hφ => (f.sat M φ).1 (h _ ⟨φ, hφ, rfl⟩),
      fun h _ ⟨φ, hφ, e⟩ => e ▸ (f.sat M φ).2 (h φ hφ)⟩,
    f.sat⟩

/-- Rooms to consequence systems: a room goes to its semantic consequence `Room.Entails` over
sets of sentences, and a corridor to the translation by image (`Corridor.entails_map`). -/
def roomSys : Institution.Room.{w, m₁, m₂} ⥤ Sys.{w, w} where
  obj R := ⟨Set R.Sen, R.Sen, R.Entails⟩
  map f := ⟨Set.image f.sen, f.sen, fun _ _ h => Institution.Corridor.entails_map f h⟩
  map_id _ := Translation.ext (funext Set.image_id) rfl
  map_comp f g := Translation.ext (funext fun s => Set.image_comp g.sen f.sen s) rfl

/-- An institution, as a functor from signatures to rooms, gives a consequence system per
signature and a translation per signature morphism. -/
def institutionSys {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Institution.Room.{w, m₁, m₂}) :
    Sign ⥤ Sys.{w, w} :=
  I ⋙ roomSys

end Silmaril.Consequence
