module

public import Silmaril.Logic.Inst.Core.Defs

/-!
# Builders for institutions, comorphisms and semi-comorphisms

The common ways Silmaril constructs institutions and translations, without universe lists and
without writing room functors by hand.

Institutions:

* `Institution.ofFunctor I`: from a functor `Sign ⥤ Room` (universes inferred);
* `Institution.ofClassic I`: from silmaril's direct definition `ClassicInstitution`;
* `Plain` / `Plain.toInst`: from sentences, models, reducts and satisfaction given as plain
  functions with their laws; models get the discrete category (equalities as morphisms), as in
  every institution of the Wasm graph. `Plain.ofSat` is the common special case of a
  satisfaction relation that is a predicate on the reduct (an *observational semantics*:
  sentences are observations of models).

Comorphisms:

* `Comorphism.ofCorridors`: from a corridor at every signature and naturality;
* `Comorphism.ofTranslation`: from a sentence translation, a model translation (a functor) and
  the satisfaction condition, with naturality as equations;
* `Comorphism.ofPlain`: the same between `Plain` institutions, with plain functions;
* `Comorphism.ofIso`: from an equivalence (natural isomorphism) of room functors on a common
  signature category; its borrowing theorem is available from the broad compatibility entry point;
* `Comorphism.ofBehaviour`: from an *exact behaviour translation*: satisfaction factors through
  a behaviour of the model on both sides (`Behavioural`), the model translation computes the
  source behaviour exactly from the target behaviour, and the sentence translation is exact on
  behaviours.

Semi-comorphisms:

* `SemiComorphism.ofSimulation`: from a simulation between target models and translated source
  models, and a class of sentences preserved along simulations (safety sentences along
  trace inclusion, for example).
-/

@[expose] public section

namespace Silmaril.Inst

open CategoryTheory
open Silmaril.Logic.Institution (Room Corridor Inst ClassicInstitution)

universe u v w m m₁ m₂ u₁ v₁ u₂ v₂

/-! ### Institutions -/

namespace Institution

/-- The institution of a functor into rooms. -/
abbrev ofFunctor {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂}) :
    Institution.{u, v, w, m₁, m₂} :=
  ⟨Sign, I⟩

/-- The institution of a classic institution (Goguen–Burstall's direct definition). -/
abbrev ofClassic {Sign : Type u} [Category.{v} Sign]
    (I : ClassicInstitution.{u, v, w, m₁, m₂} Sign) : Institution.{u, v, w, m₁, m₂} :=
  ⟨Sign, I.toRoomFunctor⟩

end Institution

/-- A type viewed as a discrete category: the only morphisms are equalities. -/
def Disc (α : Type m) : Type m := α

instance Disc.category (α : Type m) : Category.{0} (Disc α) where
  Hom a b := PLift (a = b)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

instance Disc.subsingleton_hom {α : Type m} (a b : Disc α) : Subsingleton (a ⟶ b) :=
  ⟨fun f g => by cases f; cases g; rfl⟩

/-- A function as a functor between discrete categories. -/
def Disc.functor {α β : Type m} (f : α → β) : Disc α ⥤ Disc β where
  obj := f
  map h := ⟨congrArg f h.down⟩

theorem Disc.functor_ext {α β : Type m} {F G : Disc α ⥤ Disc β} (h : ∀ a, F.obj a = G.obj a) :
    F = G :=
  Functor.ext h (fun _ _ _ => Subsingleton.elim _ _)

@[simp] theorem Disc.functor_obj {α β : Type m} (f : α → β) (a : Disc α) :
    (Disc.functor f).obj a = f a := rfl

/-- The discrete category of a type, as an object of `Cat`. -/
abbrev Disc.cat (α : Type m) : Cat.{0, m} := Cat.of (Disc α)

/-- An institution with discrete model categories, given by plain functions and their laws:
sentences translate forwards, models reduce backwards, and satisfaction is invariant. -/
structure Plain (Sign : Type u) [Category.{v} Sign] where
  /-- Sentences over a signature. -/
  Sen : Sign → Type w
  /-- Sentence translation. -/
  map : ∀ {S S' : Sign}, (S ⟶ S') → Sen S → Sen S'
  map_id : ∀ (S : Sign) (φ : Sen S), map (𝟙 S) φ = φ
  map_comp : ∀ {S S' S'' : Sign} (σ : S ⟶ S') (τ : S' ⟶ S'') (φ : Sen S),
    map (σ ≫ τ) φ = map τ (map σ φ)
  /-- Models over a signature. -/
  Mod : Sign → Type m
  /-- The model reduct. -/
  reduct : ∀ {S S' : Sign}, (S ⟶ S') → Mod S' → Mod S
  reduct_id : ∀ (S : Sign) (M : Mod S), reduct (𝟙 S) M = M
  reduct_comp : ∀ {S S' S'' : Sign} (σ : S ⟶ S') (τ : S' ⟶ S'') (M : Mod S''),
    reduct (σ ≫ τ) M = reduct σ (reduct τ M)
  /-- Satisfaction. -/
  Sat : ∀ {S : Sign}, Mod S → Sen S → Prop
  /-- The satisfaction condition. -/
  sat_map : ∀ {S S' : Sign} (σ : S ⟶ S') (M' : Mod S') (φ : Sen S),
    Sat M' (map σ φ) ↔ Sat (reduct σ M') φ

namespace Plain

variable {Sign : Type u} [Category.{v} Sign] (P : Plain.{u, v, w, m} Sign)

/-- The room of a signature. -/
def room (S : Sign) : Room.{w, 0, m} := ⟨P.Sen S, Disc.cat (P.Mod S), fun M φ => P.Sat M φ⟩

/-- The corridor of a signature morphism. -/
def corridor {S S' : Sign} (σ : S ⟶ S') : P.room S ⟶ P.room S' :=
  ⟨P.map σ, Disc.functor (P.reduct σ), fun M φ => P.sat_map σ M φ⟩

/-- The room functor. -/
def functor : Sign ⥤ Room.{w, 0, m} where
  obj := P.room
  map := P.corridor
  map_id S := Room.hom_ext (funext (P.map_id S)) (Disc.functor_ext (P.reduct_id S))
  map_comp σ τ :=
    Room.hom_ext (funext (P.map_comp σ τ)) (Disc.functor_ext (P.reduct_comp σ τ))

/-- The institution of a plain presentation. -/
abbrev toInst : Institution.{u, v, w, 0, m} := Institution.ofFunctor P.functor

/-- An *observational* plain institution: satisfaction is a predicate `holds` on models, and a
translated sentence holds of a model iff the original holds of its reduct. Sentences are
predicates, so the sentence translation (precomposition with the reduct) is strictly
functorial for free. -/
def ofSat (Mod : Sign → Type m) (reduct : ∀ {S S' : Sign}, (S ⟶ S') → Mod S' → Mod S)
    (reduct_id : ∀ (S : Sign) (M : Mod S), reduct (𝟙 S) M = M)
    (reduct_comp : ∀ {S S' S'' : Sign} (σ : S ⟶ S') (τ : S' ⟶ S'') (M : Mod S''),
      reduct (σ ≫ τ) M = reduct σ (reduct τ M)) : Plain.{u, v, m, m} Sign where
  Sen S := Mod S → Prop
  map σ φ := fun M' => φ (reduct σ M')
  map_id S φ := funext fun M => by simp only [reduct_id]
  map_comp σ τ φ := funext fun M => by simp only [reduct_comp]
  Mod := Mod
  reduct := reduct
  reduct_id := reduct_id
  reduct_comp := reduct_comp
  Sat M φ := φ M
  sat_map _ _ _ := Iff.rfl

end Plain

/-! ### Comorphisms -/

namespace Comorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}

/-- A comorphism from a signature functor, a corridor at each signature, and naturality. -/
def ofCorridors (Φ : A.Sign ⥤ B.Sign) (ρ : ∀ S : A.Sign, A.room S ⟶ B.room (Φ.obj S))
    (nat : ∀ {S S' : A.Sign} (σ : S ⟶ S'), A.I.map σ ≫ ρ S' = ρ S ≫ B.I.map (Φ.map σ)) :
    Comorphism A B :=
  ⟨Φ, { app := ρ, naturality := fun _ _ σ => nat σ }⟩

/-- A comorphism from a sentence translation, a model translation and the satisfaction
condition, with naturality as equations. -/
def ofTranslation (Φ : A.Sign ⥤ B.Sign) (sen : ∀ S : A.Sign, A.Sen S → B.Sen (Φ.obj S))
    (mod : ∀ S : A.Sign, (B.room (Φ.obj S)).Mod ⥤ (A.room S).Mod)
    (sat : ∀ S (M' : B.Mod (Φ.obj S)) (φ : A.Sen S),
      M' ⊨[B] (sen S φ) ↔ ((mod S).obj M') ⊨[A] φ)
    (sen_nat : ∀ {S S' : A.Sign} (σ : S ⟶ S') (φ : A.Sen S),
      sen S' (A.map σ φ) = B.map (Φ.map σ) (sen S φ))
    (mod_nat : ∀ {S S' : A.Sign} (σ : S ⟶ S'),
      mod S' ⋙ (A.I.map σ).mod = (B.I.map (Φ.map σ)).mod ⋙ mod S) :
    Comorphism A B :=
  ofCorridors Φ (fun S => ⟨sen S, mod S, sat S⟩)
    (fun σ => Room.hom_ext (funext (sen_nat σ)) (mod_nat σ))

/-- An identity-on-signatures comorphism between institutions over the same signature
category (the shape of every edge of the Wasm logic graph). -/
def ofTranslationId {Sign : Type u} [Category.{v} Sign] {I J : Sign ⥤ Room.{w, m₁, m₂}}
    (sen : ∀ S : Sign, (I.obj S).Sen → (J.obj S).Sen)
    (mod : ∀ S : Sign, (J.obj S).Mod ⥤ (I.obj S).Mod)
    (sat : ∀ S M' φ, (J.obj S).Sat M' (sen S φ) ↔ (I.obj S).Sat ((mod S).obj M') φ)
    (sen_nat : ∀ {S S' : Sign} (σ : S ⟶ S') φ, sen S' ((I.map σ).sen φ) = (J.map σ).sen (sen S φ))
    (mod_nat : ∀ {S S' : Sign} (σ : S ⟶ S'), mod S' ⋙ (I.map σ).mod = (J.map σ).mod ⋙ mod S) :
    Comorphism (Institution.ofFunctor I) (Institution.ofFunctor J) :=
  ofTranslation (𝟭 Sign) sen mod sat sen_nat mod_nat

/-- A comorphism between plain institutions, from plain functions. -/
def ofPlain {Sign : Type u₁} [Category.{v₁} Sign] {Sign' : Type u₂} [Category.{v₂} Sign']
    {P : Plain.{u₁, v₁, w, m} Sign} {Q : Plain.{u₂, v₂, w, m} Sign'} (Φ : Sign ⥤ Sign')
    (sen : ∀ S : Sign, P.Sen S → Q.Sen (Φ.obj S))
    (mod : ∀ S : Sign, Q.Mod (Φ.obj S) → P.Mod S)
    (sat : ∀ S (M' : Q.Mod (Φ.obj S)) (φ : P.Sen S), Q.Sat M' (sen S φ) ↔ P.Sat (mod S M') φ)
    (sen_nat : ∀ {S S' : Sign} (σ : S ⟶ S') (φ : P.Sen S),
      sen S' (P.map σ φ) = Q.map (Φ.map σ) (sen S φ))
    (mod_nat : ∀ {S S' : Sign} (σ : S ⟶ S') (M' : Q.Mod (Φ.obj S')),
      P.reduct σ (mod S' M') = mod S (Q.reduct (Φ.map σ) M')) :
    Comorphism P.toInst Q.toInst :=
  ofTranslation (A := P.toInst) (B := Q.toInst) Φ sen (fun S => Disc.functor (mod S)) sat
    sen_nat (fun σ => Disc.functor_ext (mod_nat σ))

/-- The comorphism of an equivalence (natural isomorphism) of room functors. -/
def ofIso {Sign : Type u} [Category.{v} Sign] {I J : Sign ⥤ Room.{w, m₁, m₂}} (e : I ≅ J) :
    Comorphism (Institution.ofFunctor I) (Institution.ofFunctor J) :=
  ⟨𝟭 Sign, e.hom ≫ (Functor.leftUnitor J).inv⟩

/-- The comorphism of an equivalence, inverted. -/
def ofIso' {Sign : Type u} [Category.{v} Sign] {I J : Sign ⥤ Room.{w, m₁, m₂}} (e : I ≅ J) :
    Comorphism (Institution.ofFunctor J) (Institution.ofFunctor I) :=
  ofIso e.symm

end Comorphism

/-! ### Exact behaviour translations -/

/-- Satisfaction in `A` factors through a *behaviour* of models: `M ⊨ φ` iff `φ` holds of the
behaviour of `M`. -/
structure Behavioural (A : Institution.{u, v, w, m₁, m₂}) where
  /-- Behaviours at a signature. -/
  Beh : A.Sign → Type m
  /-- The behaviour of a model. -/
  beh : ∀ {S : A.Sign}, A.Mod S → Beh S
  /-- Satisfaction on behaviours. -/
  Holds : ∀ {S : A.Sign}, Beh S → A.Sen S → Prop
  sat_iff : ∀ {S : A.Sign} (M : A.Mod S) (φ : A.Sen S), M ⊨[A] φ ↔ Holds (beh M) φ

/-- An **exact behaviour translation** `A → B`: a sentence and model translation such that the
behaviour of a translated model is computed exactly (by `obs`) from the behaviour of the
target model, and translated sentences mean on behaviours what the source sentences mean on
the computed behaviours. -/
structure BehaviourTranslation {A : Institution.{u₁, v₁, w, m₁, m₂}}
    {B : Institution.{u₂, v₂, w, m₁, m₂}} (bA : Behavioural A)
    (bB : Behavioural B) where
  /-- The signature translation. -/
  Φ : A.Sign ⥤ B.Sign
  /-- The sentence translation. -/
  sen : ∀ S : A.Sign, A.Sen S → B.Sen (Φ.obj S)
  /-- The model translation. -/
  mod : ∀ S : A.Sign, (B.room (Φ.obj S)).Mod ⥤ (A.room S).Mod
  /-- The behaviour translation. -/
  obs : ∀ S : A.Sign, bB.Beh (Φ.obj S) → bA.Beh S
  /-- Exactness on models: the source behaviour of a translated model is computed from the
  target behaviour. -/
  beh_mod : ∀ S (M' : B.Mod (Φ.obj S)), bA.beh ((mod S).obj M') = obs S (bB.beh M')
  /-- Exactness on sentences. -/
  holds_sen : ∀ S (b : bB.Beh (Φ.obj S)) (φ : A.Sen S), bB.Holds b (sen S φ) ↔ bA.Holds (obs S b) φ
  sen_nat : ∀ {S S' : A.Sign} (σ : S ⟶ S') (φ : A.Sen S),
    sen S' (A.map σ φ) = B.map (Φ.map σ) (sen S φ)
  mod_nat : ∀ {S S' : A.Sign} (σ : S ⟶ S'),
    mod S' ⋙ (A.I.map σ).mod = (B.I.map (Φ.map σ)).mod ⋙ mod S

namespace Comorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}

/-- The comorphism of an exact behaviour translation. -/
def ofBehaviour {bA : Behavioural A}
    {bB : Behavioural B} (T : BehaviourTranslation bA bB) :
    Comorphism A B :=
  ofTranslation T.Φ T.sen T.mod
    (fun S M' φ => by
      rw [bB.sat_iff, bA.sat_iff, T.beh_mod, T.holds_sen])
    T.sen_nat T.mod_nat

end Comorphism

/-! ### Semi-comorphisms from simulations -/

namespace SemiComorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}

/-- A preserving semi-comorphism from a simulation: every target model `M'` is related by
`Sim` to its translation, and class sentences carry from a model to every model related to
it (`pres`). With trace inclusion as `Sim` and safety sentences as the class, this is "a
refinement preserves safety". -/
def ofSimulation (sig : A.Sign → B.Sign) (sen : ∀ S : A.Sign, A.Sen S → B.Sen (sig S))
    (mod : ∀ S : A.Sign, B.Mod (sig S) → A.Mod S)
    (Sim : ∀ S : A.Sign, B.Mod (sig S) → A.Mod S → Prop)
    (sim : ∀ S (M' : B.Mod (sig S)), Sim S M' (mod S M'))
    (cls : ∀ S : A.Sign, A.Sen S → Prop)
    (pres : ∀ S (M' : B.Mod (sig S)) (M : A.Mod S) (φ : A.Sen S), cls S φ → Sim S M' M →
      M ⊨[A] φ → M' ⊨[B] (sen S φ)) : SemiComorphism A B where
  sig := sig
  sen := sen
  mod := mod
  cls := cls
  Fwd := True
  Bwd := False
  sat_fwd _ S M' φ hc h := pres S M' (mod S M') φ hc (sim S M') h
  sat_bwd h := h.elim

/-- A two-way semi-comorphism from a bisimulation: class sentences are invariant along `Sim`. -/
def ofBisimulation (sig : A.Sign → B.Sign) (sen : ∀ S : A.Sign, A.Sen S → B.Sen (sig S))
    (mod : ∀ S : A.Sign, B.Mod (sig S) → A.Mod S)
    (Sim : ∀ S : A.Sign, B.Mod (sig S) → A.Mod S → Prop)
    (sim : ∀ S (M' : B.Mod (sig S)), Sim S M' (mod S M'))
    (cls : ∀ S : A.Sign, A.Sen S → Prop)
    (inv : ∀ S (M' : B.Mod (sig S)) (M : A.Mod S) (φ : A.Sen S), cls S φ → Sim S M' M →
      (M ⊨[A] φ ↔ M' ⊨[B] (sen S φ))) : SemiComorphism A B where
  sig := sig
  sen := sen
  mod := mod
  cls := cls
  Fwd := True
  Bwd := True
  sat_fwd _ S M' φ hc h := (inv S M' (mod S M') φ hc (sim S M')).1 h
  sat_bwd _ S M' φ hc h := (inv S M' (mod S M') φ hc (sim S M')).2 h

end SemiComorphism

end Silmaril.Inst
