module

public import Silmaril.Logic.Institution.Morphism

/-!
# The institution facade `Silmaril.Inst`

One namespace for the notions Silmaril builds on silmaril's institutions
(`Silmaril.Logic.Institution.Inst`, `Inst.Hom`, `Inst.CoHom`, `Theory`), under
consistent names, with notation. Everything here is an `abbrev` of a silmaril notion or a thin
new definition, so values built with the facade are silmaril values and the other way round:
existing statements need no change.

| facade (`open Silmaril.Inst`) | silmaril |
| --- | --- |
| `Institution` (`Institution₀`, `Institution₁`) | `Inst.{u,v,w,m₁,m₂}` (`Inst.{0,0,0,0,0}`, `Inst.{1,0,0,0,0}`) |
| `Institution₀₁`, `Institution₁₁` | `Inst.{0,0,0,0,1}`, `Inst.{1,0,0,0,1}` |
| `M ⊨ φ` (class `Satisfies`; rooms, observational semantics, game properties) | `(A.I.obj S).Sat M φ` and the other satisfaction relations |
| `A.Sen S`, `A.Mod S`, `M ⊨[A] φ` | `(A.I.obj S).Sen`, `(A.I.obj S).Mod`, `(A.I.obj S).Sat M φ` |
| `A.SignatureMorphism S S'`, `A.map σ`, `A.reduct σ` | `S ⟶ S'`, `(A.I.map σ).sen`, `(A.I.map σ).mod.obj` |
| `Comorphism A B`, `f.sig`, `f.sen S`, `f.mod S` | `Inst.CoHom A B`, `f.Φ.obj`, `(f.ρ.app S).sen`, `(f.ρ.app S).mod.obj` |
| `Morphism A B`, `f.sen S`, `f.mod S` | `Inst.Hom A B`, `(f.η.app S).sen`, `(f.η.app S).mod.obj` |
| `f ≫ᶜ g`, `𝟙ᶜ A`; `f ≫ᵐ g`, `𝟙ᵐ A` | `Inst.CoHom.comp`, `Inst.CoHom.id`; `Inst.Hom.comp`, `Inst.Hom.id` |
| `A.Theory`, `A.TheoryMorphism T T'` | `Theory A.I`, `T ⟶ T'` |
| `SemiComorphism A B` | new: a comorphism whose satisfaction condition holds in one direction, on a class |

The notation is scoped: `open Silmaril.Inst` (or `open scoped Silmaril.Inst`) enables it. The facade
names are also exported as aliases into silmaril's `Inst`, `Inst.CoHom` and `Inst.Hom`
namespaces (end of this file and of `Thms`), so dot notation works on silmaril-typed values.
Builders live in `Silmaril.Logic.Inst.Builders`, the typed logic-graph builder in
`Silmaril.Logic.Inst.Graph`, and the transfer lemmas (`simp`) in `Silmaril.Logic.Inst.Thms`. The guide
is `docs/projects/logic-inst.md`.

Universes: an `Institution.{u,v,w,m₁,m₂}` has signatures in `Type u` with morphisms in
`Type v`, sentences in `Type w` and model categories `Cat.{m₁,m₂}`. A comorphism or morphism
relates institutions with the same `w, m₁, m₂` (silmaril's convention). The two aliases
`Institution₀` and `Institution₁` cover the cases that occur in Silmaril without a universe list.
-/

@[expose] public section

namespace Silmaril.Inst

open CategoryTheory
open Silmaril.Logic.Institution (Room Corridor Inst)

universe u v w m₁ m₂ u₁ v₁ u₂ v₂ u₃ v₃

set_option linter.checkUnivs false in
/-- An institution: a category of signatures and a functor into rooms (silmaril's `Inst`). -/
abbrev Institution : Type _ := Inst.{u, v, w, m₁, m₂}

/-- Institutions whose signatures, sentences and models live in `Type`. -/
abbrev Institution₀ : Type 1 := Institution.{0, 0, 0, 0, 0}

/-- Institutions whose signatures live in `Type 1` (signatures that contain a type, such as
the variable set of an observational signature), with morphisms, sentences and models in
`Type`. This is silmaril's `Inst.{1, 0, 0, 0, 0}`, the most common case in Silmaril. -/
abbrev Institution₁ : Type 2 := Institution.{1, 0, 0, 0, 0}

/-- Institutions whose signatures, sentence and signature-morphism types live in `Type` and whose
models live in `Type 1` (silmaril's `Inst.{0, 0, 0, 0, 1}`: the unified Wasm institution
`Silmaril.Wasm.Unified.inst`). Naming scheme: the first subscript is the universe of signatures,
the second (omitted when `0`) the universe of models. -/
abbrev Institution₀₁ : Type 2 := Institution.{0, 0, 0, 0, 1}

/-- Institutions whose signatures and models live in `Type 1` (silmaril's
`Inst.{1, 0, 0, 0, 1}`: propositional, equational and first-order logic, `PL.inst`, `EQ.inst`,
`FOL.inst`). -/
abbrev Institution₁₁ : Type 2 := Institution.{1, 0, 0, 0, 1}

namespace Institution

variable (A : Institution.{u, v, w, m₁, m₂})

/-- Signature morphisms `S ⟶ S'` of `A`. -/
abbrev SignatureMorphism (S S' : A.Sign) : Type v := S ⟶ S'

/-- The room `(Sen S, Mod S, ⊨)` of a signature. -/
abbrev room (S : A.Sign) : Room.{w, m₁, m₂} := A.I.obj S

/-- Sentences over `S`. -/
abbrev Sen (S : A.Sign) : Type w := (A.I.obj S).Sen

/-- Models over `S`. -/
abbrev Mod (S : A.Sign) : Type m₂ := (A.I.obj S).Mod

/-- Satisfaction `M ⊨[A] φ`. -/
abbrev Sat {S : A.Sign} (M : A.Mod S) (φ : A.Sen S) : Prop := (A.I.obj S).Sat M φ

/-- Sentence translation along a signature morphism. -/
abbrev map {S S' : A.Sign} (σ : S ⟶ S') : A.Sen S → A.Sen S' := (A.I.map σ).sen

/-- The model reduct along a signature morphism. -/
abbrev reduct {S S' : A.Sign} (σ : S ⟶ S') : A.Mod S' → A.Mod S := (A.I.map σ).mod.obj

/-- Semantic consequence `Γ ⊨ φ` over `S`. -/
abbrev Entails {S : A.Sign} (Γ : Set (A.Sen S)) (φ : A.Sen S) : Prop := (A.I.obj S).Entails Γ φ

/-- A sentence is valid when every model satisfies it. -/
def Valid {S : A.Sign} (φ : A.Sen S) : Prop := ∀ M : A.Mod S, A.Sat M φ

/-- Theories of `A` (closed sets of sentences over a signature). -/
abbrev Theory : Type (max u w) := Silmaril.Logic.Institution.Theory A.I

/-- Theory morphisms: signature morphisms mapping the theory into the target theory. -/
abbrev TheoryMorphism (T T' : A.Theory) : Type v := T ⟶ T'

/-- The institution of theories of `A` (silmaril's `Inst.th`). -/
abbrev theories : Institution.{max u w, v, w, m₁, m₂} := A.th

end Institution

/-- Satisfaction `M ⊨[A] φ` in the institution `A`. -/
scoped notation:50 M:51 " ⊨[" A "] " φ:51 => Institution.Sat A M φ

/-! ### The canonical satisfaction notation

`M ⊨ φ` is *the* satisfaction notation of Silmaril's institutions: one class, `Satisfies`, with
one scoped notation in `Silmaril.Inst`. Every room is an instance (so `M ⊨ φ` works for the models
and sentences of any institution, and is `M ⊨[A] φ` by `Iff.rfl`), and the other satisfaction
relations of Silmaril are instances too: the observational semantics of
`Silmaril.Wasm.Institution` (`ObsSemantics.instSatisfies`, in `Silmaril.Wasm.Institution.Api.Defs`),
the unified Wasm institution (`Unified.instSatisfies`) and the game properties of `Silmaril.Games`
(`GSen.instSatisfies`, `DGSen.instSatisfies`, in `Silmaril.Games.InstFacade.Defs`).
`M ⊨[A] φ` stays for statements that name the institution. -/

universe s₁ s₂

/-- A satisfaction relation between models `M` and sentences `Φ`: the class behind the
canonical notation `M ⊨ φ`. -/
class Satisfies (M : Sort s₁) (Φ : Sort s₂) where
  /-- Satisfaction `M ⊨ φ`. -/
  Sat : M → Φ → Prop

@[inherit_doc Satisfies.Sat]
scoped infix:50 " ⊨ " => Satisfies.Sat

/-- Rooms (so every institution at every signature): `M ⊨ φ` is the room's satisfaction. -/
@[reducible] instance Satisfies.room (R : Room.{w, m₁, m₂}) : Satisfies R.Mod R.Sen := ⟨R.Sat⟩

/-- In a room, `M ⊨ φ` unfolds to the room's satisfaction. -/
@[simp] theorem Satisfies.room_sat_iff (R : Room.{w, m₁, m₂}) (M : R.Mod) (φ : R.Sen) :
    M ⊨ φ ↔ R.Sat M φ :=
  Iff.rfl

/-- In an institution, `M ⊨ φ` is `M ⊨[A] φ`. -/
theorem Institution.satisfies_iff (A : Institution.{u, v, w, m₁, m₂}) {S : A.Sign} (M : A.Mod S)
    (φ : A.Sen S) : M ⊨ φ ↔ M ⊨[A] φ :=
  Iff.rfl

/-- An institution comorphism `A → B` (silmaril's `Inst.CoHom`): signatures and sentences go
forwards, models backwards. -/
abbrev Comorphism (A : Institution.{u₁, v₁, w, m₁, m₂}) (B : Institution.{u₂, v₂, w, m₁, m₂}) :
    Type _ :=
  Inst.CoHom A B

/-- An institution morphism `A → B` (silmaril's `Inst.Hom`): signatures and models go
forwards, sentences backwards. -/
abbrev Morphism (A : Institution.{u₁, v₁, w, m₁, m₂}) (B : Institution.{u₂, v₂, w, m₁, m₂}) :
    Type _ :=
  Inst.Hom A B

namespace Comorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}} (f : Comorphism A B)

/-- The signature translation. -/
abbrev sig (S : A.Sign) : B.Sign := f.Φ.obj S

/-- The sentence translation at `S`. -/
abbrev sen (S : A.Sign) : A.Sen S → B.Sen (f.Φ.obj S) := (f.ρ.app S).sen

/-- The model translation at `S` (backwards). -/
abbrev mod (S : A.Sign) : B.Mod (f.Φ.obj S) → A.Mod S := (f.ρ.app S).mod.obj

/-- The identity comorphism. -/
abbrev id (A : Institution.{u₁, v₁, w, m₁, m₂}) : Comorphism A A := Inst.CoHom.id A

/-- Composition of comorphisms, in diagrammatic order. -/
abbrev comp (f : Comorphism A B) (g : Comorphism B C) : Comorphism A C := Inst.CoHom.comp f g



end Comorphism

namespace Morphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}} (f : Morphism A B)

/-- The signature translation. -/
abbrev sig (S : A.Sign) : B.Sign := f.Φ.obj S

/-- The sentence translation at `S` (backwards). -/
abbrev sen (S : A.Sign) : B.Sen (f.Φ.obj S) → A.Sen S := (f.η.app S).sen

/-- The model translation at `S` (forwards). -/
abbrev mod (S : A.Sign) : A.Mod S → B.Mod (f.Φ.obj S) := (f.η.app S).mod.obj

/-- The identity morphism. -/
abbrev id (A : Institution.{u₁, v₁, w, m₁, m₂}) : Morphism A A := Inst.Hom.id A

/-- Composition of morphisms, in diagrammatic order. -/
abbrev comp (f : Morphism A B) (g : Morphism B C) : Morphism A C := Inst.Hom.comp f g



end Morphism

/-- Composition of comorphisms. -/
scoped infixr:80 " ≫ᶜ " => Comorphism.comp
/-- The identity comorphism. -/
scoped notation "𝟙ᶜ" => Comorphism.id
/-- Composition of morphisms. -/
scoped infixr:80 " ≫ᵐ " => Morphism.comp
/-- The identity morphism. -/
scoped notation "𝟙ᵐ" => Morphism.id

/-! ### Semi-comorphisms -/

/-- A **semi-comorphism** `A → B`: a comorphism whose satisfaction condition is only required
on a class of sentences `cls`, and only in the directions that hold.

* `Fwd`: the translation *preserves*: `mod M' ⊨ φ → M' ⊨ sen φ`;
* `Bwd`: the translation *reflects*: `M' ⊨ sen φ → mod M' ⊨ φ`.

Both directions on every sentence make a comorphism without the naturality conditions
(`Comorphism.toSemi` goes the other way). This is the institutional reading of the atlas
transitions (`Silmaril.Wasm.Atlas.Transition`), of `Linked2.sound` and of the SpecTec
semi-comorphisms. No naturality is required: the notion is used per signature. -/
structure SemiComorphism (A : Institution.{u₁, v₁, w, m₁, m₂})
    (B : Institution.{u₂, v₂, w, m₁, m₂}) where
  /-- The signature translation. -/
  sig : A.Sign → B.Sign
  /-- The sentence translation. -/
  sen : ∀ S : A.Sign, A.Sen S → B.Sen (sig S)
  /-- The model translation (backwards). -/
  mod : ∀ S : A.Sign, B.Mod (sig S) → A.Mod S
  /-- The class of sentences on which satisfaction is related. -/
  cls : ∀ S : A.Sign, A.Sen S → Prop
  /-- Whether satisfaction is preserved. -/
  Fwd : Prop
  /-- Whether satisfaction is reflected. -/
  Bwd : Prop
  /-- Preservation on the class. -/
  sat_fwd : Fwd → ∀ S (M' : B.Mod (sig S)) (φ : A.Sen S), cls S φ →
    (mod S M') ⊨[A] φ → M' ⊨[B] (sen S φ)
  /-- Reflection on the class. -/
  sat_bwd : Bwd → ∀ S (M' : B.Mod (sig S)) (φ : A.Sen S), cls S φ →
    M' ⊨[B] (sen S φ) → (mod S M') ⊨[A] φ

namespace SemiComorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}}

/-- The identity semi-comorphism: both directions, every sentence. -/
def id (A : Institution.{u₁, v₁, w, m₁, m₂}) : SemiComorphism A A where
  sig S := S
  sen _ φ := φ
  mod _ M := M
  cls _ _ := True
  Fwd := True
  Bwd := True
  sat_fwd _ _ _ _ _ h := h
  sat_bwd _ _ _ _ _ h := h

/-- Composition: the class is pulled back, the directions are met. -/
def comp (f : SemiComorphism A B) (g : SemiComorphism B C) : SemiComorphism A C where
  sig S := g.sig (f.sig S)
  sen S φ := g.sen (f.sig S) (f.sen S φ)
  mod S M := f.mod S (g.mod (f.sig S) M)
  cls S φ := f.cls S φ ∧ g.cls (f.sig S) (f.sen S φ)
  Fwd := f.Fwd ∧ g.Fwd
  Bwd := f.Bwd ∧ g.Bwd
  sat_fwd h S M φ hc hM :=
    g.sat_fwd h.2 (f.sig S) M (f.sen S φ) hc.2 (f.sat_fwd h.1 S (g.mod (f.sig S) M) φ hc.1 hM)
  sat_bwd h S M φ hc hM :=
    f.sat_bwd h.1 S (g.mod (f.sig S) M) φ hc.1 (g.sat_bwd h.2 (f.sig S) M (f.sen S φ) hc.2 hM)

/-- Restrict a semi-comorphism to a smaller class of sentences. -/
def restrict (f : SemiComorphism A B) (c : ∀ S : A.Sign, A.Sen S → Prop)
    (hc : ∀ S φ, c S φ → f.cls S φ) : SemiComorphism A B :=
  { f with
    cls := c
    sat_fwd := fun h S M φ hφ => f.sat_fwd h S M φ (hc S φ hφ)
    sat_bwd := fun h S M φ hφ => f.sat_bwd h S M φ (hc S φ hφ) }

end SemiComorphism

/-- Composition of semi-comorphisms. -/
scoped infixr:80 " ≫ˢ " => SemiComorphism.comp

/-- A comorphism is a semi-comorphism in both directions on every sentence. -/
def Comorphism.toSemi {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
    (f : Comorphism A B) : SemiComorphism A B where
  sig := f.sig
  sen := f.sen
  mod := f.mod
  cls _ _ := True
  Fwd := True
  Bwd := True
  sat_fwd _ S M φ _ h := ((f.ρ.app S).sat M φ).2 h
  sat_bwd _ S M φ _ h := ((f.ρ.app S).sat M φ).1 h

/-- Comorphisms coerce to semi-comorphisms. -/
instance {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}} :
    Coe (Comorphism A B) (SemiComorphism A B) :=
  ⟨Comorphism.toSemi⟩

end Silmaril.Inst

/-! ## Dot notation on silmaril-typed values

Dot notation follows the head constant of a value's type. A value declared at a facade type
(`f : Comorphism A B`) finds `Silmaril.Inst.Comorphism.sen`; a value that keeps its silmaril type
(`dn : Inst.CoHom PL.inst PL.inst`, `PL.inst : Inst.{1, 0, 0, 0, 1}`) looks in silmaril's
namespaces. The `export`s below put the facade names there as *aliases* (no new constants), so
`dn.sen P φ`, `dn.mod P v`, `PL.inst.Mod P`, `PL.inst.Entails Γ φ` elaborate to the same terms
as the facade spellings and every facade `simp` lemma applies. The aliased names are not
declared by silmaril (checked against the pinned revision; see the guide). -/

namespace Silmaril.Logic.Institution.Inst

export Silmaril.Inst.Institution (SignatureMorphism room Sen Mod Sat map reduct Entails Valid Theory
  TheoryMorphism theories)

namespace CoHom

export Silmaril.Inst.Comorphism (sig sen mod toSemi)

end CoHom

namespace Hom

export Silmaril.Inst.Morphism (sig sen mod)

end Hom

end Silmaril.Logic.Institution.Inst
