module

public import Silmaril.Logic.Inst.Core.Defs

/-!
# Transfer lemmas of the institution facade (core)

The lemmas that need only the public institution core
(`Silmaril.Logic.Institution.Morphism`). Borrowing (model expansiveness, `entails_iff`,
`valid_iff`) is in `Silmaril.Logic.Inst.Thms`, which re-exports this module.

The satisfaction conditions as `simp` lemmas, oriented to move translations off sentences and
onto models:

* `Institution.sat_map_iff`: `M' ⊨[A] A.map σ φ ↔ A.reduct σ M' ⊨[A] φ`;
* `Comorphism.sat_sen_iff`: `M' ⊨[B] f.sen S φ ↔ f.mod S M' ⊨[A] φ`;
* `Morphism.sat_sen_iff`: `M ⊨[A] f.sen S φ ↔ f.mod S M ⊨[B] φ`;

the composition and identity laws of `≫ᶜ`, `𝟙ᶜ`, `≫ᵐ`, `𝟙ᵐ` on `sig`, `sen` and `mod`
(all `rfl`, so `simp` computes composite translations), preservation of validity, and the
transfer lemmas of semi-comorphisms.
-/

@[expose] public section

namespace Silmaril.Inst

open CategoryTheory
open Silmaril.Logic.Institution (Room Corridor Inst)

universe u v w m₁ m₂ u₁ v₁ u₂ v₂ u₃ v₃

namespace Institution

variable {A : Institution.{u, v, w, m₁, m₂}}

/-- **The satisfaction condition** of an institution. -/
@[simp] theorem sat_map_iff {S S' : A.Sign} (σ : S ⟶ S') (M' : A.Mod S') (φ : A.Sen S) :
    M' ⊨[A] (A.map σ φ) ↔ (A.reduct σ M') ⊨[A] φ :=
  (A.I.map σ).sat M' φ

@[simp] theorem map_id_apply (S : A.Sign) (φ : A.Sen S) : A.map (𝟙 S) φ = φ := by
  simp [Institution.map]

theorem map_comp_apply {S S' S'' : A.Sign} (σ : S ⟶ S') (τ : S' ⟶ S'') (φ : A.Sen S) :
    A.map (σ ≫ τ) φ = A.map τ (A.map σ φ) := by
  simp [Institution.map]

@[simp] theorem reduct_id_apply (S : A.Sign) (M : A.Mod S) : A.reduct (𝟙 S) M = M := by
  simp [Institution.reduct]

theorem reduct_comp_apply {S S' S'' : A.Sign} (σ : S ⟶ S') (τ : S' ⟶ S'') (M : A.Mod S'') :
    A.reduct (σ ≫ τ) M = A.reduct σ (A.reduct τ M) := by
  simp [Institution.reduct]

theorem valid_iff {S : A.Sign} (φ : A.Sen S) : A.Valid φ ↔ ∀ M : A.Mod S, M ⊨[A] φ := Iff.rfl

/-- Validity is consequence from no hypotheses. -/
theorem valid_iff_entails {S : A.Sign} (φ : A.Sen S) : A.Valid φ ↔ A.Entails ∅ φ := by
  simp [Institution.Valid, Institution.Entails, Room.Entails]

/-- Validity is preserved by translation along signature morphisms. -/
theorem Valid.map {S S' : A.Sign} (σ : S ⟶ S') {φ : A.Sen S} (h : A.Valid φ) :
    A.Valid (A.map σ φ) := fun M' => (sat_map_iff σ M' φ).2 (h _)

end Institution

namespace Comorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}} {D : Institution.{u, v, w, m₁, m₂}}

/-- **The satisfaction condition** of a comorphism, as a rewrite rule. -/
@[simp] theorem sat_sen_iff (f : Comorphism A B) (S : A.Sign) (M' : B.Mod (f.sig S))
    (φ : A.Sen S) : M' ⊨[B] (f.sen S φ) ↔ (f.mod S M') ⊨[A] φ :=
  (f.ρ.app S).sat M' φ

/-- Naturality of the sentence translation. -/
theorem sen_map (f : Comorphism A B) {S S' : A.Sign} (σ : S ⟶ S') (φ : A.Sen S) :
    f.sen S' (A.map σ φ) = B.map (f.Φ.map σ) (f.sen S φ) := by
  have h := congrArg Corridor.sen (f.ρ.naturality σ)
  exact congrFun h φ

/-- Naturality of the model translation. -/
theorem mod_reduct (f : Comorphism A B) {S S' : A.Sign} (σ : S ⟶ S')
    (M' : B.Mod (f.sig S')) :
    A.reduct σ (f.mod S' M') = f.mod S (B.reduct (f.Φ.map σ) M') := by
  have h := congrArg Corridor.mod (f.ρ.naturality σ)
  exact congrArg (fun F : _ ⥤ _ => F.obj M') h

@[simp] theorem id_sig (S : A.Sign) : (𝟙ᶜ A).sig S = S := rfl
@[simp] theorem id_sen (S : A.Sign) (φ : A.Sen S) : (𝟙ᶜ A).sen S φ = φ := rfl
@[simp] theorem id_mod (S : A.Sign) (M : A.Mod S) : (𝟙ᶜ A).mod S M = M := rfl

@[simp] theorem comp_sig (f : Comorphism A B) (g : Comorphism B C) (S : A.Sign) :
    (f ≫ᶜ g).sig S = g.sig (f.sig S) := rfl
@[simp] theorem comp_sen (f : Comorphism A B) (g : Comorphism B C) (S : A.Sign)
    (φ : A.Sen S) : (f ≫ᶜ g).sen S φ = g.sen (f.sig S) (f.sen S φ) := rfl
@[simp] theorem comp_mod (f : Comorphism A B) (g : Comorphism B C) (S : A.Sign)
    (M : C.Mod (g.sig (f.sig S))) : (f ≫ᶜ g).mod S M = f.mod S (g.mod (f.sig S) M) := rfl

/-- Comorphisms with the same signature functor are equal when their corridors are. -/
theorem ext_app {f g : Comorphism A B} (hΦ : f.Φ = g.Φ)
    (hρ : ∀ S, HEq (f.ρ.app S) (g.ρ.app S)) : f = g := by
  obtain ⟨Φ, ρ⟩ := f
  obtain ⟨Φ', ρ'⟩ := g
  cases hΦ
  have : ρ = ρ' := NatTrans.ext (funext fun S => eq_of_heq (hρ S))
  cases this
  rfl

theorem id_comp (f : Comorphism A B) : 𝟙ᶜ A ≫ᶜ f = f := rfl
theorem comp_id (f : Comorphism A B) : f ≫ᶜ 𝟙ᶜ B = f := rfl
theorem comp_assoc (f : Comorphism A B) (g : Comorphism B C) (h : Comorphism C D) :
    (f ≫ᶜ g) ≫ᶜ h = f ≫ᶜ g ≫ᶜ h := rfl

/-- Comorphisms preserve validity. -/
theorem Valid.sen (f : Comorphism A B) {S : A.Sign} {φ : A.Sen S} (h : A.Valid φ) :
    B.Valid (f.sen S φ) := fun M' => (sat_sen_iff f S M' φ).2 (h _)

end Comorphism

namespace Morphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}} {D : Institution.{u, v, w, m₁, m₂}}

/-- **The satisfaction condition** of an institution morphism, as a rewrite rule. -/
@[simp] theorem sat_sen_iff (f : Morphism A B) (S : A.Sign) (M : A.Mod S)
    (φ : B.Sen (f.sig S)) : M ⊨[A] (f.sen S φ) ↔ (f.mod S M) ⊨[B] φ :=
  (f.η.app S).sat M φ

@[simp] theorem id_sig (S : A.Sign) : (𝟙ᵐ A).sig S = S := rfl
@[simp] theorem id_sen (S : A.Sign) (φ : A.Sen S) : (𝟙ᵐ A).sen S φ = φ := rfl
@[simp] theorem id_mod (S : A.Sign) (M : A.Mod S) : (𝟙ᵐ A).mod S M = M := rfl

@[simp] theorem comp_sig (f : Morphism A B) (g : Morphism B C) (S : A.Sign) :
    (f ≫ᵐ g).sig S = g.sig (f.sig S) := rfl
@[simp] theorem comp_sen (f : Morphism A B) (g : Morphism B C) (S : A.Sign)
    (φ : C.Sen (g.sig (f.sig S))) : (f ≫ᵐ g).sen S φ = f.sen S (g.sen (f.sig S) φ) := rfl
@[simp] theorem comp_mod (f : Morphism A B) (g : Morphism B C) (S : A.Sign) (M : A.Mod S) :
    (f ≫ᵐ g).mod S M = g.mod (f.sig S) (f.mod S M) := rfl

theorem id_comp (f : Morphism A B) : 𝟙ᵐ A ≫ᵐ f = f := rfl
theorem comp_id (f : Morphism A B) : f ≫ᵐ 𝟙ᵐ B = f := rfl
theorem comp_assoc (f : Morphism A B) (g : Morphism B C) (h : Morphism C D) :
    (f ≫ᵐ g) ≫ᵐ h = f ≫ᵐ g ≫ᵐ h := rfl

end Morphism

namespace SemiComorphism

variable {A : Institution.{u₁, v₁, w, m₁, m₂}} {B : Institution.{u₂, v₂, w, m₁, m₂}}
  {C : Institution.{u₃, v₃, w, m₁, m₂}}

/-- A preserving semi-comorphism carries validity of class sentences over models of the form
`mod M'`: if every translated model satisfies `φ` then `M'` satisfies `sen φ`. -/
theorem transfer_fwd (f : SemiComorphism A B) (hf : f.Fwd) {S : A.Sign} {φ : A.Sen S}
    (hc : f.cls S φ) {M' : B.Mod (f.sig S)} (h : (f.mod S M') ⊨[A] φ) :
    M' ⊨[B] (f.sen S φ) :=
  f.sat_fwd hf S M' φ hc h

/-- A reflecting semi-comorphism carries satisfaction of translated class sentences back. -/
theorem transfer_bwd (f : SemiComorphism A B) (hf : f.Bwd) {S : A.Sign} {φ : A.Sen S}
    (hc : f.cls S φ) {M' : B.Mod (f.sig S)} (h : M' ⊨[B] (f.sen S φ)) :
    (f.mod S M') ⊨[A] φ :=
  f.sat_bwd hf S M' φ hc h

/-- A semi-comorphism in both directions relates satisfaction exactly on its class. -/
theorem sat_sen_iff (f : SemiComorphism A B) (hf : f.Fwd) (hb : f.Bwd) {S : A.Sign}
    {φ : A.Sen S} (hc : f.cls S φ) (M' : B.Mod (f.sig S)) :
    M' ⊨[B] (f.sen S φ) ↔ (f.mod S M') ⊨[A] φ :=
  ⟨f.sat_bwd hb S M' φ hc, f.sat_fwd hf S M' φ hc⟩

/-- A reflecting semi-comorphism whose model translation is surjective reflects validity of
class sentences. -/
theorem valid_of_valid_sen (f : SemiComorphism A B) (hf : f.Bwd)
    (hsurj : ∀ S (M : A.Mod S), ∃ M', f.mod S M' = M) {S : A.Sign} {φ : A.Sen S}
    (hc : f.cls S φ) (h : B.Valid (f.sen S φ)) : A.Valid φ := by
  intro M
  obtain ⟨M', rfl⟩ := hsurj S M
  exact f.sat_bwd hf S M' φ hc (h M')

/-- A preserving semi-comorphism carries validity of class sentences forwards. -/
theorem valid_sen_of_valid (f : SemiComorphism A B) (hf : f.Fwd) {S : A.Sign} {φ : A.Sen S}
    (hc : f.cls S φ) (h : A.Valid φ) : B.Valid (f.sen S φ) :=
  fun M' => f.sat_fwd hf S M' φ hc (h _)

@[simp] theorem comp_sen (f : SemiComorphism A B) (g : SemiComorphism B C) (S : A.Sign)
    (φ : A.Sen S) : (f ≫ˢ g).sen S φ = g.sen (f.sig S) (f.sen S φ) := rfl

@[simp] theorem comp_mod (f : SemiComorphism A B) (g : SemiComorphism B C) (S : A.Sign)
    (M : C.Mod (g.sig (f.sig S))) : (f ≫ˢ g).mod S M = f.mod S (g.mod (f.sig S) M) := rfl

@[simp] theorem toSemi_sen (f : Comorphism A B) (S : A.Sign) (φ : A.Sen S) :
    f.toSemi.sen S φ = f.sen S φ := rfl

@[simp] theorem toSemi_mod (f : Comorphism A B) (S : A.Sign) (M' : B.Mod (f.sig S)) :
    f.toSemi.mod S M' = f.mod S M' := rfl

/-- `toSemi` turns composition of comorphisms into composition of semi-comorphisms, on
translations. -/
theorem toSemi_comp_sen (f : Comorphism A B) (g : Comorphism B C) (S : A.Sign) (φ : A.Sen S) :
    (f ≫ᶜ g).toSemi.sen S φ = (f.toSemi ≫ˢ g.toSemi).sen S φ := rfl

end SemiComorphism

end Silmaril.Inst

/-! ## Dot notation on silmaril-typed values

The transfer lemmas, exported as aliases into silmaril's namespaces (see the end of
`Silmaril.Logic.Inst.Core.Defs`), so that `dn.sat_sen_iff P v φ` works for `dn : Inst.CoHom A B` and
`A.sat_map_iff σ M φ` for `A : Inst`. -/

namespace Silmaril.Logic.Institution.Inst

export Silmaril.Inst.Institution (sat_map_iff map_id_apply map_comp_apply reduct_id_apply
  reduct_comp_apply valid_iff valid_iff_entails)

namespace CoHom

export Silmaril.Inst.Comorphism (sat_sen_iff sen_map mod_reduct id_sig id_sen id_mod comp_sig
  comp_sen comp_mod ext_app)

end CoHom

namespace Hom

export Silmaril.Inst.Morphism (sat_sen_iff id_sig id_sen id_mod comp_sig comp_sen comp_mod)

end Hom

end Silmaril.Logic.Institution.Inst
