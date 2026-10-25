module

public import Silmaril.Logic.Institution.Morphism

@[expose] public section

/-!
# Borrowing

A comorphism `(Φ, ρ) : A → B` translates every `A`-signature `Σ` into a `B`-signature `ΦΣ`
and every `Σ`-sentence into a `ΦΣ`-sentence. Its corridors always preserve semantic
consequence; when every `A`-model is the reduct of a `B`-model (the comorphism is
*model-expansive*), they also reflect it:

  `Γ ⊨_Σ φ  ↔  ρ(Γ) ⊨_{ΦΣ} ρ(φ)`.

So a decision procedure, prover or consequence relation for `B` can be "borrowed" for `A`
(Cerioli–Meseguer 1997, *May I borrow your logic?*, cited by Goguen–Roşu §4 and
Mossakowski–Diaconescu–Tarlecki §4). Goguen and Burstall's Proposition 35 is the same statement
for an institution morphism whose model translations are surjective ("sound" morphisms).

In the room view all of these are the single-room lemma `Corridor.entails_map_iff`, applied to
the components of a natural transformation of room functors.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe w m₁ m₂ u₁ v₁ u₂ v₂

namespace Inst

variable {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}

/-- A comorphism is model-expansive when each model translation is surjective on objects.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6, lifted to comorphisms in §4.1 ("easily lift from the non-indexed to the indexed
level"). -/
def CoHom.ModelExpansive (f : CoHom A B) : Prop :=
  ∀ S : A.Sign, Corridor.ModelExpansive (f.ρ.app S)

/-- Comorphisms preserve semantic consequence.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7 (first part), at each signature. -/
theorem CoHom.entails_map (f : CoHom A B) {S : A.Sign} {Γ : Set (A.I.obj S).Sen}
    {φ : (A.I.obj S).Sen} (h : (A.I.obj S).Entails Γ φ) :
    (B.I.obj (f.Φ.obj S)).Entails ((f.ρ.app S).sen '' Γ) ((f.ρ.app S).sen φ) :=
  (f.ρ.app S).entails_map h

/-- Borrowing: a model-expansive comorphism preserves and reflects semantic consequence.

Source: Cerioli and Meseguer 1997, *May I borrow your logic?* (citation only);
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7, lifted to comorphisms in §4.1;
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, after Theorem 4.4. -/
theorem CoHom.entails_iff (f : CoHom A B) (hf : f.ModelExpansive) (S : A.Sign)
    (Γ : Set (A.I.obj S).Sen) (φ : (A.I.obj S).Sen) :
    (A.I.obj S).Entails Γ φ ↔
      (B.I.obj (f.Φ.obj S)).Entails ((f.ρ.app S).sen '' Γ) ((f.ρ.app S).sen φ) :=
  (f.ρ.app S).entails_map_iff (hf S) Γ φ

/-- Borrowing a consequence checker: if `P` decides (characterizes) semantic consequence in `B`,
then `P` composed with the translation characterizes semantic consequence in `A`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, after
Theorem 4.4 (re-use of theorem provers via borrowing, after Cerioli and Meseguer 1997). -/
theorem CoHom.borrow (f : CoHom A B) (hf : f.ModelExpansive)
    (P : ∀ S' : B.Sign, Set (B.I.obj S').Sen → (B.I.obj S').Sen → Prop)
    (hP : ∀ S' Γ' φ', P S' Γ' φ' ↔ (B.I.obj S').Entails Γ' φ') (S : A.Sign)
    (Γ : Set (A.I.obj S).Sen) (φ : (A.I.obj S).Sen) :
    (A.I.obj S).Entails Γ φ ↔ P (f.Φ.obj S) ((f.ρ.app S).sen '' Γ) ((f.ρ.app S).sen φ) :=
  (f.entails_iff hf S Γ φ).trans (hP _ _ _).symm

/-- Comorphisms translate closures into closures: `ρ(Γ•) ⊆ ρ(Γ)•` and `ρ(Γ•)• = ρ(Γ)•`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §5.1,
Proposition 5.8. -/
theorem CoHom.image_closure_subset (f : CoHom A B) (S : A.Sign) (Γ : Set (A.I.obj S).Sen) :
    (f.ρ.app S).sen '' (A.I.obj S).closure Γ ⊆
      (B.I.obj (f.Φ.obj S)).closure ((f.ρ.app S).sen '' Γ) :=
  (f.ρ.app S).image_closure_subset Γ

/-- An institution morphism is sound when each model translation is surjective on objects.

Source: `goguen-burstall-1992` in `references.bib`, §4.1, Definition 34. -/
def Hom.Sound (f : Hom A B) : Prop :=
  ∀ S : A.Sign, Corridor.ModelExpansive (f.η.app S)

/-- Borrowing along a sound institution morphism: for `Σ' = ΦΣ`, a `Σ'`-sentence `e'` follows
from `E'` iff `η_Σ(e')` follows from `η_Σ(E')`.

Source: `goguen-burstall-1992` in `references.bib`, §4.1, Proposition 35;
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Theorem 4.4. -/
theorem Hom.entails_iff (f : Hom A B) (hf : f.Sound) (S : A.Sign)
    (E' : Set (B.I.obj (f.Φ.obj S)).Sen) (e' : (B.I.obj (f.Φ.obj S)).Sen) :
    (B.I.obj (f.Φ.obj S)).Entails E' e' ↔
      (A.I.obj S).Entails ((f.η.app S).sen '' E') ((f.η.app S).sen e') :=
  (f.η.app S).entails_map_iff (hf S) E' e'

end Inst

end Silmaril.Logic.Institution
