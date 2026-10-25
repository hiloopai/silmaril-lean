module

public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

/-!
# Faithful corridors and comorphisms

Model-expansiveness (`Corridor.ModelExpansive`) asks every source model to be *equal* to the
reduct of a target model. Many natural translations only reach every source model up to
isomorphism, or up to elementary equivalence: the comorphism from first-order logic into Common
Logic, for example, reducts a CL interpretation to the structure on its universe of discourse
(a subtype), so a structure is only *isomorphic* to such a reduct.

Borrowing only needs the weaker property (Mossakowski et al. 2014, §4.6, the maps `δ_Σ`):

* `Corridor.Faithful c`: `c` reflects semantic consequence, `αΓ ⊨ αφ → Γ ⊨ φ`;
* `Corridor.ElemExpansive c`: every source model `M` has a target model `N` whose reduct
  satisfies exactly the sentences `M` satisfies (`βN ≡ M`);
* `Corridor.ElemExpansive.faithful`: elementarily expansive corridors are faithful, hence
  (with `Corridor.entails_map`) `Γ ⊨ φ ↔ αΓ ⊨ αφ` (`Corridor.entails_map_iff_of_elemExpansive`);
* `Corridor.ModelExpansive.elemExpansive`: model-expansive corridors are elementarily
  expansive, so `Corridor.entails_map_iff` is the special case;
* `Room.IsoInvariant R`: satisfaction is invariant under isomorphism of models, and then a
  corridor reaching every model up to isomorphism (`Corridor.IsoExpansive`) is elementarily
  expansive.

The comorphism-level versions (`Inst.CoHom.Faithful`, `Inst.CoHom.ElemExpansive`,
`Inst.CoHom.entails_iff_of_elemExpansive`) apply these at every signature.

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.6
(faithful comorphisms, Theorem 1 and its proof via `δ_Σ`), p. 10;
`mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6 and Proposition 3.7.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe w m₁ m₂ u₁ v₁ u₂ v₂

namespace Room

variable (R : Room.{w, m₁, m₂})

/-- Satisfaction is invariant under isomorphism of models. -/
def IsoInvariant : Prop := ∀ (M N : R.Mod), Nonempty (M ≅ N) → ∀ φ, R.Sat M φ ↔ R.Sat N φ

end Room

namespace Corridor

variable {R₁ R₂ : Room.{w, m₁, m₂}} (c : R₁ ⟶ R₂)

/-- A corridor is faithful when it reflects semantic consequence.

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.6, p. 10
("faithfulness ... ensures we can borrow proofs"). -/
def Faithful : Prop :=
  ∀ (Γ : Set R₁.Sen) (φ : R₁.Sen), R₂.Entails (c.sen '' Γ) (c.sen φ) → R₁.Entails Γ φ

/-- A corridor is elementarily expansive when every source model is elementarily equivalent to
the reduct of a target model.

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.6, proof
of Theorem 1, p. 10 (the map `δ_Σ` with `M ⊨ e ↔ δ_Σ(M) ⊨ α(e)`). -/
def ElemExpansive : Prop :=
  ∀ M : R₁.Mod, ∃ N : R₂.Mod, ∀ φ : R₁.Sen, R₁.Sat (c.mod.obj N) φ ↔ R₁.Sat M φ

/-- A corridor is expansive up to isomorphism when every source model is isomorphic to the
reduct of a target model. -/
def IsoExpansive : Prop := ∀ M : R₁.Mod, ∃ N : R₂.Mod, Nonempty (c.mod.obj N ≅ M)

variable {c}

/-- Model-expansive corridors are elementarily expansive. -/
theorem ModelExpansive.elemExpansive (hc : ModelExpansive c) : ElemExpansive c := by
  intro M
  obtain ⟨N, rfl⟩ := hc M
  exact ⟨N, fun _ => Iff.rfl⟩

/-- Corridors expansive up to isomorphism into an isomorphism-invariant room are elementarily
expansive. -/
theorem IsoExpansive.elemExpansive (hR : R₁.IsoInvariant) (hc : IsoExpansive c) :
    ElemExpansive c := by
  intro M
  obtain ⟨N, e⟩ := hc M
  exact ⟨N, fun φ => hR _ _ e φ⟩

/-- Elementarily expansive corridors are faithful.

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.6, proof
of Theorem 1, p. 10. -/
theorem ElemExpansive.faithful (hc : ElemExpansive c) : Faithful c := by
  intro Γ φ h M hM
  obtain ⟨N, hN⟩ := hc M
  refine (hN φ).1 ((c.sat N φ).1 (h N ?_))
  rintro _ ⟨χ, hχ, rfl⟩
  exact (c.sat N χ).2 ((hN χ).2 (hM χ hχ))

/-- Borrowing along a faithful corridor: `Γ ⊨ φ ↔ αΓ ⊨ αφ`. -/
theorem entails_map_iff_of_faithful (hc : Faithful c) (Γ : Set R₁.Sen) (φ : R₁.Sen) :
    R₁.Entails Γ φ ↔ R₂.Entails (c.sen '' Γ) (c.sen φ) :=
  ⟨c.entails_map, hc Γ φ⟩

/-- Borrowing along an elementarily expansive corridor. -/
theorem entails_map_iff_of_elemExpansive (hc : ElemExpansive c) (Γ : Set R₁.Sen)
    (φ : R₁.Sen) : R₁.Entails Γ φ ↔ R₂.Entails (c.sen '' Γ) (c.sen φ) :=
  entails_map_iff_of_faithful hc.faithful Γ φ

/-- Elementarily expansive corridors compose. -/
theorem ElemExpansive.comp {R₃ : Room.{w, m₁, m₂}} {c : R₁ ⟶ R₂} {d : R₂ ⟶ R₃}
    (hc : ElemExpansive c) (hd : ElemExpansive d) : ElemExpansive (c ≫ d) := by
  intro M
  obtain ⟨N, hN⟩ := hc M
  obtain ⟨P, hP⟩ := hd N
  exact ⟨P, fun φ => (c.sat (d.mod.obj P) φ).symm.trans ((hP (c.sen φ)).trans
    ((c.sat N φ).trans (hN φ)))⟩

end Corridor

namespace Inst

variable {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}

/-- A comorphism is faithful when every corridor reflects semantic consequence.

Source: `mossakowski-et-al-2014-proof-support-common-logic` in `references.bib`, §4.6, p. 10. -/
def CoHom.Faithful (f : CoHom A B) : Prop := ∀ S : A.Sign, Corridor.Faithful (f.ρ.app S)

/-- A comorphism is elementarily expansive when every corridor is. -/
def CoHom.ElemExpansive (f : CoHom A B) : Prop :=
  ∀ S : A.Sign, Corridor.ElemExpansive (f.ρ.app S)

theorem CoHom.ModelExpansive.elemExpansive {f : CoHom A B} (hf : f.ModelExpansive) :
    f.ElemExpansive :=
  fun S => (hf S).elemExpansive

theorem CoHom.ElemExpansive.faithful {f : CoHom A B} (hf : f.ElemExpansive) : f.Faithful :=
  fun S => (hf S).faithful

/-- Borrowing along an elementarily expansive comorphism; `CoHom.entails_iff` is the
model-expansive special case. -/
theorem CoHom.entails_iff_of_elemExpansive (f : CoHom A B) (hf : f.ElemExpansive) (S : A.Sign)
    (Γ : Set (A.I.obj S).Sen) (φ : (A.I.obj S).Sen) :
    (A.I.obj S).Entails Γ φ ↔
      (B.I.obj (f.Φ.obj S)).Entails ((f.ρ.app S).sen '' Γ) ((f.ρ.app S).sen φ) :=
  Corridor.entails_map_iff_of_elemExpansive (hf S) Γ φ

end Inst

end Silmaril.Logic.Institution
