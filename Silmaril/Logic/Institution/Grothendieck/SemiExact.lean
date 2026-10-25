module

public import Silmaril.Logic.Institution.Grothendieck.Amalgamation
public import Silmaril.Logic.Institution.Grothendieck.Pushout
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

/-!
# Semi-exactness of comorphism-based Grothendieck institutions

For an indexed coinstitution `F : Ind ⥤ CoIns` the three conditions of Diaconescu's Theorem 5 and
Mossakowski's Proposition 3.5 are `LocallySemiExact F` (every component is semi-exact),
`IndexSemiExact F` (pushouts of indices give pullbacks of model categories along the
comorphisms) and `AllExact F` (every comorphism is exact).

* `IndexedCoInst.amalgamates_flat` is the core of the sufficiency proof. A canonical
  Grothendieck square splits into four squares: the index square, two exactness squares and a
  pushout in one component. If each of the four amalgamates, so does the whole square.
* `IndexedCoInst.semiExact_flat_iff` is the characterisation: the flattening is semi-exact iff
  all three conditions hold.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory Limits

universe u₀ v₀ u v w m₁ m₂

/-! ### Model reduct functors -/

section ModHom

variable {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})

/-- Model reducts are contravariantly functorial.

Source: `goguen-burstall-1992` in `references.bib`, §2.5, Definition 12 (the
model functor `𝒥 ; Left`). -/
theorem modHom_comp {S₁ S₂ S₃ : Sign} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    modHom I (f ≫ g) = modHom I g ≫ modHom I f := by
  simp only [modHom, Functor.map_comp, Room.comp_mod]
  rfl

/-- The model reduct of an identity is the identity.

Source: `goguen-burstall-1992` in `references.bib`, §2.5, Definition 12. -/
theorem modHom_id (S : Sign) : modHom I (𝟙 S) = 𝟙 _ :=
  congrArg (fun c : I.obj S ⟶ I.obj S => Cat.Hom.ofFunctor c.mod) (I.map_id S)

/-- Pullback squares are invariant under equality of their edges. -/
theorem isPullback_congr {C : Type u} [Category.{v} C] {P X Y Z : C} {a a' : P ⟶ X}
    {b b' : P ⟶ Y} {c c' : X ⟶ Z} {d d' : Y ⟶ Z} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') : IsPullback a b c d ↔ IsPullback a' b' c' d' := by
  subst ha hb hc hd
  rfl

variable {I}

/-- Amalgamation squares flip. -/
theorem Amalgamates.flip {S S₁ S₂ S' : Sign} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂} {g₁ : S₁ ⟶ S'}
    {g₂ : S₂ ⟶ S'} (h : Amalgamates I f₁ f₂ g₁ g₂) : Amalgamates I f₂ f₁ g₂ g₁ :=
  IsPullback.flip h

/-- Amalgamation squares paste horizontally (in the layout of `IsPushout.paste_horiz`).

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Theorem 5 (printed page 14, PDF page 15: "composing the four pullback squares"). -/
theorem Amalgamates.paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : Sign} {h₁₁ : X₁₁ ⟶ X₁₂}
    {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X₁₁ ⟶ X₂₁}
    {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃} (s : Amalgamates I h₁₁ v₁₁ v₁₂ h₂₁)
    (t : Amalgamates I h₁₂ v₁₂ v₁₃ h₂₂) :
    Amalgamates I (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) := by
  unfold Amalgamates at *
  rw [modHom_comp, modHom_comp]
  exact IsPullback.paste_vert t s

/-- Amalgamation squares paste vertically (in the layout of `IsPushout.paste_vert`).

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Theorem 5 (printed page 14, PDF page 15). -/
theorem Amalgamates.paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : Sign} {h₁₁ : X₁₁ ⟶ X₁₂}
    {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂}
    {v₂₁ : X₂₁ ⟶ X₃₁} {v₂₂ : X₂₂ ⟶ X₃₂} (s : Amalgamates I h₁₁ v₁₁ v₁₂ h₂₁)
    (t : Amalgamates I h₂₁ v₂₁ v₂₂ h₃₁) :
    Amalgamates I h₁₁ (v₁₁ ≫ v₂₁) (v₁₂ ≫ v₂₂) h₃₁ :=
  (Amalgamates.paste_horiz s.flip t.flip).flip

/-- Amalgamation only depends on the span of a pushout square: two pushouts of the same span
amalgamate together (their apexes are isomorphic, and so are their model categories).

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3
(PDF page 5: "semi-exact, if any pushout of signatures is (weakly) amalgamable"). -/
theorem Amalgamates.of_isPushout {S S₁ S₂ S' S'' : Sign} {f₁ : S ⟶ S₁} {f₂ : S ⟶ S₂}
    {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'} {g₁' : S₁ ⟶ S''} {g₂' : S₂ ⟶ S''}
    (h : IsPushout f₁ f₂ g₁ g₂) (h' : IsPushout f₁ f₂ g₁' g₂') (ha : Amalgamates I f₁ f₂ g₁ g₂) :
    Amalgamates I f₁ f₂ g₁' g₂' := by
  obtain ⟨e, he₁, he₂⟩ : ∃ e : S' ≅ S'', g₁ ≫ e.hom = g₁' ∧ g₂ ≫ e.hom = g₂' :=
    ⟨h.isoIsPushout _ _ h', by simp, by simp⟩
  have e₁ : g₁' ≫ e.inv = g₁ := by rw [Iso.comp_inv_eq, he₁]
  have e₂ : g₂' ≫ e.inv = g₂ := by rw [Iso.comp_inv_eq, he₂]
  let m : (I.obj S').Mod ≅ (I.obj S'').Mod :=
    { hom := modHom I e.inv
      inv := modHom I e.hom
      hom_inv_id := by rw [← modHom_comp, e.hom_inv_id, modHom_id]
      inv_hom_id := by rw [← modHom_comp, e.inv_hom_id, modHom_id] }
  refine IsPullback.of_iso ha m (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, m]
    rw [← modHom_comp, e₁]
  · simp only [Iso.refl_hom, Category.comp_id, m]
    rw [← modHom_comp, e₂]
  · simp
  · simp

/-- `Amalgamates.of_isPushout`, with the span given up to equality. -/
theorem Amalgamates.of_isPushout' {S S₁ S₂ S' S'' : Sign} {f₁ f₁' : S ⟶ S₁} {f₂ f₂' : S ⟶ S₂}
    {g₁ : S₁ ⟶ S'} {g₂ : S₂ ⟶ S'} {g₁' : S₁ ⟶ S''} {g₂' : S₂ ⟶ S''}
    (h : IsPushout f₁' f₂' g₁ g₂) (ha : Amalgamates I f₁' f₂' g₁ g₂)
    (h' : IsPushout f₁ f₂ g₁' g₂') (e₁ : f₁ = f₁') (e₂ : f₂ = f₂') :
    Amalgamates I f₁ f₂ g₁' g₂' := by
  subst e₁ e₂
  exact Amalgamates.of_isPushout h h' ha

end ModHom

/-- The exactness square of a comorphism at `σ`, with the corner `Φ(Σ)` replaced by an equal
signature `T`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3
(PDF page 5: the naturality diagram in the definition of an exact comorphism). -/
theorem Inst.CoHom.exactSquare_transport_iff {A B : Inst.{u, v, w, m₁, m₂}}
    (f : Inst.CoHom A B) {S S₁ : A.Sign} (σ : S ⟶ S₁) {T : B.Sign} (h : T = f.Φ.obj S) :
    IsPullback (Cat.Hom.ofFunctor (f.ρ.app S₁).mod) (modHom B.I (eqToHom h ≫ f.Φ.map σ))
        (modHom A.I σ) (modHom B.I (eqToHom h.symm) ≫ Cat.Hom.ofFunctor (f.ρ.app S).mod) ↔
      IsPullback (modHom B.I (f.Φ.map σ)) (Cat.Hom.ofFunctor (f.ρ.app S₁).mod)
        (Cat.Hom.ofFunctor (f.ρ.app S).mod) (modHom A.I σ) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, modHom_id]
  exact IsPullback.flip_iff

/-- The exactness square of an exact comorphism at `σ`, with the corner `Φ(Σ)` replaced by an
equal signature `T`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3
(PDF page 5: the naturality diagram in the definition of an exact comorphism). -/
theorem Inst.CoHom.Exact.transport {A B : Inst.{u, v, w, m₁, m₂}} {f : Inst.CoHom A B}
    (hf : f.Exact) {S S₁ : A.Sign} (σ : S ⟶ S₁) {T : B.Sign} (h : T = f.Φ.obj S) :
    IsPullback (Cat.Hom.ofFunctor (f.ρ.app S₁).mod) (modHom B.I (eqToHom h ≫ f.Φ.map σ))
      (modHom A.I σ) (modHom B.I (eqToHom h.symm) ≫ Cat.Hom.ofFunctor (f.ρ.app S).mod) :=
  (Inst.CoHom.exactSquare_transport_iff f σ h).2 (hf σ)

/-! ### Amalgamation in comorphism-based Grothendieck institutions -/

namespace IndexedCoInst

variable {Ind : Type u₀} [Category.{v₀} Ind] (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂})

/-- The model reduct of a Grothendieck signature morphism `(d, σ)` is the reduct along `σ`
followed by the comorphism model translation.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Definition
3.1 (PDF page 4, last item). -/
theorem modHom_flat {X Y : FlatSig F} (f : X ⟶ Y) :
    modHom (flat F) f = modHom (inst F Y.base).I f.fiber ≫
      Cat.Hom.ofFunctor ((coHom F f.base).ρ.app X.fiber).mod :=
  rfl

/-- The flattening restricted along a fiber inclusion is the component.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Proposition 2 (printed page 12, PDF page 13). -/
theorem flat_map_ι (i : Ind) {S S' : (inst F i).Sign} (f : S ⟶ S') :
    (flat F).map ((ι F i).Φ.map f) = (inst F i).I.map f :=
  (Category.id_comp _).symm.trans (((ι F i).ρ.naturality f).symm.trans (Category.comp_id _))

/-- The model reducts of the flattening along a fiber inclusion are those of the component.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Proposition 2 (printed page 12, PDF page 13). -/
theorem modHom_flat_ι (i : Ind) {S S' : (inst F i).Sign} (f : S ⟶ S') :
    modHom (flat F) ((ι F i).Φ.map f) = modHom (inst F i).I f :=
  congrArg (fun c => Cat.Hom.ofFunctor c.mod) (flat_map_ι F i f)

/-- The naturality square of a cocartesian lift `(d, 𝟙)` along `σ` amalgamates in the
flattening iff the naturality square of the model translation of `F d` at `σ` is a pullback
(the exactness square of `Inst.CoHom.Exact`).

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Theorem 5 (printed page 14, PDF page 15: the up-right and down-left
squares are mapped to pullbacks "because the institution embeddings … are exact"). -/
theorem amalgamates_cocart_iff {i j : Ind} (d : i ⟶ j) {S S₁ : (inst F i).Sign} (σ : S ⟶ S₁)
    {T : (inst F j).Sign} (p : (coHom F d).Φ.obj S = T) :
    Amalgamates (flat F) ((ι F i).Φ.map σ) (⟨d, eqToHom p⟩ : (⟨i, S⟩ : FlatSig F) ⟶ ⟨j, T⟩)
        (⟨d, 𝟙 _⟩ : (⟨i, S₁⟩ : FlatSig F) ⟶ ⟨j, (coHom F d).Φ.obj S₁⟩)
        ((ι F j).Φ.map (eqToHom p.symm ≫ (coHom F d).Φ.map σ)) ↔
      IsPullback (modHom (inst F j).I ((coHom F d).Φ.map σ))
        (Cat.Hom.ofFunctor ((coHom F d).ρ.app S₁).mod)
        (Cat.Hom.ofFunctor ((coHom F d).ρ.app S).mod) (modHom (inst F i).I σ) := by
  have e₁ : modHom (flat F)
      (⟨d, 𝟙 _⟩ : (⟨i, S₁⟩ : FlatSig F) ⟶ ⟨j, (coHom F d).Φ.obj S₁⟩) =
      Cat.Hom.ofFunctor ((coHom F d).ρ.app S₁).mod :=
    calc _ = modHom (inst F j).I (𝟙 ((coHom F d).Φ.obj S₁)) ≫
          Cat.Hom.ofFunctor ((coHom F d).ρ.app S₁).mod := rfl
      _ = _ := by rw [modHom_id, Category.id_comp]
  have e₄ : modHom (flat F) (⟨d, eqToHom p⟩ : (⟨i, S⟩ : FlatSig F) ⟶ ⟨j, T⟩) =
      modHom (inst F j).I (eqToHom p) ≫ Cat.Hom.ofFunctor ((coHom F d).ρ.app S).mod := rfl
  exact (isPullback_congr e₁ (modHom_flat_ι F j _) (modHom_flat_ι F i σ) e₄).trans
    (Inst.CoHom.exactSquare_transport_iff (coHom F d) σ p.symm)

/-- The index square `d₁ ≫ e₁ = d₂ ≫ e₂` *amalgamates at `Σ`* when the flattening amalgamates
the square of Grothendieck signatures with corners `(i, Σ)`, `(i₁, Φ^{d₁}Σ)`, `(i₂, Φ^{d₂}Σ)`,
`(j, Φ^{d₁≫e₁}Σ)` and identity fiber components (up to `Φ^{e}Φ^{d} = Φ^{d≫e}`). Its model
square is `Modⁱ(Σ) ← Mod^{i₁}(Φ^{d₁}Σ) ← Mod^j(…) → Mod^{i₂}(Φ^{d₂}Σ) → Modⁱ(Σ)`, with the
comorphism model translations as edges.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: the square of `β`'s in the definition of a "(weakly) semi-exact" indexed coinstitution);
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
Definition 15 (printed page 13, PDF page 14). -/
def IndexAmalgamates {i i₁ i₂ j : Ind} (d₁ : i ⟶ i₁) (d₂ : i ⟶ i₂) (e₁ : i₁ ⟶ j) (e₂ : i₂ ⟶ j)
    (hsq : d₁ ≫ e₁ = d₂ ≫ e₂) (S : (inst F i).Sign) : Prop :=
  Amalgamates (flat F)
    (⟨d₁, 𝟙 _⟩ : (⟨i, S⟩ : FlatSig F) ⟶ ⟨i₁, (coHom F d₁).Φ.obj S⟩)
    (⟨d₂, 𝟙 _⟩ : (⟨i, S⟩ : FlatSig F) ⟶ ⟨i₂, (coHom F d₂).Φ.obj S⟩)
    (⟨e₁, eqToHom (congrArg (fun g => g.Φ.obj S) (coHom_comp F d₁ e₁).symm)⟩ :
      (⟨i₁, (coHom F d₁).Φ.obj S⟩ : FlatSig F) ⟶ ⟨j, (coHom F (d₁ ≫ e₁)).Φ.obj S⟩)
    (⟨e₂, eqToHom (congrArg (fun g => g.Φ.obj S)
        ((coHom_comp F d₂ e₂).symm.trans (congrArg (coHom F) hsq.symm)))⟩ :
      (⟨i₂, (coHom F d₂).Φ.obj S⟩ : FlatSig F) ⟶ ⟨j, (coHom F (d₁ ≫ e₁)).Φ.obj S⟩)

/-- Every component is semi-exact.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "(weakly) locally semi-exact, if each institution `Iⁱ` is (weakly) semi-exact");
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
Definition 14 (printed page 12, PDF page 13). -/
def LocallySemiExact : Prop := ∀ i : Ind, SemiExact (inst F i).I

/-- Every pushout square of indices amalgamates at every signature.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3 (PDF
page 5: "(weakly) semi-exact if for each pullback in `Ind` … the square … is a (weak) pullback
for each signature `Σ`"; a pullback in Mossakowski's `Ind` is a pushout in our `Ind = Ind*`);
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
Definition 15 (printed page 13, PDF page 14). -/
def IndexSemiExact : Prop :=
  ∀ ⦃i i₁ i₂ j : Ind⦄ (d₁ : i ⟶ i₁) (d₂ : i ⟶ i₂) (e₁ : i₁ ⟶ j) (e₂ : i₂ ⟶ j)
    (h : IsPushout d₁ d₂ e₁ e₂) (S : (inst F i).Sign), IndexAmalgamates F d₁ d₂ e₁ e₂ h.w S

/-- Every comorphism of the diagram is exact.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Proposition 3.5, third condition (PDF page 5). -/
def AllExact : Prop := ∀ ⦃i j : Ind⦄ (d : i ⟶ j), (coHom F d).Exact

/-- **Amalgamation for comorphism-based Grothendieck institutions** (one square).

Let `(d₁, σ₁) : (i, Σ) ⟶ (i₁, Σ₁)`, `(d₂, σ₂) : (i, Σ) ⟶ (i₂, Σ₂)`, `(e₁, θ₁) : (i₁, Σ₁) ⟶ (j, Σ')`
and `(e₂, θ₂) : (i₂, Σ₂) ⟶ (j, Σ')` be Grothendieck signature morphisms over a commuting index
square. The square splits into four: the index square at `Σ`, the exactness squares of `F e₁`
at `σ₁` and of `F e₂` at `σ₂`, and the transported fiber square in `Sign_j`. If

* the index square amalgamates at `Σ`,
* `F e₁` and `F e₂` are exact,
* `F j` is semi-exact, and
* the transported fiber square `Φ^{d₁≫e₁}Σ ⟶ Φ^{e₁}Σ₁, Φ^{e₂}Σ₂ ⟶ Σ'` is a pushout in `Sign_j`,

then the square amalgamates in the Grothendieck institution, by pasting the four pullbacks.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Theorem 5, sufficiency (printed page 14, PDF page 15: "the pushout square of extra
signature morphisms can be expressed as the following composition of four pushout squares");
`mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Proposition 3.5
(PDF page 5) and its proof (PDF page 13). -/
theorem amalgamates_flat {i i₁ i₂ j : Ind} (d₁ : i ⟶ i₁) (d₂ : i ⟶ i₂) (e₁ : i₁ ⟶ j)
    (e₂ : i₂ ⟶ j) (hsq : d₁ ≫ e₁ = d₂ ≫ e₂) {S : (inst F i).Sign} {S₁ : (inst F i₁).Sign}
    {S₂ : (inst F i₂).Sign} {S' : (inst F j).Sign} (σ₁ : (coHom F d₁).Φ.obj S ⟶ S₁)
    (σ₂ : (coHom F d₂).Φ.obj S ⟶ S₂) (θ₁ : (coHom F e₁).Φ.obj S₁ ⟶ S')
    (θ₂ : (coHom F e₂).Φ.obj S₂ ⟶ S')
    (hidx : IndexAmalgamates F d₁ d₂ e₁ e₂ hsq S)
    (he₁ : (coHom F e₁).Exact) (he₂ : (coHom F e₂).Exact)
    (hj : SemiExact (inst F j).I)
    (hfib : IsPushout
      (eqToHom (congrArg (fun g => g.Φ.obj S) (coHom_comp F d₁ e₁)) ≫ (coHom F e₁).Φ.map σ₁ :
        (coHom F (d₁ ≫ e₁)).Φ.obj S ⟶ (coHom F e₁).Φ.obj S₁)
      (eqToHom (congrArg (fun g => g.Φ.obj S)
          ((congrArg (coHom F) hsq).trans (coHom_comp F d₂ e₂))) ≫ (coHom F e₂).Φ.map σ₂ :
        (coHom F (d₁ ≫ e₁)).Φ.obj S ⟶ (coHom F e₂).Φ.obj S₂)
      θ₁ θ₂) :
    Amalgamates (flat F)
      (⟨d₁, σ₁⟩ : (⟨i, S⟩ : FlatSig F) ⟶ ⟨i₁, S₁⟩)
      (⟨d₂, σ₂⟩ : (⟨i, S⟩ : FlatSig F) ⟶ ⟨i₂, S₂⟩)
      (⟨e₁, θ₁⟩ : (⟨i₁, S₁⟩ : FlatSig F) ⟶ ⟨j, S'⟩)
      (⟨e₂, θ₂⟩ : (⟨i₂, S₂⟩ : FlatSig F) ⟶ ⟨j, S'⟩) := by
  have TL : Amalgamates (inst F j).I _ _ θ₁ θ₂ := hj _ _ _ _ hfib
  have TR := he₁.transport σ₁ (T := (coHom F (d₁ ≫ e₁)).Φ.obj S)
    (congrArg (fun g => g.Φ.obj S) (coHom_comp F d₁ e₁))
  have BL := (he₂.transport σ₂ (T := (coHom F (d₁ ≫ e₁)).Φ.obj S)
    (congrArg (fun g => g.Φ.obj S) ((congrArg (coHom F) hsq).trans (coHom_comp F d₂ e₂)))).flip
  have BR := hidx
  unfold IndexAmalgamates Amalgamates at BR
  have top := IsPullback.paste_horiz TL TR
  have bot := IsPullback.paste_horiz BL BR
  have hall := IsPullback.paste_vert top bot
  have e₁ : modHom (inst F i₁).I σ₁ ≫ modHom (inst F i₁).I (𝟙 ((coHom F d₁).Φ.obj S)) ≫
      Cat.Hom.ofFunctor ((coHom F d₁).ρ.app S).mod =
      modHom (inst F i₁).I σ₁ ≫ Cat.Hom.ofFunctor ((coHom F d₁).ρ.app S).mod := by
    rw [modHom_id, Category.id_comp]
  have e₂ : modHom (inst F i₂).I σ₂ ≫ modHom (inst F i₂).I (𝟙 ((coHom F d₂).Φ.obj S)) ≫
      Cat.Hom.ofFunctor ((coHom F d₂).ρ.app S).mod =
      modHom (inst F i₂).I σ₂ ≫ Cat.Hom.ofFunctor ((coHom F d₂).ρ.app S).mod := by
    rw [modHom_id, Category.id_comp]
  exact (isPullback_congr rfl rfl e₁ e₂).1 hall

/-- Within a single component, the flattening amalgamates a square of fiber morphisms iff the
component does: the fiber inclusion has identity corridors.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Proposition 2 (printed page 12, PDF page 13: "the model functor `MODⁱ` is the restriction
`MOD♯((i, −))`"). -/
theorem amalgamates_ι_iff (i : Ind) {S S₁ S₂ S' : (inst F i).Sign} (f₁ : S ⟶ S₁) (f₂ : S ⟶ S₂)
    (g₁ : S₁ ⟶ S') (g₂ : S₂ ⟶ S') :
    Amalgamates (flat F) ((ι F i).Φ.map f₁) ((ι F i).Φ.map f₂) ((ι F i).Φ.map g₁)
        ((ι F i).Φ.map g₂) ↔
      Amalgamates (inst F i).I f₁ f₂ g₁ g₂ :=
  isPullback_congr (modHom_flat_ι F i g₁) (modHom_flat_ι F i g₂) (modHom_flat_ι F i f₁)
    (modHom_flat_ι F i f₂)

/-- **Semi-exactness of comorphism-based Grothendieck institutions.** For an indexed
coinstitution with pushouts of indices and of signatures, whose signature translations preserve
pushouts, the Grothendieck institution is semi-exact iff the indexed coinstitution is locally
semi-exact, semi-exact, and all its comorphisms are exact.

Mossakowski's Proposition 3.5 assumes cocontinuous signature
translations and no existence of pushouts. Here the translations only need to preserve
pushouts, and pushouts of indices and of component signatures are assumed to exist, so that
the pushouts of the Grothendieck signature category are the canonical ones (Mossakowski,
Proposition 3.4). As in Diaconescu's Definition 5, (semi-)exactness means pullbacks in `Cat`
(model homomorphisms included), not only unique amalgamation of models. The index category is
Mossakowski's `Ind*`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Proposition 3.5 (PDF page 5) with Proposition 3.4 (PDF page 5);
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
Theorem 5 (printed page 13, PDF page 14), for embedding-indexed institutions. -/
theorem semiExact_flat_iff [HasPushouts Ind] [∀ i : Ind, HasPushouts (inst F i).Sign]
    (hΦ : ∀ ⦃i j : Ind⦄ (d : i ⟶ j), PreservesColimitsOfShape WalkingSpan (coHom F d).Φ) :
    SemiExact (flat F) ↔ LocallySemiExact F ∧ IndexSemiExact F ∧ AllExact F := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · unfold LocallySemiExact SemiExact
      intro i S S₁ S₂ S' f₁ f₂ g₁ g₂ hP
      exact (amalgamates_ι_iff F i f₁ f₂ g₁ g₂).1
        (h _ _ _ _ (GrothendieckPushout.isPushout_vert (G := sign F) hP (fun u => hΦ u)))
    · unfold IndexSemiExact
      intro i i₁ i₂ j d₁ d₂ e₁ e₂ hI S
      exact h _ _ _ _ (GrothendieckPushout.isPushout_index (G := sign F) hI S
        (congrArg (fun g => g.Φ.obj S) (coHom_comp F d₁ e₁).symm)
        (congrArg (fun g => g.Φ.obj S)
          ((coHom_comp F d₂ e₂).symm.trans (congrArg (coHom F) hI.w.symm))))
    · unfold AllExact Inst.CoHom.Exact
      intro i j d S S' σ
      have hA := h _ _ _ _ (GrothendieckPushout.isPushout_cocart (G := sign F) d σ
        (T := (coHom F d).Φ.obj S) rfl)
      exact (amalgamates_cocart_iff F d σ rfl).1 hA
  · rintro ⟨hloc, hidx, hex⟩
    unfold SemiExact
    intro X X₁ X₂ Y f₁ f₂ g₁ g₂ hP
    obtain ⟨j, e₁, e₂, hI⟩ : ∃ (j : Ind) (e₁ : X₁.base ⟶ j) (e₂ : X₂.base ⟶ j),
        IsPushout f₁.base f₂.base e₁ e₂ :=
      ⟨_, _, _, IsPushout.of_hasPushout f₁.base f₂.base⟩
    have p₁ : (coHom F e₁).Φ.obj ((coHom F f₁.base).Φ.obj X.fiber) =
        (coHom F (f₁.base ≫ e₁)).Φ.obj X.fiber :=
      congrArg (fun g => g.Φ.obj X.fiber) (coHom_comp F f₁.base e₁).symm
    have p₂ : (coHom F e₂).Φ.obj ((coHom F f₂.base).Φ.obj X.fiber) =
        (coHom F (f₁.base ≫ e₁)).Φ.obj X.fiber :=
      congrArg (fun g => g.Φ.obj X.fiber)
        ((coHom_comp F f₂.base e₂).symm.trans (congrArg (coHom F) hI.w.symm))
    obtain ⟨S', θ₁, θ₂, hfib⟩ : ∃ (S' : (inst F j).Sign)
        (θ₁ : (coHom F e₁).Φ.obj X₁.fiber ⟶ S') (θ₂ : (coHom F e₂).Φ.obj X₂.fiber ⟶ S'),
        IsPushout (eqToHom p₁.symm ≫ (coHom F e₁).Φ.map f₁.fiber)
          (eqToHom p₂.symm ≫ (coHom F e₂).Φ.map f₂.fiber) θ₁ θ₂ :=
      ⟨_, _, _, IsPushout.of_hasPushout _ _⟩
    have pTL := GrothendieckPushout.isPushout_index (G := sign F) hI X.fiber p₁ p₂
    have aTL : Amalgamates (flat F) _ _ _ _ := hidx f₁.base f₂.base e₁ e₂ hI X.fiber
    have pTR := GrothendieckPushout.isPushout_cocart (G := sign F) e₁ f₁.fiber p₁
    have aTR := (amalgamates_cocart_iff F e₁ f₁.fiber p₁).2 (hex e₁ f₁.fiber)
    have pBL := (GrothendieckPushout.isPushout_cocart (G := sign F) e₂ f₂.fiber p₂).flip
    have aBL := ((amalgamates_cocart_iff F e₂ f₂.fiber p₂).2 (hex e₂ f₂.fiber)).flip
    have pBR := GrothendieckPushout.isPushout_vert (G := sign F) hfib (fun u => hΦ u)
    have aBR := (amalgamates_ι_iff F j _ _ θ₁ θ₂).2 (hloc j _ _ _ _ hfib)
    have pAll := (pTL.paste_horiz pTR).paste_vert (pBL.paste_horiz pBR)
    have aAll := (aTL.paste_horiz aTR).paste_vert (aBL.paste_horiz aBR)
    exact Amalgamates.of_isPushout' pAll aAll hP
      (GrothendieckPushout.eq_cart_comp_vert f₁)
      (GrothendieckPushout.eq_cart_comp_vert f₂)

end IndexedCoInst

end Silmaril.Logic.Institution
