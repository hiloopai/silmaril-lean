module

public import Silmaril.Logic.Institution.Hets.StructuredSpec
public import Silmaril.Logic.Institution.Hets.DevGraph
public import Silmaril.Logic.Institution.Grothendieck.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic

@[expose] public section

/-!
# Heterogeneous specification over a logic graph

Hets realises heterogeneous specification as structured specification over the Grothendieck
institution of a logic graph `F : Ind ⥤ CoIns` (`IndexedCoInst.flat F`): a heterogeneous
specification is a `StrSpec (flat F)`, and a heterogeneous development graph is a `DevGraph`
over `flat F` (Mossakowski, Definition 6.25).

* `IndexedCoInst.lift F d S : (i, Σ) ⟶ (j, Φᵈ Σ)` is the Grothendieck signature morphism
  `(d, id)` of an index morphism `d : i ⟶ j`. Its corridor is the comorphism corridor `ρᵈ_Σ`
  (`flat_map_lift`).
* Heterogeneous translation `translateAlong F d SP` is translation along `lift F d S`; its model
  class is Mossakowski's `{M' | β_Σ(M') ∈ Mod(SP)}` (`models_translateAlong`).
* `hideAlong F d SP'` is ordinary hiding in the Grothendieck institution along `lift F d S`: it
  goes *back* along the comorphism of `d`, from `(j, Φᵈ Σ)` to `(i, Σ)`, with model class
  `{βᵈ_Σ(M') | M' ∈ Mod(SP')}` (`models_hideAlong`). This is not Mossakowski's heterogeneous
  hiding `derive from SP by μ` of §6.11, which goes *forward* along an institution morphism `μ`
  and needs morphisms in the indexed coinstitution; that construct is not formalised here.
* Borrowing: along a model-expansive comorphism heterogeneous translation preserves and reflects
  entailment and refinement (`entails_translateAlong_iff`, `refines_translateAlong_iff`), and
  consequence in the Grothendieck institution is borrowed along `lift` (`entails_lift_iff`).
* Borrowing along a path `p : Quiver.Path i j` of index morphisms: if every comorphism on the
  path is model-expansive (`PathModelExpansive`), so is the comorphism of the composite
  (`modelExpansive_composePath`), and entailment is borrowed along the whole path
  (`entails_translatePath_iff`).

## References

* `mossakowski-2005-habilitation-hets` in `references.bib`: §6.11 (printed pages 179–180,
  PDF pages 181–182: heterogeneous translation and hiding); §6.4, Definition 6.25 (printed
  page 161, PDF page 163); §5.2, Definition 5.1, Proposition 5.2 and Theorem 5.3 (printed pages
  126–127, PDF pages 128–129).
* `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Definition 3.1
  (PDF page 4): the Grothendieck institution.
* `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
  Definition 3.6 and Proposition 3.7: model expansion and borrowing.
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u₀ v₀ u v w m₁ m₂ u₁ v₁ u₂ v₂ u₃ v₃

/-! ### Model expansion is closed under composition -/

namespace Inst

/-- The identity comorphism is model-expansive. -/
theorem CoHom.modelExpansive_id (A : Inst.{u, v, w, m₁, m₂}) : (CoHom.id A).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Model-expansive comorphisms compose.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6 (model expansion), lifted to comorphisms in §4.1. -/
theorem CoHom.ModelExpansive.comp {A : Inst.{u₁, v₁, w, m₁, m₂}} {B : Inst.{u₂, v₂, w, m₁, m₂}}
    {C : Inst.{u₃, v₃, w, m₁, m₂}} {f : CoHom A B} {g : CoHom B C} (hf : f.ModelExpansive)
    (hg : g.ModelExpansive) : (f.comp g).ModelExpansive :=
  fun S => (hf S).comp ((hg (f.Φ.obj S)).comp (Corridor.modelExpansive_id _))

end Inst

namespace IndexedCoInst

variable {Ind : Type u₀} [Category.{v₀} Ind] (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂})

/-- The Grothendieck signature `(i, Σ)`. -/
abbrev mkSig (i : Ind) (S : (inst F i).Sign) : FlatSig F := ⟨i, S⟩

/-- The Grothendieck signature morphism `(d, id) : (i, Σ) ⟶ (j, Φᵈ Σ)` moving a signature along
the comorphism of `d`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.11 (printed page 180,
PDF page 182: the link `N ⟶(id,d) K` of `translate SP by d`);
`mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4:
Grothendieck signature morphisms `(ρ, σ)`). -/
def lift {i j : Ind} (d : i ⟶ j) (S : (inst F i).Sign) :
    mkSig F i S ⟶ mkSig F j ((coHom F d).Φ.obj S) :=
  ⟨d, 𝟙 _⟩

/-- The corridor of `(d, id)` is the comorphism corridor `ρᵈ_Σ`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3,
Definition 3.1 (PDF page 4), with `σ = id`. -/
theorem flat_map_lift {i j : Ind} (d : i ⟶ j) (S : (inst F i).Sign) :
    (flat F).map (lift F d S) = (coHom F d).ρ.app S := by
  rw [flat_map]
  exact (congrArg ((coHom F d).ρ.app S ≫ ·) ((inst F j).I.map_id _)).trans (Category.comp_id _)

/-- Consequence is borrowed along `(d, id)` when the comorphism of `d` is model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7; `mossakowski-2005-habilitation-hets` in `references.bib`, §6.4 (printed
page 161, PDF page 163: "Shifting of proof goals is sound if the involved comorphism admit model
expansion"). -/
theorem entails_lift_iff {i j : Ind} (d : i ⟶ j) (hd : (coHom F d).ModelExpansive)
    (S : (inst F i).Sign) (Γ : Set ((flat F).obj (mkSig F i S)).Sen)
    (φ : ((flat F).obj (mkSig F i S)).Sen) :
    ((flat F).obj (mkSig F i S)).Entails Γ φ ↔
      ((flat F).obj (mkSig F j ((coHom F d).Φ.obj S))).Entails
        (((flat F).map (lift F d S)).sen '' Γ) (((flat F).map (lift F d S)).sen φ) := by
  have h : Corridor.ModelExpansive ((flat F).map (lift F d S)) := by
    rw [flat_map_lift]
    exact hd S
  exact ((flat F).map (lift F d S)).entails_map_iff h Γ φ

/-! ### Heterogeneous structured specifications -/

/-- Heterogeneous structured specifications: structured specifications over the Grothendieck
institution.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5 introduction (printed
page 125, PDF page 127: "we then will realize heterogeneous specification by just considering
structured specification over a so-called Grothendieck institution") and §6.11. -/
abbrev HetSpec (X : FlatSig F) : Type _ := StrSpec (flat F) X

/-- A basic specification in the logic `i`. -/
abbrev basicIn (i : Ind) (S : (inst F i).Sign) (E : Set ((inst F i).I.obj S).Sen) :
    HetSpec F (mkSig F i S) :=
  StrSpec.basic (mkSig F i S) E

/-- Heterogeneous translation `translate SP by d` along the comorphism of `d`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.11 (printed page 180,
PDF page 182: heterogeneous translation). -/
abbrev translateAlong {i j : Ind} (d : i ⟶ j) {S : (inst F i).Sign}
    (SP : HetSpec F (mkSig F i S)) : HetSpec F (mkSig F j ((coHom F d).Φ.obj S)) :=
  StrSpec.translate (lift F d S) SP

/-- Hiding along the comorphism of `d`: from a specification at `(j, Φᵈ Σ)` back to `(i, Σ)`.
This is the kernel-language `derive from SP' by (d, id)` in the Grothendieck institution, not
Mossakowski's heterogeneous hiding along an institution morphism (§6.11, printed page 180),
which moves forward from `I` to `I'`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127: `derive from SP' by σ`), applied to the Grothendieck signature morphism `(d, id)`;
`mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §8.1.4 (PDF
page 21). -/
abbrev hideAlong {i j : Ind} (d : i ⟶ j) {S : (inst F i).Sign}
    (SP' : HetSpec F (mkSig F j ((coHom F d).Φ.obj S))) : HetSpec F (mkSig F i S) :=
  StrSpec.hide (lift F d S) SP'

/-- The models of a heterogeneous translation: `{M' | βᵈ_Σ(M') ∈ Mod(SP)}`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §6.11 (printed page 180,
PDF page 182) and proof of Theorem 6.45 (printed page 181, PDF page 183). -/
theorem models_translateAlong {i j : Ind} (d : i ⟶ j) {S : (inst F i).Sign}
    (SP : HetSpec F (mkSig F i S)) :
    (translateAlong F d SP).models = ((coHom F d).ρ.app S).mod.obj ⁻¹' SP.models :=
  congrArg
    (fun (c : (flat F).obj (mkSig F i S) ⟶ (flat F).obj (mkSig F j ((coHom F d).Φ.obj S))) =>
      c.mod.obj ⁻¹' SP.models)
    (flat_map_lift F d S)

/-- The models of hiding along `(d, id)`: `{βᵈ_Σ(M') | M' ∈ Mod(SP')}`. The shape matches the
model class of Mossakowski's heterogeneous hiding, but with the model translation `βᵈ` of a
comorphism going backwards rather than that of a morphism going forwards.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.1 (printed page 125,
PDF page 127), with the corridor of `(d, id)` from `flat_map_lift`; compare §6.11 (printed
page 180, PDF page 182). -/
theorem models_hideAlong {i j : Ind} (d : i ⟶ j) {S : (inst F i).Sign}
    (SP' : HetSpec F (mkSig F j ((coHom F d).Φ.obj S))) :
    (hideAlong F d SP').models = ((coHom F d).ρ.app S).mod.obj '' SP'.models :=
  congrArg
    (fun (c : (flat F).obj (mkSig F i S) ⟶ (flat F).obj (mkSig F j ((coHom F d).Φ.obj S))) =>
      c.mod.obj '' SP'.models)
    (flat_map_lift F d S)

/-- **Heterogeneous borrowing of entailment**: along a model-expansive comorphism, a
heterogeneous specification entails `φ` iff its translation entails `αᵈ_Σ(φ)`.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Definition 5.1 and
Proposition 5.2(2) (printed pages 126–127, PDF pages 128–129). -/
theorem entails_translateAlong_iff {i j : Ind} (d : i ⟶ j) (hd : (coHom F d).ModelExpansive)
    {S : (inst F i).Sign} (SP : HetSpec F (mkSig F i S)) (φ : ((inst F i).I.obj S).Sen) :
    SP.Entails φ ↔ (translateAlong F d SP).Entails (((coHom F d).ρ.app S).sen φ) := by
  have h : Corridor.ModelExpansive ((flat F).map (lift F d S)) := by
    rw [flat_map_lift]
    exact hd S
  have := StrSpec.entails_translate_iff (lift F d S) h SP φ
  rw [flat_map_lift] at this
  exact this

/-- **Heterogeneous borrowing of refinement**: along a model-expansive comorphism,
heterogeneous translation preserves and reflects refinement.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Definition 5.1 and
Proposition 5.2(2) (printed pages 126–127, PDF pages 128–129). -/
theorem refines_translateAlong_iff {i j : Ind} (d : i ⟶ j) (hd : (coHom F d).ModelExpansive)
    {S : (inst F i).Sign} (SP₁ SP₂ : HetSpec F (mkSig F i S)) :
    SP₁.Refines SP₂ ↔ (translateAlong F d SP₁).Refines (translateAlong F d SP₂) := by
  have h : Corridor.ModelExpansive ((flat F).map (lift F d S)) := by
    rw [flat_map_lift]
    exact hd S
  exact StrSpec.refines_translate_iff (lift F d S) h SP₁ SP₂

/-! ### Borrowing along a path of comorphisms -/

/-- Every comorphism along a path of index morphisms is model-expansive. -/
def PathModelExpansive {i : Ind} : {j : Ind} → Quiver.Path i j → Prop
  | _, .nil => True
  | _, .cons p e => PathModelExpansive p ∧ (coHom F e).ModelExpansive

/-- The comorphism of the composite of a path of model-expansive comorphisms is
model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6, §4.1; composition of comorphisms as in
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §4, Definition 4.2. -/
theorem modelExpansive_composePath {i : Ind} :
    {j : Ind} → (p : Quiver.Path i j) → PathModelExpansive F p →
      (coHom F (composePath p)).ModelExpansive
  | _, .nil, _ => by
    rw [composePath_nil, coHom_id]
    exact Inst.CoHom.modelExpansive_id _
  | _, .cons p e, h => by
    obtain ⟨hp, he⟩ : PathModelExpansive F p ∧ (coHom F e).ModelExpansive := h
    rw [composePath_cons, coHom_comp]
    exact (modelExpansive_composePath p hp).comp he

/-- Heterogeneous translation along the composite of a path of comorphisms. -/
abbrev translatePath {i j : Ind} (p : Quiver.Path i j) {S : (inst F i).Sign}
    (SP : HetSpec F (mkSig F i S)) :
    HetSpec F (mkSig F j ((coHom F (composePath p)).Φ.obj S)) :=
  translateAlong F (composePath p) SP

/-- **Borrowing along a path of comorphisms**: if every comorphism along `p` is
model-expansive, a heterogeneous specification entails `φ` iff its translation along the whole
path entails the translated sentence.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.2, Theorem 5.3
(printed page 127, PDF page 129) and §6.4 (printed page 161, PDF page 163: internalized
borrowing); `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`,
§3, Proposition 3.7. -/
theorem entails_translatePath_iff {i j : Ind} (p : Quiver.Path i j)
    (hp : PathModelExpansive F p) {S : (inst F i).Sign} (SP : HetSpec F (mkSig F i S))
    (φ : ((inst F i).I.obj S).Sen) :
    SP.Entails φ ↔
      (translatePath F p SP).Entails (((coHom F (composePath p)).ρ.app S).sen φ) :=
  entails_translateAlong_iff F (composePath p) (modelExpansive_composePath F p hp) SP φ

end IndexedCoInst

end Silmaril.Logic.Institution
