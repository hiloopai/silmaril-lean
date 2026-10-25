module

public import Silmaril.Logic.Institution.Borrowing
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op

@[expose] public section

/-!
# Indexed institutions and Grothendieck institutions

An *indexed coinstitution* is a functor `F : Ind ⥤ CoIns` from an index category into the
category of institutions and comorphisms: a graph of logics and logic translations, as in the
logic graph of the Heterogeneous Tool Set. Its *Grothendieck institution* (Mossakowski,
*Comorphism-based Grothendieck logics*, MFCS 2002, Definition 3.1) flattens the graph into one
institution:

* a signature is a pair `(i, Σ)` of an index and a signature of the institution `F i`;
* a signature morphism `(d, σ) : (i, Σ) → (j, Σ')` is an index morphism `d : i ⟶ j` together
  with a signature morphism `σ : Φᵈ(Σ) ⟶ Σ'` of `F j`;
* sentences, models and satisfaction at `(i, Σ)` are those of `F i` at `Σ`, and the corridor of
  `(d, σ)` is the comorphism corridor `ρᵈ_Σ` followed by the corridor of `σ` in `F j`.

The signature category is Mathlib's Grothendieck construction `CategoryTheory.Grothendieck` of
the indexed category of signatures `F ⋙ CoIns.signFunctor : Ind ⥤ Cat`, and the room functor is
the functor out of it determined by the room functors of the components and the coherent family
of comorphism components (the data of Mathlib's `Grothendieck.functorFrom`; that definition is
not used directly because its coherence hypotheses mention private proof terms which the module
system does not export). The satisfaction condition of the flattening is the satisfaction
condition of a functor into `Room`, and each component `F i` embeds into the flattening by a
comorphism with identity corridors (`IndexedCoInst.ι`), which is model-expansive and so borrows
consequence both ways.

Dually, an *indexed institution* `F : Indᵒᵖ ⥤ Ins` (Diaconescu, *Grothendieck institutions*,
Appl. Categ. Struct. 10, 2002) has the Grothendieck institution whose signature category is
Goguen–Roşu's flattening `Flat` of the indexed category of signatures `Indᵒᵖ ⥤ Cat`: a morphism
`(i, Σ) → (i', Σ')` is `u : i ⟶ i'` with `φ : Σ ⟶ Φᵘ(Σ')`. In Mathlib terms this is the opposite
of the Grothendieck construction of the pointwise-opposite indexed category, and the corridor of
`(u, φ)` is `Iᵢ(φ) ; ηᵘ_{Σ'}` (`IndexedInst.flat`).

## Main definitions

* `IndexedCoInst Ind`, `IndexedCoInst.flat`, `IndexedCoInst.flatInst`, `IndexedCoInst.ι`.
* `IndexedInst Ind`, `IndexedInst.flat`, `IndexedInst.flatInst`, `IndexedInst.ι`.

## Main results

* `IndexedCoInst.satisfaction`, `IndexedInst.satisfaction`: the satisfaction condition of the
  flattening, in components.
* `IndexedCoInst.ι_modelExpansive`, `IndexedCoInst.entails_iff_flat` (and the `IndexedInst`
  versions): each component embeds into the flattening and consequence is the same in both.

## References

* `diaconescu-2002-grothendieck-institutions` in `references.bib` (IMAR
  preprint of Diaconescu, *Grothendieck institutions*, Appl. Categ. Struct. 10, 2002), §3:
  Definition 8, Theorem 2 and Remark 1 (printed pages 7–9, PDF pages 8–10).
* `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib` (Mossakowski,
  *Comorphism-based Grothendieck logics*, MFCS 2002), §3, Definition 3.1 (PDF page 4).
  Mossakowski indexes by `Ind* ⥤ coIns` with `Ind*` the dual of `Ind`; our `Ind` is his `Ind*`,
  so his `(σ, d)` with `d : j ⟶ i` in `Ind` is our `(d, σ)` with `d : i ⟶ j`.
* `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4, printed
  page 122): Grothendieck signatures `(L, Σ)` and morphisms `(ρ, σ)` with `σ : Φ(Σ₁) ⟶ Σ₂`.
* `goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.1, Definition 2.1
  (the flattening `Flat(C)` of an indexed category `C : Indᵒᵖ ⥤ Cat`).
-/

namespace Silmaril.Logic.Institution

open CategoryTheory

universe u₀ v₀ u v w m₁ m₂

/-- A comorphism equal to the identity has identity corridors, up to the induced transport. -/
theorem Inst.CoHom.ρ_app_eq_of_eq_id {A : Inst.{u, v, w, m₁, m₂}} (a : Inst.CoHom A A)
    (h : a = Inst.CoHom.id A) (S : A.Sign) :
    a.ρ.app S = eqToHom
      (congrArg (fun g : Inst.CoHom A A => (g.Φ ⋙ A.I).obj S) h).symm := by
  subst h
  rfl

/-- A comorphism equal to a composite has the composite corridors, up to the induced
transport. -/
theorem Inst.CoHom.ρ_app_eq_of_eq_comp {A B C : Inst.{u, v, w, m₁, m₂}} (a : Inst.CoHom A C)
    (f : Inst.CoHom A B) (g : Inst.CoHom B C) (h : a = f.comp g) (S : A.Sign) :
    a.ρ.app S = f.ρ.app S ≫ g.ρ.app (f.Φ.obj S) ≫ eqToHom
      (congrArg (fun k : Inst.CoHom A C => (k.Φ ⋙ C.I).obj S) h).symm := by
  subst h
  simp [Inst.CoHom.comp]

/-- The functor-identity law of a comorphism-based Grothendieck room functor, for a comorphism
equal to the identity. -/
theorem Inst.CoHom.flat_map_id_aux {A : Inst.{u, v, w, m₁, m₂}} (a : Inst.CoHom A A)
    (h : a = Inst.CoHom.id A) (S : A.Sign) (e : a.Φ.obj S = S) :
    a.ρ.app S ≫ A.I.map (eqToHom e) = 𝟙 (A.I.obj S) := by
  subst h
  rw [show (eqToHom e) = 𝟙 _ from rfl]
  simp [Inst.CoHom.id]

/-- The functor-composition law of a comorphism-based Grothendieck room functor, for a
comorphism equal to a composite. -/
theorem Inst.CoHom.flat_map_comp_aux {A B C : Inst.{u, v, w, m₁, m₂}} (a : Inst.CoHom A C)
    (f : Inst.CoHom A B) (g : Inst.CoHom B C) (h : a = f.comp g) (S : A.Sign) (T : B.Sign)
    (U : C.Sign) (φ : f.Φ.obj S ⟶ T) (ψ : g.Φ.obj T ⟶ U)
    (e : a.Φ.obj S = g.Φ.obj (f.Φ.obj S)) :
    a.ρ.app S ≫ C.I.map (eqToHom e ≫ g.Φ.map φ ≫ ψ) =
      (f.ρ.app S ≫ B.I.map φ) ≫ (g.ρ.app T ≫ C.I.map ψ) := by
  subst h
  have nat := g.ρ.naturality φ
  simp only [Functor.comp_map] at nat
  rw [show (eqToHom e) = 𝟙 _ from rfl]
  simp [Inst.CoHom.comp, reassoc_of% nat]

/-- Naturality of the identity corridors of a component embedding into a comorphism-based
Grothendieck institution. -/
theorem Inst.CoHom.flat_ι_naturality_aux {A : Inst.{u, v, w, m₁, m₂}} (a : Inst.CoHom A A)
    (h : a = Inst.CoHom.id A) {S S' : A.Sign} (σ : S ⟶ S') (e : a.Φ.obj S = S) :
    A.I.map σ ≫ 𝟙 (A.I.obj S') = 𝟙 (A.I.obj S) ≫ (a.ρ.app S ≫ A.I.map (eqToHom e ≫ σ)) := by
  subst h
  rw [show (eqToHom e) = 𝟙 _ from rfl]
  simp [Inst.CoHom.id]

/-- The functor-identity law of a morphism-based Grothendieck room functor, for a morphism equal
to the identity. -/
theorem Inst.Hom.flat_map_id_aux {A : Inst.{u, v, w, m₁, m₂}} (a : Inst.Hom A A)
    (h : a = Inst.Hom.id A) (S : A.Sign) (e : Opposite.op (a.Φ.obj S) = Opposite.op S) :
    A.I.map (eqToHom e).unop ≫ a.η.app S = 𝟙 (A.I.obj S) := by
  subst h
  rw [show (eqToHom e) = 𝟙 _ from rfl]
  simp [Inst.Hom.id]

/-- The functor-composition law of a morphism-based Grothendieck room functor, for a morphism
equal to a composite. -/
theorem Inst.Hom.flat_map_comp_aux {A B C : Inst.{u, v, w, m₁, m₂}} (a : Inst.Hom A C)
    (f : Inst.Hom A B) (g : Inst.Hom B C) (h : a = f.comp g) (S : A.Sign) (T : B.Sign)
    (U : C.Sign) (φ : Opposite.op (f.Φ.obj S) ⟶ Opposite.op T)
    (ψ : Opposite.op (g.Φ.obj T) ⟶ Opposite.op U)
    (e : Opposite.op (a.Φ.obj S) = Opposite.op (g.Φ.obj (f.Φ.obj S))) :
    C.I.map (eqToHom e ≫ g.Φ.op.map φ ≫ ψ).unop ≫ a.η.app S =
      (C.I.map ψ.unop ≫ g.η.app T) ≫ (B.I.map φ.unop ≫ f.η.app S) := by
  subst h
  have nat := g.η.naturality φ.unop
  simp only [Functor.comp_map] at nat
  rw [show (eqToHom e) = 𝟙 _ from rfl]
  simp [Inst.Hom.comp, reassoc_of% nat]

/-- Naturality of the identity corridors of a component embedding into a morphism-based
Grothendieck institution. -/
theorem Inst.Hom.flat_ι_naturality_aux {A : Inst.{u, v, w, m₁, m₂}} (a : Inst.Hom A A)
    (h : a = Inst.Hom.id A) {S S' : A.Sign} (σ : S ⟶ S')
    (e : Opposite.op (a.Φ.obj S') = Opposite.op S') :
    A.I.map σ ≫ 𝟙 (A.I.obj S') =
      𝟙 (A.I.obj S) ≫ (A.I.map (eqToHom e ≫ σ.op).unop ≫ a.η.app S') := by
  subst h
  rw [show (eqToHom e) = 𝟙 _ from rfl]
  simp [Inst.Hom.id]

/-! ### Comorphism-based Grothendieck institutions -/

set_option linter.checkUnivs false in
/-- An indexed coinstitution: a diagram of institutions and comorphisms (a "logic graph").

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, before
Definition 3.1 (PDF page 4: "a 2-indexed
coinstitution is a 2-functor `I : Ind* ⟶ coIns`", here without the 2-cells);
`mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4: "some
graph of logics and logic translations, formalized as institutions and comorphisms"). -/
abbrev IndexedCoInst (Ind : Type u₀) [Category.{v₀} Ind] : Type _ :=
  Ind ⥤ CoIns.{u, v, w, m₁, m₂}

namespace IndexedCoInst

variable {Ind : Type u₀} [Category.{v₀} Ind] (F : Ind ⥤ CoIns.{u, v, w, m₁, m₂})

/-- The institution at an index. -/
def inst (i : Ind) : Inst.{u, v, w, m₁, m₂} := F.obj i

/-- The comorphism at an index morphism. -/
def coHom {i j : Ind} (d : i ⟶ j) : Inst.CoHom (inst F i) (inst F j) := F.map d

theorem coHom_id (i : Ind) : coHom F (𝟙 i) = Inst.CoHom.id (inst F i) :=
  F.map_id i

theorem coHom_comp {i j k : Ind} (d : i ⟶ j) (e : j ⟶ k) :
    coHom F (d ≫ e) = (coHom F d).comp (coHom F e) :=
  F.map_comp d e

/-- The indexed category of signatures `Ind ⥤ Cat`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.3, Proposition 2.10
(the signature-extracting functor), applied pointwise to the diagram. -/
def sign : Ind ⥤ Cat.{v, u} := F ⋙ CoIns.signFunctor

/-- The signatures of the Grothendieck institution: Mathlib's Grothendieck construction of the
indexed category of signatures. Objects are pairs `(i, Σ)`; a morphism `(i, Σ) ⟶ (j, Σ')` is
`d : i ⟶ j` with `σ : Φᵈ(Σ) ⟶ Σ'`.

Source: `mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4,
printed page 122: "a Grothendieck signature morphism `(ρ, σ) : (L₁, Σ₁) → (L₂, Σ₂)` consists of a
logic translation `ρ` … plus an `L₂`-signature morphism `σ : Φ(Σ₁) ⟶ Σ₂`");
`mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Definition 3.1 (PDF
page 4), items 1–3. -/
abbrev FlatSig : Type _ := CategoryTheory.Grothendieck (sign F)

/-- The Grothendieck institution of an indexed coinstitution, as a room functor on the
Grothendieck construction: `(i, Σ) ↦ Iᵢ(Σ)` and `(d, σ) ↦ ρᵈ_Σ ; Iⱼ(σ)`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Definition
3.1 (PDF page 4, last item:
"`I#(σ, d) = I^i(Σ₁) --ρᵈ--> I^j(Φᵈ(Σ₁)) --I^j(σ)--> I^j(Σ₂)`");
`mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4: "Sentences,
models and satisfaction in the Grothendieck institution are defined in a component wise
manner"). -/
def flat : FlatSig F ⥤ Room.{w, m₁, m₂} where
  obj X := (inst F X.base).I.obj X.fiber
  map {X Y} f := (coHom F f.base).ρ.app X.fiber ≫ (inst F Y.base).I.map f.fiber
  map_id X := by
    exact Inst.CoHom.flat_map_id_aux (coHom F (𝟙 X.base)) (coHom_id F X.base) X.fiber
      (congrArg (fun c : Inst.CoHom (inst F X.base) (inst F X.base) => c.Φ.obj X.fiber)
        (coHom_id F X.base))
  map_comp {X Y Z} f g := by
    exact Inst.CoHom.flat_map_comp_aux (coHom F (f.base ≫ g.base)) (coHom F f.base)
      (coHom F g.base) (coHom_comp F f.base g.base) X.fiber Y.fiber Z.fiber f.fiber g.fiber _

/-- The Grothendieck institution, bundled. -/
def flatInst : Inst := ⟨FlatSig F, flat F⟩

theorem flat_obj (X : FlatSig F) : (flat F).obj X = (inst F X.base).I.obj X.fiber := rfl

theorem flat_map {X Y : FlatSig F} (f : X ⟶ Y) :
    (flat F).map f = (coHom F f.base).ρ.app X.fiber ≫ (inst F Y.base).I.map f.fiber := rfl

/-- The satisfaction condition of the Grothendieck institution, in components: for
`(d, σ) : (i, Σ) ⟶ (j, Σ')`, a `Σ'`-model `M'` of `F j` satisfies the translation
`Sen(σ)(αᵈ_Σ φ)` iff the `Σ`-model `βᵈ_Σ(Mod(σ) M')` of `F i` satisfies `φ`.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Definition
3.1 (PDF page 4);
`mossakowski-maeder-luttich-2007-hets-verify` in `references.bib`, §2 (PDF page 4, the
comorphism satisfaction condition `M' ⊨ α_Σ(φ) ⇔ β_Σ(M') ⊨ φ`, combined component-wise). -/
theorem satisfaction {X Y : FlatSig F} (f : X ⟶ Y) (M' : ((inst F Y.base).I.obj Y.fiber).Mod)
    (φ : ((inst F X.base).I.obj X.fiber).Sen) :
    ((inst F Y.base).I.obj Y.fiber).Sat M'
        (((inst F Y.base).I.map f.fiber).sen (((coHom F f.base).ρ.app X.fiber).sen φ)) ↔
      ((inst F X.base).I.obj X.fiber).Sat
        (((coHom F f.base).ρ.app X.fiber).mod.obj (((inst F Y.base).I.map f.fiber).mod.obj M'))
        φ :=
  ((flat F).map f).sat M' φ

/-- The embedding of the component `F i` into the Grothendieck institution: signatures `Σ ↦
(i, Σ)` (Mathlib's fiber inclusion `Grothendieck.ι`), with identity corridors.

Source: `mossakowski-2002-comorphism-grothendieck-logics` in `references.bib`, §3, Definition
3.1 (PDF page 4); the fiber inclusion of the flattening,
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.1, Definition 2.1. -/
def ι (i : Ind) : Inst.CoHom (inst F i) (flatInst F) where
  Φ := CategoryTheory.Grothendieck.ι (sign F) i
  ρ :=
    { app := fun S => 𝟙 ((inst F i).I.obj S)
      naturality := fun S S' σ => by
        exact Inst.CoHom.flat_ι_naturality_aux (coHom F (𝟙 i)) (coHom_id F i) σ _ }

/-- The component embeddings have identity model translations, so they are model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6 (model expansion), §4.1. -/
theorem ι_modelExpansive (i : Ind) : (ι F i).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Consequence in a component is consequence in the Grothendieck institution: heterogeneous
specification is conservative over each logic of the graph.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7, via `Inst.CoHom.entails_iff`. -/
theorem entails_iff_flat (i : Ind) (S : (inst F i).Sign) (Γ : Set ((inst F i).I.obj S).Sen)
    (φ : ((inst F i).I.obj S).Sen) :
    ((inst F i).I.obj S).Entails Γ φ ↔
      ((flat F).obj ((ι F i).Φ.obj S)).Entails (((ι F i).ρ.app S).sen '' Γ)
        (((ι F i).ρ.app S).sen φ) :=
  (ι F i).entails_iff (ι_modelExpansive F i) S Γ φ

end IndexedCoInst

/-! ### Morphism-based Grothendieck institutions -/

set_option linter.checkUnivs false in
/-- An indexed institution in the sense of Diaconescu: a functor `Indᵒᵖ ⥤ Ins`.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §3,
Definition 8 (printed page 7, PDF page 8);
the indexed categories of `goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.1,
Definition 2.1, with values in `INS`. -/
abbrev IndexedInst (Ind : Type u₀) [Category.{v₀} Ind] : Type _ :=
  Indᵒᵖ ⥤ Ins.{u, v, w, m₁, m₂}

namespace IndexedInst

variable {Ind : Type u₀} [Category.{v₀} Ind] (F : Indᵒᵖ ⥤ Ins.{u, v, w, m₁, m₂})

/-- The institution at an index. -/
def inst (i : Indᵒᵖ) : Inst.{u, v, w, m₁, m₂} := F.obj i

/-- The institution morphism at an index morphism. -/
def hom {i j : Indᵒᵖ} (d : i ⟶ j) : Inst.Hom (inst F i) (inst F j) := F.map d

theorem hom_id (i : Indᵒᵖ) : hom F (𝟙 i) = Inst.Hom.id (inst F i) :=
  F.map_id i

theorem hom_comp {i j k : Indᵒᵖ} (d : i ⟶ j) (e : j ⟶ k) :
    hom F (d ≫ e) = (hom F d).comp (hom F e) :=
  F.map_comp d e

/-- The pointwise-opposite indexed category of signatures `Indᵒᵖ ⥤ Cat`, `i ↦ (Signᵢ)ᵒᵖ`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.1 (the indexed
category `Cᵒᵖ` defined after Theorem 2.2). -/
def sign : Indᵒᵖ ⥤ Cat.{v, u} := F ⋙ Ins.signFunctor ⋙ Cat.opFunctor

/-- The signatures of the Grothendieck institution: Goguen–Roşu's flattening of the indexed
category of signatures, realised as the opposite of Mathlib's Grothendieck construction of the
pointwise-opposite indexed category. A morphism `(i, Σ) → (i', Σ')` is `u : i ⟶ i'` in `Ind`
with `φ : Σ ⟶ Φᵘ(Σ')`.

Source: `goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.1, Definition 2.1
(PDF page 4: "`(α, f) : (i, a) → (i', a')` … where `α ∈ Ind(i, i')` and `f ∈ Cᵢ(a, C_α(a'))`");
`diaconescu-2002-grothendieck-institutions` in `references.bib`, §3, Remark 1,
item 1 (printed page 9, PDF page 10). -/
abbrev FlatSig : Type _ := (CategoryTheory.Grothendieck (sign F))ᵒᵖ

/-- The Grothendieck institution of an indexed institution: `(i, Σ) ↦ Iᵢ(Σ)`, and the corridor
of `(u, φ) : (i, Σ) → (i', Σ')` (with `φ : Σ ⟶ Φᵘ(Σ')`) is `Iᵢ(φ) ; ηᵘ_{Σ'}`.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §3,
Theorem 2 and Remark 1, items 2–4 (printed
pages 7–9, PDF pages 8–10: "`MOD♯((u, φ)) = β^u_Σ' ; MODⁱ(φ)`"); signatures as in
`goguen-rosu-2002-institution-morphisms` in `references.bib`, §2.1, Definition 2.1. -/
def flat : FlatSig F ⥤ Room.{w, m₁, m₂} where
  obj X := (inst F X.unop.base).I.obj (Opposite.unop X.unop.fiber)
  map {X Y} f :=
    (inst F X.unop.base).I.map (Quiver.Hom.unop f.unop.fiber) ≫
      (hom F f.unop.base).η.app (Opposite.unop Y.unop.fiber)
  map_id X := by
    exact Inst.Hom.flat_map_id_aux (hom F (𝟙 X.unop.base)) (hom_id F X.unop.base)
      (Opposite.unop X.unop.fiber)
      (congrArg (fun c : Inst.Hom (inst F X.unop.base) (inst F X.unop.base) =>
          Opposite.op (c.Φ.obj (Opposite.unop X.unop.fiber)))
        (hom_id F X.unop.base))
  map_comp {X Y Z} f g := by
    exact Inst.Hom.flat_map_comp_aux (hom F (g.unop.base ≫ f.unop.base)) (hom F g.unop.base)
      (hom F f.unop.base) (hom_comp F g.unop.base f.unop.base) (Opposite.unop Z.unop.fiber)
      (Opposite.unop Y.unop.fiber) (Opposite.unop X.unop.fiber) g.unop.fiber f.unop.fiber _

/-- The Grothendieck institution, bundled. -/
def flatInst : Inst := ⟨FlatSig F, flat F⟩

theorem flat_obj (X : FlatSig F) :
    (flat F).obj X = (inst F X.unop.base).I.obj (Opposite.unop X.unop.fiber) :=
  rfl

/-- The satisfaction condition of the Grothendieck institution of an indexed institution: the
satisfaction condition of the corridor `Iᵢ(φ) ; ηᵘ_{Σ'}` of `(u, φ)`.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §3,
Remark 1, item 4 (printed page 9, PDF page 10); it is
the satisfaction condition of the room functor
`flat`, `goguen-burstall-1992` in `references.bib`, §2.5, Definition 12. -/
theorem satisfaction {X Y : FlatSig F} (f : X ⟶ Y) (M' : ((flat F).obj Y).Mod)
    (φ : ((flat F).obj X).Sen) :
    ((flat F).obj Y).Sat M' (((flat F).map f).sen φ) ↔
      ((flat F).obj X).Sat (((flat F).map f).mod.obj M') φ :=
  ((flat F).map f).sat M' φ

/-- The embedding of the component `F i` into the Grothendieck institution, with identity
corridors.

Source: `diaconescu-2002-grothendieck-institutions` in `references.bib`, §4.3,
proof of Proposition 2 (printed page 12, PDF page 13:
the canonical injection `Signⁱ → Sign♯`). -/
def ι (i : Indᵒᵖ) : Inst.CoHom (inst F i) (flatInst F) where
  Φ := (CategoryTheory.Grothendieck.ι (sign F) i).rightOp
  ρ :=
    { app := fun S => 𝟙 ((inst F i).I.obj S)
      naturality := fun S S' σ => by
        exact Inst.Hom.flat_ι_naturality_aux (hom F (𝟙 i)) (hom_id F i) σ _ }

/-- The component embeddings are model-expansive.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Definition 3.6. -/
theorem ι_modelExpansive (i : Indᵒᵖ) : (ι F i).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Consequence in a component is consequence in the Grothendieck institution of an indexed
institution.

Source: `mossakowski-diaconescu-tarlecki-2009-logic-translation` in `references.bib`, §3,
Proposition 3.7, via `Inst.CoHom.entails_iff`. -/
theorem entails_iff_flat (i : Indᵒᵖ) (S : (inst F i).Sign) (Γ : Set ((inst F i).I.obj S).Sen)
    (φ : ((inst F i).I.obj S).Sen) :
    ((inst F i).I.obj S).Entails Γ φ ↔
      ((flat F).obj ((ι F i).Φ.obj S)).Entails (((ι F i).ρ.app S).sen '' Γ)
        (((ι F i).ρ.app S).sen φ) :=
  (ι F i).entails_iff (ι_modelExpansive F i) S Γ φ

end IndexedInst

end Silmaril.Logic.Institution
