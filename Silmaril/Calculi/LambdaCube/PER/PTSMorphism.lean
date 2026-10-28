module

public import Silmaril.Calculi.LambdaCube.PER.Cube

@[expose] public section

set_option autoImplicit true

/-! # PTS morphisms and the pullback comorphism construction

The general construction (`GSemantics.pullback`): a *PTS morphism*
`φ : P → Q` (a map of sorts preserving axioms and rules, Barendregt's PTS
morphisms) translates judgments and preserves derivability (`HasType.mapSorts`).
Any semantics of `Q`, pulled back along `φ`, is a semantics of `P`, and the
pullback is an institution comorphism `P → Q` whose satisfaction condition holds
by construction (sentences translate along `φ`, models are kept). Pullback is
functorial in `φ` (`pullback_id`, `pullback_comp`).

The cube's edges `c ≤ d` are PTS morphisms with identity sort map
(`Corner.ptsMorphism`); `Semantics.restrict` is the cube-level instance, related
to the general one by `Semantics.restrict_toG`, and its comorphism is the
existing `SemanticInclusion.comorphism`. The parametric PER semantics fed into
this construction are in `PER/CubeMorphisms.lean`.

Sources: Goguen–Roşu 2002, Definition 4.2 (comorphisms).
-/

namespace Silmaril.Calculi.LambdaCube

open CategoryTheory Silmaril.Logic.Institution

/-! ## PTS morphisms -/

/-- A morphism of PTS specifications: a map of sorts preserving axioms and rules. -/
structure PTSMorphism (P Q : Specification) where
  sort : P.Sorts → Q.Sorts
  ax : ∀ s t, P.Ax s t → Q.Ax (sort s) (sort t)
  rule : ∀ s t u, P.Rule s t u → Q.Rule (sort s) (sort t) (sort u)

namespace PTSMorphism

/-- The identity PTS morphism. -/
def id (P : Specification) : PTSMorphism P P :=
  ⟨_root_.id, fun _ _ => _root_.id, fun _ _ _ => _root_.id⟩

/-- Composition of PTS morphisms. -/
def comp {P Q R : Specification} (ψ : PTSMorphism Q R) (φ : PTSMorphism P Q) :
    PTSMorphism P R :=
  ⟨ψ.sort ∘ φ.sort, fun s t h => ψ.ax _ _ (φ.ax s t h),
    fun s t u h => ψ.rule _ _ _ (φ.rule s t u h)⟩

end PTSMorphism

namespace Pseudo

/-- Translate the sorts of a pseudo-term. -/
def mapSorts {S T : Type} (f : S → T) : Pseudo S → Pseudo T
  | .sort s => .sort (f s)
  | .var n => .var n
  | .app a b => .app (mapSorts f a) (mapSorts f b)
  | .lam A b => .lam (mapSorts f A) (mapSorts f b)
  | .pi A B => .pi (mapSorts f A) (mapSorts f B)

theorem mapSorts_id {S : Type} (t : Pseudo S) : t.mapSorts _root_.id = t := by
  induction t <;> simp_all [mapSorts]

theorem mapSorts_comp {S T U : Type} (g : T → U) (f : S → T) (t : Pseudo S) :
    (t.mapSorts f).mapSorts g = t.mapSorts (g ∘ f) := by
  induction t <;> simp_all [mapSorts]

theorem mapSorts_rename {S T : Type} (f : S → T) (ρ : ℕ → ℕ) (t : Pseudo S) :
    (t.rename ρ).mapSorts f = (t.mapSorts f).rename ρ := by
  induction t generalizing ρ <;> simp_all [mapSorts, rename]

/-- Sort translation commutes with lifting a substitution under a binder. -/
theorem mapSorts_liftSub {S T : Type} (f : S → T) (σ : ℕ → Pseudo S) (n : ℕ) :
    (liftSub σ n).mapSorts f = liftSub (fun k => (σ k).mapSorts f) n := by
  cases n with
  | zero => rfl
  | succ n => exact mapSorts_rename f Nat.succ (σ n)

/-- Sort translation commutes with simultaneous substitution. -/
theorem mapSorts_subst {S T : Type} (f : S → T) (σ : ℕ → Pseudo S) (t : Pseudo S) :
    (t.subst σ).mapSorts f = (t.mapSorts f).subst (fun k => (σ k).mapSorts f) := by
  induction t generalizing σ with
  | sort s => rfl
  | var n => rfl
  | app a b iha ihb => simp only [subst, mapSorts, iha, ihb]
  | lam A b ihA ihb =>
    simp only [subst, mapSorts, ihA, ihb]
    congr 2
    funext n
    exact mapSorts_liftSub f σ n
  | pi A B ihA ihB =>
    simp only [subst, mapSorts, ihA, ihB]
    congr 2
    funext n
    exact mapSorts_liftSub f σ n

theorem mapSorts_substOne {S T : Type} (f : S → T) (b a : Pseudo S) :
    (b.substOne a).mapSorts f = (b.mapSorts f).substOne (a.mapSorts f) := by
  unfold substOne
  rw [mapSorts_subst]
  congr 1
  funext n
  cases n <;> rfl

/-- Sort translation preserves β-conversion. -/
theorem Conv.mapSorts {S T : Type} (f : S → T) {t u : Pseudo S} (h : Conv t u) :
    Conv (t.mapSorts f) (u.mapSorts f) := by
  induction h with
  | refl t => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta A b a =>
    rw [mapSorts_substOne]
    exact .beta _ _ _
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | pi _ _ ih₁ ih₂ => exact .pi ih₁ ih₂

end Pseudo

/-- PTS morphisms preserve derivations (generalizes `HasType.mono`, where the
sort map is the identity). -/
theorem HasType.mapSorts {P Q : Specification} (φ : PTSMorphism P Q) {Γ t A}
    (h : HasType P Γ t A) :
    HasType Q (Γ.map (Pseudo.mapSorts φ.sort)) (t.mapSorts φ.sort) (A.mapSorts φ.sort) := by
  induction h with
  | start h => exact .start (φ.ax _ _ h)
  | var _ ih =>
    rw [Pseudo.mapSorts_rename]
    exact .var ih
  | weak _ _ ih₁ ih₂ =>
    rw [Pseudo.mapSorts_rename, Pseudo.mapSorts_rename]
    exact .weak ih₁ ih₂
  | pi _ _ h ih₁ ih₂ => exact .pi ih₁ ih₂ (φ.rule _ _ _ h)
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | app _ _ ih₁ ih₂ =>
    rw [Pseudo.mapSorts_substOne]
    exact .app ih₁ ih₂
  | conv _ h _ ih₁ ih₂ => exact .conv ih₁ (h.mapSorts φ.sort) ih₂

/-! ## Judgments and semantics over an arbitrary PTS -/

/-- PTS judgments over sorts `S`: typings and typed conversions. -/
inductive GJudgment (S : Type) where
  | typing (Γ : List (Pseudo S)) (t A : Pseudo S)
  | equation (Γ : List (Pseudo S)) (t u A : Pseudo S)

namespace GJudgment

/-- Derivability, as for `PTSJudgment.Derivable`. -/
def Derivable (P : Specification) : GJudgment P.Sorts → Prop
  | .typing Γ t A => HasType P Γ t A
  | .equation Γ t u A => HasType P Γ t A ∧ HasType P Γ u A ∧ Pseudo.Conv t u

/-- Translate the sorts of a judgment. -/
def map {S T : Type} (f : S → T) : GJudgment S → GJudgment T
  | .typing Γ t A => .typing (Γ.map (Pseudo.mapSorts f)) (t.mapSorts f) (A.mapSorts f)
  | .equation Γ t u A =>
      .equation (Γ.map (Pseudo.mapSorts f)) (t.mapSorts f) (u.mapSorts f) (A.mapSorts f)

theorem map_id {S : Type} (j : GJudgment S) : j.map _root_.id = j := by
  have hl : ∀ Γ : List (Pseudo S), Γ.map (Pseudo.mapSorts _root_.id) = Γ := fun Γ => by
    rw [show Pseudo.mapSorts (_root_.id : S → S) = _root_.id from funext Pseudo.mapSorts_id,
      List.map_id]
  cases j <;> simp [map, hl, Pseudo.mapSorts_id]

theorem map_comp {S T U : Type} (g : T → U) (f : S → T) (j : GJudgment S) :
    (j.map f).map g = j.map (g ∘ f) := by
  have hl : ∀ Γ : List (Pseudo S),
      (Γ.map (Pseudo.mapSorts f)).map (Pseudo.mapSorts g) = Γ.map (Pseudo.mapSorts (g ∘ f)) :=
    fun Γ => by
      rw [List.map_map]
      congr 1
      funext t
      exact Pseudo.mapSorts_comp g f t
  cases j <;> simp [map, hl, Pseudo.mapSorts_comp]

/-- PTS morphisms preserve derivability of judgments. -/
theorem Derivable.map {P Q : Specification} (φ : PTSMorphism P Q) {j : GJudgment P.Sorts}
    (h : j.Derivable P) : (j.map φ.sort).Derivable Q := by
  cases j with
  | typing Γ t A => exact HasType.mapSorts φ h
  | equation Γ t u A =>
    exact ⟨HasType.mapSorts φ h.1, HasType.mapSorts φ h.2.1, h.2.2.mapSorts φ.sort⟩

end GJudgment

/-- A semantics of an arbitrary PTS: a model category, satisfaction of
judgments, and soundness of derivable judgments (the PTS-generic `Semantics`). -/
structure GSemantics (P : Specification) where
  Model : Type 1
  [category : Category.{1} Model]
  sat : Model → GJudgment P.Sorts → Prop
  sound : ∀ {j}, j.Derivable P → ∀ M, sat M j

attribute [instance] GSemantics.category

namespace GSemantics

variable {P Q R : Specification}

/-- The single-signature room. -/
def room (N : GSemantics P) : Room.{0, 1, 1} :=
  ⟨GJudgment P.Sorts, Cat.of N.Model, N.sat⟩

/-- The single-signature institution. -/
def inst (N : GSemantics P) : Inst.{0, 0, 0, 1, 1} :=
  ⟨Discrete Unit, Discrete.functor (fun _ => N.room)⟩

/-- **Pullback along a PTS morphism.** Satisfaction of a `P`-judgment is
satisfaction of its translation; soundness is preserved derivability. -/
def pullback (φ : PTSMorphism P Q) (N : GSemantics Q) : GSemantics P where
  Model := N.Model
  sat X j := N.sat X (j.map φ.sort)
  sound h X := N.sound (h.map φ) X

/-- The corridor of the pullback: translate sentences, keep models. -/
def pullbackCorridor (φ : PTSMorphism P Q) (N : GSemantics Q) :
    (N.pullback φ).room ⟶ N.room :=
  ⟨GJudgment.map φ.sort, 𝟭 _, fun _ _ => Iff.rfl⟩

/-- **The general construction**: every PTS morphism `φ : P → Q` and semantics
of `Q` give an institution comorphism from the pulled-back semantics of `P`. -/
def pullbackComorphism (φ : PTSMorphism P Q) (N : GSemantics Q) :
    Inst.CoHom (N.pullback φ).inst N.inst where
  Φ := 𝟭 _
  ρ := Discrete.natTrans (fun _ => N.pullbackCorridor φ)

/-- The satisfaction condition of the pullback comorphism. -/
theorem pullback_sat (φ : PTSMorphism P Q) (N : GSemantics Q) (X : N.Model)
    (j : GJudgment P.Sorts) : (N.pullback φ).sat X j ↔ N.sat X (j.map φ.sort) :=
  Iff.rfl

/-- Pullback along the identity is the identity. -/
theorem pullback_id (N : GSemantics P) : N.pullback (PTSMorphism.id P) = N := by
  cases N
  simp only [pullback, PTSMorphism.id, GJudgment.map_id]

/-- Pullback is contravariantly functorial. -/
theorem pullback_comp (ψ : PTSMorphism Q R) (φ : PTSMorphism P Q) (N : GSemantics R) :
    N.pullback (ψ.comp φ) = (N.pullback ψ).pullback φ := by
  cases N
  simp only [pullback, PTSMorphism.comp, GJudgment.map_comp]

end GSemantics

/-! ## The cube as an instance -/

namespace PTSJudgment

/-- Cube judgments are the judgments over `CubeSort`. -/
def toG : PTSJudgment → GJudgment CubeSort
  | .typing Γ t A => .typing Γ t A
  | .equation Γ t u A => .equation Γ t u A

/-- The inverse of `toG`. -/
def ofG : GJudgment CubeSort → PTSJudgment
  | .typing Γ t A => .typing Γ t A
  | .equation Γ t u A => .equation Γ t u A

theorem ofG_toG (j : PTSJudgment) : ofG (toG j) = j := by
  cases j <;> rfl

theorem toG_ofG (j : GJudgment CubeSort) : toG (ofG j) = j := by
  cases j <;> rfl

theorem derivable_ofG (c : Corner) (j : GJudgment CubeSort) :
    (ofG j).Derivable c ↔ GJudgment.Derivable c.specification j := by
  cases j <;> exact Iff.rfl

end PTSJudgment

/-- A cube edge is a PTS morphism with identity sort map. -/
def Corner.ptsMorphism {c d : Corner} (h : c ≤ d) :
    PTSMorphism c.specification d.specification where
  sort := id
  ax _ _ := id
  rule := by
    intro s t u hr
    rcases hr with ⟨hu, harrow | hpoly | hcon | hdep⟩
    · exact ⟨hu, Or.inl harrow⟩
    · exact ⟨hu, Or.inr (Or.inl ⟨hpoly.1, hpoly.2.1, h.1 hpoly.2.2⟩)⟩
    · exact ⟨hu, Or.inr (Or.inr (Or.inl ⟨hcon.1, hcon.2.1, h.2.1 hcon.2.2⟩))⟩
    · exact ⟨hu, Or.inr (Or.inr (Or.inr ⟨hdep.1, hdep.2.1, h.2.2 hdep.2.2⟩))⟩

namespace Semantics

variable {c d e : Corner}

/-- A cube semantics as a PTS-generic semantics. -/
def toG (N : Semantics c) : GSemantics c.specification where
  Model := N.Model
  sat X j := N.sat X (PTSJudgment.ofG j)
  sound h X := N.sound ((PTSJudgment.derivable_ofG c _).mpr h) X

/-- Restrict a semantics along a cube edge: same models and satisfaction. -/
def restrict (h : c ≤ d) (N : Semantics d) : Semantics c where
  Model := N.Model
  sat := N.sat
  sound hj X := N.sound (PTSJudgment.inclusion h hj) X

/-- The restriction is a semantic inclusion with identity reduct. -/
def restrictInclusion (h : c ≤ d) (N : Semantics d) : SemanticInclusion h (N.restrict h) N :=
  ⟨𝟭 _, fun _ _ => Iff.rfl⟩

/-- The comorphism of a cube edge induced by a semantics of the larger corner. -/
def restrictComorphism (h : c ≤ d) (N : Semantics d) :
    Inst.CoHom (N.restrict h).inst N.inst :=
  (N.restrictInclusion h).comorphism

/-- Restriction is the cube instance of the general pullback construction. -/
theorem restrict_toG (h : c ≤ d) (N : Semantics d) :
    (N.restrict h).toG = N.toG.pullback (Corner.ptsMorphism h) := by
  cases N
  simp only [toG, restrict, GSemantics.pullback]
  congr
  funext X j
  congr 2
  exact (GJudgment.map_id j).symm

theorem restrict_refl (N : Semantics c) : N.restrict (le_refl c) = N := by
  cases N; rfl

theorem restrict_trans (h : c ≤ d) (k : d ≤ e) (N : Semantics e) :
    (N.restrict k).restrict h = N.restrict (h.trans k) := by
  rfl

end Semantics

end Silmaril.Calculi.LambdaCube
