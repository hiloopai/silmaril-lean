module

public import Silmaril.Logic.Institution.Hets.Lib.AlgebraI
public import Silmaril.Logic.Institution.Hets.CalculusExample
public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-!
# Hets-lib `Basic/Algebra_I`: the view `AbelianGroup_in_Ring_add` and Mathlib

Proofs about the selected presentations from `Basic/Algebra_I` (`Hets/Lib/AlgebraI.lean`), relating its
specifications to Mathlib's algebraic hierarchy.

* `view_derivable`: the proof obligation of the view `AbelianGroup_in_Ring_add` is derivable
  in the development-graph calculus (Subsumption: the view morphism is the composite of the
  renaming and the inclusions of the graph, `viewMor_eq`); `view_globalThm` by soundness.
* `rightInv_derivable`: the right-inverse law `∀ x • ∃ x' • x * x' = e` is derivable at the
  node `Group` (Basic Inference over first-order semantic consequence); the library's `Group`
  only asserts **left** inverses (`%(inv_Group)%`), so this is the classical one-sided group
  axioms theorem.
* Models from Mathlib: `monoidModel` (a Mathlib `Monoid` interprets the common signature of
  `Monoid`, `Group`, …),
  `addModel` (an additive monoid interprets `Monoid`'s signature with `e ↦ 0`, `* ↦ +`) and
  `ringModel`. `monoidModel_mem`, `groupModel_mem`, `addModel_mem_abelianGroup` and
  `ringModel_mem`: every Mathlib monoid, group, additive commutative group and ring is a model
  of the formalized presentation.
* Models to Mathlib: `monoidOfModel` and `groupOfModel` (via `Group.ofLeftAxioms`) turn
  models of the formalized `Monoid` and `Group` into Mathlib structures;
  `groupOfModel_monoidModel`: the round trip from a Mathlib group gives back the group, and
  `monoidOfModel_monoidModel`: the definitional link `Monoid → Group` is Mathlib's
  `Group.toMonoid`.
* `view_reduct_ringModel`: the view reduces the model of a Mathlib ring to the additive model
  of its underlying additive group (`Ring → AddCommGroup`), so the formalized view is Mathlib's
  forgetful map from rings to additive groups; with `view_globalThm` this re-derives that the
  additive group of a ring is a model of `AbelianGroup` (`addModel_mem_of_ring`).
* Independence: `monoid_not_implies_invGroup` (`ℕ` under multiplication is a monoid and not a
  group) and `group_not_implies_comm` (the permutations of `Fin 3` form a non-abelian group).

## References

* `cofi-2004-casl-reference-manual` in `references.bib`, Part V §4 (printed pages 393–394,
  PDF pages 407–408): `Monoid`, `Group`, `AbelianGroup`, `Ring`, `AbelianGroup_in_Ring_add`.
* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2 (PDF
  pages 13–14): the decomposition rules (Subsumption, Basic Inference).
-/

namespace Silmaril.Logic.Institution.Hets.Lib.AlgebraI

open CategoryTheory Silmaril.Logic.Institution.Examples Silmaril.Logic.Institution.Hets.CASL
  FinSig DevGraph Silmaril.Logic.Institution.Hets.CalculusExample

/-- The unit `e` of a structure for the signature of `Monoid`. -/
def oneOf (A : FOL.Structure monSig.toSignature) : A.carrier Elem :=
  A.op (Op.mk (D := monSig) ⟨0, by decide⟩) (fun j : Fin 0 => j.elim0)

/-- The operation `*` of a structure for the signature of `Monoid`. -/
def mulOf (A : FOL.Structure monSig.toSignature) (x y : A.carrier Elem) : A.carrier Elem :=
  A.op (Op.mk (D := monSig) ⟨1, by decide⟩) (![x, y] : Fin 2 → A.carrier Elem)

/-! ### Helpers: evaluation, satisfaction and the model classes of the nodes -/

/-- Equality of first-order signature morphisms, componentwise. -/
theorem hom_ext {Sg Sg' : FOL.Signature} {f g : FOL.Signature.Hom Sg Sg'}
    (hs : f.sorts = g.sorts)
    (ho : ∀ {n w s} (o : Sg.Op n w s), HEq (f.ops o) (g.ops o))
    (hr : ∀ {n w} (r : Sg.Rel n w), HEq (f.rels r) (g.rels r)) : f = g := by
  obtain ⟨⟨fs, fo⟩, fr⟩ := f
  obtain ⟨⟨gs, go⟩, gr⟩ := g
  obtain rfl : fs = gs := hs
  obtain rfl : @fo = @go := by
    funext n w s o
    exact eq_of_heq (ho o)
  obtain rfl : @fr = @gr := by
    funext n w r
    exact eq_of_heq (hr r)
  rfl

/-- Equality of first-order structures with the same carriers, componentwise. -/
theorem structure_eq {Sg : FOL.Signature} (c : Sg.S → Type)
    {o o' : ∀ {n : ℕ} {w : Fin n → Sg.S} {s : Sg.S}, Sg.Op n w s → (∀ j, c (w j)) → c s}
    {r r' : ∀ {n : ℕ} {w : Fin n → Sg.S}, Sg.Rel n w → (∀ j, c (w j)) → Prop}
    (ho : ∀ {n w s} (f : Sg.Op n w s) args, o f args = o' f args)
    (hr : ∀ {n w} (p : Sg.Rel n w) args, r p args = r' p args) :
    (⟨⟨c, o⟩, r⟩ : FOL.Structure Sg) = ⟨⟨c, o'⟩, r'⟩ := by
  obtain rfl : @o = @o' := by
    funext n w s f args
    exact ho f args
  obtain rfl : @r = @r' := by
    funext n w p args
    exact hr p args
  rfl

theorem eval_mul (A : FOL.Structure monSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (ρ : ∀ i, A.carrier (Γ i)) (t u : Tm monSig Γ Elem) :
    (mul t u).eval A.toAlgebra ρ = mulOf A (t.eval A.toAlgebra ρ) (u.eval A.toAlgebra ρ) :=
  congrArg (A.op (Op.mk (D := monSig) ⟨1, by decide⟩)) (funext fun j => by
    rcases j with ⟨_ | _ | n, hj⟩
    · rfl
    · rfl
    · change n + 1 + 1 < 2 at hj
      omega)

theorem eval_one (A : FOL.Structure monSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (ρ : ∀ i, A.carrier (Γ i)) : (one : Tm monSig Γ Elem).eval A.toAlgebra ρ = oneOf A :=
  congrArg (A.op (Op.mk (D := monSig) ⟨0, by decide⟩)) (funext fun j => Fin.elim0 j)

theorem eval_mul_mul_l (A : FOL.Structure monSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (ρ : ∀ i, A.carrier (Γ i)) (a b c : Tm monSig Γ Elem) :
    (mul (mul a b) c).eval A.toAlgebra ρ =
      mulOf A (mulOf A (a.eval A.toAlgebra ρ) (b.eval A.toAlgebra ρ)) (c.eval A.toAlgebra ρ) := by
  rw [eval_mul, eval_mul]

theorem eval_mul_mul_r (A : FOL.Structure monSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (ρ : ∀ i, A.carrier (Γ i)) (a b c : Tm monSig Γ Elem) :
    (mul a (mul b c)).eval A.toAlgebra ρ =
      mulOf A (a.eval A.toAlgebra ρ) (mulOf A (b.eval A.toAlgebra ρ) (c.eval A.toAlgebra ρ)) := by
  rw [eval_mul, eval_mul]

theorem eval_mul_one_l (A : FOL.Structure monSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (ρ : ∀ i, A.carrier (Γ i)) (a : Tm monSig Γ Elem) :
    (mul one a).eval A.toAlgebra ρ = mulOf A (oneOf A) (a.eval A.toAlgebra ρ) := by
  rw [eval_mul, eval_one]

theorem eval_mul_one_r (A : FOL.Structure monSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (ρ : ∀ i, A.carrier (Γ i)) (a : Tm monSig Γ Elem) :
    (mul a one).eval A.toAlgebra ρ = mulOf A (a.eval A.toAlgebra ρ) (oneOf A) := by
  rw [eval_mul, eval_one]

/-- A universally closed equation over the signature of `Monoid`. -/
theorem holds_eq_closed (A : FOL.Structure monSig.toSignature) {k : ℕ}
    (t u : Tm monSig (ctx k) Elem) :
    (closed (ctx k) (.eq t u)).Holds A ↔
      ∀ ρ : Fin k → A.carrier Elem, t.eval A.toAlgebra ρ = u.eval A.toAlgebra ρ :=
  holds_closed A _

/-- `∀ x • ∃ x' • t = u` over the signature of `Monoid` (`x'` is variable `0`). -/
theorem holds_ex_closed (A : FOL.Structure monSig.toSignature) (t u : Tm monSig (ctx 2) Elem) :
    (closed (ctx 1) (ex (Δ := ctx 2) rfl (.eq t u))).Holds A ↔
      ∀ x : A.carrier Elem, ∃ x' : A.carrier Elem,
        t.eval A.toAlgebra ![x', x] = u.eval A.toAlgebra ![x', x] := by
  refine (holds_closed A _).trans ⟨fun h x => ?_, fun h ρ => ?_⟩
  · have hx := h ![x]
    refine Classical.byContradiction fun hc => hx fun ρ' hρ' he => hc ⟨ρ' 0, ?_⟩
    have e1 : ρ' 1 = x := eq_of_heq (hρ' 0)
    have e : (ρ' : Fin 2 → A.carrier Elem) = ![ρ' 0, x] := by
      funext i
      rcases i with ⟨_ | _ | n, hi⟩
      · rfl
      · exact e1
      · omega
    rw [← e]
    exact he
  · intro hall
    obtain ⟨x', hx'⟩ := h (ρ 0)
    refine hall ![x', ρ 0] (fun i => ?_) hx'
    obtain rfl := Fin.fin_one_eq_zero i
    exact HEq.rfl

theorem sat_assoc (A : FOL.Structure monSig.toSignature) :
    assocAx.Holds A ↔ ∀ x y z, mulOf A (mulOf A x y) z = mulOf A x (mulOf A y z) := by
  refine (holds_eq_closed A _ _).trans ⟨fun h x y z => ?_, fun h ρ => ?_⟩
  · have hxyz := h ![z, y, x]
    rw [eval_mul_mul_l, eval_mul_mul_r] at hxyz
    exact hxyz
  · rw [eval_mul_mul_l, eval_mul_mul_r]
    exact h _ _ _

theorem sat_unitL (A : FOL.Structure monSig.toSignature) :
    unitLAx.Holds A ↔ ∀ x, mulOf A (oneOf A) x = x := by
  refine (holds_eq_closed A _ _).trans ⟨fun h x => ?_, fun h ρ => ?_⟩
  · have hx := h ![x]
    rw [eval_mul_one_l] at hx
    exact hx
  · rw [eval_mul_one_l]
    exact h _

theorem sat_unitR (A : FOL.Structure monSig.toSignature) :
    unitRAx.Holds A ↔ ∀ x, mulOf A x (oneOf A) = x := by
  refine (holds_eq_closed A _ _).trans ⟨fun h x => ?_, fun h ρ => ?_⟩
  · have hx := h ![x]
    rw [eval_mul_one_r] at hx
    exact hx
  · rw [eval_mul_one_r]
    exact h _

theorem sat_comm (A : FOL.Structure monSig.toSignature) :
    commAx.Holds A ↔ ∀ x y, mulOf A x y = mulOf A y x := by
  refine (holds_eq_closed A _ _).trans ⟨fun h x y => ?_, fun h ρ => ?_⟩
  · have hxy := h ![y, x]
    rw [eval_mul, eval_mul] at hxy
    exact hxy
  · rw [eval_mul, eval_mul]
    exact h _ _

theorem sat_invGroup (A : FOL.Structure monSig.toSignature) :
    invGroupAx.Holds A ↔ ∀ x, ∃ x', mulOf A x' x = oneOf A :=
  (holds_ex_closed A _ _).trans
    (forall_congr' fun _ => exists_congr fun _ => Eq.congr (eval_mul A _ _ _) (eval_one A _))

theorem sat_rightInv (A : FOL.Structure monSig.toSignature) :
    rightInvAx.Holds A ↔ ∀ x, ∃ x', mulOf A x x' = oneOf A :=
  (holds_ex_closed A _ _).trans
    (forall_congr' fun _ => exists_congr fun _ => Eq.congr (eval_mul A _ _ _) (eval_one A _))


/-- The axioms of `Monoid`, in terms of `mulOf` and `oneOf`. -/
def MonLaws (A : FOL.Structure monSig.toSignature) : Prop :=
  (∀ x y z, mulOf A (mulOf A x y) z = mulOf A x (mulOf A y z)) ∧
    (∀ x, mulOf A (oneOf A) x = x) ∧ (∀ x, mulOf A x (oneOf A) = x)

/-- `%(inv_Group)%`, in terms of `mulOf` and `oneOf`. -/
def LeftInv (A : FOL.Structure monSig.toSignature) : Prop :=
  ∀ x, ∃ x', mulOf A x' x = oneOf A

/-- `comm`, in terms of `mulOf`. -/
def CommLaw (A : FOL.Structure monSig.toSignature) : Prop :=
  ∀ x y, mulOf A x y = mulOf A y x

theorem monAx_iff (A : FOL.Structure monSig.toSignature) :
    (∀ φ ∈ ({assocAx, unitLAx, unitRAx} : Set (FOL.Sentence monSig.toSignature)), φ.Holds A) ↔
      MonLaws A := by
  constructor
  · intro h
    exact ⟨(sat_assoc A).1 (h _ (Or.inl rfl)), (sat_unitL A).1 (h _ (Or.inr (Or.inl rfl))),
      (sat_unitR A).1 (h _ (Or.inr (Or.inr rfl)))⟩
  · rintro ⟨h1, h2, h3⟩ φ hφ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
    rcases hφ with rfl | rfl | rfl
    exacts [(sat_assoc A).2 h1, (sat_unitL A).2 h2, (sat_unitR A).2 h3]

/-- The model class of a node: local axioms and reducts along incoming global definition links
(the graph has no local and no hiding definition links). -/
theorem mem_models {N : Node} {A : (FOL.institution.obj (sig N)).Mod} :
    A ∈ graph.models N ↔ (∀ φ ∈ axioms N, (FOL.institution.obj (sig N)).Sat A φ) ∧
      ∀ K, ∀ σ ∈ globalDef K N, reduct (I := FOL.institution) σ A ∈ graph.models K :=
  (graph.mem_models_iff N A).trans ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, fun _ _ h => (h : False).elim, fun _ _ h => (h : False).elim⟩⟩

theorem mem_monoid_iff (A : FOL.Structure monSig.toSignature) :
    A ∈ graph.models .monoid ↔ MonLaws A := by
  refine mem_models.trans ?_
  rw [← monAx_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun K σ hσ => by cases K <;> exact (hσ : False).elim⟩⟩

theorem mem_group_iff (A : FOL.Structure monSig.toSignature) :
    A ∈ graph.models .group ↔ MonLaws A ∧ LeftInv A := by
  refine mem_models.trans ?_
  constructor
  · rintro ⟨hax, hg⟩
    exact ⟨(mem_monoid_iff (reduct (I := FOL.institution) idM A)).1 (hg .monoid idM rfl),
      (sat_invGroup A).1 (hax _ rfl)⟩
  · rintro ⟨hm, hi⟩
    refine ⟨fun φ hφ => ?_, fun K σ hσ => ?_⟩
    · obtain rfl : φ = invGroupAx := hφ
      exact (sat_invGroup A).2 hi
    · cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = idM := hσ
      exact (mem_monoid_iff _).2 hm

theorem mem_commMonoid_iff (A : FOL.Structure monSig.toSignature) :
    A ∈ graph.models .commMonoid ↔ MonLaws A ∧ CommLaw A := by
  refine mem_models.trans ?_
  constructor
  · rintro ⟨hax, hg⟩
    exact ⟨(mem_monoid_iff (reduct (I := FOL.institution) idM A)).1 (hg .monoid idM rfl),
      (sat_comm A).1 (hax _ rfl)⟩
  · rintro ⟨hm, hc⟩
    refine ⟨fun φ hφ => ?_, fun K σ hσ => ?_⟩
    · obtain rfl : φ = commAx := hφ
      exact (sat_comm A).2 hc
    · cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = idM := hσ
      exact (mem_monoid_iff _).2 hm

theorem mem_abelianGroup_iff (A : FOL.Structure monSig.toSignature) :
    A ∈ graph.models .abelianGroup ↔ MonLaws A ∧ LeftInv A ∧ CommLaw A := by
  refine mem_models.trans ?_
  constructor
  · rintro ⟨-, hg⟩
    have h1 := (mem_group_iff _).1 (hg .group idM rfl)
    have h2 := (mem_commMonoid_iff _).1 (hg .commMonoid idM rfl)
    exact ⟨h1.1, h1.2, h2.2⟩
  · rintro ⟨hm, hi, hc⟩
    refine ⟨fun φ hφ => (hφ : False).elim, fun K σ hσ => ?_⟩
    cases K <;> try exact (hσ : False).elim
    · obtain rfl : σ = idM := hσ
      exact (mem_commMonoid_iff _).2 ⟨hm, hc⟩
    · obtain rfl : σ = idM := hσ
      exact (mem_group_iff _).2 ⟨hm, hi⟩

theorem mem_abGroupAdd_iff (B : FOL.Structure addSig.toSignature) :
    B ∈ graph.models .abGroupAdd ↔
      reduct (I := FOL.institution) renAdd.toHom B ∈ graph.models .abelianGroup := by
  refine mem_models.trans ?_
  constructor
  · rintro ⟨-, hg⟩
    exact hg .abelianGroup renAdd.toHom rfl
  · intro h
    refine ⟨fun φ hφ => (hφ : False).elim, fun K σ hσ => ?_⟩
    cases K <;> try exact (hσ : False).elim
    obtain rfl : σ = renAdd.toHom := hσ
    exact h

theorem mem_ringUnion_iff (C : FOL.Structure ringSig.toSignature) :
    C ∈ graph.models .ringUnion ↔
      reduct (I := FOL.institution) inclAdd.toHom C ∈ graph.models .abGroupAdd ∧
        reduct (I := FOL.institution) inclMon.toHom C ∈ graph.models .monoid := by
  refine mem_models.trans ?_
  constructor
  · rintro ⟨-, hg⟩
    exact ⟨hg .abGroupAdd inclAdd.toHom rfl, hg .monoid inclMon.toHom rfl⟩
  · rintro ⟨ha, hm⟩
    refine ⟨fun φ hφ => (hφ : False).elim, fun K σ hσ => ?_⟩
    cases K <;> try exact (hσ : False).elim
    · obtain rfl : σ = inclMon.toHom := hσ
      exact hm
    · obtain rfl : σ = inclAdd.toHom := hσ
      exact ha

theorem mem_ring_iff (D : FOL.Structure ringSig.toSignature) :
    D ∈ graph.models .ring ↔ distr1Ax.Holds D ∧ distr2Ax.Holds D ∧
      reduct (I := FOL.institution) idRg D ∈ graph.models .ringUnion := by
  refine mem_models.trans ?_
  constructor
  · rintro ⟨hax, hg⟩
    exact ⟨hax _ (Or.inl rfl), hax _ (Or.inr rfl), hg .ringUnion idRg rfl⟩
  · rintro ⟨h1, h2, hu⟩
    refine ⟨fun φ hφ => ?_, fun K σ hσ => ?_⟩
    · obtain rfl | rfl : φ = distr1Ax ∨ φ = distr2Ax := hφ
      exacts [h1, h2]
    · cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = idRg := hσ
      exact hu

/-! ### The view and an additional goal in the calculus -/

/-- The view morphism is the composite of the renaming `renAdd`, the inclusion `inclAdd` and
the identity along which `Ring` extends the union. -/
theorem viewMor_eq : viewMor.toHom = renAdd.toHom ≫ inclAdd.toHom ≫ idRg := by
  refine hom_ext (f := viewMor.toHom) (g := renAdd.toHom ≫ inclAdd.toHom ≫ idRg) rfl
    (fun o => ?_) (fun r => ?_)
  · cases o with
    | mk i =>
      rcases i with ⟨_ | _ | n, hi⟩
      · rfl
      · rfl
      · change n + 1 + 1 < 2 at hi
        omega
  · cases r with
    | mk i => exact i.elim0

/-- **The view `AbelianGroup_in_Ring_add` is derivable** with Subsumption.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF page 13: rule Subsumption). -/
theorem view_derivable :
    Derivable Rule.decomposition (semEnt FOL.institution) graph viewGoal := by
  show Derivable _ _ graph (.glob .abelianGroup .ring viewMor.toHom)
  rw [viewMor_eq]
  have h3 : graph.GlobReach .ringUnion .ring idRg :=
    GlobReach.of_globalDef (G := graph) (Set.mem_singleton _)
  have h2 : graph.GlobReach .abGroupAdd .ring (inclAdd.toHom ≫ idRg) :=
    GlobReach.step (G := graph) (M := .abGroupAdd) (K := .ringUnion) (N := .ring)
      (σ' := inclAdd.toHom) (σ'' := idRg) (Set.mem_singleton _) h3
  have h1 : graph.GlobReach .abelianGroup .ring (renAdd.toHom ≫ inclAdd.toHom ≫ idRg) :=
    GlobReach.step (G := graph) (M := .abelianGroup) (K := .abGroupAdd) (N := .ring)
      (σ' := renAdd.toHom) (σ'' := inclAdd.toHom ≫ idRg) (Set.mem_singleton _) h2
  exact .subsumption (by simp [Rule.decomposition]) h1

/-- The view holds, by soundness of the calculus. -/
theorem view_globalThm : graph.GlobalThm .abelianGroup .ring viewMor.toHom :=
  view_derivable.sound fun _ _ _ h => h

/-- **Right inverses in `Group`** are derivable with Basic Inference over first-order semantic
consequence. -/
theorem rightInv_derivable :
    Derivable Rule.decomposition (semEnt FOL.institution) graph (.impl .group {rightInvAx}) := by
  refine .basicInference (by simp [Rule.decomposition]) fun φ hφ => ?_
  obtain rfl : φ = rightInvAx := hφ
  intro A hA
  have hinv : LeftInv A := (sat_invGroup A).1 (hA _ (Or.inl rfl))
  have hreach : graph.LocReach .monoid .group idM :=
    Or.inl (GlobReach.of_globalDef (G := graph) (M := .monoid) (N := .group) (σ := idM)
      (Set.mem_singleton _))
  have hmon : MonLaws A := (monAx_iff (reduct (I := FOL.institution) idM A)).1 fun ψ hψ =>
    ((FOL.institution.map idM).sat A ψ).1 (hA _ (Or.inr ⟨.monoid, idM, hreach, ψ, hψ, rfl⟩))
  let _ : Mul (A.carrier Elem) := ⟨mulOf A⟩
  let _ : One (A.carrier Elem) := ⟨oneOf A⟩
  let _ : Inv (A.carrier Elem) := ⟨fun x => Classical.choose (hinv x)⟩
  let _ : Group (A.carrier Elem) :=
    Group.ofLeftAxioms hmon.1 hmon.2.1 fun x => Classical.choose_spec (hinv x)
  exact (sat_rightInv A).2 fun x => ⟨x⁻¹, mul_inv_cancel x⟩

/-- The development graph is faithful to the structured specifications.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Theorem 5.19
(printed page 137, PDF page 139). -/
theorem models_eq_spec (N : Node) : graph.models N = (spec N).models := by
  have hM : graph.models .monoid = monoidSpec.models := by
    ext A
    refine mem_models.trans ?_
    exact ⟨fun h => h.1, fun h => ⟨h, fun K σ hσ => by cases K <;> exact (hσ : False).elim⟩⟩
  have hCM : graph.models .commMonoid = commMonoidSpec.models := by
    ext A
    refine mem_models.trans ?_
    constructor
    · rintro ⟨hax, hg⟩
      have h1 := hg .monoid idM rfl
      rw [hM] at h1
      exact ⟨h1, hax⟩
    · rintro ⟨h1, hax⟩
      refine ⟨hax, fun K σ hσ => ?_⟩
      cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = idM := hσ
      rw [hM]
      exact h1
  have hG : graph.models .group = groupSpec.models := by
    ext A
    refine mem_models.trans ?_
    constructor
    · rintro ⟨hax, hg⟩
      have h1 := hg .monoid idM rfl
      rw [hM] at h1
      exact ⟨h1, hax⟩
    · rintro ⟨h1, hax⟩
      refine ⟨hax, fun K σ hσ => ?_⟩
      cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = idM := hσ
      rw [hM]
      exact h1
  have hAG : graph.models .abelianGroup = abelianGroupSpec.models := by
    ext A
    refine mem_models.trans ?_
    constructor
    · rintro ⟨-, hg⟩
      have h1 := hg .group idM rfl
      have h2 := hg .commMonoid idM rfl
      rw [hG] at h1
      rw [hCM] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun φ hφ => (hφ : False).elim, fun K σ hσ => ?_⟩
      cases K <;> try exact (hσ : False).elim
      · obtain rfl : σ = idM := hσ
        rw [hCM]
        exact h2
      · obtain rfl : σ = idM := hσ
        rw [hG]
        exact h1
  have hAA : graph.models .abGroupAdd = abGroupAddSpec.models := by
    ext B
    refine mem_models.trans ?_
    constructor
    · rintro ⟨-, hg⟩
      have h1 := hg .abelianGroup renAdd.toHom rfl
      rw [hAG] at h1
      exact h1
    · intro h1
      refine ⟨fun φ hφ => (hφ : False).elim, fun K σ hσ => ?_⟩
      cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = renAdd.toHom := hσ
      rw [hAG]
      exact h1
  have hRU : graph.models .ringUnion = ringUnionSpec.models := by
    ext C
    refine mem_models.trans ?_
    constructor
    · rintro ⟨-, hg⟩
      have h1 := hg .abGroupAdd inclAdd.toHom rfl
      have h2 := hg .monoid inclMon.toHom rfl
      rw [hAA] at h1
      rw [hM] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun φ hφ => (hφ : False).elim, fun K σ hσ => ?_⟩
      cases K <;> try exact (hσ : False).elim
      · obtain rfl : σ = inclMon.toHom := hσ
        rw [hM]
        exact h2
      · obtain rfl : σ = inclAdd.toHom := hσ
        rw [hAA]
        exact h1
  have hR : graph.models .ring = ringSpec.models := by
    ext D
    refine mem_models.trans ?_
    constructor
    · rintro ⟨hax, hg⟩
      have h1 := hg .ringUnion idRg rfl
      rw [hRU] at h1
      exact ⟨h1, hax⟩
    · rintro ⟨h1, hax⟩
      refine ⟨hax, fun K σ hσ => ?_⟩
      cases K <;> try exact (hσ : False).elim
      obtain rfl : σ = idRg := hσ
      rw [hRU]
      exact h1
  cases N
  exacts [hM, hCM, hG, hAG, hAA, hRU, hR]

/-! ### Models from Mathlib -/

/-- A Mathlib monoid as a structure for the signature of `Monoid`: `e ↦ 1`, `* ↦ *`. -/
def monoidModel (M : Type) [Monoid M] : FOL.Structure monSig.toSignature :=
  model1 monSig M
    (fun i l =>
      match i.val, l with
      | 0, _ => 1
      | _, [x, y] => x * y
      | _, _ => 1)
    fun i _ => i.elim0

/-- An additive monoid as a structure for the signature of `Monoid`: `e ↦ 0`, `* ↦ +`. -/
def addModel (A : Type) [AddMonoid A] : FOL.Structure monSig.toSignature :=
  model1 monSig A
    (fun i l =>
      match i.val, l with
      | 0, _ => 0
      | _, [x, y] => x + y
      | _, _ => 0)
    fun i _ => i.elim0

/-- A Mathlib ring as a structure for the signature of `Ring`. -/
def ringModel (R : Type) [Ring R] : FOL.Structure ringSig.toSignature :=
  model1 ringSig R
    (fun i l =>
      match i.val, l with
      | 0, _ => 0
      | 1, [x, y] => x + y
      | 2, _ => 1
      | 3, [x, y] => x * y
      | _, _ => 0)
    fun i _ => i.elim0

/-- Every Mathlib monoid is a model of `Monoid`. -/
theorem monoidModel_mem (M : Type) [Monoid M] : monoidModel M ∈ graph.models .monoid :=
  (mem_monoid_iff _).2
    ⟨fun x y z => @mul_assoc M _ x y z, fun x => @one_mul M _ x, fun x => @mul_one M _ x⟩

/-- Every Mathlib group is a model of `Group`. -/
theorem groupModel_mem (G : Type) [Group G] : monoidModel G ∈ graph.models .group :=
  (mem_group_iff _).2
    ⟨(mem_monoid_iff _).1 (monoidModel_mem G), fun x => ⟨@Inv.inv G _ x, @inv_mul_cancel G _ x⟩⟩

/-- Every Mathlib additive commutative group is a model of `AbelianGroup`. -/
theorem addModel_mem_abelianGroup (A : Type) [AddCommGroup A] :
    addModel A ∈ graph.models .abelianGroup :=
  (mem_abelianGroup_iff _).2
    ⟨⟨fun x y z => @add_assoc A _ x y z, fun x => @zero_add A _ x, fun x => @add_zero A _ x⟩,
      fun x => ⟨@Neg.neg A _ x, @neg_add_cancel A _ x⟩, fun x y => @add_comm A _ x y⟩

theorem sat_distr1 (R : Type) [Ring R] : distr1Ax.Holds (ringModel R) :=
  (holds_closed (ringModel R) _).2 fun ρ => (fun a b c : R => add_mul a b c) (ρ 2) (ρ 1) (ρ 0)

theorem sat_distr2 (R : Type) [Ring R] : distr2Ax.Holds (ringModel R) :=
  (holds_closed (ringModel R) _).2 fun ρ => (fun a b c : R => mul_add c a b) (ρ 2) (ρ 1) (ρ 0)

/-- Every Mathlib ring is a model of `Ring`. -/
theorem ringModel_mem (R : Type) [Ring R] : ringModel R ∈ graph.models .ring :=
  (mem_ring_iff _).2 ⟨sat_distr1 R, sat_distr2 R, (mem_ringUnion_iff _).2
    ⟨(mem_abGroupAdd_iff _).2 ((mem_abelianGroup_iff _).2
      ⟨⟨fun x y z => @add_assoc R _ x y z, fun x => @zero_add R _ x,
          fun x => @add_zero R _ x⟩,
        fun x => ⟨@Neg.neg R _ x, @neg_add_cancel R _ x⟩, fun x y => @add_comm R _ x y⟩),
      (mem_monoid_iff _).2
        ⟨fun x y z => @mul_assoc R _ x y z, fun x => @one_mul R _ x,
          fun x => @mul_one R _ x⟩⟩⟩

/-! ### Models to Mathlib -/

/-- The axioms of `Monoid` in a model of `Monoid`. -/
theorem monoid_laws {A : FOL.Structure monSig.toSignature} (hA : A ∈ graph.models .monoid) :
    (∀ x y z, mulOf A (mulOf A x y) z = mulOf A x (mulOf A y z)) ∧
      (∀ x, mulOf A (oneOf A) x = x) ∧ (∀ x, mulOf A x (oneOf A) = x) :=
  (mem_monoid_iff A).1 hA

/-- A model of `Group` has left inverses. -/
theorem exists_leftInv {A : FOL.Structure monSig.toSignature} (hA : A ∈ graph.models .group)
    (x : A.carrier Elem) : ∃ x', mulOf A x' x = oneOf A :=
  ((mem_group_iff A).1 hA).2 x

/-- A model of `Group` is a model of `Monoid` (the definitional link `Monoid → Group` along the
identity). -/
theorem mem_monoid_of_mem_group {A : FOL.Structure monSig.toSignature}
    (hA : A ∈ graph.models .group) : A ∈ graph.models .monoid :=
  (mem_monoid_iff A).2 ((mem_group_iff A).1 hA).1

/-- The Mathlib monoid of a model of `Monoid`. -/
@[instance_reducible]
def monoidOfModel (A : FOL.Structure monSig.toSignature) (hA : A ∈ graph.models .monoid) :
    Monoid (A.carrier Elem) where
  mul := mulOf A
  one := oneOf A
  mul_assoc := (monoid_laws hA).1
  one_mul := (monoid_laws hA).2.1
  mul_one := (monoid_laws hA).2.2

/-- **The Mathlib group of a model of `Group`**, from the one-sided axioms of the library by
`Group.ofLeftAxioms`. -/
@[instance_reducible]
noncomputable def groupOfModel (A : FOL.Structure monSig.toSignature)
    (hA : A ∈ graph.models .group) : Group (A.carrier Elem) :=
  letI : Mul (A.carrier Elem) := ⟨mulOf A⟩
  letI : One (A.carrier Elem) := ⟨oneOf A⟩
  letI : Inv (A.carrier Elem) := ⟨fun x => Classical.choose (exists_leftInv hA x)⟩
  Group.ofLeftAxioms (monoid_laws (mem_monoid_of_mem_group hA)).1
    (monoid_laws (mem_monoid_of_mem_group hA)).2.1
    fun x => Classical.choose_spec (exists_leftInv hA x)

/-- The definitional link `Monoid → Group` is `Group.toMonoid`: the Mathlib monoid of the
model of a Mathlib group is the group's monoid. -/
theorem monoidOfModel_monoidModel (G : Type) [Group G] :
    monoidOfModel (monoidModel G) (mem_monoid_of_mem_group (groupModel_mem G)) =
      (inferInstance : Group G).toMonoid :=
  Monoid.ext (by funext x y; rfl)

/-- **Round trip**: the Mathlib group of the model of a Mathlib group is the group itself. -/
theorem groupOfModel_monoidModel (G : Type) [Group G] :
    groupOfModel (monoidModel G) (groupModel_mem G) = (inferInstance : Group G) :=
  Group.ext (by funext x y; rfl)

/-- **The view is the forgetful map from rings to additive groups**: the view reduces the
model of a Mathlib ring to the additive model of its additive group. -/
theorem view_reduct_ringModel (R : Type) [Ring R] :
    reduct (I := FOL.institution) viewMor.toHom (ringModel R) = addModel R := by
  refine structure_eq (fun _ => R) (fun f args => ?_) (fun p _ => ?_)
  · cases f with
    | mk i =>
      rcases i with ⟨_ | _ | n, hi⟩
      · rfl
      · rfl
      · change n + 1 + 1 < 2 at hi
        omega
  · cases p with
    | mk i => exact i.elim0

/-- The additive group of a Mathlib ring is a model of `AbelianGroup`, derived from the view. -/
theorem addModel_mem_of_ring (R : Type) [Ring R] : addModel R ∈ graph.models .abelianGroup :=
  view_reduct_ringModel R ▸ view_globalThm _ (ringModel_mem R)

/-! ### Independence -/

/-- **`Monoid` does not prove `%(inv_Group)%`**: `ℕ` under multiplication is a monoid and `0`
has no inverse. -/
theorem monoid_not_implies_invGroup : ¬ graph.LocalImpl .monoid {invGroupAx} := by
  intro h
  obtain ⟨x', hx'⟩ : ∃ x' : ℕ, x' * 0 = 1 := (sat_invGroup (monoidModel ℕ)).1
    (h (monoidModel ℕ) (monoidModel_mem ℕ) invGroupAx (Set.mem_singleton _)) (0 : ℕ)
  simp at hx'

/-- **`Group` does not prove commutativity**: the permutations of `Fin 3`. -/
theorem group_not_implies_comm : ¬ graph.LocalImpl .group {commAx} := by
  intro h
  have hc := (sat_comm (monoidModel (Equiv.Perm (Fin 3)))).1
    (h (monoidModel (Equiv.Perm (Fin 3))) (groupModel_mem (Equiv.Perm (Fin 3))) commAx
      (Set.mem_singleton _))
  have h01 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 0 =
      (Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 0 :=
    congrArg (fun f : Equiv.Perm (Fin 3) => f 0)
      (hc (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2))
  exact absurd h01 (by decide)

end Silmaril.Logic.Institution.Hets.Lib.AlgebraI
