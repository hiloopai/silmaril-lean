module

public import Silmaril.Logic.Institution.Hets.Lib.RelationsAndOrders
public import Silmaril.Logic.Institution.Hets.CalculusExample
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

/-!
# Hets-lib `Basic/RelationsAndOrders`: the `%implies` obligation and Mathlib

Proofs about the selected presentations from `Basic/RelationsAndOrders`
(`Hets/Lib/RelationsAndOrders.lean`).

* `implies_derivable`: the proof obligation of the `%implies` annotation in `StrictOrder`,
  `IrreflexiveRelation and TransitiveRelation ⊢ AsymmetricRelation`, is **derivable** in the
  development-graph calculus with the decomposition rules (Glob-Decomposition, Local Inference,
  Basic Inference) over first-order semantic consequence; `implies_globalThm` is the theorem
  link, by soundness (`DevGraph.Derivable.sound`), and `implies_holds` is the CASL semantics
  of the annotation (the model classes before and after the extension agree).
* `models_eq_spec`: the development graph is faithful to the structured specifications: the
  model class of each node is that of its specification.
* Mathlib: a relation `r` on `α` gives a model of the signature of `Relation` (`relModel`),
  `<` and `≤` give models of the signatures of `StrictOrder` and of `PreOrder`, `PartialOrder`,
  `TotalOrder`. The formalized presentations axiomatize exactly Mathlib's unbundled order
  classes: `ltModel_mem_strictOrder_iff` (`IsStrictOrder`), `leModel_mem_preOrder_iff`
  (`IsPreorder`), `leModel_mem_partialOrder_iff` (`IsPartialOrder`),
  `leModel_mem_totalOrder_iff` (`IsLinearOrder`).
* `asymm_of_isStrictOrder`: every strict order in Mathlib's sense is asymmetric, derived from
  the formalized theorem link `implies_globalThm` (Mathlib proves this directly as an instance of
  `Std.Asymm`).
* `irreflexive_not_implies_asym`: the obligation needs transitivity: `≠` on `Bool` is an
  irreflexive relation that is not asymmetric.
* Helpers: `holds_reflAx`, …, `holds_dichotomyAx` read each formalized axiom as a statement
  about the interpreted relation (`relOf`, `leOf`, `ltOf`); `mem_reflexive`, … unfold the
  definition links of each node; `sem_irrTrans`, `sem_preOrder`, … combine both.

## References

* `cofi-2004-casl-reference-manual` in `references.bib`, Part V §3 (printed page 389,
  PDF page 403: `StrictOrder`) and Part II §5.2.5 (printed page 111, PDF page 125: semantics
  of `%implies`).
* `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2 and
  Proposition 13 (PDF pages 13–15): the decomposition rules and their soundness.
-/

namespace Silmaril.Logic.Institution.Hets.Lib.RelationsAndOrders

open CategoryTheory Silmaril.Logic.Institution.Examples Silmaril.Logic.Institution.Hets.CASL
  FinSig DevGraph Silmaril.Logic.Institution.Hets.CalculusExample


/-! ### Semantics of the formalized axioms

The interpretation of the single predicate symbol of `relSig`, `leSig` and `ltSig` in a
structure, and the meaning of each formalized axiom in terms of it. -/

/-- The interpretation of `__~__` in a structure for the signature of `Relation`. -/
def relOf (M : FOL.Structure relSig.toSignature) (x y : M.carrier Elem) : Prop :=
  M.rel (Rel.mk (D := relSig) ⟨0, by decide⟩) (![x, y] : Fin 2 → M.carrier Elem)

/-- The interpretation of `__<=__` in a structure for the signature of `PreOrder`. -/
def leOf (M : FOL.Structure leSig.toSignature) (x y : M.carrier Elem) : Prop :=
  M.rel (Rel.mk (D := leSig) ⟨0, by decide⟩) (![x, y] : Fin 2 → M.carrier Elem)

/-- The interpretation of `__<__` in a structure for the signature of `StrictOrder`. -/
def ltOf (M : FOL.Structure ltSig.toSignature) (x y : M.carrier Elem) : Prop :=
  M.rel (Rel.mk (D := ltSig) ⟨0, by decide⟩) (![x, y] : Fin 2 → M.carrier Elem)

theorem holds_sim (M : FOL.Structure relSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (t u : Tm relSig Γ Elem) (ρ : ∀ i, M.carrier (Γ i)) :
    (sim t u).Holds M ρ ↔ relOf M (t.eval M.toAlgebra ρ) (u.eval M.toAlgebra ρ) := by
  refine Iff.of_eq (congrArg (M.rel (Rel.mk (D := relSig) ⟨0, by decide⟩)) (funext fun j => ?_))
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨n + 2, h⟩ => exact absurd h (by change ¬ (n + 2 < 2); omega)

theorem holds_le (M : FOL.Structure leSig.toSignature) {k : ℕ} {Γ : Fin k → Fin 1}
    (t u : Tm leSig Γ Elem) (ρ : ∀ i, M.carrier (Γ i)) :
    (le t u).Holds M ρ ↔ leOf M (t.eval M.toAlgebra ρ) (u.eval M.toAlgebra ρ) := by
  refine Iff.of_eq (congrArg (M.rel (Rel.mk (D := leSig) ⟨0, by decide⟩)) (funext fun j => ?_))
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨n + 2, h⟩ => exact absurd h (by change ¬ (n + 2 < 2); omega)

theorem holds_reflAx (M : FOL.Structure relSig.toSignature) :
    reflAx.Holds M ↔ ∀ x, relOf M x x := by
  refine (holds_closed M _).trans ?_
  exact ⟨fun h x => (holds_sim M _ _ _).1 (h fun _ => x),
    fun h ρ => (holds_sim M _ _ _).2 (h (ρ 0))⟩

theorem holds_irreflAx (M : FOL.Structure relSig.toSignature) :
    irreflAx.Holds M ↔ ∀ x, ¬ relOf M x x := by
  refine (holds_closed M _).trans ?_
  exact ⟨fun h x hx => h (fun _ => x) ((holds_sim M _ _ _).2 hx),
    fun h ρ hρ => h (ρ 0) ((holds_sim M _ _ _).1 hρ)⟩

theorem holds_asymAx (M : FOL.Structure relSig.toSignature) :
    asymAx.Holds M ↔ ∀ x y, relOf M x y → ¬ relOf M y x := by
  refine (holds_closed M _).trans ?_
  exact ⟨fun h x y hxy hyx =>
      (holds_imp M _ _ _).1 (h (![x, y] : Fin 2 → M.carrier Elem))
        ((holds_sim M _ _ _).2 hxy) ((holds_sim M _ _ _).2 hyx),
    fun h ρ => (holds_imp M _ _ _).2 fun h1 h2 =>
      h (ρ 0) (ρ 1) ((holds_sim M _ _ _).1 h1) ((holds_sim M _ _ _).1 h2)⟩

theorem holds_antisymAx (M : FOL.Structure relSig.toSignature) :
    antisymAx.Holds M ↔ ∀ x y, relOf M x y → relOf M y x → x = y := by
  refine (holds_closed M _).trans ?_
  exact ⟨fun h x y hxy hyx =>
      (holds_imp M _ _ _).1 (h (![y, x] : Fin 2 → M.carrier Elem))
        ⟨(holds_sim M _ _ _).2 hxy, (holds_sim M _ _ _).2 hyx⟩,
    fun h ρ => (holds_imp M _ _ _).2 fun hρ =>
      h (ρ 1) (ρ 0) ((holds_sim M _ _ _).1 hρ.1) ((holds_sim M _ _ _).1 hρ.2)⟩

theorem holds_transAx (M : FOL.Structure relSig.toSignature) :
    transAx.Holds M ↔ ∀ x y z, relOf M x y → relOf M y z → relOf M x z := by
  refine (holds_closed M _).trans ?_
  exact ⟨fun h x y z hxy hyz => (holds_sim M _ _ _).1
      ((holds_imp M _ _ _).1 (h (![z, y, x] : Fin 3 → M.carrier Elem))
        ⟨(holds_sim M _ _ _).2 hxy, (holds_sim M _ _ _).2 hyz⟩),
    fun h ρ => (holds_imp M _ _ _).2 fun hρ => (holds_sim M _ _ _).2
      (h (ρ 2) (ρ 1) (ρ 0) ((holds_sim M _ _ _).1 hρ.1) ((holds_sim M _ _ _).1 hρ.2))⟩

theorem holds_dichotomyAx (M : FOL.Structure leSig.toSignature) :
    dichotomyAx.Holds M ↔ ∀ x y, leOf M x y ∨ leOf M y x := by
  refine (holds_closed M _).trans ?_
  exact ⟨fun h x y => ((holds_or M _ _ _).1 (h (![y, x] : Fin 2 → M.carrier Elem))).imp
      (holds_le M _ _ _).1 (holds_le M _ _ _).1,
    fun h ρ => (holds_or M _ _ _).2
      ((h (ρ 1) (ρ 0)).imp (holds_le M _ _ _).2 (holds_le M _ _ _).2)⟩

/-! ### Membership in the model classes of the nodes -/

/-- The model class of a node of `graph`: the local axioms and the global definition links
(the graph has no local or hiding links). -/
theorem mem_models_iff' (N : Node) (m : (FOL.institution.obj (sig N)).Mod) :
    m ∈ graph.models N ↔ (∀ φ ∈ axioms N, (FOL.institution.obj (sig N)).Sat m φ) ∧
      ∀ K, ∀ σ ∈ globalDef K N, reduct (I := FOL.institution) σ m ∈ graph.models K := by
  refine (graph.mem_models_iff N m).trans ?_
  exact ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, fun _ _ hσ => (hσ : False).elim, fun _ _ hσ => (hσ : False).elim⟩⟩

/-- Unfolds the incoming global definition links of a concrete node. -/
local macro "node_links" : tactic => `(tactic| (
  refine (mem_models_iff' _ _).trans ?_
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h K σ hσ => ?_⟩
  · first
    | trivial
    | exact h _ _ (by exact rfl)
    | exact ⟨h _ _ (by exact rfl), h _ _ (by exact rfl)⟩
  · cases K <;> first
    | exact (hσ : False).elim
    | (cases hσ; first | exact h | exact h.1 | exact h.2)))

/-- The local axioms of a node hold. -/
abbrev AxSat (N : Node) (m : (FOL.institution.obj (sig N)).Mod) : Prop :=
  ∀ φ ∈ axioms N, (FOL.institution.obj (sig N)).Sat m φ

/-- The first-order reduct along a signature morphism. -/
abbrev rd {S S' : FOL.Signature} (σ : S ⟶ S') (m : FOL.Structure S') : FOL.Structure S :=
  reduct (I := FOL.institution) σ m

theorem mem_relation_iff (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .relation ↔ AxSat .relation m ∧ True := by node_links

theorem mem_reflexive (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .reflexive ↔
      AxSat .reflexive m ∧ rd idR m ∈ graph.models .relation := by node_links

theorem mem_irreflexive (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .irreflexive ↔
      AxSat .irreflexive m ∧ rd idR m ∈ graph.models .relation := by node_links

theorem mem_asymmetric (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .asymmetric ↔
      AxSat .asymmetric m ∧ rd idR m ∈ graph.models .relation := by node_links

theorem mem_antisymmetric (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .antisymmetric ↔
      AxSat .antisymmetric m ∧ rd idR m ∈ graph.models .relation := by node_links

theorem mem_transitive (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .transitive ↔
      AxSat .transitive m ∧ rd idR m ∈ graph.models .relation := by node_links

theorem mem_reflTrans (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .reflTrans ↔ AxSat .reflTrans m ∧
      (rd idR m ∈ graph.models .reflexive ∧ rd idR m ∈ graph.models .transitive) := by
  node_links

theorem mem_preOrder (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .preOrder ↔
      AxSat .preOrder m ∧ rd renLe.toHom m ∈ graph.models .reflTrans := by node_links

theorem mem_irrTrans (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .irrTrans ↔ AxSat .irrTrans m ∧
      (rd idR m ∈ graph.models .irreflexive ∧ rd idR m ∈ graph.models .transitive) := by
  node_links

theorem mem_strictBody (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .strictBody ↔ AxSat .strictBody m ∧
      (rd idR m ∈ graph.models .irrTrans ∧ rd idR m ∈ graph.models .asymmetric) := by
  node_links

theorem mem_strictOrder (m : FOL.Structure ltSig.toSignature) :
    m ∈ graph.models .strictOrder ↔
      AxSat .strictOrder m ∧ rd renLt.toHom m ∈ graph.models .strictBody := by node_links

theorem mem_antisymLe (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .antisymLe ↔
      AxSat .antisymLe m ∧ rd renLe.toHom m ∈ graph.models .antisymmetric := by node_links

theorem mem_partialOrder (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .partialOrder ↔ AxSat .partialOrder m ∧
      (rd idL m ∈ graph.models .preOrder ∧ rd idL m ∈ graph.models .antisymLe) := by
  node_links

theorem mem_totalOrder (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .totalOrder ↔
      AxSat .totalOrder m ∧ rd idL m ∈ graph.models .partialOrder := by node_links

/-- Every structure is a model of `Relation`. -/
theorem mem_relation (m : FOL.Structure relSig.toSignature) : m ∈ graph.models .relation :=
  (mem_relation_iff m).2 ⟨fun _ h => (h : False).elim, trivial⟩

/-! ### The model classes in terms of the interpreted relation -/

theorem sem_reflexive (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .reflexive ↔ ∀ x, relOf m x x := by
  rw [mem_reflexive]
  exact ⟨fun h => (holds_reflAx m).1 (h.1 reflAx rfl), fun h =>
    ⟨fun φ hφ => by obtain rfl : φ = reflAx := hφ; exact (holds_reflAx m).2 h,
      mem_relation _⟩⟩

theorem sem_irreflexive (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .irreflexive ↔ ∀ x, ¬ relOf m x x := by
  rw [mem_irreflexive]
  exact ⟨fun h => (holds_irreflAx m).1 (h.1 irreflAx rfl), fun h =>
    ⟨fun φ hφ => by obtain rfl : φ = irreflAx := hφ; exact (holds_irreflAx m).2 h,
      mem_relation _⟩⟩

theorem sem_asymmetric (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .asymmetric ↔ ∀ x y, relOf m x y → ¬ relOf m y x := by
  rw [mem_asymmetric]
  exact ⟨fun h => (holds_asymAx m).1 (h.1 asymAx rfl), fun h =>
    ⟨fun φ hφ => by obtain rfl : φ = asymAx := hφ; exact (holds_asymAx m).2 h,
      mem_relation _⟩⟩

theorem sem_antisymmetric (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .antisymmetric ↔ ∀ x y, relOf m x y → relOf m y x → x = y := by
  rw [mem_antisymmetric]
  exact ⟨fun h => (holds_antisymAx m).1 (h.1 antisymAx rfl), fun h =>
    ⟨fun φ hφ => by obtain rfl : φ = antisymAx := hφ; exact (holds_antisymAx m).2 h,
      mem_relation _⟩⟩

theorem sem_transitive (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .transitive ↔
      ∀ x y z, relOf m x y → relOf m y z → relOf m x z := by
  rw [mem_transitive]
  exact ⟨fun h => (holds_transAx m).1 (h.1 transAx rfl), fun h =>
    ⟨fun φ hφ => by obtain rfl : φ = transAx := hφ; exact (holds_transAx m).2 h,
      mem_relation _⟩⟩

theorem sem_irrTrans (m : FOL.Structure relSig.toSignature) :
    m ∈ graph.models .irrTrans ↔
      (∀ x, ¬ relOf m x x) ∧ ∀ x y z, relOf m x y → relOf m y z → relOf m x z := by
  rw [mem_irrTrans, sem_irreflexive, sem_transitive]
  exact ⟨fun h => h.2, fun h => ⟨fun _ h => (h : False).elim, h⟩⟩

theorem sem_preOrder (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .preOrder ↔
      (∀ x, leOf m x x) ∧ ∀ x y z, leOf m x y → leOf m y z → leOf m x z := by
  rw [mem_preOrder, mem_reflTrans, sem_reflexive, sem_transitive]
  exact ⟨fun h => h.2.2,
    fun h => ⟨fun _ h => (h : False).elim, fun _ h => (h : False).elim, h⟩⟩

theorem sem_antisymLe (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .antisymLe ↔ ∀ x y, leOf m x y → leOf m y x → x = y := by
  rw [mem_antisymLe, sem_antisymmetric]
  exact ⟨fun h => h.2, fun h => ⟨fun _ h => (h : False).elim, h⟩⟩

theorem sem_partialOrder (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .partialOrder ↔
      (∀ x, leOf m x x) ∧ (∀ x y z, leOf m x y → leOf m y z → leOf m x z) ∧
        ∀ x y, leOf m x y → leOf m y x → x = y := by
  rw [mem_partialOrder, sem_preOrder, sem_antisymLe]
  exact ⟨fun h => ⟨h.2.1.1, h.2.1.2, h.2.2⟩,
    fun h => ⟨fun _ h => (h : False).elim, ⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem sem_totalOrder (m : FOL.Structure leSig.toSignature) :
    m ∈ graph.models .totalOrder ↔
      ((∀ x, leOf m x x) ∧ (∀ x y z, leOf m x y → leOf m y z → leOf m x z) ∧
        ∀ x y, leOf m x y → leOf m y x → x = y) ∧ ∀ x y, leOf m x y ∨ leOf m y x := by
  rw [mem_totalOrder, sem_partialOrder]
  exact ⟨fun h => ⟨h.2, (holds_dichotomyAx m).1 (h.1 dichotomyAx rfl)⟩, fun h =>
    ⟨fun φ hφ => by obtain rfl : φ = dichotomyAx := hφ; exact (holds_dichotomyAx m).2 h.2,
      h.1⟩⟩

/-- Irreflexivity and transitivity give asymmetry: the first-order semantic consequence behind
the `%implies` obligation. -/
theorem asymmetric_of_irrTrans (m : FOL.Structure relSig.toSignature)
    (hm : m ∈ graph.models .irrTrans) : rd idR m ∈ graph.models .asymmetric := by
  obtain ⟨hirr, htrans⟩ := (sem_irrTrans m).1 hm
  exact (sem_asymmetric _).2 fun x y hxy hyx => hirr x (htrans x y x hxy hyx)

/-- The node `irrTrans` is flattenable (the graph has no hiding links). -/
theorem flattenable_irrTrans : graph.Flattenable .irrTrans :=
  fun _ ⟨_, _, hσ⟩ => (hσ : False).elim

/-! ### The `%implies` obligation -/

/-- **The `%implies` obligation of `StrictOrder` is derivable** with the decomposition rules
over first-order semantic consequence.

Source: `mossakowski-autexier-hutter-2006-development-graphs` in `references.bib`, §5.2
(PDF pages 13–14: Glob-Decomposition, Local Inference, Basic Inference). -/
theorem implies_derivable :
    Derivable Rule.decomposition (semEnt FOL.institution) graph impliesGoal := by
  show Derivable Rule.decomposition (semEnt FOL.institution) graph
    (.glob .asymmetric .irrTrans idR)
  refine .globDecomposition _ (by simp [Rule.decomposition]) ?_ ?_
  · intro K τ hτ
    refine .localInference _ (by simp [Rule.decomposition])
      (.basicInference (by simp [Rule.decomposition]) ?_)
    rintro _ ⟨ψ, hψ, rfl⟩ m hm
    have hm' : m ∈ graph.models .irrTrans :=
      (graph.models_eq_modelsOf_theory flattenable_irrTrans).superset hm
    have h := DevGraph.LocReach.reduct_sat_axioms graph hτ (asymmetric_of_irrTrans m hm') ψ hψ
    have e := DevGraph.reduct_comp (I := FOL.institution) τ idR m
    exact ((FOL.institution.map (τ ≫ idR)).sat m ψ).2
      ((congrArg (fun n => (FOL.institution.obj (graph.sig K)).Sat n ψ) e).mpr h)
  · intro _ _ _ _ hθ _
    exact (hθ : False).elim

/-- The `%implies` theorem link holds, by soundness of the calculus. -/
theorem implies_globalThm : graph.GlobalThm .asymmetric .irrTrans idR :=
  implies_derivable.sound fun _ _ _ h => h

/-! ### The development graph and the structured specifications -/

theorem models_relation : graph.models .relation = relationSpec.models := by
  ext m
  exact (mem_relation_iff m).trans ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem models_reflexive : graph.models .reflexive = reflexiveSpec.models := by
  ext m
  exact (mem_reflexive m).trans ⟨fun h => ⟨models_relation.subset h.2, h.1⟩,
    fun h => ⟨h.2, models_relation.superset h.1⟩⟩

theorem models_irreflexive : graph.models .irreflexive = irreflexiveSpec.models := by
  ext m
  exact (mem_irreflexive m).trans ⟨fun h => ⟨models_relation.subset h.2, h.1⟩,
    fun h => ⟨h.2, models_relation.superset h.1⟩⟩

theorem models_asymmetric : graph.models .asymmetric = asymmetricSpec.models := by
  ext m
  exact (mem_asymmetric m).trans ⟨fun h => ⟨models_relation.subset h.2, h.1⟩,
    fun h => ⟨h.2, models_relation.superset h.1⟩⟩

theorem models_antisymmetric : graph.models .antisymmetric = antisymmetricSpec.models := by
  ext m
  exact (mem_antisymmetric m).trans ⟨fun h => ⟨models_relation.subset h.2, h.1⟩,
    fun h => ⟨h.2, models_relation.superset h.1⟩⟩

theorem models_transitive : graph.models .transitive = transitiveSpec.models := by
  ext m
  exact (mem_transitive m).trans ⟨fun h => ⟨models_relation.subset h.2, h.1⟩,
    fun h => ⟨h.2, models_relation.superset h.1⟩⟩

theorem models_reflTrans : graph.models .reflTrans = reflTransSpec.models := by
  ext m
  exact (mem_reflTrans m).trans
    ⟨fun h => ⟨models_reflexive.subset h.2.1, models_transitive.subset h.2.2⟩,
      fun h => ⟨fun _ h => (h : False).elim,
        models_reflexive.superset h.1, models_transitive.superset h.2⟩⟩

theorem models_preOrder : graph.models .preOrder = preOrderSpec.models := by
  ext m
  exact (mem_preOrder m).trans ⟨fun h => models_reflTrans.subset h.2,
    fun h => ⟨fun _ h => (h : False).elim, models_reflTrans.superset h⟩⟩

theorem models_irrTrans : graph.models .irrTrans = irrTransSpec.models := by
  ext m
  exact (mem_irrTrans m).trans
    ⟨fun h => ⟨models_irreflexive.subset h.2.1, models_transitive.subset h.2.2⟩,
      fun h => ⟨fun _ h => (h : False).elim,
        models_irreflexive.superset h.1, models_transitive.superset h.2⟩⟩

theorem models_strictBody : graph.models .strictBody = strictBodySpec.models := by
  ext m
  exact (mem_strictBody m).trans
    ⟨fun h => ⟨models_irrTrans.subset h.2.1, models_asymmetric.subset h.2.2⟩,
      fun h => ⟨fun _ h => (h : False).elim,
        models_irrTrans.superset h.1, models_asymmetric.superset h.2⟩⟩

theorem models_strictOrder : graph.models .strictOrder = strictOrderSpec.models := by
  ext m
  exact (mem_strictOrder m).trans ⟨fun h => models_strictBody.subset h.2,
    fun h => ⟨fun _ h => (h : False).elim, models_strictBody.superset h⟩⟩

theorem models_antisymLe : graph.models .antisymLe = antisymLeSpec.models := by
  ext m
  exact (mem_antisymLe m).trans ⟨fun h => models_antisymmetric.subset h.2,
    fun h => ⟨fun _ h => (h : False).elim, models_antisymmetric.superset h⟩⟩

theorem models_partialOrder : graph.models .partialOrder = partialOrderSpec.models := by
  ext m
  exact (mem_partialOrder m).trans
    ⟨fun h => ⟨models_preOrder.subset h.2.1, models_antisymLe.subset h.2.2⟩,
      fun h => ⟨fun _ h => (h : False).elim,
        models_preOrder.superset h.1, models_antisymLe.superset h.2⟩⟩

theorem models_totalOrder : graph.models .totalOrder = totalOrderSpec.models := by
  ext m
  exact (mem_totalOrder m).trans ⟨fun h => ⟨models_partialOrder.subset h.2, h.1⟩,
    fun h => ⟨h.2, models_partialOrder.superset h.1⟩⟩

/-- The development graph is faithful to the structured specifications: the model class of
each node is the model class of its specification.

Source: `mossakowski-2005-habilitation-hets` in `references.bib`, §5.5, Theorem 5.19
(printed page 137, PDF page 139: "The verification semantics preserves model classes of
structured specifications … `Mod[SP] = Mod_DG(N)`"). -/
theorem models_eq_spec (N : Node) : graph.models N = (spec N).models := by
  cases N
  exacts [models_relation, models_reflexive, models_irreflexive, models_asymmetric,
    models_antisymmetric, models_transitive, models_reflTrans, models_preOrder, models_irrTrans,
    models_strictBody, models_strictOrder, models_antisymLe, models_partialOrder,
    models_totalOrder]

/-- **The `%implies` annotation holds**: the model class of
`IrreflexiveRelation and TransitiveRelation then AsymmetricRelation` is the model class of
`IrreflexiveRelation and TransitiveRelation`.

Source: `cofi-2004-casl-reference-manual` in `references.bib`, Part II §5.2.5 (printed
page 111, PDF page 125). -/
theorem implies_holds : strictBodySpec.models = irrTransSpec.models := by
  refine models_strictBody.symm.trans (Eq.trans ?_ models_irrTrans)
  ext m
  refine (mem_strictBody m).trans
    ⟨fun h => (sem_irrTrans m).2 ((sem_irrTrans (rd idR m)).1 h.2.1),
    fun h => ?_⟩
  have h' : rd idR m ∈ graph.models .irrTrans :=
    (sem_irrTrans (rd idR m)).2 ((sem_irrTrans m).1 h)
  exact ⟨fun _ h => (h : False).elim, h', (sem_asymmetric (rd idR m)).2
    ((sem_asymmetric (rd idR (rd idR m))).1 (implies_globalThm _ h'))⟩

/-- A model of `StrictOrder` is a structure whose relation is irreflexive and transitive; the
asymmetry carried by the node is the `%implies` theorem link `implies_globalThm`. -/
theorem mem_strictOrder_iff_irrTrans (m : FOL.Structure ltSig.toSignature) :
    m ∈ graph.models .strictOrder ↔ rd idR (rd renLt.toHom m) ∈ graph.models .irrTrans := by
  refine (mem_strictOrder m).trans ⟨fun h => ((mem_strictBody _).1 h.2).2.1, fun h => ?_⟩
  refine ⟨fun _ h => (h : False).elim,
    (mem_strictBody _).2 ⟨fun _ h => (h : False).elim, h, ?_⟩⟩
  exact (sem_asymmetric (rd idR (rd renLt.toHom m))).2
    ((sem_asymmetric (rd idR (rd idR (rd renLt.toHom m)))).1 (implies_globalThm _ h))

/-! ### Mathlib models -/

/-- A binary relation as a structure for the signature of `Relation`. -/
def relModel (α : Type) (r : α → α → Prop) : FOL.Structure relSig.toSignature :=
  model1 relSig α (fun i _ => i.elim0) fun _ l =>
    match l with
    | [x, y] => r x y
    | _ => False

/-- `<` as a structure for the signature of `StrictOrder`. -/
def ltModel (α : Type) [LT α] : FOL.Structure ltSig.toSignature :=
  model1 ltSig α (fun i _ => i.elim0) fun _ l =>
    match l with
    | [x, y] => x < y
    | _ => False

/-- `≤` as a structure for the signature of `PreOrder`. -/
def leModel (α : Type) [LE α] : FOL.Structure leSig.toSignature :=
  model1 leSig α (fun i _ => i.elim0) fun _ l =>
    match l with
    | [x, y] => x ≤ y
    | _ => False

/-- The models of `IrreflexiveRelation and TransitiveRelation` are the irreflexive transitive
relations. -/
theorem relModel_mem_irrTrans_iff (α : Type) (r : α → α → Prop) :
    relModel α r ∈ graph.models .irrTrans ↔ Std.Irrefl r ∧ IsTrans α r := by
  rw [sem_irrTrans]
  exact ⟨fun h => ⟨⟨h.1⟩, ⟨h.2⟩⟩, fun ⟨⟨h1⟩, ⟨h2⟩⟩ => ⟨h1, h2⟩⟩

/-- **`StrictOrder` axiomatizes Mathlib's strict orders**. The converse direction needs the
`%implies` theorem: the node `strictOrder` also carries `AsymmetricRelation`. -/
theorem ltModel_mem_strictOrder_iff (α : Type) [LT α] :
    ltModel α ∈ graph.models .strictOrder ↔ IsStrictOrder α (· < ·) := by
  rw [mem_strictOrder_iff_irrTrans, sem_irrTrans]
  exact ⟨fun h => { irrefl := h.1, trans := h.2 },
    fun _ => ⟨fun x => Std.Irrefl.irrefl (r := fun a b : α => a < b) x,
      fun x y z => IsTrans.trans (r := fun a b : α => a < b) x y z⟩⟩

/-- **`PreOrder` axiomatizes Mathlib's preorders.** -/
theorem leModel_mem_preOrder_iff (α : Type) [LE α] :
    leModel α ∈ graph.models .preOrder ↔ IsPreorder α (· ≤ ·) := by
  rw [sem_preOrder]
  exact ⟨fun h => { refl := h.1, trans := h.2 },
    fun _ => ⟨fun x => Std.Refl.refl (r := fun a b : α => a ≤ b) x,
      fun x y z => IsTrans.trans (r := fun a b : α => a ≤ b) x y z⟩⟩

/-- **`PartialOrder` axiomatizes Mathlib's partial orders.** -/
theorem leModel_mem_partialOrder_iff (α : Type) [LE α] :
    leModel α ∈ graph.models .partialOrder ↔ IsPartialOrder α (· ≤ ·) := by
  rw [sem_partialOrder]
  exact ⟨fun h => { refl := h.1, trans := h.2.1, antisymm := h.2.2 },
    fun _ => ⟨fun x => Std.Refl.refl (r := fun a b : α => a ≤ b) x,
      fun x y z => IsTrans.trans (r := fun a b : α => a ≤ b) x y z,
      fun x y => Std.Antisymm.antisymm (r := fun a b : α => a ≤ b) x y⟩⟩

/-- **`TotalOrder` axiomatizes Mathlib's linear orders.** -/
theorem leModel_mem_totalOrder_iff (α : Type) [LE α] :
    leModel α ∈ graph.models .totalOrder ↔ IsLinearOrder α (· ≤ ·) := by
  rw [sem_totalOrder]
  exact ⟨fun h => { refl := h.1.1, trans := h.1.2.1, antisymm := h.1.2.2, total := h.2 },
    fun _ => ⟨⟨fun x => Std.Refl.refl (r := fun a b : α => a ≤ b) x,
      fun x y z => IsTrans.trans (r := fun a b : α => a ≤ b) x y z,
      fun x y => Std.Antisymm.antisymm (r := fun a b : α => a ≤ b) x y⟩,
      fun x y => Std.Total.total (r := fun a b : α => a ≤ b) x y⟩⟩

/-- Every Mathlib linear order is a model of the formalized `TotalOrder`. -/
theorem leModel_mem_totalOrder (α : Type) [LinearOrder α] :
    leModel α ∈ graph.models .totalOrder :=
  (leModel_mem_totalOrder_iff α).2 inferInstance

/-- **Every strict order is asymmetric**, derived from the formalized theorem link
`implies_globalThm` (not from Mathlib's instance `IsStrictOrder → Std.Asymm`). -/
theorem asymm_of_isStrictOrder (α : Type) (r : α → α → Prop) [IsStrictOrder α r] :
    Std.Asymm r := by
  have hm : relModel α r ∈ graph.models .irrTrans :=
    (relModel_mem_irrTrans_iff α r).2 ⟨inferInstance, inferInstance⟩
  exact ⟨(sem_asymmetric (rd idR (relModel α r))).1 (implies_globalThm _ hm)⟩

/-! ### Independence -/

/-- **Transitivity is needed**: `IrreflexiveRelation` alone does not prove `%(asym)%`; `≠` on
`Bool` is irreflexive and not asymmetric. -/
theorem irreflexive_not_implies_asym : ¬ graph.LocalImpl .irreflexive {asymAx} := by
  intro h
  have hm : relModel Bool (· ≠ ·) ∈ graph.models .irreflexive :=
    (sem_irreflexive _).2 fun x hx => hx rfl
  have ha := (holds_asymAx _).1 (h _ hm asymAx rfl)
  exact ha true false (show (true : Bool) ≠ false by decide)
    (show (false : Bool) ≠ true by decide)

end Silmaril.Logic.Institution.Hets.Lib.RelationsAndOrders
