module

public import Silmaril.Logic.Metamath.Category.Basic
public import Silmaril.Logic.Metamath.Category.Lattice
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Iso

@[expose] public section

/-!
# The lattice of axiom sets inside the category

Fix a grammar `G` with infinitely many variables. Tree axiom sets over `G`,
preordered by derivability (`TAxiomSet G`), form a thin category, and so do
tree theories (`TTheory G`). Sending an axiom set to the grammatical axiom set
it presents and `Γ ≤ Δ` to the identity rewrite gives functors
`GAxSet.axiomSetFunctor G` and `GAxSet.theoryFunctor G` into `GAxSet`.

* An identity-rewrite morphism `Γ ⟶ Δ` exists exactly when `Γ ≤ Δ`
  (`GAxSet.exists_hom_id_iff`).
* Both functors are faithful, and injective on objects
  (`GAxSet.ofAxiomSet_injective`). Two axiom sets are equivalent exactly when
  their images are isomorphic through identity rewrites
  (`GAxSet.antisymmRel_iff_exists_iso`), so the functor identifies exactly the
  classes of the antisymmetrization, the lattice of theories.
* The functors are not full in general: over a grammar with two constants of
  the same sort, swapping the constants is an endomorphism of the empty axiom
  set that is not an identity rewrite (`GAxSet.Swap.not_full`). They do not
  even reflect the existence of morphisms: swapping sends `{⊢ a}` to `{⊢ b}`
  although `⊢ a` is not derivable from `⊢ b` (`GAxSet.Swap.not_reflects`).
-/

namespace Silmaril.Logic.Metamath.GAxSet

open CategoryTheory Grammar

universe u

section Embedding

variable {L C V : Type u} [DecidableEq V]

variable (G : Grammar L C V) in
/-- The grammatical axiom set presented by a tree axiom set over `G`. -/
abbrev ofAxiomSet (Γ : TAxiomSet G) : GAxSet.{u} :=
  GAxSet.of G (TWFAssertion.toSet Γ.axioms) fun _ h => TWFAssertion.wellFormed_of_mem_toSet h

variable {G : Grammar L C V}

theorem ofAxiomSet_injective : Function.Injective (ofAxiomSet G) := by
  intro Γ Δ h
  simp only [ofAxiomSet, GAxSet.of, GAxSet.mk.injEq, heq_eq_eq, true_and] at h
  exact Set.image_injective.2 Subtype.val_injective h

section

variable [Infinite V]

/-- The identity rewrite, as a morphism `Γ ⟶ Δ` when `Γ ≤ Δ`. -/
def idHom {Γ Δ : TAxiomSet G} (h : Γ ≤ Δ) : ofAxiomSet G Γ ⟶ ofAxiomSet G Δ where
  toRewrite := Rewrite.id G
  map_derivable A hA hd := by
    rw [Rewrite.id_assertion hA]
    exact TAxiomSet.le_iff_derivable.1 h A hd

@[simp] theorem idHom_toRewrite {Γ Δ : TAxiomSet G} (h : Γ ≤ Δ) :
    (idHom h).toRewrite = Rewrite.id G := rfl

/-- An identity-rewrite morphism `Γ ⟶ Δ` exists exactly when `Γ ≤ Δ`. -/
theorem exists_hom_id_iff {Γ Δ : TAxiomSet G} :
    (∃ f : ofAxiomSet G Γ ⟶ ofAxiomSet G Δ, f.toRewrite = Rewrite.id G) ↔ Γ ≤ Δ := by
  refine ⟨fun ⟨f, hf⟩ A hA => ?_, fun h => ⟨idHom h, rfl⟩⟩
  have hd := f.derivable_axiom (A := A.1) (TWFAssertion.mem_toSet_of_mem hA)
  rw [hf, Rewrite.id_assertion A.2] at hd
  exact hd

variable (G) in
/-- The thin category of tree axiom sets over `G` in `GAxSet`. -/
def axiomSetFunctor : TAxiomSet G ⥤ GAxSet.{u} where
  obj := ofAxiomSet G
  map f := idHom (leOfHom f)
  map_id _ := Hom.ext' rfl
  map_comp _ _ := Hom.ext' (Rewrite.id_comp _).symm

@[simp] theorem axiomSetFunctor_obj (Γ : TAxiomSet G) :
    (axiomSetFunctor G).obj Γ = ofAxiomSet G Γ := rfl

/-- The image of every morphism is an identity rewrite. -/
@[simp] theorem axiomSetFunctor_map_toRewrite {Γ Δ : TAxiomSet G} (f : Γ ⟶ Δ) :
    ((axiomSetFunctor G).map f).toRewrite = Rewrite.id G := rfl

instance : (axiomSetFunctor G).Faithful := ⟨fun _ => Subsingleton.elim _ _⟩

/-- Two axiom sets are equivalent exactly when their images are isomorphic
through identity rewrites. -/
theorem antisymmRel_iff_exists_iso {Γ Δ : TAxiomSet G} :
    AntisymmRel (· ≤ ·) Γ Δ ↔
      ∃ e : ofAxiomSet G Γ ≅ ofAxiomSet G Δ, e.hom.toRewrite = Rewrite.id G := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨idHom h₁, idHom h₂, Hom.ext' (Rewrite.id_comp _), Hom.ext' (Rewrite.id_comp _)⟩,
      rfl⟩
  · rintro ⟨e, he⟩
    have hinv : e.inv.toRewrite = Rewrite.id G := by
      have h := congrArg Hom.toRewrite e.hom_inv_id
      rw [comp_toRewrite, he, Rewrite.id_comp] at h
      exact h
    exact ⟨exists_hom_id_iff.1 ⟨e.hom, he⟩, exists_hom_id_iff.1 ⟨e.inv, hinv⟩⟩

/-- Equivalent axiom sets are exactly those with the same tree theory. -/
theorem theory_eq_iff_exists_iso {Γ Δ : TAxiomSet G} :
    TTheory.of Γ.axioms = TTheory.of Δ.axioms ↔
      ∃ e : ofAxiomSet G Γ ≅ ofAxiomSet G Δ, e.hom.toRewrite = Rewrite.id G :=
  TAxiomSet.antisymmRel_iff.symm.trans antisymmRel_iff_exists_iso

variable (G) in
/-- The lattice of tree theories over `G` in `GAxSet`. -/
def theoryFunctor : TTheory G ⥤ GAxSet.{u} where
  obj T := ofAxiomSet G (TAxiomSet.of T.val)
  map f := idHom (TAxiomSet.le_of_subset (leOfHom f))
  map_id _ := Hom.ext' rfl
  map_comp _ _ := Hom.ext' (Rewrite.id_comp _).symm

instance : (theoryFunctor G).Faithful := ⟨fun _ => Subsingleton.elim _ _⟩

theorem theoryFunctor_obj_injective : Function.Injective (theoryFunctor G).obj :=
  fun _ _ h => Subtype.ext (ofAxiomSet_injective h)

/-- An identity-rewrite morphism between theories exists exactly when they are
ordered. -/
theorem theory_exists_hom_id_iff {T T' : TTheory G} :
    (∃ f : (theoryFunctor G).obj T ⟶ (theoryFunctor G).obj T', f.toRewrite = Rewrite.id G) ↔
      T ≤ T' := by
  have h := (exists_hom_id_iff (G := G) (Γ := TAxiomSet.of T.val)
    (Δ := TAxiomSet.of T'.val)).trans TAxiomSet.le_iff_theory
  simp only [TAxiomSet.axioms_of, TTheory.of_val] at h
  exact h

end

end Embedding

/-! ### The embedding is not full -/

namespace Swap

/-- Typecodes and constants. -/
inductive C
  | wff | pf | a | b
  deriving DecidableEq

/-- Rule labels. -/
inductive L
  | a | b
  deriving DecidableEq

/-- Two constants of sort `wff`. -/
def rules : L → SyntaxRule C ℕ
  | .a => ⟨.wff, [], [.const .a], .nil, .nil⟩
  | .b => ⟨.wff, [], [.const .b], .nil, .nil⟩

/-- The grammar with one sort, two constants, and `pf` read as `wff`. -/
def grammar : Grammar L C ℕ where
  sorts := {.wff}
  prov
    | .pf => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> simp [rules]
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; simp

/-- Swapping the two constants. -/
def swap : Rewrite grammar grammar where
  tc c := c
  var := Function.Embedding.refl ℕ
  tmpl
    | .a => .node .b []
    | .b => .node .a []
  sort_mem _ h := h
  prov_eq h := h
  tmpl_sort l := by cases l <;> exact .node rfl (by simp)

/-- Swapping is an endomorphism of the empty axiom set. -/
def swapHom : (axiomSetFunctor grammar).obj (TAxiomSet.of ∅) ⟶
    (axiomSetFunctor grammar).obj (TAxiomSet.of ∅) :=
  Hom.ofImage swap fun _ h => by
    obtain ⟨B, hB, -⟩ := h
    exact (hB : B ∈ (∅ : Set (TWFAssertion grammar))).elim

theorem swapHom_ne_id : swapHom.toRewrite ≠ Rewrite.id grammar := by
  intro h
  have := congrArg (fun f : Rewrite grammar grammar => f.tmpl .a) h
  simp [swapHom, swap, Rewrite.id, grammar, rules] at this

/-- The embedding of the thin category of axiom sets is not full. -/
theorem not_full : ¬ (axiomSetFunctor grammar).Full := by
  intro hF
  obtain ⟨f, hf⟩ := (axiomSetFunctor grammar).map_surjective swapHom
  exact swapHom_ne_id (hf ▸ axiomSetFunctor_map_toRewrite f)

/-- The axiom `⊢ l` for a constant `l`. -/
def ax (l : L) : TAssertion L C ℕ := ⟨[], [], ⟨.pf, .node l []⟩⟩

theorem wellFormed_ax (l : L) : (ax l).WellFormed grammar where
  floats_nodup := by simp [ax, TAssertion.floats]
  float_sort v s h := by simp [ax, TAssertion.ctx] at h
  ess_wellTyped e he := by simp [ax, TAssertion.essentials] at he
  concl_wellTyped := ⟨.wff, rfl, by cases l <;> exact .node rfl (by simp)⟩
  dv_irrefl x y h := by simp [ax] at h
  dv_float x y h := by simp [ax] at h

/-- The axiom set `{⊢ l}`. -/
def axSet (l : L) : TAxiomSet grammar := TAxiomSet.of {⟨ax l, wellFormed_ax l⟩}

theorem mem_toSet_axSet {l : L} {B : TAssertion L C ℕ} (h : B ∈ TWFAssertion.toSet (axSet l)) :
    B = ax l := by
  obtain ⟨B', hB', rfl⟩ := h
  rw [show B' = ⟨ax l, wellFormed_ax l⟩ from hB']

/-- Without essential hypotheses, `{⊢ l}` only derives `⊢ l`. -/
theorem concl_eq {l : L} {A : TAssertion L C ℕ} (hA : A.essentials = [])
    {e : TExpr L C ℕ} (d : TDerivation grammar (TWFAssertion.toSet (axSet l)) A e) :
    e = (ax l).concl := by
  cases d with
  | hyp h => simp [hA] at h
  | app B hB τ _ _ _ =>
    obtain rfl := mem_toSet_axSet hB
    rfl

theorem not_le : ¬ axSet .a ≤ axSet .b := by
  intro h
  obtain ⟨⟨D, d⟩⟩ := h (show (⟨ax .a, wellFormed_ax .a⟩ : TWFAssertion grammar) ∈ (axSet .a).axioms
    from rfl)
  have := concl_eq (by rw [TAssertion.essentials_extend]; rfl) d
  simp [ax] at this

/-- Swapping sends `⊢ a` to `⊢ b`. -/
def swapAB : (axiomSetFunctor grammar).obj (axSet .a) ⟶ (axiomSetFunctor grammar).obj (axSet .b) :=
  Hom.ofImage swap fun _ h => by
    obtain rfl := mem_toSet_axSet h
    exact ⟨⟨ax .b, wellFormed_ax .b⟩, rfl, rfl⟩

/-- The embedding does not even reflect the existence of morphisms. -/
theorem not_reflects : ∃ Γ Δ : TAxiomSet grammar,
    ¬ Γ ≤ Δ ∧ Nonempty ((axiomSetFunctor grammar).obj Γ ⟶ (axiomSetFunctor grammar).obj Δ) :=
  ⟨axSet .a, axSet .b, not_le, ⟨swapAB⟩⟩

end Swap

end Silmaril.Logic.Metamath.GAxSet
