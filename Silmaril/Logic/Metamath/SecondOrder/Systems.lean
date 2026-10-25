module

public import Silmaril.Logic.Metamath.SecondOrder.Syntax
public import Silmaril.Logic.Metamath.Model.Check
public import Silmaril.Logic.Metamath.Category.Lattice
public import Silmaril.Logic.Metamath.Grammar.DecidableEq

@[expose] public section

/-!
# Subsystems of second-order arithmetic

The axiom sets of `data/metamath/z2.mm` as sets of tree assertions over
`SecondOrder.grammar` (Simpson, *Subsystems of Second Order Arithmetic*):

* `base`: the predicate calculus of both sorts with its definitions, the
  equality axioms, the basic axioms of arithmetic, and the formation rules of
  the formula classes `bnd`, `sig1`, `pi1` and `arith`;
* `RCA0 = base + Σ⁰₁-induction + Δ⁰₁-comprehension`;
* `WKL0 = RCA0 + Σ⁰₁-separation`, which is equivalent over `RCA0` to weak
  König's lemma (Simpson, Lemma IV.4.4);
* `ACA0 = base + Σ⁰₁-induction + arithmetical comprehension`;
* `Z2 = ACA0 + full induction + full comprehension`.

Every axiom is well formed (`wellFormed_all`), and the axioms listed here are
all the logical axioms of the database (`axiomList_eq`).

In the lattice of tree theories `RCA0 ≤ WKL0` and `ACA0 ≤ Z2` hold by
inclusion. `RCA0 ≤ ACA0` holds by derivation: Δ⁰₁-comprehension follows from
arithmetical comprehension through the coercion `arith-sig1`
(`tderivable_axDcomp`, the tree form of the theorem `dcomp-aca` of the
database). The Σ⁰₁ schemes are instances of the full ones, so `Z2` is
equivalent to `base + induction + comprehension` (`Z2_equiv`).

Derivation steps between concrete tree assertions are checked by evaluation
(`Grammar.TDerivation.nonempty_step`).
-/

namespace Silmaril.Logic.Metamath

open Grammar

universe u

namespace Grammar

variable {L C V : Type u} {G : Grammar L C V}

/-- A hypothesis of the frame. -/
theorem TDerivation.nonempty_hyp {Γ : Set (TAssertion L C V)} {A : TAssertion L C V}
    {e : TExpr L C V} (h : e ∈ A.essentials) : Nonempty (TDerivation G Γ A e) :=
  ⟨.hyp h⟩

/-- A derivation of the conclusion without dummy variables proves the assertion. -/
theorem TDerivable.of_nonempty {Γ : Set (TAssertion L C V)} {A : TAssertion L C V}
    (h : Nonempty (TDerivation G Γ A A.concl)) : TDerivable G Γ A := by
  obtain ⟨d⟩ := h
  exact tderivable_iff.2 ⟨TDummies.none A, ⟨by rw [TAssertion.extend_none]; exact d⟩⟩

variable [DecidableEq V]

/-- A decidable form of the disjoint-variable condition of a step applying
`B` under `τ` in the frame `A`. -/
def TAssertion.dvCheck (B A : TAssertion L C V) (τ : V → Tree L V) : Bool :=
  B.dv.all fun p => (τ p.1).vars.all fun a => (τ p.2).vars.all fun b =>
    a != b && (A.dv.contains (a, b) || A.dv.contains (b, a))

theorem TAssertion.dvSafe_of_dvCheck {A B : TAssertion L C V} {τ : V → Tree L V}
    (h : B.dvCheck A τ = true) : B.DVSafe τ A.Disjoint := by
  intro x y hxy a ha b hb
  simp only [dvCheck, List.all_eq_true] at h
  have := h _ hxy a ha b hb
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, List.contains_iff_mem] at this
  exact ⟨this.1, this.2⟩

variable [DecidableEq C]

/-- A derivation step whose side conditions are checked by evaluation: the
substituted floating variables have their sorts in the frame `A`, and the
disjoint-variable conditions hold. -/
theorem TDerivation.nonempty_step {Γ : Set (TAssertion L C V)} {A B : TAssertion L C V}
    (hB : B ∈ Γ) (τ : V → Tree L V)
    (hsort : B.floats.all (fun p => G.check A.sortOf (τ p.2) p.1) = true)
    (hdv : B.dvCheck A τ = true)
    (hprem : ∀ e ∈ B.essentials, Nonempty (TDerivation G Γ A (e.subst τ))) :
    Nonempty (TDerivation G Γ A (B.concl.subst τ)) := by
  refine ⟨.app B hB τ (fun v s h => ?_) (fun e he => Classical.choice (hprem e he))
    (TAssertion.dvSafe_of_dvCheck hdv)⟩
  rw [List.all_eq_true] at hsort
  have := hsort _ (TAssertion.mem_floats.2 h)
  exact ((check_iff _ _).1 this).mono fun _ _ => TAssertion.ctx_of_sortOf

end Grammar

namespace SecondOrder

/-! ## The axiom sets -/

/-- The predicate calculus of numbers and sets, its definitions and the
equality axioms, in database order. -/
def logicList : List (TAssertion L C V) :=
  [axMp, ax1, ax2, ax3, dfBi1, dfBi2, dfBi3, dfAn, axGen, ax4, ax5, ax6, ax7, ax10, ax11, ax12,
    ax13, axTex, dfEx, axSgen, axS4, axS5, axS6, axS7, axS10, axS11, axS12, axS13, axNs11,
    axSn11, dfSex, dfSeq, axEqS, axEqpl1, axEqpl2, axEqmu1, axEqmu2, axEqlt1, axEqlt2, axEqel1,
    axEqel2]

/-- The basic axioms of arithmetic. -/
def basicList : List (TAssertion L C V) :=
  [axS0, axSinj, axPl0, axPlS, axMu0, axMuS, axLt0, axLtS]

/-- The formation rules of the formula classes. -/
def classList : List (TAssertion L C V) :=
  [bndEq, bndLt, bndEl, bndN, bndI, bndB, bndA, bndRal, bndRex, sig1Bnd, sig1Ex, pi1Bnd, pi1Al,
    arithEq, arithLt, arithEl, arithSeq, arithN, arithAl, arithEx, arithI, arithB, arithA,
    arithSig1, arithPi1]

/-- The lists above and the six schemes are the logical axioms of `z2.mm`. -/
theorem axiomList_eq : axiomList.map Prod.snd =
    logicList ++ basicList ++ classList ++ [axIndSig1, axDcomp, axSep1, axAcomp, axInd, axComp] :=
  rfl

/-- The axioms common to all subsystems. -/
def base : Set (TAssertion L C V) := {A | A ∈ logicList ++ basicList ++ classList}

/-- `RCA0`: Σ⁰₁-induction and Δ⁰₁-comprehension. -/
def RCA0 : Set (TAssertion L C V) := base ∪ {axIndSig1, axDcomp}

/-- `WKL0`: `RCA0` and Σ⁰₁-separation. -/
def WKL0 : Set (TAssertion L C V) := RCA0 ∪ {axSep1}

/-- `ACA0`: Σ⁰₁-induction and arithmetical comprehension. -/
def ACA0 : Set (TAssertion L C V) := base ∪ {axIndSig1, axAcomp}

/-- `Z2`: `ACA0`, full induction and full comprehension. -/
def Z2 : Set (TAssertion L C V) := ACA0 ∪ {axInd, axComp}

/-- Full second-order arithmetic without the restricted schemes. -/
def Z2' : Set (TAssertion L C V) := base ∪ {axInd, axComp}

/-- All logical axioms of the database. -/
def allAxioms : Set (TAssertion L C V) := {A | A ∈ axiomList.map Prod.snd}

theorem RCA0_subset_WKL0 : RCA0 ⊆ WKL0 := Set.subset_union_left

theorem ACA0_subset_Z2 : ACA0 ⊆ Z2 := Set.subset_union_left

theorem Z2'_subset_Z2 : Z2' ⊆ Z2 :=
  Set.union_subset (Set.subset_union_left.trans Set.subset_union_left) Set.subset_union_right

theorem base_subset_allAxioms : base ⊆ allAxioms := fun A hA => by
  simp only [allAxioms, Set.mem_ofPred_eq, axiomList_eq]
  exact List.mem_append_left _ hA

theorem WKL0_subset_allAxioms : WKL0 ⊆ allAxioms := by
  refine Set.union_subset (Set.union_subset base_subset_allAxioms ?_) ?_ <;>
    simp [Set.insert_subset_iff, allAxioms, axiomList_eq]

theorem Z2_subset_allAxioms : Z2 ⊆ allAxioms := by
  refine Set.union_subset (Set.union_subset base_subset_allAxioms ?_) ?_ <;>
    simp [Set.insert_subset_iff, allAxioms, axiomList_eq]

theorem RCA0_subset_allAxioms : RCA0 ⊆ allAxioms := RCA0_subset_WKL0.trans WKL0_subset_allAxioms

theorem ACA0_subset_allAxioms : ACA0 ⊆ allAxioms := ACA0_subset_Z2.trans Z2_subset_allAxioms

/-! ## Well-formedness -/

theorem checkWF_all : (axiomList.map Prod.snd).all (TAssertion.checkWF grammar) = true := by
  decide

/-- Every logical axiom of the database is well formed. -/
theorem wellFormed_all : ∀ B ∈ allAxioms, B.WellFormed grammar := fun _ hB =>
  .of_checkWF (List.all_eq_true.1 checkWF_all _ hB)

theorem wellFormed_base : ∀ B ∈ base, B.WellFormed grammar :=
  fun B hB => wellFormed_all B (base_subset_allAxioms hB)

theorem wellFormed_RCA0 : ∀ B ∈ RCA0, B.WellFormed grammar :=
  fun B hB => wellFormed_all B (RCA0_subset_allAxioms hB)

theorem wellFormed_WKL0 : ∀ B ∈ WKL0, B.WellFormed grammar :=
  fun B hB => wellFormed_all B (WKL0_subset_allAxioms hB)

theorem wellFormed_ACA0 : ∀ B ∈ ACA0, B.WellFormed grammar :=
  fun B hB => wellFormed_all B (ACA0_subset_allAxioms hB)

theorem wellFormed_Z2 : ∀ B ∈ Z2, B.WellFormed grammar :=
  fun B hB => wellFormed_all B (Z2_subset_allAxioms hB)

theorem wellFormed_Z2' : ∀ B ∈ Z2', B.WellFormed grammar :=
  fun B hB => wellFormed_Z2 B (Z2'_subset_Z2 hB)

/-! ## Derivations -/

/-- The universal closure `A. x ( ph <-> ps )` in `ax-dcomp`. -/
abbrev allIff : Tree L V := .node .wal [.node .wb [.var .ph, .var .ps], .var .x]

/-- The comprehension formula `E. X A. x ( x e. X <-> ph )`. -/
abbrev compr : Tree L V := axAcomp.concl.tree

/-- Δ⁰₁-comprehension is derivable in `ACA0` (the tree form of `dcomp-aca`):
arithmetical comprehension applies to the Σ⁰₁ formula through `arith-sig1`,
and `ax-1` with modus ponens adds the antecedent. -/
theorem tderivable_axDcomp : TDerivable grammar ACA0 axDcomp := by
  have mem : ∀ B ∈ ({axIndSig1, axAcomp} : Set (TAssertion L C V)), B ∈ ACA0 :=
    fun _ h => Or.inr h
  have hbase : ∀ B ∈ logicList ++ basicList ++ classList, B ∈ ACA0 := fun _ h => Or.inl h
  -- `arith ph` from `sig1 ph`.
  have d₁ : Nonempty (TDerivation grammar ACA0 axDcomp ⟨.arith, .var .ph⟩) :=
    TDerivation.nonempty_step (B := arithSig1) (hbase _ (by simp [classList])) Tree.var
      (by decide) (by decide) fun e he => by
        simp only [TAssertion.essentials, arithSig1, List.filterMap_cons,
          List.filterMap_nil, List.mem_singleton] at he
        subst he
        exact TDerivation.nonempty_hyp (by decide)
  -- Arithmetical comprehension.
  have d₂ : Nonempty (TDerivation grammar ACA0 axDcomp ⟨.turnstile, compr⟩) :=
    TDerivation.nonempty_step (B := axAcomp) (mem _ (by simp)) Tree.var (by decide)
      (by decide) fun e he => by
        simp only [TAssertion.essentials, axAcomp, List.filterMap_cons,
          List.filterMap_nil, List.mem_singleton] at he
        subst he
        exact d₁
  -- `ax-1`.
  let τ₃ : V → Tree L V := fun
    | .ph => compr
    | .ps => allIff
    | a => .var a
  have d₃ : Nonempty (TDerivation grammar ACA0 axDcomp
      ⟨.turnstile, .node .wi [compr, .node .wi [allIff, compr]]⟩) :=
    TDerivation.nonempty_step (B := ax1) (hbase _ (by simp [logicList])) τ₃ (by decide)
      (by decide) fun e he => by simp [TAssertion.essentials, ax1] at he
  -- Modus ponens.
  let τ₄ : V → Tree L V := fun
    | .ph => compr
    | .ps => .node .wi [allIff, compr]
    | a => .var a
  have d₄ : Nonempty (TDerivation grammar ACA0 axDcomp (axMp.concl.subst τ₄)) :=
    TDerivation.nonempty_step (B := axMp) (hbase _ (by simp [logicList])) τ₄ (by decide)
      (by decide) fun e he => by
        simp only [TAssertion.essentials, axMp, List.filterMap_cons, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        exacts [d₂, d₃]
  exact TDerivable.of_nonempty d₄

/-- Σ⁰₁-induction is an instance of full induction (`ind-sig1-ind`). -/
theorem tderivable_axIndSig1 : TDerivable grammar Z2' axIndSig1 :=
  TDerivable.of_nonempty <| TDerivation.nonempty_step (B := axInd) (Or.inr (by simp)) Tree.var
    (by decide) (by decide) fun e he => by simp [TAssertion.essentials, axInd] at he

/-- Arithmetical comprehension is an instance of full comprehension
(`acomp-comp`). -/
theorem tderivable_axAcomp : TDerivable grammar Z2' axAcomp :=
  TDerivable.of_nonempty <| TDerivation.nonempty_step (B := axComp) (Or.inr (by simp)) Tree.var
    (by decide) (by decide) fun e he => by simp [TAssertion.essentials, axComp] at he

/-! ## The lattice of subsystems -/

/-- A set of well-formed tree assertions. -/
def wf (Γ : Set (TAssertion L C V)) : Set (TWFAssertion grammar) := {A | A.1 ∈ Γ}

theorem toSet_wf {Γ : Set (TAssertion L C V)} (h : ∀ B ∈ Γ, B.WellFormed grammar) :
    TWFAssertion.toSet (wf Γ) = Γ := by
  ext A
  exact ⟨fun ⟨B, hB, e⟩ => e ▸ hB, fun hA => ⟨⟨A, h A hA⟩, hA, rfl⟩⟩

theorem wf_mono {Γ Δ : Set (TAssertion L C V)} (h : Γ ⊆ Δ) : wf Γ ⊆ wf Δ := fun _ hA => h hA

/-- An axiom set of the lattice. -/
abbrev axiomSet (Γ : Set (TAssertion L C V)) : TAxiomSet grammar := TAxiomSet.of (wf Γ)

/-- A tree theory of the lattice. -/
abbrev theory (Γ : Set (TAssertion L C V)) : TTheory grammar := TTheory.of (wf Γ)

theorem axiomSet_le {Γ Δ : Set (TAssertion L C V)} (hΔ : ∀ B ∈ Δ, B.WellFormed grammar)
    (h : ∀ A ∈ Γ, TDerivable grammar Δ A) : axiomSet Γ ≤ axiomSet Δ := by
  intro A hA
  change TDerivable grammar (TWFAssertion.toSet (wf Δ)) A.1
  rw [toSet_wf hΔ]
  exact h A.1 hA

theorem RCA0_le_WKL0 : axiomSet RCA0 ≤ axiomSet WKL0 :=
  TAxiomSet.le_of_subset (wf_mono RCA0_subset_WKL0)

theorem ACA0_le_Z2 : axiomSet ACA0 ≤ axiomSet Z2 :=
  TAxiomSet.le_of_subset (wf_mono ACA0_subset_Z2)

/-- `ACA0` contains `RCA0`: Δ⁰₁-comprehension is derivable from arithmetical
comprehension. -/
theorem RCA0_le_ACA0 : axiomSet RCA0 ≤ axiomSet ACA0 := by
  refine axiomSet_le wellFormed_ACA0 fun A hA => ?_
  rcases hA with hA | hA
  · exact TDerivable.of_mem (Or.inl hA) (wellFormed_base A hA)
  · rcases hA with rfl | rfl
    · exact TDerivable.of_mem (Or.inr (by simp)) (wellFormed_RCA0 _ (Or.inr (by simp)))
    · exact tderivable_axDcomp

theorem RCA0_le_Z2 : axiomSet RCA0 ≤ axiomSet Z2 := RCA0_le_ACA0.trans ACA0_le_Z2

/-- `Z2` is equivalent to `base` with full induction and full comprehension. -/
theorem Z2_equiv : AntisymmRel (· ≤ ·) (axiomSet Z2) (axiomSet Z2') := by
  refine ⟨axiomSet_le wellFormed_Z2' fun A hA => ?_,
    TAxiomSet.le_of_subset (wf_mono Z2'_subset_Z2)⟩
  rcases hA with (hA | hA) | hA
  · exact TDerivable.of_mem (Or.inl hA) (wellFormed_base A hA)
  · rcases hA with rfl | rfl
    exacts [tderivable_axIndSig1, tderivable_axAcomp]
  · exact TDerivable.of_mem (Or.inr hA) (wellFormed_Z2 A (Or.inr hA))

theorem theory_RCA0_le_WKL0 : theory RCA0 ≤ theory WKL0 := TAxiomSet.le_iff_theory.1 RCA0_le_WKL0

theorem theory_RCA0_le_ACA0 : theory RCA0 ≤ theory ACA0 := TAxiomSet.le_iff_theory.1 RCA0_le_ACA0

theorem theory_ACA0_le_Z2 : theory ACA0 ≤ theory Z2 := TAxiomSet.le_iff_theory.1 ACA0_le_Z2

theorem theory_Z2_eq : theory Z2 = theory Z2' := TAxiomSet.antisymmRel_iff.1 Z2_equiv

end SecondOrder

end Silmaril.Logic.Metamath
