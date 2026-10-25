module

public import Silmaril.Logic.SetTheory.Inductive.Classical
public import Silmaril.Logic.SetTheory.Inductive.ZF
public import Silmaril.Logic.SetTheory.Inductive.ZFCChoice

@[expose] public section

/-!
# Choice in the scoped pure membership language

`choiceBody` is set.mm's `ax-ac`, with `x` as its sole free variable.
Binders introduce, successively, `y`, `z`, `w`, `v`, `u`, and `t`.
The declaration is an independent finite syntax tree, not a semantic
predicate or a native Metamath derivability alias.
-/

namespace Silmaril.Logic.SetTheory.Inductive.ZFC

open Formula

/-- The exact choice schema in a one-variable context. -/
def choiceBody : Formula 1 :=
  .ex (.all (.all (.imp (.conj (.mem 1 0) (.mem 0 3))
    (.ex (.all (.iff
      (.ex (.conj (.conj (.mem 1 3) (.mem 3 0)) (.conj (.mem 1 0) (.mem 0 5))))
      (.eq 0 1)))))))

/-- A variable instance of choice; substitution is capture avoiding. -/
def choice {n : Nat} (x : Term n) : Formula n := choiceBody.subst (fun _ => x)

/-- Schema instances are stable under every capture-avoiding variable substitution. -/
theorem choice_subst {n m : Nat} (x : Term n) (σ : Term n → Term m) :
    (choice x).subst σ = choice (σ x) := by
  rw [choice, subst_subst]
  rfl

/-- Universal closure of choice. All quantified objects are sets. -/
def choiceSentence : Sentence := .all choiceBody

/-- Lift the closed choice sentence into any variable context. -/
def closedChoice (n : Nat) : Formula n := choiceSentence.subst Fin.elim0

/-- Additional axiom instances for the choice extension of the ZF calculus. -/
def ChoiceAxiom (n : Nat) (p : Formula n) : Prop :=
  ∃ x : Term n, p = choice x

theorem choiceAxiom_subst {n m : Nat} {p : Formula n} (hp : ChoiceAxiom n p)
    (σ : Term n → Term m) : ChoiceAxiom m (p.subst σ) := by
  obtain ⟨x, rfl⟩ := hp
  exact ⟨σ x, choice_subst x σ⟩

@[simp] theorem choice_zero : choice (0 : Term 1) = choiceBody := by
  have h : (fun _ : Term 1 => (0 : Term 1)) = id :=
    funext fun _ => Subsingleton.elim _ _
  simp [choice, h]

/-- Explicit extension of a nonlogical ZF base, using the same syntax and rules. -/
def extend (Base : Classical.AxiomFamily) : Classical.AxiomFamily :=
  fun n p => Base n p ∨ ChoiceAxiom n p

/-- Adding choice transforms the actual proof object while fixing every formula. -/
noncomputable def fromBase {Base : Classical.AxiomFamily} {n : Nat}
    {Γ : List (Formula n)} {p : Formula n} (d : Classical.Derivation Base Γ p) :
    Classical.Derivation (extend Base) Γ p :=
  d.mono (fun _ _ h => Or.inl h)

/-- An explicit proof of the universally quantified choice assertion. -/
def choiceProof (Base : Classical.AxiomFamily) :
    Classical.Derivation (extend Base) [] choiceSentence := by
  apply Classical.Derivation.allI
  apply Classical.Derivation.ax
  exact Or.inr ⟨0, choice_zero.symm⟩

/-- A variable instance has an axiom proof in every undischarged context. -/
def choiceInstanceProof (Base : Classical.AxiomFamily) {n : Nat}
    (Γ : List (Formula n)) (x : Term n) :
    Classical.Derivation (extend Base) Γ (choice x) :=
  .ax (Or.inr ⟨x, rfl⟩)

/-- Choice and a theorem of the base can be combined without replacing either proof. -/
noncomputable def choiceAndBase {Base : Classical.AxiomFamily} {p : Sentence}
    (d : Classical.Derivation Base [] p) :
    Classical.Derivation (extend Base) [] (.conj choiceSentence p) :=
  .conjI (choiceProof Base) (fromBase d)

/-- Independent ZFC is exactly the choice extension of the shared independent ZF base. -/
def axiomFamily : Classical.AxiomFamily := extend ZF.axiomFamily

/-- ZFC reuses ZF's syntax and proof constructors. -/
abbrev Derivation {n : Nat} := @Classical.Derivation axiomFamily n

/-- Every ZF proof transports to the choice extension on its original formula and context. -/
noncomputable def fromZF {n : Nat} {Γ : List (Formula n)} {p : Formula n}
    (d : ZF.Derivation Γ p) : Derivation Γ p := fromBase d

/-- A genuine closed ZFC proof combining choice with an inherited ZF existence theorem. -/
noncomputable def choiceAndEmptyProof : Derivation [] (.conj choiceSentence ZF.emptySet) :=
  choiceAndBase ZF.emptySetProof

universe u

variable {M : Type u} [Membership M M]

/-- Every index and binder in the independent tree has the intended ax-ac meaning. -/
theorem eval_choiceBody (E : Fin 1 → M) :
    choiceBody.eval E ↔ Choice.AxAC (E 0) := Iff.rfl

/-- Capture-avoiding schema instantiation preserves the designated family variable. -/
theorem eval_choice {n : Nat} (x : Term n) (E : Fin n → M) :
    (choice x).eval E ↔ Choice.AxAC (E x) := by
  rw [choice, eval_subst, eval_choiceBody]
  rfl

/-- The closed formula asserts choice for every set family. -/
theorem holds_choiceSentence :
    choiceSentence.holds (M := M) ↔ ∀ x : M, Choice.AxAC x := by
  simp only [choiceSentence, holds, eval]
  exact forall_congr' fun x => eval_choiceBody (Fin.cons x Fin.elim0)

/-- The closed axiom keeps its meaning when embedded in an open context. -/
theorem eval_closedChoice (n : Nat) (E : Fin n → M) :
    (closedChoice n).eval E ↔ ∀ x : M, Choice.AxAC x := by
  rw [closedChoice, eval_subst]
  have h : E ∘ (Fin.elim0 : Fin 0 → Fin n) = (Fin.elim0 : Fin 0 → M) := by
    funext i
    exact i.elim0
  rw [h]
  exact holds_choiceSentence

/-- Soundness of the additional schema in any membership structure satisfying ax-ac. -/
theorem choiceAxiom_valid (h : ∀ x : M, Choice.AxAC x) {n : Nat} {p : Formula n}
    (hp : ChoiceAxiom n p) (E : Fin n → M) : p.eval E := by
  obtain ⟨x, rfl⟩ := hp
  exact (eval_choice x E).2 (h (E x))

/-- The entire extension is sound over precisely a sound base plus ax-ac. -/
theorem sound {Base : Classical.AxiomFamily}
    (hBase : ∀ n p, Base n p → ∀ E : Fin n → M, p.eval E)
    (hChoice : ∀ x : M, Choice.AxAC x) {n : Nat} {Γ : List (Formula n)}
    {p : Formula n} (d : Classical.Derivation (extend Base) Γ p)
    (E : Fin n → M) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E := by
  apply d.sound _ E hΓ
  intro k q hq F
  rcases hq with hb | hc
  · exact hBase k q hb F
  · exact choiceAxiom_valid hChoice hc F

/-- The intended ambient model satisfies the independently encoded choice sentence. -/
theorem zfSet_choiceSentence : choiceSentence.holds (M := ZFSet.{u}) :=
  holds_choiceSentence.2 Choice.zfSet_axAC

/-- Soundness of independent ZFC in the standard ambient set universe. -/
theorem zfSet_sound {n : Nat} {Γ : List (Formula n)} {p : Formula n}
    (d : Derivation Γ p) (E : Fin n → _root_.ZFSet.{u})
    (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E :=
  sound (ZF.axiom_sound (fun k => SetTheory.zf_zfset (V := Fin k)))
    Choice.zfSet_axAC d E hΓ

end Silmaril.Logic.SetTheory.Inductive.ZFC
