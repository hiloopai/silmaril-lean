module

public import Silmaril.Logic.SetTheory.Inductive.Semantics

@[expose] public section

/-!
# Independent classical natural deduction

Proofs are inductive objects in `Type`. The nonlogical axiom family is an
explicit parameter, so extensions such as ZFC reuse this calculus. Universal
introduction and existential elimination express their eigenvariable condition
by weakening the entire undischarged context. The intuitionistic presentation
can reuse Syntax/Semantics without importing this file.
-/

namespace Silmaril.Logic.SetTheory.Inductive.Classical

open Formula

/-- A family of nonlogical axiom instances at every context size. -/
abbrev AxiomFamily := (n : Nat) → Formula n → Prop

/-- First-order natural deduction, with explicit classical double-negation elimination. -/
inductive Derivation (Ax : AxiomFamily) : {n : Nat} → List (Formula n) → Formula n → Type
  | hyp {n Γ p} (h : p ∈ Γ) : @Derivation Ax n Γ p
  | ax {n Γ p} (h : Ax n p) : @Derivation Ax n Γ p
  | impI {n Γ p q} : @Derivation Ax n (p :: Γ) q → Derivation Ax Γ (.imp p q)
  | impE {n Γ p q} : @Derivation Ax n Γ (.imp p q) → Derivation Ax Γ p → Derivation Ax Γ q
  | botE {n Γ p} : @Derivation Ax n Γ .bot → Derivation Ax Γ p
  | negI {n Γ p} : @Derivation Ax n (p :: Γ) .bot → Derivation Ax Γ (.neg p)
  | negE {n Γ p} : @Derivation Ax n Γ (.neg p) → Derivation Ax Γ p → Derivation Ax Γ .bot
  | dne {n Γ p} : @Derivation Ax n Γ (.neg (.neg p)) → Derivation Ax Γ p
  | conjI {n Γ p q} : @Derivation Ax n Γ p → Derivation Ax Γ q → Derivation Ax Γ (.conj p q)
  | conjL {n Γ p q} : @Derivation Ax n Γ (.conj p q) → Derivation Ax Γ p
  | conjR {n Γ p q} : @Derivation Ax n Γ (.conj p q) → Derivation Ax Γ q
  | disjL {n Γ p q} : @Derivation Ax n Γ p → Derivation Ax Γ (.disj p q)
  | disjR {n Γ p q} : @Derivation Ax n Γ q → Derivation Ax Γ (.disj p q)
  | disjE {n Γ p q r} : @Derivation Ax n Γ (.disj p q) →
      Derivation Ax (p :: Γ) r → Derivation Ax (q :: Γ) r → Derivation Ax Γ r
  | iffI {n Γ p q} : @Derivation Ax n Γ (.imp p q) → Derivation Ax Γ (.imp q p) →
      Derivation Ax Γ (.iff p q)
  | iffL {n Γ p q} : @Derivation Ax n Γ (.iff p q) → Derivation Ax Γ (.imp p q)
  | iffR {n Γ p q} : @Derivation Ax n Γ (.iff p q) → Derivation Ax Γ (.imp q p)
  | allI {n Γ p} : @Derivation Ax (n + 1) (Γ.map Formula.weaken) p →
      @Derivation Ax n Γ (.all p)
  | allE {n Γ p} (t : Term n) : @Derivation Ax n Γ (.all p) → Derivation Ax Γ (p.instantiate t)
  | exI {n Γ p} (t : Term n) : @Derivation Ax n Γ (p.instantiate t) → Derivation Ax Γ (.ex p)
  | exE {n Γ p q} : @Derivation Ax n Γ (.ex p) →
      Derivation Ax (p :: Γ.map Formula.weaken) q.weaken → Derivation Ax Γ q
  | eqRefl {n Γ} (t : Term n) : @Derivation Ax n Γ (.eq t t)
  | eqSub {n Γ} (p : Formula (n + 1)) (x y : Term n) :
      @Derivation Ax n Γ (.eq x y) → Derivation Ax Γ (p.instantiate x) →
      Derivation Ax Γ (p.instantiate y)

namespace Derivation

/-- Extend the nonlogical theory without changing inference objects. -/
noncomputable def mono {Ax Bx : AxiomFamily} (h : ∀ n p, Ax n p → Bx n p)
    {n : Nat} {Γ : List (Formula n)} {p : Formula n} (d : Derivation Ax Γ p) :
    Derivation Bx Γ p := by
  induction d with
  | hyp hp => exact .hyp hp
  | ax hp => exact .ax (h _ _ hp)
  | impI _ ih => exact .impI ih
  | impE _ _ ih iq => exact .impE ih iq
  | botE _ ih => exact .botE ih
  | negI _ ih => exact .negI ih
  | negE _ _ ih iq => exact .negE ih iq
  | dne _ ih => exact .dne ih
  | conjI _ _ ih iq => exact .conjI ih iq
  | conjL _ ih => exact .conjL ih
  | conjR _ ih => exact .conjR ih
  | disjL _ ih => exact .disjL ih
  | disjR _ ih => exact .disjR ih
  | disjE _ _ _ ih ip iq => exact .disjE ih ip iq
  | iffI _ _ ih iq => exact .iffI ih iq
  | iffL _ ih => exact .iffL ih
  | iffR _ ih => exact .iffR ih
  | allI _ ih => exact .allI ih
  | allE t _ ih => exact .allE t ih
  | exI t _ ih => exact .exI t ih
  | exE _ _ ih iq => exact .exE ih iq
  | eqRefl t => exact .eqRefl t
  | eqSub p x y _ _ ih iq => exact .eqSub p x y ih iq

/-- Soundness is conditional on truth of precisely the nonlogical axioms used. -/
theorem sound {M : Type*} [Membership M M] {Ax : AxiomFamily}
    (hAx : ∀ n p, Ax n p → ∀ E : Fin n → M, p.eval E)
    {n : Nat} {Γ : List (Formula n)} {p : Formula n} (d : Derivation Ax Γ p) :
    ∀ E : Fin n → M, (∀ q ∈ Γ, q.eval E) → p.eval E := by
  induction d with
  | hyp hp => exact fun _ hΓ => hΓ _ hp
  | ax hp => exact fun E _ => hAx _ _ hp E
  | impI _ ih =>
    intro E hΓ hp
    exact ih E (by simpa using And.intro hp hΓ)
  | impE _ _ ih iq => exact fun E hΓ => ih E hΓ (iq E hΓ)
  | botE _ ih => exact fun E hΓ => (ih E hΓ).elim
  | negI _ ih =>
    intro E hΓ hp
    exact ih E (by simpa using And.intro hp hΓ)
  | negE _ _ ih iq => exact fun E hΓ => ih E hΓ (iq E hΓ)
  | dne _ ih => exact fun E hΓ => Classical.not_not.mp (ih E hΓ)
  | conjI _ _ ih iq => exact fun E hΓ => ⟨ih E hΓ, iq E hΓ⟩
  | conjL _ ih => exact fun E hΓ => (ih E hΓ).1
  | conjR _ ih => exact fun E hΓ => (ih E hΓ).2
  | disjL _ ih => exact fun E hΓ => Or.inl (ih E hΓ)
  | disjR _ ih => exact fun E hΓ => Or.inr (ih E hΓ)
  | disjE _ _ _ ih ip iq =>
    intro E hΓ
    rcases ih E hΓ with hp | hq
    · exact ip E (by simpa using And.intro hp hΓ)
    · exact iq E (by simpa using And.intro hq hΓ)
  | iffI _ _ ih iq => exact fun E hΓ => ⟨ih E hΓ, iq E hΓ⟩
  | iffL _ ih => exact fun E hΓ => (ih E hΓ).mp
  | iffR _ ih => exact fun E hΓ => (ih E hΓ).mpr
  | allI _ ih =>
    intro E hΓ a
    apply ih (Fin.cons a E)
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact (eval_weaken r E a).mpr (hΓ r hr)
  | allE t _ ih => exact fun E hΓ => (eval_instantiate _ t E).mpr (ih E hΓ (E t))
  | exI t _ ih => exact fun E hΓ => ⟨E t, (eval_instantiate _ t E).mp (ih E hΓ)⟩
  | exE _ _ ih iq =>
    intro E hΓ
    obtain ⟨a, ha⟩ := ih E hΓ
    apply (eval_weaken _ E a).mp
    apply iq (Fin.cons a E)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ha
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact (eval_weaken s E a).mpr (hΓ s hs)
  | eqRefl t => exact fun _ _ => rfl
  | eqSub p x y _ _ ih iq =>
    intro E hΓ
    apply (eval_instantiate p y E).mpr
    have hp := (eval_instantiate p x E).mp (iq E hΓ)
    have he : E x = E y := ih E hΓ
    rwa [he] at hp

/-- Identity has an actual inference object, independently of any theory. -/
def identity {Ax : AxiomFamily} {n : Nat} (p : Formula n) :
    Derivation Ax [] (.imp p p) := .impI (.hyp (by simp))

/-- Universal instantiation followed by implication introduction. -/
def specialize {Ax : AxiomFamily} {n : Nat} (p : Formula (n + 1)) (t : Term n) :
    Derivation Ax [] (.imp (.all p) (p.instantiate t)) :=
  .impI (.allE t (.hyp (by simp)))

end Derivation
end Silmaril.Logic.SetTheory.Inductive.Classical
