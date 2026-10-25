module

public import Silmaril.Logic.SetTheory.Inductive.Named
public import Silmaril.Logic.SetTheory.Inductive.Classical
public import Silmaril.Logic.SetTheory.ZFSetModel

@[expose] public section

/-!
# Independent syntactic ZF axiom schemata

These are the nine set-theoretic schemata of set.mm's ZF0, transcribed in
finite named syntax and lowered to scoped syntax. In particular `rep` is
set.mm's exact replacement schema (with the inner `A. y`), not a silently
substituted textbook statement. Separation forbids occurrences of its output
and input-set names in its predicate, including bound occurrences: this is
exactly the stronger syntactic Metamath `$d` condition. Arbitrarily many
additional parameter names may occur in the predicate.

The classical calculus is independent and parameterized by this axiom family.
This file proves model soundness, not syntactic completeness or native
conservativity.
-/

namespace Silmaril.Logic.SetTheory.Inductive.ZF

open Named.Formula

namespace Axioms

variable {V : Type*}

/-- Extensionality. -/
def ext (x y z : V) : Named.Formula V :=
  .imp (.all z (.iff (.mem z x) (.mem z y))) (.eq x y)
/-- set.mm replacement, with its shadowing binder preserved. -/
def rep (x y z w : V) (p : Named.Formula V) : Named.Formula V :=
  .imp (.all w (.ex y (.all z (.imp (.all y p) (.eq z y)))))
    (.ex y (.all z (.iff (.mem z y) (.ex w (.conj (.mem w x) (.all y p))))))
/-- Separation. -/
def sep (x y z : V) (p : Named.Formula V) : Named.Formula V :=
  .ex y (.all x (.iff (.mem x y) (.conj (.mem x z) p)))
/-- Empty set. -/
def nul (x y : V) : Named.Formula V := .ex x (.all y (.neg (.mem y x)))
/-- Power-set bounding axiom as stated in set.mm. -/
def pow (x y z w : V) : Named.Formula V :=
  .ex y (.all z (.imp (.all w (.imp (.mem w z) (.mem w x))) (.mem z y)))
/-- Pair bounding axiom as stated in set.mm. -/
def pair (x y z w : V) : Named.Formula V :=
  .ex z (.all w (.imp (.disj (.eq w x) (.eq w y)) (.mem w z)))
/-- Union bounding axiom as stated in set.mm. -/
def union (x y z w : V) : Named.Formula V :=
  .ex y (.all z (.imp (.ex w (.conj (.mem z w) (.mem w x))) (.mem z y)))
/-- Foundation. -/
def reg (x y z : V) : Named.Formula V :=
  .imp (.ex y (.mem y x))
    (.ex y (.conj (.mem y x) (.all z (.imp (.mem z y) (.neg (.mem z x))))))
/-- The weak infinity formulation used by set.mm's primitive ZF axiom list. -/
def inf (x y z w : V) : Named.Formula V :=
  .ex y (.conj (.mem x y) (.all z (.imp (.mem z y) (.ex w (.conj (.mem z w) (.mem w y))))))

end Axioms

/-- Exact nonlogical syntactic schema instances and their parameter conditions. -/
inductive Schema {V : Type*} : Named.Formula V → Prop
  | ext (x y z : V) (distinct : [x, y, z].Nodup) : Schema (Axioms.ext x y z)
  | rep (x y z w : V) (p : Named.Formula V) (distinct : [x, y, z, w].Nodup) :
      Schema (Axioms.rep x y z w p)
  | sep (x y z : V) (p : Named.Formula V) (distinct : [x, y, z].Nodup)
      (outputFresh : y ∉ p.vars) (inputFresh : z ∉ p.vars) : Schema (Axioms.sep x y z p)
  | nul (x y : V) (distinct : [x, y].Nodup) : Schema (Axioms.nul x y)
  | pow (x y z w : V) (distinct : [x, y, z, w].Nodup) : Schema (Axioms.pow x y z w)
  | pair (x y z w : V) (dx : [x, z, w].Nodup) (dy : [y, z, w].Nodup) :
      Schema (Axioms.pair x y z w)
  | union (x y z w : V) (distinct : [x, y, z, w].Nodup) : Schema (Axioms.union x y z w)
  | reg (x y z : V) (distinct : [x, y, z].Nodup) : Schema (Axioms.reg x y z)
  | inf (x y z w : V) (distinct : [x, y, z, w].Nodup) : Schema (Axioms.inf x y z w)

/-- Lowered schema instances in a scoped context. -/
def axiomFamily : Classical.AxiomFamily := fun n p =>
  ∃ k, ∃ q : Named.Formula (Fin k), ∃ σ : Fin k → Option (Fin n),
    Schema q ∧ q.scope σ = some p

/-- Independent classical ZF derivations. -/
abbrev Derivation {n : Nat} := @Classical.Derivation axiomFamily n

/-- Every finite schema is true in any model of the existing semantic ZF axioms. -/
theorem schema_sound {M V : Type*} [Membership M M] [DecidableEq V]
    (hZF : SetTheory.ZF M V) {p : Named.Formula V} (hp : Schema p) : ∀ E : V → M, p.eval E := by
  cases hp with
  | ext x y z h => exact hZF.ext x y z h
  | rep x y z w p h => exact hZF.rep x y z w (fun E => p.eval E) h
  | sep x y z p h hy hz =>
    exact hZF.sep x y z (fun E => p.eval E) h (p.notFree_of_not_mem y hy) (p.notFree_of_not_mem z hz)
  | nul x y _ => exact hZF.nul x y
  | pow x y z w h => exact hZF.pow x y z w h
  | pair x y z w hx hy => exact hZF.pr x y z w hx hy
  | union x y z w h => exact hZF.un x y z w h
  | reg x y z h => exact hZF.reg x y z h
  | inf x y z w h => exact hZF.inf x y z w h

/-- Lowering transports schema truth to the scoped presentation. -/
theorem axiom_sound {M : Type*} [Membership M M] [Nonempty M]
    (hZF : ∀ n, SetTheory.ZF M (Fin n)) :
    ∀ n p, axiomFamily n p → ∀ E : Fin n → M, p.eval E := by
  classical
  rintro n p ⟨k, q, σ, hq, hs⟩ E
  exact (q.eval_scope σ p hs E (_root_.Classical.choice inferInstance)).mpr
    (schema_sound (hZF k) hq _)

/-- Soundness of the independent derivation system in arbitrary ZF models. -/
theorem sound {M : Type*} [Membership M M] [Nonempty M] (hZF : ∀ n, SetTheory.ZF M (Fin n))
    {n : Nat} {Γ : List (Formula n)} {p : Formula n} (d : Derivation Γ p)
    (E : Fin n → M) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E :=
  d.sound (axiom_sound hZF) E hΓ

/-- A model bridge to Mathlib's standard `ZFSet` universe. -/
theorem zfSet_sound {n : Nat} {Γ : List (Formula n)} {p : Formula n} (d : Derivation Γ p)
    (E : Fin n → _root_.ZFSet) (hΓ : ∀ q ∈ Γ, q.eval E) : p.eval E :=
  sound (fun n => SetTheory.zf_zfset (V := Fin n)) d E hΓ

/-- An actual independent proof of any permitted extensionality instance. -/
def extensionality {n : Nat} (x y z : Fin n) (h : [x, y, z].Nodup) :
    Derivation [] ((Axioms.ext x y z).lower id) :=
  .ax ⟨n, _, some ∘ id, .ext x y z h, Named.Formula.scope_total _ id⟩

/-- The closed empty-set axiom is supported with no artificial free variables. -/
def emptySet : Sentence := .ex (.all (.neg (.mem 0 1)))

/-- A genuine axiom inference object in context zero. -/
def emptySetProof : Derivation [] emptySet :=
  .ax ⟨2, Axioms.nul (0 : Fin 2) 1, fun _ => none,
    .nul 0 1 (by decide), by decide⟩

end Silmaril.Logic.SetTheory.Inductive.ZF
